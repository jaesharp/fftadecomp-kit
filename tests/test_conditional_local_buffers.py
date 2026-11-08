"""The opt-in contracts preserve frame bounds and expose their assumptions."""
import hashlib
from pathlib import Path
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import conditional_local_buffer_profile as local
import named_data_buffer_profile as named
import owner_admission_profile as owner

R0 = match.ARM_REG_R0
LOCAL = (False, False, True)
SAVED = (False, True, False)


def proof(policy, calls):
    result = object.__new__(local.ConditionalLocalBufferProof)
    result.policy, result.calls, result.observations = policy, calls, {}
    result.runtime_dependencies = []
    result.environment = {}
    return result


def bound_output(calls, body, pinned):
    """Run the real OUTPUT bind_root with only ROM/index access stubbed."""
    result = object.__new__(local.ConditionalLocalBufferProof)
    result.policy, result.rom, result.entries = local.OUTPUT, b'', []
    result.mapping = result.index = b''
    result.dependencies, result.records, result.identities = {}, {}, {}
    result.span = lambda target: body
    with mock.patch.dict(local.DEPENDENCIES, {local.OUTPUT_CALLEE: pinned}), \
            mock.patch.object(local.named, 'validate_owner'), \
            mock.patch.object(local.graph, 'graph', return_value=({}, None, {}, dict(calls), {})), \
            mock.patch.object(owner, 'refine'), \
            mock.patch('known_query_native_closure_profile.environment_fingerprint', return_value={}):
        result.bind_root(b'', 0x08080EB8, calls)
    return result


class ConditionalLocalBufferTests(unittest.TestCase):
    def test_scheduler_accepts_complete_descriptor_and_preserved_alias(self):
        p = proof(local.SCHEDULER, {100: 0x08005B6C})
        stack = [LOCAL]*7 + [SAVED]*4
        self.assertEqual(p.check_call(0x08005B6C, {R0+2: -44, R0+4: -44}, stack, site=100), {})
        manifest = p.contract_manifest()
        self.assertFalse(manifest['actual_callback_effects_proved'])
        self.assertFalse(manifest['nonescape_proved'])
        self.assertIn('ambient original R9', ' '.join(manifest['assumptions']))

    def test_scheduler_rejects_short_descriptor_and_saved_words(self):
        for offset in (-48, -40, -16, -4, 0):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                proof(local.SCHEDULER, {100: 0x08005B6C}).check_call(
                    0x08005B6C, {R0+2: offset}, [LOCAL]*7+[SAVED]*4, site=100)

    def test_scheduler_rejects_extra_argument_and_pointer_words(self):
        for aliases, slots in (({R0+2: -44, R0: -44}, None),
                               ({R0+2: -44}, {-40: -44})):
            with self.subTest(aliases=aliases, slots=slots), self.assertRaises(ValueError):
                proof(local.SCHEDULER, {100: 0x08005B6C}).check_call(
                    0x08005B6C, aliases, [LOCAL]*7+[SAVED]*4, slots, site=100)

    def test_state_clear_requires_constant_four_and_complete_local_word(self):
        p = proof(local.STATE, {100: 0x0814224C})
        self.assertEqual(p.check_call(0x0814224C, {R0: -20}, [LOCAL]*3+[SAVED]*2,
                                     constants={R0+1: 4}, site=100), {})
        self.assertIn('not a proof', ' '.join(p.contract_manifest()['assumptions']))
        for constants in ({}, {R0+1: 8}):
            with self.subTest(constants=constants), self.assertRaises(ValueError):
                p.check_call(0x0814224C, {R0: -20}, [LOCAL]*3+[SAVED]*2,
                             constants=constants, site=100)

    def test_visitor_requires_exact_pointer_word(self):
        p = proof(local.STATE, {100: 0x080C7CC0})
        self.assertEqual(p.check_call(0x080C7CC0, {R0+2: -16}, [LOCAL]*3+[SAVED]*2,
                                     {-16: -20}, site=100), {})
        for slots in ({}, {-16: -12}, {-12: -20}):
            with self.subTest(slots=slots), self.assertRaises(ValueError):
                p.check_call(0x080C7CC0, {R0+2: -16}, [LOCAL]*3+[SAVED]*2, slots, site=100)

    def test_output_word_accepts_single_local_result_word(self):
        p = proof(local.OUTPUT, {100: 0x080799C0})
        stack = [LOCAL] + [SAVED]*3
        self.assertEqual(p.check_call(0x080799C0, {R0+2: -16}, stack, site=100), {})
        self.assertEqual(p.check_call(0x080799C0, {R0+2: -16}, stack, site=100), {})
        manifest = p.contract_manifest()
        self.assertFalse(manifest['actual_callback_effects_proved'])
        self.assertFalse(manifest['nonescape_proved'])
        self.assertIn('not alias-analysed', ' '.join(manifest['assumptions']))
        self.assertEqual(manifest['observations'][0]['bytes'], 4)
        self.assertEqual(manifest['observations'][0]['observed_store_bytes'], 2)

    def test_output_word_rejects_offsets_outside_its_local_word(self):
        for offset in (-20, -14, -12, -4, 0):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                proof(local.OUTPUT, {100: 0x080799C0}).check_call(
                    0x080799C0, {R0+2: offset}, [LOCAL]+[SAVED]*3, site=100)
        # The alias and count checks pass here; only the local-word check refuses.
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            proof(local.OUTPUT, {100: 0x080799C0}).check_call(
                0x080799C0, {R0+2: -16}, [SAVED, LOCAL, SAVED, SAVED], site=100)

    def test_output_word_rejects_extra_aliases_slots_and_wider_frames(self):
        for aliases, stack, slots in (({R0+2: -16, R0: -16}, [LOCAL]+[SAVED]*3, None),
                                      ({R0+2: -16, R0+1: -16}, [LOCAL]+[SAVED]*3, None),
                                      ({R0+2: -16, R0+4: -16}, [LOCAL]+[SAVED]*3, None),
                                      ({R0: -16}, [LOCAL]+[SAVED]*3, None),
                                      ({R0+2: -16}, [LOCAL]+[SAVED]*3, {-16: -16}),
                                      ({R0+2: -20}, [LOCAL]*2+[SAVED]*3, None)):
            with self.subTest(aliases=aliases, slots=slots), self.assertRaises(ValueError):
                proof(local.OUTPUT, {100: 0x080799C0}).check_call(
                    0x080799C0, aliases, stack, slots, site=100)

    def test_output_word_rejects_other_targets_and_sites(self):
        p = proof(local.OUTPUT, {100: 0x080799C0})
        for address, site in ((0x0808CBDC, 100), (0x080799C0, 102)):
            with self.subTest(address=address, site=site), self.assertRaises(ValueError):
                p.check_call(address, {R0+2: -16}, [LOCAL]+[SAVED]*3, site=site)
        with self.assertRaises(ValueError):
            p.contract_manifest()
        with self.assertRaises(ValueError):
            p.check_indirect_target(local.thunk.ALIASES['_call_via_r2'], {}, (), site=100)

    def test_output_word_bind_root_accepts_one_pinned_callee(self):
        body = bytes(range(256))*6 + bytes(212)
        p = bound_output({100: 0x080799C0}, body, (1748, hashlib.sha256(body).hexdigest()))
        self.assertEqual(p.dependencies, {0x080799C0: body})
        self.assertEqual(p.records[0x080799C0]['bytes'], 1748)
        self.assertEqual(p.runtime_dependencies, [])

    def test_output_word_bind_root_rejects_call_shape(self):
        body = bytes(1748)
        pinned = (1748, hashlib.sha256(body).hexdigest())
        for calls in ({100: 0x080799C0, 120: 0x080799C0}, {100: 0x0808CBDC},
                      {100: 0x080799C0, 120: 0x0808CBDC}, {}):
            with self.subTest(calls=calls), self.assertRaisesRegex(ValueError, 'one actual indexed output-word call'):
                bound_output(calls, body, pinned)

    def test_output_word_bind_root_rejects_callee_identity(self):
        body = bytes(range(256))*6 + bytes(212)
        flipped = bytearray(body)
        flipped[100] ^= 1
        short = body[:-2]
        for actual, pinned in ((bytes(flipped), (1748, hashlib.sha256(body).hexdigest())),
                               (short, (1748, hashlib.sha256(short).hexdigest()))):
            with self.subTest(size=len(actual)), self.assertRaisesRegex(ValueError, 'dependency identity differs'):
                bound_output({100: 0x080799C0}, actual, pinned)

    def test_unauthenticated_site_and_unobserved_call_refused(self):
        p = proof(local.SCHEDULER, {100: 0x08005B6C})
        with self.assertRaises(ValueError):
            p.check_call(0x08005B6C, {R0+2: -44}, [LOCAL]*7+[SAVED]*4, site=102)
        with self.assertRaises(ValueError):
            p.contract_manifest()

    def test_indirect_target_cannot_be_local_or_saved_return(self):
        p = proof(local.STATE, {100: 0x0814224C})
        p.check_indirect_target(0x0814224C, {R0: -20}, {match.ARM_REG_LR}, site=100)
        for aliases, returns in (({R0+2: -20}, ()), ({}, (R0+2,))):
            with self.subTest(aliases=aliases, returns=returns), self.assertRaises(ValueError):
                p.check_indirect_target(0x0814224C, aliases, returns, site=100)

    def test_profile_report_selection_is_explicit(self):
        for policy, schema in local.SCHEMAS.items():
            self.assertIn(policy, named.SELECTORS)
            self.assertEqual(owner.selector_for_report(f'* verification: `{schema}`'), policy)
        self.assertFalse(named.conditional_thunk_replay(None))

    def test_selectors_are_registered_with_dispatch_and_cli(self):
        self.assertEqual(named.LOCAL_CALL_SELECTORS, local.SELECTORS)
        source = (Path(match.__file__).read_text(encoding='utf-8'))
        line, = [row for row in source.splitlines() if '"--owner-runtime-profile", choices=(' in row]
        for policy in local.SELECTORS:
            self.assertIn(f'"{policy}"', line)


if __name__ == '__main__':
    unittest.main()
