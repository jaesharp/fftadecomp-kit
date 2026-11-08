"""The opt-in contracts preserve frame bounds and expose their assumptions."""
from pathlib import Path
import hashlib
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


FRAME = 'private frame holding the complete descriptor'
ADJACENT = 'exactly the descriptor and one adjacent nonempty payload'
POINTER = r'one descriptor\+4 word addressing the payload'
SCHEDULER_BODY, ALLOCATOR_BODY = bytes(range(60)), bytes(range(206))
PINNED = {0x08005B6C: (60, hashlib.sha256(SCHEDULER_BODY).hexdigest()),
          0x08005954: (206, hashlib.sha256(ALLOCATOR_BODY).hexdigest())}


def bound_scheduler(calls, bodies=None):
    """Run the real payload-scheduler bind_root with only ROM/index access stubbed."""
    bodies = {0x08005B6C: SCHEDULER_BODY, 0x08005954: ALLOCATOR_BODY, **(bodies or {})}
    result = object.__new__(local.ConditionalLocalBufferProof)
    result.policy, result.rom, result.entries = local.SCHEDULER_PAYLOAD, b'', []
    result.mapping = result.index = b''
    result.dependencies, result.records, result.identities = {}, {}, {}
    result.span = lambda target: bodies.get(target, b'\x00\x00')
    with mock.patch.dict(local.DEPENDENCIES, PINNED), \
            mock.patch.object(local.named, 'validate_owner'), \
            mock.patch.object(local.graph, 'graph', return_value=({}, None, {}, dict(calls), {})), \
            mock.patch.object(local.thunk, 'dependencies', return_value=[]), \
            mock.patch.object(owner, 'refine'), \
            mock.patch('known_query_native_closure_profile.environment_fingerprint', return_value={}):
        result.bind_root(b'', 0x080DF9AC, calls)
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

    def test_scheduler_payload_root_records_both_pinned_dependencies(self):
        p = bound_scheduler({0x080DF9AC+40: 0x08005B6C})
        self.assertEqual(sorted(p.records), [0x08005954, 0x08005B6C])
        self.assertEqual(p.calls, {0x080DF9AC+40: 0x08005B6C})

    def test_scheduler_payload_root_refuses_guard_call_and_other_callees(self):
        # 0x08115AE4 shape: a guard call before the scheduler call.
        for calls in ({0x08115AE4+10: 0x080DD494, 0x08115AE4+34: 0x08005B6C},
                      {0x080DF9AC+40: 0x080DD494}, {}):
            with self.subTest(calls=calls), \
                    self.assertRaisesRegex(ValueError, 'one actual scheduler call'):
                bound_scheduler(calls)

    def test_scheduler_payload_root_refuses_wrong_dependency_body(self):
        for target, body in ((0x08005B6C, bytes(60)), (0x08005954, ALLOCATOR_BODY[:-2])):
            with self.subTest(target=hex(target)), \
                    self.assertRaisesRegex(ValueError, 'dependency identity differs'):
                bound_scheduler({0x080DF9AC+40: 0x08005B6C}, {target: body})

    def test_scheduler_payload_accepts_one_pointer_word_to_trailing_payload(self):
        # 0x080DF9AC: descriptor at sp, 12-byte payload at sp+0x1C, r4 keeps the payload.
        p = proof(local.SCHEDULER_PAYLOAD, {100: 0x08005B6C})
        stack = [LOCAL]*10 + [SAVED]*4
        self.assertEqual(p.check_call(0x08005B6C, {R0+2: -56, R0+4: -28}, stack,
                                      {-52: -28}, site=100), {})
        manifest = p.contract_manifest()
        observation = manifest['observations'][0]
        self.assertEqual((observation['payload_offset'], observation['payload_frame_bytes'],
                          observation['payload_extent']), (-28, 12, 'remaining-private-frame'))
        self.assertEqual(manifest['schema'], local.SCHEMAS[local.SCHEDULER_PAYLOAD])
        self.assertFalse(manifest['actual_callback_effects_proved'])
        self.assertFalse(manifest['nonescape_proved'])
        self.assertIn('premises, not proofs', ' '.join(manifest['assumptions']))
        self.assertIn('initialization is not checked', ' '.join(manifest['assumptions']))

    def test_scheduler_payload_records_sixteen_byte_extent(self):
        p = proof(local.SCHEDULER_PAYLOAD, {100: 0x08005B6C})
        p.check_call(0x08005B6C, {R0+2: -60}, [LOCAL]*11+[SAVED]*4, {-56: -32}, site=100)
        self.assertEqual(p.observations[100]['payload_frame_bytes'], 16)

    def test_scheduler_payload_accepts_payload_below_descriptor(self):
        # 0x080DE0AC: 12-byte payload at sp, descriptor at sp+0xC up to the saved words.
        p = proof(local.SCHEDULER_PAYLOAD, {100: 0x08005B6C})
        p.check_call(0x08005B6C, {R0+2: -44}, [LOCAL]*10+[SAVED]*4, {-40: -56}, site=100)
        self.assertEqual((p.observations[100]['payload_offset'], p.observations[100]['payload_frame_bytes']), (-56, 12))

    def test_scheduler_payload_rejects_descriptor_between_private_words(self):
        for aliases, slots in (({R0+2: -52}, {-48: -56}), ({R0+2: -52}, {-48: -24}),
                               ({R0+2: -48}, {-44: -56})):
            with self.subTest(aliases=aliases, slots=slots), self.assertRaisesRegex(ValueError, ADJACENT):
                proof(local.SCHEDULER_PAYLOAD, {100: 0x08005B6C}).check_call(
                    0x08005B6C, aliases, [LOCAL]*10+[SAVED]*4, slots, site=100)

    def test_scheduler_payload_rejects_near_miss_pointer_words(self):
        stack = [LOCAL]*10 + [SAVED]*4
        cases = [(-56, slots) for slots in (None, {}, {-48: -28}, {-52: -32}, {-52: -56}, {-52: -12},
                                            {-52: -28, -48: -28}, {-52: -28, -24: -56})]
        cases += [(-44, {-40: -52}), (-44, {-40: -16})]  # payload below the descriptor
        for descriptor, slots in cases:
            with self.subTest(descriptor=descriptor, slots=slots), self.assertRaisesRegex(ValueError, POINTER):
                proof(local.SCHEDULER_PAYLOAD, {100: 0x08005B6C}).check_call(
                    0x08005B6C, {R0+2: descriptor}, stack, slots, site=100)

    def test_scheduler_payload_rejects_other_frames_and_aliases(self):
        cases = (({R0+2: -56, R0: -28}, [LOCAL]*10+[SAVED]*4, {-52: -28}, 'additional register aliases'),
                 ({R0+2: -52}, [LOCAL]*10+[SAVED]*4, {-48: -24}, ADJACENT),         # descriptor inside the frame
                 ({R0+2: -44}, [LOCAL]*7+[SAVED]*4, {-40: -16}, ADJACENT),          # empty payload
                 ({R0+2: -56}, [LOCAL]*9+[SAVED]+[LOCAL]+[SAVED]*3, {-52: -28}, FRAME),  # saved word inside
                 ({R0+2: -56}, [LOCAL]*10+[SAVED]*4, {-52: -28, -36: -40}, POINTER),  # second pointer word
                 ({R0+2: -54}, [LOCAL]*10+[SAVED]*4, {-50: -26}, FRAME),            # unaligned descriptor
                 ({R0+2: -40}, [LOCAL]*10+[SAVED]*4, {-36: -56}, FRAME),            # descriptor overflows frame
                 ({R0+2: -16}, [SAVED]*4, {-12: -16}, FRAME))                       # no private words
        for aliases, stack, slots, reason in cases:
            with self.subTest(aliases=aliases, slots=slots), self.assertRaisesRegex(ValueError, reason):
                proof(local.SCHEDULER_PAYLOAD, {100: 0x08005B6C}).check_call(
                    0x08005B6C, aliases, stack, slots, site=100)

    def test_descriptor_only_scheduler_still_refuses_payload_word(self):
        with self.assertRaises(ValueError):
            proof(local.SCHEDULER, {100: 0x08005B6C}).check_call(
                0x08005B6C, {R0+2: -56}, [LOCAL]*10+[SAVED]*4, {-52: -28}, site=100)

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


if __name__ == '__main__':
    unittest.main()
