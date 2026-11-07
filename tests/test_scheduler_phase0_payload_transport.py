"""New symbolic phase0 payload states, with the retained independent oracle."""
from dataclasses import replace
import copy
import unittest

import scheduler_zero40_state as zero
import scheduler_small_entry_state as small
import test_scheduler_zero40_state as fixtures


def fixture():
    result = fixtures.fixture()
    result['phase0_transport_policy'] = zero.PHASE0_TRANSPORT
    return result


def unknowns(f, *, counter=True, tag=True):
    if counter:
        f['cells'][fixtures.SUBJECT] = ('opaque-byte', 'phase0 arbitrary counter', 0)
        f['cells'][fixtures.SUBJECT+1] = ('opaque-byte', 'phase0 arbitrary counter', 1)
    if tag:
        f['cells'][fixtures.SUBJECT+2] = ('opaque-byte', 'phase0 arbitrary type byte', 0)


class Phase0PayloadTransportTests(unittest.TestCase):
    def assert_oracle(self, f, result):
        regs, memory, trace, events, pc = fixtures.raw(f)
        self.assertEqual(result['trace'], trace)
        self.assertEqual(result['final_PC'], pc)
        self.assertEqual({i:fixtures.number(v,f['arena_base']) for i,v in result['registers'].items()}, regs)
        self.assertEqual({f['arena_base']+int(k):fixtures.byte(v,f['arena_base'])
                          for k,v in result['post_cells'].items()}, memory)
        actual = [(row['site'], row['operation'], row['coordinate'],
                   tuple(fixtures.byte(v,f['arena_base']) for v in row['bytes']))
                  for row in result['memory_events'] if 'coordinate' in row]
        self.assertEqual(actual, events)

    def test_arbitrary_tag_byte_is_transported_without_a_numeric_fact(self):
        f = fixture(); unknowns(f, counter=False)
        result = zero.derive(**f)
        self.assertIsNone(result['boundary'])
        self.assertEqual(result['post_cells'][str(fixtures.NODE+26)], f['cells'][fixtures.SUBJECT+2])
        self.assertEqual([row['operation'] for row in result['opaque_payload_events']], ['read','write'])
        self.assert_oracle(f, result)

    def test_arbitrary_counter_halfword_preserves_both_origins(self):
        f = fixture(); unknowns(f, tag=False)
        result = zero.derive(**f)
        self.assertIsNone(result['boundary'])
        self.assertEqual([result['post_cells'][str(fixtures.NODE+24+i)] for i in range(2)],
                         [f['cells'][fixtures.SUBJECT+i] for i in range(2)])
        self.assertEqual([row['width'] for row in result['opaque_payload_events']], [2,2])
        self.assert_oracle(f, result)

    def test_all_phase0_fields_remain_symbolic_on_the_real_ordered_path(self):
        f = fixture(); unknowns(f)
        before = copy.deepcopy(f)
        result = zero.derive(**f)
        self.assertIsNone(result['boundary'])
        self.assertEqual(f, before)
        self.assertEqual(result['callback_observed_phase'], 0)
        cb = f['layout'].prior.callback
        contract = result['phase0_payload_transport']
        self.assertEqual([pc for pc in result['trace'] if cb <= pc < cb+136],
                         contract['conditional_callback_path'])
        self.assertEqual(len(contract['conditional_callback_path']), 23)
        self.assertEqual([row['site'] for row in result['opaque_payload_events']],
                         [cb+42,cb+44,cb+50,cb+52])
        self.assertEqual(tuple(result['post_cells'][str(fixtures.NODE+28+i)] for i in range(4)),
                         tuple(f['cells'][fixtures.SUBJECT+4+i] for i in range(4)))
        self.assert_oracle(f, result)

    def test_explicit_transport_contract_does_not_grant_call_authority(self):
        f = fixture(); unknowns(f)
        contract = zero.phase0_transport_contract(f['layout'], selector=zero.PHASE0_TRANSPORT)
        self.assertEqual(len(contract['complete_owner_pins']), 10)
        self.assertEqual([row['width'] for row in contract['ordered_payload_transfers']], [1,4,2])
        for field in ('actual_phase_reaching_proved', 'nested_pointer_nonescape_proved',
                      'actual_physical_access_proved', 'native_admission'):
            self.assertFalse(contract[field])

    def test_default_policy_retains_the_opaque_narrow_load_refusal(self):
        f = fixture(); unknowns(f)
        del f['phase0_transport_policy']
        result = zero.derive(**f)
        self.assertEqual(result['boundary']['site'], f['layout'].prior.callback+42)
        self.assertIn('scalar field', result['boundary']['reason'])
        self.assertNotIn('phase0_payload_transport', result)

    def test_transport_requires_the_exact_versioned_selector(self):
        for selector in (True, 1, {}, 'other'):
            f = fixture(); f['phase0_transport_policy'] = selector
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'transport selector'):
                zero.derive(**f)

    def test_complete_callback_mutation_is_rejected_before_transport(self):
        f = fixture(); p = f['layout'].prior
        changed = p.callback_data[:-1] + bytes([p.callback_data[-1] ^ 1])
        f['layout'] = replace(f['layout'], prior=replace(p, callback_data=changed))
        with self.assertRaisesRegex(ValueError, 'callback shape differs'):
            zero.phase0_transport_contract(f['layout'], selector=zero.PHASE0_TRANSPORT)

    def test_narrow_pointer_fragments_are_bytes_without_address_authority(self):
        f = fixture()
        pointer = fixtures.pointer(1232)
        for offset in range(3):f['cells'][fixtures.SUBJECT+offset] = pointer[offset]
        result = zero.derive(**f)
        self.assertIsNone(result['boundary'])
        field = tuple(result['post_cells'][str(fixtures.NODE+24+i)] for i in range(4))
        self.assertEqual(field[:3], pointer[:3])
        self.assertEqual(zero.words.observe(field)['kind'], 'opaque-or-partial')
        self.assert_oracle(f, result)

    def test_opaque_nested_pointer_still_refuses_at_the_address_observation(self):
        f = fixture(); unknowns(f)
        fixtures.put(f['cells'], fixtures.E+8, fixtures.opaque('opaque nested pointer'))
        result = zero.derive(**f)
        self.assertEqual(result['boundary']['site'], f['layout'].prior.callback+42)
        self.assertIn('provenance', result['boundary']['reason'])
        self.assertEqual(result['opaque_payload_events'], [])

    def test_numeric_pointer_bits_do_not_replace_common_base_provenance(self):
        f = fixture(); unknowns(f)
        fixtures.put(f['cells'], fixtures.E+8, fixtures.integer(fixtures.BASE+fixtures.SUBJECT))
        result = zero.derive(**f)
        self.assertEqual(result['boundary']['site'], f['layout'].prior.callback+42)
        self.assertIn('provenance', result['boundary']['reason'])

    def test_missing_counter_byte_refuses_after_the_earlier_real_writes(self):
        f = fixture(); unknowns(f)
        del f['cells'][fixtures.SUBJECT+1]
        result = zero.derive(**f)
        self.assertEqual(result['boundary']['site'], f['layout'].prior.callback+50)
        self.assertIn('reaching byte origins', result['boundary']['reason'])
        self.assertEqual(result['post_cells'][str(fixtures.NODE+26)], f['cells'][fixtures.SUBJECT+2])
        self.assertEqual(tuple(result['post_cells'][str(fixtures.NODE+28+i)] for i in range(4)),
                         tuple(f['cells'][fixtures.SUBJECT+4+i] for i in range(4)))
        self.assertFalse(result['conditional_returns']['callback'])

    def test_unread_high_byte_is_neither_required_nor_interpreted(self):
        f = fixture(); unknowns(f)
        f['cells'][fixtures.SUBJECT+3] = ('opaque-byte', 'unread high byte', 0)
        result = zero.derive(**f)
        self.assertIsNone(result['boundary'])
        cb = f['layout'].prior.callback
        reads = [row for row in result['memory_events'] if cb <= row['site'] < cb+136
                 and row['operation'].startswith('read')]
        self.assertFalse(any(row['coordinate'] <= fixtures.SUBJECT+3 <
                             row['coordinate']+len(row['bytes']) for row in reads))

    def test_transport_policy_cannot_bypass_protected_zero_writes(self):
        f = fixture(); unknowns(f)
        f['protected_spans'] = ((fixtures.NODE+26,fixtures.NODE+27),)
        result = zero.derive(**f)
        self.assertIn('protected', result['boundary']['reason'])
        self.assertFalse(result['callback_entered'])
        self.assertNotIn(str(fixtures.NODE+26), result['changed_cells'])
        self.assertEqual(result['opaque_payload_events'], [])

    def test_copy_and_payload_aliases_use_post_write_bytes_and_real_saved_words(self):
        f = fixture(); unknowns(f)
        f['registers'][0] = f['registers'][7] = fixtures.pointer(fixtures.E-48)
        # Copy word two overlaps the allocation's callback word. Its actual
        # reloaded value must still name the complete bound Thumb callback.
        fixtures.put(f['cells'], fixtures.E+12, fixtures.integer(f['layout'].prior.callback|1))
        result = zero.derive(**f)
        self.assertIsNone(result['boundary'])
        self.assertEqual([row['width'] for row in result['opaque_payload_events']], [1,1,2,2])
        # The scheduler's final phase flag and tag share its saved R8 word.
        self.assertEqual(result['registers'][8], (0,1,42,0))
        self.assertFalse(result['ABI_preservation_assumed'])
        self.assert_oracle(f, result)

    def test_corrupted_saved_return_is_not_repaired_after_symbolic_payload_writes(self):
        f = fixture(); unknowns(f)
        f['registers'][0] = f['registers'][7] = fixtures.pointer(fixtures.E-32)
        fixtures.put(f['cells'], fixtures.E+28, fixtures.integer(f['layout'].prior.callback|1))
        result = zero.derive(**f)
        self.assertTrue(result['conditional_returns']['callback'])
        self.assertFalse(result['conditional_returns']['scheduler'])
        self.assertIsNotNone(result['boundary'])
        self.assertIn('scalar/control', result['boundary']['reason'])
        self.assertEqual(len(result['opaque_payload_events']), 4)

    def test_payload_pointer_transport_does_not_claim_nonescape(self):
        f = fixture(); unknowns(f)
        fixtures.put(f['cells'], fixtures.SUBJECT+4, fixtures.pointer(fixtures.E-52))
        result = zero.derive(**f)
        self.assertIsNone(result['boundary'])
        payload = tuple(result['post_cells'][str(fixtures.NODE+28+i)] for i in range(4))
        self.assertEqual(payload, fixtures.pointer(fixtures.E-52))
        self.assertFalse(result['phase0_payload_transport']['nested_pointer_nonescape_proved'])
        self.assertFalse(result['actual_lifetime_proved'])

    def test_consume_new_cutpoint_without_replaying_the_prefix_producer(self):
        f = fixture(); unknowns(f)
        r = f['registers']; l = f['layout']; s = l.prior.scheduler.address
        thunk = l.prior.scheduler.allocator.allocator.thunk
        report = dict(schema=small.SELECTOR, starts_at=s, allocation_count=40,
            reaches_unproved_installed_call=True, registers=r, entry_SP=fixtures.E,
            complete_owner_pins=zero.phase0_transport_contract(l, selector=zero.PHASE0_TRANSPORT)['complete_owner_pins'],
            boundary={'site':thunk}, post_cells={str(k):v for k,v in f['cells'].items()},
            retired_spans=[], obligations=['unproved actual reaching'],
            nested_call_cutpoint=dict(call_site=s+48, thunk=thunk,target=l.image_base,
                target_word=l.image_base|1,callee_executed=False,SP=fixtures.E-56,
                return_word=r[14],register_arguments={i:r[i] for i in range(4)}))
        before = copy.deepcopy(report)
        result = zero.continue_from_078(l, fixtures.BASE, report, selector=zero.SELECTOR,
                                       phase0_transport_policy=zero.PHASE0_TRANSPORT)
        self.assertIsNone(result['boundary'])
        self.assertEqual(report, before)
        self.assertEqual(result['inherited_078_obligations'], ['unproved actual reaching'])
        self.assertFalse(result['actual_078_reaching_authentication_proved'])


if __name__ == '__main__':
    unittest.main()
