"""Descriptor-origin observation barriers, independent of heap executions."""
from dataclasses import replace
import unittest

import scheduler_allocator_descriptor_prefix as model
import test_scheduler_small_entry_state as layouts


class DescriptorPrefixTests(unittest.TestCase):
    def layout(self):
        return layouts.layout().scheduler

    def test_nonzero_descriptor_handoff_and_fresh_local_overwrite(self):
        layout = self.layout()
        result = model.prove(layout, 12, selector=model.SELECTOR)
        self.assertEqual(result['derived_allocator_request_bytes'], 40)
        self.assertEqual(result['wrapper_prefix']['handoff_site'], layout.allocator.address+34)
        core = result['allocator_prefix']
        self.assertEqual(core['overwrite_site'], layout.allocator.allocator.address+14)
        self.assertEqual(core['private_frame_bytes_at_overwrite'], 32)
        self.assertEqual(core['new_R3_SP_displacement'], 4)
        self.assertEqual(core['new_R3_entry_SP_offset'], -28)
        self.assertFalse(core['new_R3_is_scalar'])
        self.assertTrue(core['new_R3_still_has_alias_obligations'])
        self.assertEqual(core['incoming_R3_read_sites'], [])
        self.assertEqual(core['incoming_R3_spill_sites'], [])

    def test_both_wrapper_rounding_paths_are_checked(self):
        layout = self.layout()
        result = model.prove(layout, 13, selector=model.SELECTOR)
        prefix = result['wrapper_prefix']
        self.assertTrue(prefix['rounding_alternatives_checked'])
        self.assertEqual(prefix['complete_instructions'], 26)
        self.assertTrue(all(layout.allocator.address+off in prefix['sites'] for off in (18,20,22,24,26,28)))
        self.assertNotIn(layout.allocator.address+8, prefix['sites'])

    def test_original_input_and_sixteen_bit_request_wrap_are_distinct(self):
        layout = self.layout()
        for value, expected in [(0,28), (65535,27), (2**32-1,27), (65536,28)]:
            with self.subTest(value=value):
                result = model.prove(layout, value, selector=model.SELECTOR)
                self.assertEqual(result['incoming_R2_condition'], value)
                self.assertEqual(result['derived_allocator_request_bytes'], expected)

    def test_zero_derived_request_does_not_gain_an_erasure_claim(self):
        layout = self.layout()
        for value in (65508, 131044):
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, 'zero request'):
                model.prove(layout, value, selector=model.SELECTOR)

    def test_selector_and_exact_numeric_premise_are_required(self):
        layout = self.layout()
        for selector in (True, {}, 'other'):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                model.prove(layout, 12, selector=selector)
        for value in (True, -1, 2**32, None):
            with self.subTest(value=value), self.assertRaises(ValueError):
                model.prove(layout, value, selector=model.SELECTOR)

    def test_mutated_complete_scheduler_identity_is_rejected(self):
        layout = replace(self.layout(), sha256='0'*64)
        with self.assertRaisesRegex(ValueError, 'scheduler identity'):
            model.prove(layout, 12, selector=model.SELECTOR)

    def test_mutated_complete_allocator_identity_is_rejected(self):
        layout = self.layout()
        core = replace(layout.allocator.allocator, sha256='0'*64)
        layout = replace(layout, allocator=replace(layout.allocator, allocator=core))
        with self.assertRaisesRegex(ValueError, 'identity'):
            model.prove(layout, 12, selector=model.SELECTOR)

    def test_alias_read_or_spill_before_overwrite_is_rejected(self):
        for raw in ('002b', '0360', '08b4', '181c'):
            with self.subTest(raw=raw), self.assertRaisesRegex(ValueError, 'observed'):
                model._core_prefix(bytes.fromhex(raw+'01ab'), 0x08000000)

    def test_call_or_branch_before_overwrite_is_rejected(self):
        for raw in ('00f000f8', '00e0', '1847'):
            with self.subTest(raw=raw), self.assertRaisesRegex(ValueError, 'control transfer'):
                model._core_prefix(bytes.fromhex(raw+'01ab'), 0x08000000)

    def test_unallocated_or_saved_word_is_not_a_fresh_local_pointer(self):
        for raw in ('01ab', '10b501ab', '81b001ab'):
            with self.subTest(raw=raw), self.assertRaisesRegex(ValueError, 'allocated local'):
                model._core_prefix(bytes.fromhex(raw), 0x08000000)

    def test_absent_overwrite_or_arbitrary_scalar_kill_is_rejected(self):
        for raw, message in [('0020', 'no descriptor'), ('0023', 'fresh allocated local')]:
            with self.subTest(raw=raw), self.assertRaisesRegex(ValueError, message):
                model._core_prefix(bytes.fromhex(raw), 0x08000000)

    def test_origin_prefix_does_not_grant_allocator_or_scheduler_admission(self):
        result = model.prove(self.layout(), 12, selector=model.SELECTOR)
        for name in ('actual_incoming_R2_proved', 'zero_request_shortcut_supported',
                     'whole_allocator_effects_proved', 'allocator_return_proved',
                     'physical_or_saved_memory_separation_proved',
                     'actual_pointer_nonescape_proved', 'native_admission'):
            self.assertFalse(result[name], name)
        self.assertFalse(result['scheduler_handoff']['R9_preservation_proved'])
        self.assertTrue(result['tracked_incoming_R3_origin_removed_at_overwrite'])
        self.assertTrue(result['all_other_origin_and_alias_obligations_unchanged'])
