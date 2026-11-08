"""Private pointer words remain tracked through exact alias-addressed STR."""
from pathlib import Path
import struct
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import conditional_local_buffer_profile as local

R0 = match.ARM_REG_R0
LOCAL, SAVED = (False, False, True), (False, True, False)
BASE, CALLEE = 0x08001000, 0x08005B6C


def proof(policy=local.SCHEDULER_PAYLOAD, calls=None):
    result = object.__new__(local.ConditionalLocalBufferProof)
    result.policy, result.stack_arguments = policy, True
    result.calls, result.observations = dict(calls or {}), {}
    result.environment, result.runtime_dependencies = {}, []
    return result


def body(*, descriptor=4, middle=(), store=0x6050, before_store=()):
    # push {r4,lr}; sub sp,#32; mov r0,sp; add r2,sp,#descriptor;
    # str r0,[r2,#4]; movs r0,#0; bl scheduler; restore frame and return.
    data = struct.pack('<'+'H'*(6+len(middle)+len(before_store)),
        0xB510, 0xB088, 0x4668, 0xAA00+descriptor//4,
        *before_store, store, *middle, 0x2000)
    site = BASE+len(data)
    displacement = CALLEE-site-4
    data += struct.pack('<HH', 0xF000 | ((displacement >> 12) & 0x7FF),
                        0xF800 | ((displacement >> 1) & 0x7FF))
    data += struct.pack('<HHHH', 0xB008, 0xBC10, 0xBC02, 0x4708)
    return data, {site: CALLEE}


class PayloadPointerStoreTests(unittest.TestCase):
    def store(self, stack, slots, *, offset=-32, value=-40, width=4,
              policy=local.SCHEDULER_PAYLOAD, returns=()):
        return match.stack_alias_store(stack, slots, {R0: value}, set(returns),
            offset, width, R0, pointer_proof=proof(policy))

    def verify(self, data, calls, policy=local.SCHEDULER_PAYLOAD):
        context = proof(policy, calls)
        result = match.verify_leaf_instructions(data, BASE, True, calls, buffer_proof=context)
        return result, context

    def test_full_word_records_exact_pointer_and_clears_return_provenance(self):
        stack, slots = [LOCAL]*8+[SAVED]*2, {}
        stack[2] = (True, False, True)
        self.assertTrue(self.store(stack, slots))
        self.assertEqual(slots, {-32: -40})
        self.assertEqual(stack[2], LOCAL)
        self.assertEqual(stack[-2:], [SAVED]*2)

    def test_default_and_other_contracts_keep_pointer_store_refusal(self):
        for context in (None, proof(local.SCHEDULER), proof(local.STATE), proof(local.OUTPUT)):
            stack, slots = [LOCAL]*8+[SAVED]*2, {}
            with self.subTest(context=context), self.assertRaisesRegex(ValueError, 'stored or spilled'):
                match.stack_alias_store(stack, slots, {R0: -40}, set(), -32, 4, R0,
                                       pointer_proof=context)
            self.assertEqual(slots, {})
            self.assertEqual(stack, [LOCAL]*8+[SAVED]*2)

    def test_pointer_width_alignment_and_bounds_refuse_without_mutation(self):
        for offset, width in ((-32, 1), (-32, 2), (-31, 4), (-44, 4), (0, 4)):
            stack, slots = [LOCAL]*8+[SAVED]*2, {}
            with self.subTest(offset=offset, width=width), self.assertRaises(ValueError):
                self.store(stack, slots, offset=offset, width=width)
            self.assertEqual((stack, slots), ([LOCAL]*8+[SAVED]*2, {}))

    def test_source_must_address_live_aligned_private_word(self):
        for value in (-44, -39, -8, -4, 0, 4):
            stack, slots = [LOCAL]*8+[SAVED]*2, {}
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.store(stack, slots, value=value)
            self.assertEqual((stack, slots), ([LOCAL]*8+[SAVED]*2, {}))

    def test_saved_or_caller_destination_is_not_private(self):
        for offset in (-8, -4, 0, 4):
            stack, slots = [LOCAL]*8+[SAVED]*2, {}
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.store(stack, slots, offset=offset)
            self.assertEqual((stack, slots), ([LOCAL]*8+[SAVED]*2, {}))

    def test_conflicting_return_and_pointer_provenance_is_rejected(self):
        stack, slots = [LOCAL]*8+[SAVED]*2, {}
        with self.assertRaisesRegex(ValueError, 'provenance'):
            self.store(stack, slots, returns=(R0,))
        self.assertEqual((stack, slots), ([LOCAL]*8+[SAVED]*2, {}))

    def test_full_scalar_overwrite_removes_new_pointer_word(self):
        stack, slots = [LOCAL]*8+[SAVED]*2, {}
        self.store(stack, slots)
        match.stack_alias_store(stack, slots, {}, {R0+1}, -32, 4, R0+1)
        self.assertEqual(slots, {})
        self.assertEqual(stack[2], (True, False, True))

    def test_partial_overwrite_cannot_forget_new_pointer_word(self):
        stack, slots = [LOCAL]*8+[SAVED]*2, {}
        self.store(stack, slots)
        for offset, width in ((-32, 1), (-31, 1), (-30, 2)):
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError, 'partial access'):
                match.stack_alias_store(stack, slots, {}, set(), offset, width, R0+1)
            self.assertEqual(slots, {-32: -40})

    def test_complete_raw_thumb_frame_reaches_exact_payload_contract(self):
        data, calls = body()
        self.assertEqual(data[8:10], bytes.fromhex('5060'))
        _, context = self.verify(data, calls)
        observation = context.contract_manifest()['observations'][0]
        self.assertEqual(observation['pointer_words'], [(-32, -40)])
        self.assertEqual((observation['local_offset'], observation['payload_offset'],
                          observation['payload_frame_bytes']), (-36, -40, 4))
        self.assertFalse(context.contract_manifest()['actual_callback_effects_proved'])

    def test_complete_raw_thumb_default_still_rejects_same_store(self):
        data, calls = body()
        with self.assertRaisesRegex(ValueError, 'stored or spilled'):
            match.verify_leaf_instructions(data, BASE, True, calls)

    def test_extra_pointer_word_is_visible_to_scheduler_call_check(self):
        data, calls = body(middle=(0x6090,))  # str r0,[r2,#8]
        with self.assertRaisesRegex(ValueError, r'one descriptor\+4 word'):
            self.verify(data, calls)

    def test_pointer_reload_cannot_hide_extra_outgoing_alias(self):
        data, calls = body(middle=(0x6851,))  # ldr r1,[r2,#4]
        with self.assertRaisesRegex(ValueError, 'additional register aliases'):
            self.verify(data, calls)

    def test_partial_following_store_is_rejected_in_complete_cfg(self):
        data, calls = body(middle=(0x7111,))  # strb r1,[r2,#4]
        with self.assertRaisesRegex(ValueError, 'partial access'):
            self.verify(data, calls)

    def test_pointer_store_into_saved_lr_is_rejected_in_complete_cfg(self):
        data, calls = body(descriptor=32)  # destination is SP+36, saved LR
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            self.verify(data, calls)

    def test_unknown_destination_does_not_gain_pointer_store_permission(self):
        data, calls = body(before_store=(0x2200,))  # movs r2,#0
        with self.assertRaisesRegex(ValueError, 'use or escape'):
            self.verify(data, calls)

    def test_stm_pointer_spill_remains_outside_new_single_store_scope(self):
        data, calls = body(store=0xC201)  # stmia r2!,{r0}
        with self.assertRaisesRegex(ValueError, 'stored or spilled'):
            self.verify(data, calls)


if __name__ == '__main__':
    unittest.main(verbosity=2)
