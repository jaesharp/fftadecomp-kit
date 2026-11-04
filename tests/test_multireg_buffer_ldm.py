"""Synthetic live-buffer LDM transfers; no compiler or original ROM inputs."""
import json
import os
from pathlib import Path
import struct
import sys
from types import SimpleNamespace
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
if os.environ.get('FFTA_BASE_TOOLS'):
    sys.path.insert(1, os.environ['FFTA_BASE_TOOLS'])
import match
from capstone.arm_const import ARM_CC_NE
from protected_descriptor_word_profile import ProtectedDescriptorWordProof

BASE = 0x08000000
R0, R1, R2, R3, R4, R5, R6, R7 = (
    match.ARM_REG_R0 + number for number in range(8))


def body(*words):
    return struct.pack('<' + 'H' * len(words), *words)


def instruction(encoded=0xC838):
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    return next(decoder.disasm(body(encoded), BASE))


class WordPolicyProof(match.BufferCallProof):
    """Use the existing exact-word policy in the synthetic alias-replay unit."""
    word_provenance = True
    word_memory = ProtectedDescriptorWordProof.word_memory
    prune_words = ProtectedDescriptorWordProof.prune_words

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.word_reads = {}


def replay(middle, *, offset=-28, stack=None, aliases=None, constants=None,
           protected=(), proof_type=match.BufferCallProof, words=None,
           stack_arguments=True, watched=()):
    # Preserve the loaded callee-saved registers and the real entry return.
    code = body(0xB5F0, *middle, 0xBCF0, 0xBC02, 0x4708)
    mapping = json.dumps([{'rom': f'0x{BASE:08X}',
                           'end': f'0x{BASE + len(code):08X}',
                           'mode': 'thumb', 'instrs': len(code) // 2}]).encode()
    proof = proof_type(code, mapping, stack_arguments=stack_arguments)
    local = [(False, False, True)] * 7 if stack is None else stack
    arguments = {R0: offset} if aliases is None else aliases
    return proof.check_arguments(BASE, arguments, local, {}, frozenset(protected),
                                 constants=constants, words=words,
                                 frame_base=-4 * len(local), root_frame=BASE,
                                 watched=watched)


@unittest.skipIf(hasattr(match, 'thumb_buffer_alias_ldm'), 'retained production-baseline checks')
class BaselineGapTests(unittest.TestCase):
    def test_three_word_read_has_existing_alias_refusal(self):
        with self.assertRaisesRegex(ValueError, 'unsupported buffer pointer use or escape'):
            replay([0xC838])

    def test_two_three_word_reads_and_final_word_have_existing_alias_refusal(self):
        with self.assertRaisesRegex(ValueError, 'unsupported buffer pointer use or escape'):
            replay([0xC838, 0xC838, 0x6802])


class MultiregBufferLdmTests(unittest.TestCase):
    def test_three_word_read_retains_exact_base_writeback(self):
        self.assertEqual(replay([0xC838]), {R0: -16})

    def test_two_three_word_reads_and_final_word_fit_live_28_bytes(self):
        self.assertEqual(replay([0xC838, 0xC838, 0x6802]), {R0: -4})

    def test_two_and_seven_word_lists_use_their_actual_transfer_sizes(self):
        self.assertEqual(replay([0xC80C]), {R0: -20})
        self.assertEqual(replay([0xC8FE]), {R0: 0})

    def test_post_writeback_scalar_access_checks_the_new_address(self):
        self.assertEqual(replay([0xC838, 0x6802], offset=-16), {R0: -4})
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            replay([0xC838, 0x6842], offset=-16)
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            replay([0xC838, 0x7802], offset=-12)

    def test_each_loaded_destination_loses_old_alias_facts(self):
        # r3 used to be a stack pointer. A scalar load replaces that value,
        # so the following ordinary external scalar store cannot leak it.
        self.assertEqual(replay([0xC838, 0x6013],
                                aliases={R0: -28, R3: -16}), {R0: -16})

    def test_loaded_destination_cannot_retain_an_old_index_constant(self):
        with self.assertRaisesRegex(ValueError, 'buffer index is not a known scalar constant'):
            replay([0xC838, 0x5CC2], constants={R3: 0})

    def test_misaligned_and_partially_out_of_range_reads_fail(self):
        for offset in (-27, -8):
            with self.subTest(offset=offset), self.assertRaisesRegex(
                    ValueError, 'unaligned or outside allocated local words'):
                replay([0xC838], offset=offset)

    def test_read_cannot_cross_a_saved_or_nonlocal_stack_word(self):
        local = [(False, False, True)] * 7
        local[1] = (False, True, False)
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            replay([0xC838], stack=local)

    def test_every_word_is_checked_for_pointer_slot_overlap(self):
        for slot in (-28, -24, -20):
            with self.subTest(slot=slot), self.assertRaisesRegex(
                    ValueError, 'pointer-bearing argument slot'):
                replay([0xC838], protected={slot})

    def test_word_provenance_composition_stays_closed(self):
        for facts in ({}, {-24: ('pointer', -16)}, {-24: ('constant', 7)}):
            with self.subTest(facts=facts), self.assertRaisesRegex(
                    ValueError, 'multi-register buffer LDM excludes word-provenance contexts'):
                replay([0xC838], proof_type=WordPolicyProof,
                       protected={-24}, words=facts)

    def test_existing_exact_word_initialization_requirement_stays_enforced(self):
        with self.assertRaisesRegex(ValueError, 'lacks an exact surviving word value'):
            replay([0x6803], proof_type=WordPolicyProof,
                   protected={-28}, words={})

    def test_existing_alias_store_escape_stays_rejected(self):
        with self.assertRaisesRegex(ValueError, 'buffer pointers cannot be stored or spilled'):
            replay([0xC838, 0x6000])

    def test_existing_alias_return_boundary_stays_rejected(self):
        with self.assertRaisesRegex(ValueError, 'buffer pointer escapes through a return register'):
            replay([0xC838], stack_arguments=False)

    def test_existing_live_register_preservation_stays_rejected(self):
        with self.assertRaisesRegex(ValueError, 'preservation of a live alias register'):
            replay([0xC838], watched={R3})

    def test_following_stm_copy_is_not_admitted_by_read_support(self):
        # A second live-buffer alias is not permission to add block writes.
        with self.assertRaisesRegex(ValueError, 'unsupported buffer pointer use or escape'):
            replay([0xC838, 0xC138], aliases={R0: -28, R1: -16})

    def test_indirect_callback_is_not_admitted_by_read_support(self):
        # bx r2 is neither a known return nor a proved callback target.
        with self.assertRaisesRegex(ValueError, 'indirect control flow|verified return'):
            replay([0xC838, 0x4710])

    def test_separate_frame_ldm_policy_remains_single_word(self):
        with self.assertRaisesRegex(ValueError, 'unsupported stack-alias LDM encoding or register list'):
            match.thumb_stack_alias_ldm(instruction(), {R0: -28}, 7)

    def test_single_word_buffer_policy_is_not_broadened(self):
        with self.assertRaisesRegex(ValueError, 'unsupported buffer-alias LDM encoding or register list'):
            replay([0xC808])

    def test_unknown_base_does_not_gain_local_buffer_identity(self):
        self.assertIsNone(match.thumb_buffer_alias_ldm(instruction(), {R1: -28}))

    def test_real_base_in_list_form_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'unsupported buffer-alias LDM encoding or register list'):
            match.thumb_buffer_alias_ldm(instruction(0xC809), {R0: -28})

    def test_noncanonical_or_unpredictable_instruction_shapes_fail(self):
        item = instruction()
        attributes = {name: getattr(item, name) for name in (
            'size', 'bytes', 'mnemonic', 'writeback', 'cc', 'operands', 'regs_access')}
        mutations = [
            {'size': 4, 'bytes': b'\xb0\xe8\x38\x00'},
            {'writeback': False},
            {'cc': ARM_CC_NE},
            {'mnemonic': 'ldmdb'},
            {'bytes': body(0xC800), 'operands': item.operands[:1]},
            {'operands': [item.operands[0], *reversed(item.operands[1:])]},
            {'regs_access': lambda: ([R0, R3], [R0, R3, R4, R5])},
            {'regs_access': lambda: ([R0], [R3, R4, R5])},
        ]
        for mutation in mutations:
            with self.subTest(mutation=mutation), self.assertRaisesRegex(
                    ValueError, 'unsupported buffer-alias LDM encoding or register list'):
                match.thumb_buffer_alias_ldm(SimpleNamespace(**{**attributes, **mutation}),
                                             {R0: -28})

    def test_sp_pc_and_shifted_operand_shapes_fail(self):
        item = instruction()
        attributes = {name: getattr(item, name) for name in (
            'size', 'bytes', 'mnemonic', 'writeback', 'cc', 'operands', 'regs_access')}
        def operand(original, **changes):
            return SimpleNamespace(**{
                'type': original.type, 'reg': original.reg,
                'shift': original.shift, 'subtracted': original.subtracted, **changes})
        for base in (match.ARM_REG_SP, match.ARM_REG_PC):
            operands = [operand(item.operands[0], reg=base), *item.operands[1:]]
            with self.subTest(base=base), self.assertRaisesRegex(ValueError, 'unsupported buffer-alias LDM'):
                match.thumb_buffer_alias_ldm(SimpleNamespace(**{**attributes, 'operands': operands}),
                                             {base: -28})
        operands = list(item.operands)
        operands[1] = operand(operands[1], shift=SimpleNamespace(type=1, value=1))
        with self.assertRaisesRegex(ValueError, 'unsupported buffer-alias LDM'):
            match.thumb_buffer_alias_ldm(SimpleNamespace(**{**attributes, 'operands': operands}),
                                         {R0: -28})


if __name__ == '__main__':
    unittest.main()
