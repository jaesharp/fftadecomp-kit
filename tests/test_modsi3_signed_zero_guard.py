"""Signed zero comparisons establish nonzero only on strict CFG edges."""

from pathlib import Path
import struct
import sys
import unittest

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_JUMP
from capstone.arm_const import ARM_CC_AL, ARM_INS_BX

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from modsi3_profile import prove_operands


class SignedZeroGuardTests(unittest.TestCase):
    def prove(self, program):
        address = 0x08010000
        labels, offset = {}, 0
        for item in program:
            if isinstance(item, str) and item.endswith(':'):
                labels[item[:-1]] = address + offset
            else:
                offset += 4 if item in ('ordinary', 'remainder') else 2
        data, sites = bytearray(), set()
        for item in program:
            if isinstance(item, str) and item.endswith(':'):
                continue
            if item in ('ordinary', 'remainder'):
                if item == 'remainder':
                    sites.add(address + len(data))
                data.extend(struct.pack('<HH', 0xF000, 0xF800))
            elif isinstance(item, tuple):
                condition, label = item
                displacement = labels[label] - (address + len(data) + 4)
                assert displacement % 2 == 0
                if condition is None:
                    assert -2048 <= displacement <= 2046
                    word = 0xE000 | ((displacement // 2) & 0x7FF)
                else:
                    assert -256 <= displacement <= 254
                    word = 0xD000 | condition << 8 | ((displacement // 2) & 0xFF)
                data.extend(struct.pack('<H', word))
            else:
                data.extend(struct.pack('<H', item))
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        instructions = {ins.address: ins for ins in decoder.disasm(bytes(data), address)}
        edges = {}
        for current, ins in instructions.items():
            following = current + ins.size
            if ins.id == ARM_INS_BX:
                edges[current] = []
            elif ins.group(CS_GRP_JUMP):
                edges[current] = [ins.operands[0].imm]
                if ins.cc != ARM_CC_AL:
                    edges[current].append(following)
            else:
                edges[current] = [following]
        assert sites and all(site in instructions for site in sites)
        return prove_operands(instructions, edges, address, sites)

    def reject(self, program):
        with self.assertRaisesRegex(ValueError, 'signed16 r0 and nonzero r1'):
            self.prove(program)

    def guarded(self, condition, *, taken=False, compare=0x42B5,
                zero=0x2500, before_compare=(), after_compare=(), body=()):
        prefix = [0x1C0E, zero, *before_compare, compare, *after_compare]
        calls = [*body, 'ordinary', 0x0400, 0x1400, 0x1C31,
                 'remainder', 0x4770]
        if taken:
            return prefix + [(condition, 'body'), 0x4770, 'body:', *calls]
        return prefix + [(condition, 'exit'), *calls, 'exit:', 0x4770]

    def test_count_guard_survives_call_and_loop_backedge(self):
        # Initial r5 == 0; falling through signed r5 >= r6 proves r6 > 0.
        self.prove([0x1C0E, 0x2500, 0x42B5, (10, 'exit'),
                    'loop:', 'ordinary', 0x0400, 0x1400, 0x1C31,
                    'remainder', 0x3501, 0x42B5, (11, 'loop'),
                    'exit:', 0x4770])

    def test_strict_taken_edges_in_both_operand_orders(self):
        for condition in (1, 11, 12):  # ne, lt, gt
            for compare in (0x42B5, 0x42AE):  # cmp r5,r6; cmp r6,r5
                with self.subTest(condition=condition, compare=compare):
                    self.prove(self.guarded(condition, taken=True, compare=compare))

    def test_strict_fallthrough_edges_in_both_operand_orders(self):
        for condition in (0, 10, 13):  # eq, ge, le
            for compare in (0x42B5, 0x42AE):
                with self.subTest(condition=condition, compare=compare):
                    self.prove(self.guarded(condition, compare=compare))

    def test_immediate_zero_guards(self):
        for condition in (0, 10, 13):
            with self.subTest(condition=condition):
                self.prove(self.guarded(condition, compare=0x2E00))

    def test_edges_including_equality_are_rejected(self):
        for condition, taken in ((0, True), (10, True), (13, True),
                                 (1, False), (11, False), (12, False)):
            for compare in (0x42B5, 0x42AE):
                with self.subTest(condition=condition, taken=taken, compare=compare):
                    self.reject(self.guarded(condition, taken=taken, compare=compare))

    def test_nonzero_or_unknown_comparison_operand_is_rejected(self):
        self.reject(self.guarded(10, zero=0x2501))
        self.reject(self.guarded(10, zero=0x1C15))  # r5 = unknown r2
        self.reject(self.guarded(10, compare=0x2E01))

    def test_overwritten_zero_fact_is_rejected(self):
        self.reject(self.guarded(10, before_compare=(0x2501,)))
        # r2, unlike r5/r6, does not preserve its zero fact across a call.
        self.reject(self.guarded(10, zero=0x2200, compare=0x42B2,
                                 before_compare=('ordinary',)))

    def test_divisor_overwrite_is_rejected(self):
        self.reject(self.guarded(10, body=(0x2600,)))

    def test_caller_clobbered_divisor_is_rejected(self):
        self.reject([0x1C0A, 0x2500, 0x4295, (10, 'exit'),
                     'ordinary', 0x0400, 0x1400, 0x1C11,
                     'remainder', 'exit:', 0x4770])

    def test_nonadjacent_or_overwritten_flags_are_rejected(self):
        self.reject(self.guarded(10, after_compare=(0x4624,)))
        self.reject(self.guarded(10, after_compare=(0x2400,)))

    def test_comparison_bypass_is_rejected(self):
        self.reject([0x1C0E, 0x2500, 0x2B00, (0, 'guard'),
                     0x42B5, 'guard:', (10, 'exit'),
                     'ordinary', 0x0400, 0x1400, 0x1C31,
                     'remainder', 'exit:', 0x4770])

    def test_unguarded_join_is_rejected(self):
        self.reject([0x1C0E, 0x2B00, (0, 'body'), 0x2500,
                     0x42B5, (10, 'exit'), 'body:',
                     'ordinary', 0x0400, 0x1400, 0x1C31,
                     'remainder', 'exit:', 0x4770])

    def test_backedge_divisor_kill_is_rejected(self):
        self.reject([0x1C0E, 0x2500, 0x42B5, (10, 'exit'),
                     'loop:', 'ordinary', 0x0400, 0x1400, 0x1C31,
                     'remainder', 0x2600, (None, 'loop'), 'exit:', 0x4770])


if __name__ == '__main__':
    unittest.main()
