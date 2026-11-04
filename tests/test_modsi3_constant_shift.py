"""Constant-shift nonzero facts must survive only proven control-flow paths."""

from pathlib import Path
import struct
import sys
import unittest

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_JUMP
from capstone.arm_const import ARM_CC_AL, ARM_INS_BX

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from modsi3_profile import prove_operands


class ConstantShiftTests(unittest.TestCase):
    def prove(self, words):
        address = 0x08010000
        data = bytearray()
        sites = set()
        for word in words:
            if isinstance(word, str):
                if word == 'remainder':
                    sites.add(address + len(data))
                data.extend(struct.pack('<HH', 0xF000, 0xF800))
            else:
                data.extend(struct.pack('<H', word))
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
        return prove_operands(instructions, edges, address, sites)

    def reject(self, words):
        with self.assertRaisesRegex(ValueError, 'signed16 r0 and nonzero r1'):
            self.prove(words)

    def test_constant_divisor_shift(self):
        # asrs r0,#16; movs r1,#188; lsls r1,#1 -> divisor 376.
        self.prove([0x1400, 0x21BC, 0x0049, 'remainder', 0x4770])

    def test_different_source_and_register_copy(self):
        self.prove([0x1400, 0x22BC, 0x0051, 'remainder', 0x4770])
        self.prove([0x1400, 0x22BC, 0x0011, 0x0049, 'remainder', 0x4770])

    def test_shift_wraps_to_zero(self):
        self.reject([0x1400, 0x2180, 0x0649, 'remainder', 0x4770])
        self.reject([0x1400, 0x2100, 0x0049, 'remainder', 0x4770])

    def test_negative_word_remains_nonzero(self):
        self.prove([0x1400, 0x21FF, 0x07C9, 'remainder', 0x4770])

    def test_nonzero_without_constant_is_insufficient(self):
        # A nonzero input can become zero after a wrapping left shift.
        self.reject([0x1400, 0x2900, 0xD002, 0x0049, 'remainder', 0x4770])

    def test_call_and_overwrite_kill_constant(self):
        self.reject([0x21BC, 'ordinary', 0x1400, 0x0049, 'remainder', 0x4770])
        self.reject([0x1400, 0x21BC, 0x2100, 0x0049, 'remainder', 0x4770])

    def test_join_requires_same_constant_on_every_path(self):
        prefix = [0x1400, 0x2A00, 0xD001, 0x21BC, 0xE000]
        suffix = [0x0049, 'remainder', 0x4770]
        self.prove(prefix + [0x21BC] + suffix)
        self.reject(prefix + [0x2100] + suffix)
        self.reject(prefix + [0x2101] + suffix)

    def test_register_shift_stays_conservative(self):
        self.reject([0x1400, 0x21BC, 0x2201, 0x4091, 'remainder', 0x4770])


if __name__ == '__main__':
    unittest.main()
