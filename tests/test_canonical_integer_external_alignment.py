"""Authenticate assembler alignment outside an original integer owner's FUNC."""
import hashlib
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import canonical_integer_native_profile as native
import match
import owner_admission_profile as owner
from test_canonical_integer_native_profile import BASE, fixture, symbol_change


def padded(family='__umodsi3', tail=(0x46C0,)):
    values = fixture(family, suffix=(0xBC02, 0x4708, *tail))
    for slot in (0, 1):
        values[slot] = symbol_change(values[slot], f'func_{BASE:08X}', 'size', 10)
    rows = json.loads(values[4])
    rows[0].update(end=f'0x{BASE+10:08X}', instrs=4)
    values[4] = json.dumps(rows).encode()
    values[5] = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
        f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
        for row in rows).encode()
    return values


def section_field(raw, field, value):
    result = bytearray(raw)
    image = match.elf_image(raw)
    headers = struct.unpack_from('<I', raw, 32)[0]
    struct.pack_into('<I', result, headers+40*image['text_index']+4*field, value)
    return bytes(result)


class ExternalAlignmentTests(unittest.TestCase):
    def setUp(self):
        environment = patch.object(native, 'environment_fingerprint', return_value={'synthetic': True})
        environment.start()
        self.addCleanup(environment.stop)
        closure = patch.object(native.scalar, 'prove_called_closures', return_value=({}, {}, []))
        self.prove = closure.start()
        self.addCleanup(closure.stop)

    def test_external_nop_is_authenticated_but_not_part_of_complete_FUNC(self):
        values = padded()
        result, count = native.verify_original(*values)
        self.assertEqual(count, 4)
        self.assertEqual(result['original_ET_REL_sha256'], hashlib.sha256(values[0]).hexdigest())
        self.assertEqual(result['linked_ELF_sha256'], hashlib.sha256(values[1]).hexdigest())
        self.assertEqual(len(match.elf_image(values[0])['text']), 12)
        self.assertFalse(result['prerequisite']['arithmetic_C_equivalence'])
        self.assertFalse(result['prerequisite']['memory_safety_claim'])
        self.assertEqual(self.prove.call_args.args[-1], {'__umodsi3'})

    def test_other_real_compiler_integer_aliases_keep_the_same_boundary(self):
        for family in ('__udivsi3', '__divsi3', '__modsi3'):
            with self.subTest(family=family):
                result, count = native.verify_original(*padded(family))
                self.assertEqual(count, 4)
                self.assertEqual(result['prerequisite']['runtime_families'], [family])

    def test_other_terminal_instruction_is_not_assembler_alignment(self):
        for tail in ((0x0000,), (0x4770,)):
            with self.subTest(tail=tail), self.assertRaises(ValueError):
                native.verify_original(*padded(tail=tail))
        self.prove.assert_not_called()

    def test_more_than_two_external_bytes_refuses(self):
        with self.assertRaises(ValueError):
            native.verify_original(*padded(tail=(0x46C0, 0x46C0)))
        self.prove.assert_not_called()

    def test_original_section_must_have_real_four_byte_alignment(self):
        values = padded()
        values[0] = section_field(values[0], 8, 2)
        with self.assertRaises(ValueError):
            native.verify_original(*values)
        self.prove.assert_not_called()

    def test_external_bytes_cannot_have_a_symbol_owner(self):
        values = padded()
        original = bytearray(values[0])
        image = match.elf_image(values[0])
        for number, symbols in image['symbol_tables'].items():
            section = image['sections'][number]
            for index, symbol in enumerate(symbols):
                if symbol['type'] == 3 and symbol['section'] == image['text_index']:
                    struct.pack_into('<I', original, section[4]+16*index+4, 10)
        values[0] = bytes(original)
        with self.assertRaises(ValueError):
            native.verify_original(*values)
        self.prove.assert_not_called()

    def test_relocation_must_remain_wholly_inside_sized_function(self):
        values = padded()
        original = bytearray(values[0])
        image = match.elf_image(values[0])
        section = image['sections'][next(iter(image['relocations']))]
        struct.pack_into('<I', original, section[4], 8)
        values[0] = bytes(original)
        with self.assertRaises(ValueError):
            native.verify_original(*values)
        self.prove.assert_not_called()

    def test_linker_cannot_change_the_external_nop(self):
        values = padded()
        linked = bytearray(values[1])
        image = match.elf_image(values[1])
        linked[image['sections'][image['text_index']][4]+10] ^= 1
        values[1] = bytes(linked)
        with self.assertRaises(ValueError):
            native.verify_original(*values)
        self.prove.assert_not_called()

    def test_linked_section_alignment_is_authenticated_too(self):
        values = padded()
        values[1] = section_field(values[1], 8, 2)
        with self.assertRaises(ValueError):
            native.verify_original(*values)
        self.prove.assert_not_called()

    def test_ordinary_owner_selector_does_not_gain_alignment_permission(self):
        values = padded()
        with self.assertRaises(ValueError):
            owner.original_bindings(match.elf_image(values[0]), BASE, values[3], values[4], b'{}',
                selector=owner.SELECTOR, index=values[5])


if __name__ == '__main__':
    unittest.main()
