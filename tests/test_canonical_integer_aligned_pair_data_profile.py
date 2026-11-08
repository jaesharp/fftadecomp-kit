"""New aligned named-data ELF fixtures; no actual-ROM producer is replayed."""
import argparse
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import Mock, patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import canonical_integer_aligned_pair_data_profile as native
import canonical_integer_two_words_native_profile as strict
import match
import owner_admission_profile as owner
from test_canonical_integer_native_profile import symbol_change
from test_typed_switch_outgoing_frame import relocatable

BASE = 0x08000100
POINT = 0x02001000
OBJECTS = json.dumps({'g_aligned': f'0x{POINT:08X}'}).encode()


def fixture(*, read=0x9902, first=0x9801, padding=True):
    target = native.inventory.OPERATIONS['__divsi3']
    delta = target - (BASE + 12)
    body = struct.pack('<8HI3H', 0xB500, first, read, 0x4A02,
        0xF000 | ((delta >> 12) & 0x7ff), 0xF800 | ((delta >> 1) & 0x7ff),
        0xE002, 0, POINT, 0x2000, 0xBC02, 0x4708)
    rows = [dict(rom=f'0x{BASE:08X}', end=f'0x{BASE+26:08X}', mode='thumb', instrs=9),
            dict(rom=f'0x{target:08X}', end=f'0x{target+2:08X}', mode='thumb', instrs=1)]
    raw = relocatable((body + (b'\xc0\x46' if padding else b''), {'call': 8}, {},
        {16: ('g_aligned', POINT)}, {'calls': [[8, 'func_08001000']]}, rows))
    raw = raw.replace(b'func_08000000', b'func_08000100').replace(
        b'func_08001000', b'__divsi3'.ljust(13, b'\0'))
    raw = symbol_change(raw, 'func_08000100', 'size', 26)
    image = match.elf_image(raw)
    linked = bytearray(raw)
    headers = struct.unpack_from('<I', raw, 32)[0]
    struct.pack_into('<H', linked, 16, 2)
    text = image['sections'][image['text_index']]
    linked[text[4]:text[4]+26] = body
    struct.pack_into('<I', linked, headers+40*image['text_index']+12, BASE)
    for number in image['relocations']:
        linked[headers+40*number:headers+40*(number+1)] = bytes(40)
    for section_no, symbols in image['symbol_tables'].items():
        section = image['sections'][section_no]
        for number, symbol in enumerate(symbols):
            offset = section[4] + 16*number
            if symbol['name'] == 'func_08000100':
                struct.pack_into('<I', linked, offset+4, BASE | 1)
            elif symbol['type'] == 3 and symbol['section'] == image['text_index']:
                struct.pack_into('<I', linked, offset+4, BASE)
            elif symbol['name'] in ('__divsi3', 'g_aligned'):
                data = symbol['name'] == 'g_aligned'
                struct.pack_into('<I', linked, offset+4, POINT if data else target | 1)
                linked[offset+12] = 0x11 if data else 0x12
                struct.pack_into('<H', linked, offset+14, 0xfff1)
    rom = bytearray(target-match.ROM_BASE+2)
    rom[0x100:0x11a] = body
    rom[-2:] = bytes.fromhex('7047')
    index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
        f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode()
    return [raw, bytes(linked), BASE, bytes(rom), json.dumps(rows).encode(), index,
            dict(calls=[[8, '__divsi3']], data=[[16, 'g_aligned', 0]], functions=[], switches=[])]


def text_change(raw, offset, value):
    data = bytearray(raw)
    image = match.elf_image(raw)
    start = image['sections'][image['text_index']][4]
    data[start+offset:start+offset+len(value)] = value
    return bytes(data)


class AlignedPairDataTests(unittest.TestCase):
    def setUp(self):
        environment = patch.object(native, 'environment_fingerprint', return_value={'fixture': True})
        environment.start(); self.addCleanup(environment.stop)
        closure = patch.object(native.inventory.core, 'prove_called_closures', return_value=({}, {}, []))
        self.closure = closure.start(); self.addCleanup(closure.stop)

    def verify(self, values, **kwargs):
        return native.verify_original(*values, objects=kwargs.pop('objects', OBJECTS), **kwargs)

    def test_complete_function_excludes_external_alignment_and_keeps_unknown_words(self):
        result, count = self.verify(fixture())
        self.assertEqual(count, 9)
        self.assertEqual(result['external_alignment_bytes'], 2)
        proof = result['prerequisite']
        self.assertEqual(proof['end'] - proof['address'], 26)
        self.assertEqual(proof['entry_stack_policy']['words'], [0, 1])
        self.assertEqual(proof['entry_loaded_value_facts'], [])
        self.assertFalse(proof['memory_safety_claim'])
        self.closure.assert_called_once()

    def test_original_noncanonical_tail_refuses(self):
        v = fixture(); v[0] = text_change(v[0], 26, b'\0\0')
        with self.assertRaisesRegex(ValueError, 'terminal alignment'): self.verify(v)
        self.closure.assert_not_called()

    def test_linked_noncanonical_tail_refuses(self):
        v = fixture(); v[1] = text_change(v[1], 26, b'\x70\x47')
        with self.assertRaisesRegex(ValueError, 'terminal alignment'): self.verify(v)
        self.closure.assert_not_called()

    def test_missing_external_alignment_refuses_new_selector(self):
        with self.assertRaisesRegex(ValueError, 'actual external two-byte'): self.verify(fixture(padding=False))

    def test_padding_cannot_gain_a_symbol_owner(self):
        v = fixture(); raw = bytearray(v[0]); image = match.elf_image(raw)
        for no, symbols in image['symbol_tables'].items():
            for n, sym in enumerate(symbols):
                if sym['type'] == 3 and sym['section'] == image['text_index']:
                    struct.pack_into('<I', raw, image['sections'][no][4]+16*n+4, 26)
        v[0] = bytes(raw)
        with self.assertRaisesRegex(ValueError, 'symbol owner'): self.verify(v)

    def test_both_sections_require_four_byte_alignment(self):
        for slot in (0, 1):
            with self.subTest(slot=slot):
                v = fixture(); raw = bytearray(v[slot]); image = match.elf_image(raw)
                header = struct.unpack_from('<I', raw, 32)[0]
                struct.pack_into('<I', raw, header+40*image['text_index']+32, 2)
                v[slot] = bytes(raw)
                with self.assertRaisesRegex(ValueError, 'terminal alignment'): self.verify(v)

    def test_old_selector_still_refuses_external_tail(self):
        with self.assertRaisesRegex(ValueError, 'sole complete'):
            strict.verify_original(*fixture(), objects=OBJECTS)

    def test_missing_actual_incoming_read_refuses(self):
        with self.assertRaisesRegex(ValueError, 'every declared incoming word'):
            self.verify(fixture(read=0x9901))
        self.closure.assert_not_called()

    def test_third_incoming_word_refuses(self):
        with self.assertRaises(ValueError): self.verify(fixture(read=0x9903))
        self.closure.assert_not_called()

    def test_incoming_store_and_SP_address_refuse(self):
        for first in (0x9001, 0xA800):
            with self.subTest(first=first), self.assertRaises(ValueError):
                self.verify(fixture(first=first))
        self.closure.assert_not_called()

    def test_wrong_original_type_and_object_size_refuse(self):
        for field, value in (('type', 2), ('size', 4)):
            v = fixture(); v[0] = symbol_change(v[0], 'g_aligned', field, value)
            with self.subTest(field=field), self.assertRaises(ValueError): self.verify(v)

    def test_nonzero_addend_and_missing_object_refuse(self):
        with self.assertRaises(ValueError): self.verify(fixture(), objects=b'{}')
        v = fixture(); v[0] = text_change(v[0], 16, struct.pack('<I', 4))
        with self.assertRaises(ValueError): self.verify(v)

    def test_linked_literal_and_nonrelocation_bytes_are_authenticated(self):
        for offset in (16, 2):
            v = fixture(); v[1] = text_change(v[1], offset, b'\x01\0')
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError, 'outside original relocation roles'):
                self.verify(v)

    def test_wrong_index_ROM_and_original_EXEC_refuse(self):
        v = fixture(); v[5] = v[5].replace(b'26 9 return', b'26 10 return')
        with self.assertRaises(ValueError): self.verify(v)
        v = fixture(); v[3] = v[3][:0x100]+b'\1'+v[3][0x101:]
        with self.assertRaises(ValueError): self.verify(v)
        v = fixture(); v[0] = v[1]
        with self.assertRaisesRegex(ValueError, 'original relocatable'): self.verify(v)

    def test_report_binds_original_and_routes_new_selector(self):
        v = fixture(); manifest, count = self.verify(v)
        original, linked, address, rom, mapping, index, bindings = v
        result = (rom[0x100:0x11a], manifest, 'a'*64, mapping, index, OBJECTS, rom, count, original)
        report = owner.render(BASE, result)
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), native.SELECTOR)
        self.assertIn('* control flow: '+native.CONTROL_FLOW, report)
        with patch.object(owner, 'build', return_value=result) as build:
            self.assertTrue(owner.report_matches(report, '.', BASE))
            self.assertEqual(build.call_args.kwargs['selector'], native.SELECTOR)
        with patch.object(owner, 'build', side_effect=ValueError('changed object')):
            self.assertFalse(owner.report_matches(report, '.', BASE))

    def test_reserved_source_names_refuse_before_compiler(self):
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = Mock(); runner.read_binary.return_value = b'int __divsi3(int,int);'
        with self.assertRaisesRegex(ValueError, 'reserved for compiler'):
            owner.object_bytes(runner, 'unused', args, {}, BASE, b'', b'[]', OBJECTS, selector=native.SELECTOR)
        runner.sh.assert_not_called()

    def test_closed_CFG_reaches_and_rejects_forbidden_frame_operations(self):
        for changes in ({'read': 0x9903}, {'first': 0x9001}, {'first': 0xA800}):
            with self.subTest(changes=changes):
                values = fixture(**changes)
                decoded = owner.refine(values[3][0x100:0x11a], BASE, values[4])
                self.assertTrue(decoded['cfg_closed'])
                with self.assertRaises(ValueError) as error: self.verify(values)
                self.assertNotIn('structural inventory is not closed', str(error.exception))
        self.closure.assert_not_called()

    def test_closed_CFG_still_requires_actual_index_count(self):
        values = fixture(); values[5] = values[5].replace(b'26 9 return', b'26 10 return')
        self.assertTrue(owner.refine(values[3][0x100:0x11a], BASE, values[4])['cfg_closed'])
        with self.assertRaisesRegex(ValueError, 'count|metadata|index'): self.verify(values)
        self.closure.assert_not_called()


if __name__ == '__main__':
    unittest.main()
