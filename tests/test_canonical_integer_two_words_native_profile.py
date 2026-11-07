"""Authenticate real synthetic ELF roles and the unchanged incoming-word proof.

Only the canonical runtime producer is mocked. Original ELF authentication,
typed linking, CFG, frame, all two incoming reads and report routing are real.
"""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import Mock, patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import canonical_integer_two_words_native_profile as native
import match
import owner_admission_profile as owner
from test_canonical_integer_native_profile import symbol_change
from test_typed_switch_outgoing_frame import relocatable

BASE = match.ROM_BASE + 0x100
POINT = 0x02001000
OBJECTS = json.dumps({'g_two': f'0x{POINT:08X}'}).encode()


def fixture(*, replace_read=None):
    prefix = [0xB500, *range(0x9801, 0x9803)]
    if replace_read is not None:
        prefix[replace_read[0]] = replace_read[1]
    at = 8
    target = native.inventory.OPERATIONS['__divsi3']
    delta = target - (BASE + at + 4)
    body = struct.pack('<4H', *prefix, 0x4A02)
    body += struct.pack('<HHHHI', 0xF000 | ((delta >> 12) & 0x7ff),
        0xF800 | ((delta >> 1) & 0x7ff), 0xBC02, 0x4708, POINT)
    rows = [dict(rom=f'0x{BASE:08X}', end=f'0x{BASE+len(body):08X}',
                 mode='thumb', instrs=7),
            dict(rom=f'0x{target:08X}', end=f'0x{target+2:08X}', mode='thumb', instrs=1)]
    original = relocatable((body, {'call': at}, {}, {16: ('g_two', POINT)},
        {'calls': [[at, 'func_08001000']]}, rows))
    original = original.replace(b'func_08000000', b'func_08000100').replace(
        b'func_08001000', b'__divsi3'.ljust(13, b'\0'))
    image = match.elf_image(original)
    linked = bytearray(original)
    headers = struct.unpack_from('<I', original, 32)[0]
    struct.pack_into('<H', linked, 16, 2)
    section = image['sections'][image['text_index']]
    linked[section[4]:section[4]+section[5]] = body
    struct.pack_into('<I', linked, headers+40*image['text_index']+12, BASE)
    for number in image['relocations']:
        linked[headers+40*number:headers+40*(number+1)] = bytes(40)
    for section_no, symbols in image['symbol_tables'].items():
        section = image['sections'][section_no]
        for number, symbol in enumerate(symbols):
            offset = section[4]+16*number
            if symbol['name'] == 'func_08000100':
                struct.pack_into('<I', linked, offset+4, BASE | 1)
            elif symbol['type'] == 3 and symbol['section'] == image['text_index']:
                struct.pack_into('<I', linked, offset+4, BASE)
            elif symbol['name'] in ('__divsi3', 'g_two'):
                is_object = symbol['name'] == 'g_two'
                struct.pack_into('<I', linked, offset+4, POINT if is_object else target | 1)
                linked[offset+12] = 0x11 if is_object else 0x12
                struct.pack_into('<H', linked, offset+14, 0xfff1)
    rom = bytearray(target-match.ROM_BASE+2)
    rom[0x100:0x100+len(body)] = body
    rom[-2:] = bytes.fromhex('7047')
    mapping = json.dumps(rows).encode()
    index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                    f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
                    for row in rows).encode()
    bindings = dict(calls=[[at, '__divsi3']], data=[[16, 'g_two', 0]], functions=[], switches=[])
    return [original, bytes(linked), BASE, bytes(rom), mapping, index, bindings]


class TwoWordsSourceTests(unittest.TestCase):
    def setUp(self):
        env = patch.object(native, 'environment_fingerprint', return_value={'synthetic': True})
        env.start(); self.addCleanup(env.stop)
        closure = patch.object(native.inventory.core, 'prove_called_closures', return_value=({}, {}, []))
        self.prove = closure.start(); self.addCleanup(closure.stop)

    def verify(self, values, **kwargs):
        return native.verify_original(*values, objects=kwargs.pop('objects', OBJECTS), **kwargs)

    def test_complete_original_roles_and_two_unknown_readable_words(self):
        values = fixture()
        result, count = self.verify(values)
        self.assertEqual(count, 7)
        self.assertEqual(result['profile'], native.SCHEMA)
        self.assertEqual(result['original_ET_REL_sha256'], hashlib.sha256(values[0]).hexdigest())
        proof = result['prerequisite']
        self.assertEqual(proof['entry_stack_policy']['words'], list(range(2)))
        self.assertEqual(proof['entry_loaded_value_facts'], [])
        self.assertFalse(proof['arithmetic_C_equivalence'])
        self.assertFalse(proof['memory_safety_claim'])
        self.assertEqual(self.prove.call_args.args[-1], {'__divsi3'})

    def test_missing_one_actual_read_is_not_a_two_word_contract(self):
        with self.assertRaisesRegex(ValueError, 'every declared incoming word'):
            self.verify(fixture(replace_read=(2, 0x9801)))
        self.prove.assert_not_called()

    def test_third_incoming_word_is_outside_two_word_contract(self):
        with self.assertRaises(ValueError):
            self.verify(fixture(replace_read=(2, 0x9803)))
        self.prove.assert_not_called()

    def test_incoming_stores_and_SP_addresses_remain_refused(self):
        for instruction in (0x9001, 0xA800):
            with self.subTest(instruction=instruction), self.assertRaises(ValueError):
                self.verify(fixture(replace_read=(1, instruction)))
        self.prove.assert_not_called()

    def test_existing_scalar_and_six_word_selectors_keep_their_boundaries(self):
        import canonical_integer_scalar_data_native_profile as scalar
        import canonical_integer_six_words_native_profile as six
        values = fixture()
        with patch.object(scalar, 'environment_fingerprint', return_value={'synthetic': True}), self.assertRaises(ValueError):
            scalar.verify_original(*values, objects=OBJECTS)
        with patch.object(six, 'environment_fingerprint', return_value={'synthetic': True}), self.assertRaisesRegex(ValueError, 'every declared incoming word'):
            six.verify_original(*values, objects=OBJECTS)
        self.prove.assert_not_called()

    def test_original_ET_EXEC_cannot_replace_original_ET_REL(self):
        values = fixture(); values[0] = values[1]
        with self.assertRaisesRegex(ValueError, 'original relocatable'):
            self.verify(values)

    def test_original_object_type_and_size_are_authenticated(self):
        for field, value in (('type', 2), ('size', 4)):
            values = fixture(); values[0] = symbol_change(values[0], 'g_two', field, value)
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.verify(values)

    def test_unmapped_object_and_nonzero_original_data_addend_refuse(self):
        with self.assertRaises(ValueError):
            self.verify(fixture(), objects=b'{}')
        values = fixture(); original = bytearray(values[0]); image = match.elf_image(values[0])
        struct.pack_into('<I', original, image['sections'][image['text_index']][4]+16, 4)
        values[0] = bytes(original)
        with self.assertRaises(ValueError):
            self.verify(values)

    def test_link_object_type_address_and_size_remain_exact(self):
        for field, value in (('type', 2), ('value', POINT+4), ('size', 4)):
            values = fixture(); values[1] = symbol_change(values[1], 'g_two', field, value)
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'typed absolute'):
                self.verify(values)

    def test_link_nonrelocation_bytes_cannot_change(self):
        values = fixture(); linked = bytearray(values[1]); image = match.elf_image(values[1])
        linked[image['sections'][image['text_index']][4]+2] ^= 1; values[1] = bytes(linked)
        with self.assertRaisesRegex(ValueError, 'outside original relocation roles'):
            self.verify(values)

    def test_binding_roles_cannot_be_omitted_or_invented(self):
        for role in ('calls', 'data', 'functions', 'switches'):
            values = fixture(); values[6][role] = [] if values[6][role] else [[0, 'invented']]
            with self.subTest(role=role), self.assertRaisesRegex(ValueError, 'bindings differ'):
                self.verify(values)

    def test_wrong_index_and_ROM_cannot_be_admitted(self):
        values = fixture(); values[5] = values[5].replace(b'20 7 return', b'20 8 return')
        with self.assertRaises(ValueError):
            self.verify(values)
        values = fixture(); values[3] = values[3][:0x100]+b'\x01'+values[3][0x101:]
        with self.assertRaises(ValueError):
            self.verify(values)
        self.prove.assert_not_called()

    def test_source_reserved_runtime_identifiers_refuse_before_compilation(self):
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = Mock(); runner.read_binary.return_value = b'int __divsi3(int,int);'
        with self.assertRaisesRegex(ValueError, 'reserved for compiler'):
            owner.object_bytes(runner, 'unused', args, {}, BASE, b'', b'[]', OBJECTS, selector=native.SELECTOR)
        runner.sh.assert_not_called()

    def test_manifest_claim_cannot_be_changed(self):
        values = fixture(); manifest, _ = self.verify(values)
        manifest['contract'] = 'invented arithmetic equivalence'
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.verify(values, manifest=manifest)

    def test_source_report_binds_original_and_routes_fresh_replay(self):
        values = fixture(); manifest, count = self.verify(values)
        original, linked, address, rom, mapping, index, bindings = values
        result = (rom[0x100:0x114], manifest, 'a'*64, mapping, index, OBJECTS, rom, count, original)
        report = owner.render(BASE, result)
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), native.SELECTOR)
        self.assertIn('* control flow: '+native.CONTROL_FLOW, report)
        self.assertIn('original_elf_sha256', report)
        with self.assertRaisesRegex(ValueError, 'original ELF identity'):
            owner.fingerprint(BASE, result[0], manifest, 'a'*64, mapping, index, OBJECTS, rom)
        with patch.object(owner, 'build', return_value=result) as build:
            self.assertTrue(owner.report_matches(report, '.', BASE))
            self.assertEqual(build.call_args.kwargs['selector'], native.SELECTOR)
        with patch.object(owner, 'build', side_effect=ValueError('changed object')):
            self.assertFalse(owner.report_matches(report, '.', BASE))

    def test_data_only_API_and_mixed_selectors_cannot_enable_bridge(self):
        values = fixture()
        with self.assertRaisesRegex(ValueError, 'unknown complete-owner selector'):
            owner.verify(values[3][0x100:0x114], BASE, values[3], values[4], values[5], OBJECTS,
                         bindings=values[6], selector=native.SELECTOR)
        options = dict(mode='thumb', control_flow_profile='ordinary', software_double_profile=None,
            software_double_remainder_profile=None, function_address_profile=None, switch_profile=None,
            label=None, wsl='Ubuntu', wsl_path=match.DEFAULT_WSL_PATH, owner_runtime_profile=native.SELECTOR)
        with patch.object(owner, 'build') as build, self.assertRaisesRegex(ValueError, 'excludes mixed'):
            owner.issue('.', BASE, argparse.Namespace(**options, signed_runtime_profile='mixed'))
        build.assert_not_called()


if __name__ == '__main__':
    unittest.main()
