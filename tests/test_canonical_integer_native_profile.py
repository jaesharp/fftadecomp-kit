"""Synthetic original ELF authentication around the unchanged scalar proof.

Only canonical runtime closure production is mocked: these tests exercise real
ELF parsing, relocations, linked bytes, caller CFG/frame, and report routing.
The approved-ROM original qualification is a separate private invocation.
"""
import argparse
import copy
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
from test_typed_switch_outgoing_frame import relocatable

BASE = match.ROM_BASE + 0x100


def fixture(family='__divsi3', *, prefix=(0xB500,), suffix=(0xBC02, 0x4708)):
    at = len(prefix)*2
    target = native.scalar.OPERATIONS[family]
    delta = target-(BASE+at+4)
    body = struct.pack('<'+'H'*len(prefix), *prefix) + struct.pack('<HH',
        0xF000 | ((delta >> 12) & 0x7ff), 0xF800 | ((delta >> 1) & 0x7ff))
    body += struct.pack('<'+'H'*len(suffix), *suffix)
    rows = [dict(rom=f'0x{BASE:08X}', end=f'0x{BASE+len(body):08X}', mode='thumb',
                 instrs=len(prefix)+1+len(suffix)),
            dict(rom=f'0x{target:08X}', end=f'0x{target+2:08X}', mode='thumb', instrs=1)]
    f = (body, {'call': at}, {}, {}, {'calls': [[at, 'func_08001000']]}, rows)
    raw = relocatable(f).replace(b'func_08000000', b'func_08000100').replace(b'func_08001000', family.encode().ljust(13, b'\0'))
    # Original and linked are independently encoded ELF images, not dictionaries.
    output = bytearray(raw)
    image = match.elf_image(raw)
    headers = struct.unpack_from('<I', raw, 32)[0]
    struct.pack_into('<H', output, 16, 2)
    text = image['sections'][image['text_index']]
    output[text[4]:text[4]+text[5]] = body
    struct.pack_into('<I', output, headers+40*image['text_index']+12, BASE)
    for number in image['relocations']:
        output[headers+40*number:headers+40*(number+1)] = bytes(40)
    for section_no, symbols in image['symbol_tables'].items():
        section = image['sections'][section_no]
        for number, symbol in enumerate(symbols):
            offset = section[4]+16*number
            if symbol['name'] == f'func_{BASE:08X}':
                struct.pack_into('<I', output, offset+4, BASE | 1)
            elif symbol['type'] == 3 and symbol['section'] == image['text_index']:
                struct.pack_into('<I', output, offset+4, BASE)
            elif symbol['name'] == family:
                struct.pack_into('<I', output, offset+4, target | 1)
                output[offset+12] = 0x12
                struct.pack_into('<H', output, offset+14, 0xfff1)
    rom = bytearray(target-BASE+2)
    rom[BASE-match.ROM_BASE:BASE-match.ROM_BASE+len(body)] = body
    rom[-2:] = bytes.fromhex('7047')
    mapping = json.dumps(rows).encode()
    index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                    f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
                    for row in rows).encode()
    bindings = dict(calls=[[at, family]], data=[], functions=[], switches=[])
    return [raw, bytes(output), BASE, bytes(rom), mapping, index, bindings]


def symbol_change(raw, name, field, value):
    output = bytearray(raw)
    image = match.elf_image(raw)
    for section_no, symbols in image['symbol_tables'].items():
        section = image['sections'][section_no]
        for number, symbol in enumerate(symbols):
            if symbol['name'] == name:
                offset = section[4]+16*number
                if field == 'type': output[offset+12] = 0x10 | value
                elif field == 'size': struct.pack_into('<I', output, offset+8, value)
                elif field == 'value': struct.pack_into('<I', output, offset+4, value)
    return bytes(output)


class CanonicalIntegerNativeTests(unittest.TestCase):
    def setUp(self):
        self.environment = patch.object(native, 'environment_fingerprint', return_value={'synthetic': True})
        self.environment.start()
        self.addCleanup(self.environment.stop)
        self.closure = patch.object(native.scalar, 'prove_called_closures', return_value=({}, {}, []))
        self.prove = self.closure.start()
        self.addCleanup(self.closure.stop)

    def test_all_four_genuine_compiler_aliases_reach_unchanged_frame_and_closure(self):
        for family in native.scalar.OPERATIONS:
            with self.subTest(family=family):
                values = fixture(family)
                result, count = native.verify_original(*values)
                self.assertEqual(count, 4)
                self.assertEqual(result['profile'], native.SCHEMA)
                self.assertEqual(result['prerequisite']['runtime_families'], [family])
                self.assertEqual(result['original_ET_REL_sha256'], hashlib.sha256(values[0]).hexdigest())
                self.assertEqual(result['prerequisite']['numeric_operand_preconditions'], [])
                self.assertFalse(result['prerequisite']['arithmetic_C_equivalence'])
                self.assertFalse(result['prerequisite']['memory_safety_claim'])
                self.assertEqual(self.prove.call_args.args[-1], {family})

    def test_original_ET_EXEC_is_not_an_original_object(self):
        values = fixture(); values[0] = values[1]
        with self.assertRaisesRegex(ValueError, 'original relocatable'):
            native.verify_original(*values)

    def test_original_undefined_function_size_is_zero(self):
        values = fixture(); values[0] = symbol_change(values[0], '__divsi3', 'size', 4)
        with self.assertRaisesRegex(ValueError, 'zero-sized'):
            native.verify_original(*values)

    def test_typed_link_rejects_notype_and_wrong_absolute_address(self):
        for field, value in (('type', 0), ('value', native.scalar.OPERATIONS['__divsi3']+3)):
            values = fixture(); values[1] = symbol_change(values[1], '__divsi3', field, value)
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'typed absolute'):
                native.verify_original(*values)

    def test_link_changes_outside_original_relocations_refuse(self):
        values = fixture(); linked = bytearray(values[1]); image = match.elf_image(values[1])
        linked[image['sections'][image['text_index']][4]] ^= 1; values[1] = bytes(linked)
        with self.assertRaisesRegex(ValueError, 'outside original call relocations'):
            native.verify_original(*values)

    def test_binding_roles_cannot_be_added_or_omitted(self):
        for role in ('calls', 'data', 'functions', 'switches'):
            values = fixture(); values[6][role] = [] if values[6][role] else [[0, 'invented']]
            with self.subTest(role=role), self.assertRaisesRegex(ValueError, 'actual original'):
                native.verify_original(*values)

    def test_unrelocated_addressed_runtime_name_is_not_a_compiler_alias(self):
        values = fixture(); values[0] = values[0].replace(b'__divsi3\0\0\0\0\0', b'func_081426B8')
        with self.assertRaises(ValueError):
            native.verify_original(*values)

    def test_native_caller_frame_keeps_SP_alias_refusal(self):
        values = fixture(prefix=(0xB500, 0xB081, 0xA800), suffix=(0xB001, 0xBC02, 0x4708))
        with self.assertRaisesRegex(ValueError, 'SP addresses'):
            native.verify_original(*values)
        self.prove.assert_not_called()

    def test_dual_index_count_is_not_relaxed(self):
        values = fixture(); values[5] = values[5].replace(b'10 4 return', b'10 5 return')
        with self.assertRaises(ValueError):
            native.verify_original(*values)
        self.prove.assert_not_called()

    def test_manifest_and_ROM_changes_fail_closed(self):
        values = fixture(); manifest, _ = native.verify_original(*values)
        manifest['contract'] = 'invented arithmetic theorem'
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            native.verify_original(*values, manifest=manifest)
        values[3] = values[3][:0x100]+b'\x01'+values[3][0x101:]
        with self.assertRaises(ValueError):
            native.verify_original(*values)

    def test_data_only_API_cannot_select_source_profile(self):
        values = fixture()
        with self.assertRaisesRegex(ValueError, 'unknown complete-owner selector'):
            owner.verify(values[3][0x100:0x10a], BASE, values[3], values[4], values[5], b'{}',
                         bindings=values[6], selector=native.SELECTOR)

    def test_source_identifiers_reserved_before_link(self):
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        from unittest.mock import Mock
        for family in native.scalar.OPERATIONS:
            runner = Mock(); runner.read_binary.return_value = ('int '+family+'(int,int);').encode()
            with self.subTest(family=family), self.assertRaisesRegex(ValueError, 'reserved for compiler'):
                owner.object_bytes(runner, 'unused', args, {}, BASE, b'', b'[]', b'{}', selector=native.SELECTOR)
            runner.sh.assert_not_called()

    def test_source_report_requires_original_bound_replay_and_fingerprint(self):
        original, linked, address, rom, mapping, index, bindings = fixture()
        manifest, count = native.verify_original(original, linked, address, rom, mapping, index, bindings)
        result = (rom[0x100:0x10a], manifest, 'a'*64, mapping, index, b'{}', rom, count, original)
        report = owner.render(BASE, result)
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), native.SELECTOR)
        self.assertIn('* control flow: '+native.CONTROL_FLOW, report)
        with self.assertRaisesRegex(ValueError, 'original ELF identity'):
            owner.fingerprint(BASE, *result[:1], manifest, 'a'*64, mapping, index, b'{}', rom)
        with patch.object(owner, 'build', return_value=result) as build:
            self.assertTrue(owner.report_matches(report, '.', BASE))
            self.assertEqual(build.call_args.kwargs['selector'], native.SELECTOR)
        with patch.object(owner, 'build', side_effect=ValueError('changed source/object')):
            self.assertFalse(owner.report_matches(report, '.', BASE))

    def test_mixed_selector_policies_refuse_before_compilation(self):
        options = dict(mode='thumb', control_flow_profile='ordinary', software_double_profile=None,
            software_double_remainder_profile=None, function_address_profile=None, switch_profile=None,
            label=None, wsl='Ubuntu', wsl_path=match.DEFAULT_WSL_PATH, owner_runtime_profile=native.SELECTOR)
        for flag in ('signed_quotient_profile', 'signed_runtime_profile', 'unsigned_runtime_profile',
                     'addressed_signed_runtime_profile', 'switch_data_profile'):
            with self.subTest(flag=flag), patch.object(owner, 'build') as build:
                with self.assertRaisesRegex(ValueError, 'excludes mixed'):
                    owner.issue('.', BASE, argparse.Namespace(**options, **{flag: 'mixed'}))
                build.assert_not_called()


if __name__ == '__main__':
    unittest.main()
