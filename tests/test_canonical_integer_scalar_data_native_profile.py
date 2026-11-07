"""Synthetic typed ELF bridge with seven outgoing scalar words and named data.

Only canonical runtime closure generation is mocked; ELF, CFG and the existing
strict scalar frame engine execute normally. The real runtime runs once separately.
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
import canonical_integer_scalar_data_native_profile as native
import match
import owner_admission_profile as owner
from test_canonical_integer_native_profile import symbol_change
from test_typed_switch_outgoing_frame import relocatable

BASE = match.ROM_BASE + 0x100
POINT = 0x02001000
OBJECTS = json.dumps({'g_six': f'0x{POINT:08X}'}).encode()


def fixture(*, replace_read=None, halfword_local=False):
    prefix = [0xB500, 0xB087, 0x2000] + [0x9000+i for i in range(7)] + [0x4A03, 0x2100]
    if replace_read is not None:
        prefix[replace_read[0]] = replace_read[1]
    if halfword_local:
        prefix[2], prefix[9] = 0x4668, 0x8800  # MOV R0,SP; LDRH R0,[R0].
    at = 24
    target = native.inventory.OPERATIONS['__divsi3']
    delta = target - (BASE + at + 4)
    body = struct.pack('<12H', *prefix)
    body += struct.pack('<HHHHHHI', 0xF000 | ((delta >> 12) & 0x7ff),
        0xF800 | ((delta >> 1) & 0x7ff), 0xB007, 0xBC02, 0x4708, 0, POINT)
    rows = [dict(rom=f'0x{BASE:08X}', end=f'0x{BASE+len(body):08X}',
                 mode='thumb', instrs=16),
            dict(rom=f'0x{target:08X}', end=f'0x{target+2:08X}', mode='thumb', instrs=1)]
    original = relocatable((body, {'call': at}, {}, {36: ('g_six', POINT)},
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
            elif symbol['name'] in ('__divsi3', 'g_six'):
                is_object = symbol['name'] == 'g_six'
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
    bindings = dict(calls=[[at, '__divsi3']], data=[[36, 'g_six', 0]], functions=[], switches=[])
    return [original, bytes(linked), BASE, bytes(rom), mapping, index, bindings]


class ScalarDataSourceTests(unittest.TestCase):
    def setUp(self):
        environment = patch.object(native, 'environment_fingerprint', return_value={'synthetic': True})
        environment.start(); self.addCleanup(environment.stop)
        closure = patch.object(native.inventory, 'prove_called_closures', return_value=({}, {}, []))
        self.closure = closure.start(); self.addCleanup(closure.stop)

    def verify(self, values, **kwargs):
        return native.verify_original(*values, objects=kwargs.pop('objects', OBJECTS), **kwargs)

    def test_typed_data_and_seven_outgoing_scalar_words(self):
        result, count = self.verify(fixture())
        self.assertEqual(count, 16)
        self.assertEqual(result['profile'], native.SCHEMA)
        proof = result['prerequisite']
        self.assertEqual(proof['frame']['maximum_frame_bytes'], 32)
        self.assertIsNone(proof['entry_stack_contract'])
        self.assertFalse(proof['memory_safety_claim'])
        self.assertFalse(proof['arithmetic_C_equivalence'])
        self.assertEqual(self.closure.call_args.args[-1], {'__divsi3'})

    def test_sp_materialization_stays_refused(self):
        with self.assertRaisesRegex(ValueError, 'excludes SP addresses'):
            self.verify(fixture(replace_read=(2, 0x4668)))
        self.closure.assert_not_called()

    def test_nonword_stack_access_stays_refused(self):
        with self.assertRaises(ValueError):
            self.verify(fixture(halfword_local=True))
        self.closure.assert_not_called()

    def test_saved_return_word_cannot_be_overwritten(self):
        with self.assertRaises(ValueError):
            self.verify(fixture(replace_read=(9, 0x9007)))
        self.closure.assert_not_called()

    def test_incoming_word_has_no_permission(self):
        with self.assertRaises(ValueError):
            self.verify(fixture(replace_read=(9, 0x9808)))
        self.closure.assert_not_called()

    def test_original_executable_cannot_replace_relocatable(self):
        values = fixture(); values[0] = values[1]
        with self.assertRaisesRegex(ValueError, 'original relocatable'):
            self.verify(values)

    def test_original_object_type_size_and_addend(self):
        for field, value in (('type', 2), ('size', 4)):
            values = fixture(); values[0] = symbol_change(values[0], 'g_six', field, value)
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.verify(values)
        values = fixture(); image = match.elf_image(values[0]); raw = bytearray(values[0])
        struct.pack_into('<I', raw, image['sections'][image['text_index']][4]+36, 4)
        values[0] = bytes(raw)
        with self.assertRaises(ValueError):
            self.verify(values)

    def test_missing_canonical_object_refuses(self):
        with self.assertRaises(ValueError):
            self.verify(fixture(), objects=b'{}')

    def test_linked_object_identity_is_exact(self):
        for field, value in (('type', 2), ('value', POINT+4), ('size', 4)):
            values = fixture(); values[1] = symbol_change(values[1], 'g_six', field, value)
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'typed absolute'):
                self.verify(values)

    def test_nonrelocation_bytes_cannot_change(self):
        values = fixture(); image = match.elf_image(values[1]); raw = bytearray(values[1])
        raw[image['sections'][image['text_index']][4]+2] ^= 1; values[1] = bytes(raw)
        with self.assertRaisesRegex(ValueError, 'outside original relocation roles'):
            self.verify(values)

    def test_binding_roles_cannot_change(self):
        for role in ('calls', 'data', 'functions', 'switches'):
            values = fixture(); values[6][role] = [] if values[6][role] else [[0, 'invented']]
            with self.subTest(role=role), self.assertRaisesRegex(ValueError, 'bindings differ'):
                self.verify(values)

    def test_changed_rom_or_index_refuses(self):
        values = fixture(); values[5] = values[5].replace(b'40 16 return', b'40 17 return')
        with self.assertRaises(ValueError):
            self.verify(values)
        values = fixture(); values[3] = values[3][:0x100]+b'\x01'+values[3][0x101:]
        with self.assertRaises(ValueError):
            self.verify(values)
        self.closure.assert_not_called()

    def test_reserved_identifiers_refuse_before_compilation(self):
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = Mock(); runner.read_binary.return_value = b'int __divsi3(int,int);'
        with self.assertRaisesRegex(ValueError, 'reserved for compiler'):
            owner.object_bytes(runner, 'unused', args, {}, BASE, b'', b'[]', OBJECTS, selector=native.SELECTOR)
        runner.sh.assert_not_called()

    def test_report_authenticates_original_and_routes_replay(self):
        values = fixture(); manifest, count = self.verify(values)
        original, linked, address, rom, mapping, index, bindings = values
        result = (rom[0x100:0x128], manifest, 'a'*64, mapping, index, OBJECTS, rom, count, original)
        report = owner.render(BASE, result)
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), native.SELECTOR)
        self.assertIn('* control flow: '+native.CONTROL_FLOW, report)
        with self.assertRaisesRegex(ValueError, 'original ELF identity'):
            owner.fingerprint(BASE, result[0], manifest, 'a'*64, mapping, index, OBJECTS, rom)
        with patch.object(owner, 'build', return_value=result) as build:
            self.assertTrue(owner.report_matches(report, '.', BASE))
            self.assertEqual(build.call_args.kwargs['selector'], native.SELECTOR)

    def test_data_only_and_mixed_modes_cannot_enable_admission(self):
        values = fixture()
        with self.assertRaisesRegex(ValueError, 'unknown complete-owner selector'):
            owner.verify(values[3][0x100:0x128], BASE, values[3], values[4], values[5], OBJECTS,
                         bindings=values[6], selector=native.SELECTOR)
        options = dict(mode='thumb', control_flow_profile='ordinary', software_double_profile=None,
            software_double_remainder_profile=None, function_address_profile=None, switch_profile=None,
            label=None, wsl='Ubuntu', wsl_path=match.DEFAULT_WSL_PATH, owner_runtime_profile=native.SELECTOR)
        with patch.object(owner, 'build') as build, self.assertRaisesRegex(ValueError, 'excludes mixed'):
            owner.issue('.', BASE, argparse.Namespace(**options, signed_runtime_profile='mixed'))
        build.assert_not_called()

    def test_previous_profiles_still_reject_wrong_shape(self):
        import canonical_integer_private_locals_native_profile as private
        values = fixture()
        with patch.object(private, 'environment_fingerprint', return_value={'synthetic': True}), \
                self.assertRaisesRegex(ValueError, 'actual bounded local alias accesses'):
            private.verify_original(*values, objects=OBJECTS)
        with self.assertRaises(ValueError):
            native.scalar_native.verify_original(*values)
        self.closure.assert_not_called()


if __name__ == '__main__':
    unittest.main()


