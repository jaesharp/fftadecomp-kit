"""Callee-saved scalar control provenance stays separate from memory addresses."""
from contextlib import redirect_stdout
import copy
import io
import json
import struct
import sys
import unittest
from unittest.mock import patch

import test_bios_numeric_mmio_literals as numeric

profile, match, A = numeric.profile, numeric.match, numeric.A
fill = numeric.fixtures.functions.fill
bios = fill.bios


class BiosSavedScalarMmioLiteralTests(unittest.TestCase):
    def setUp(self):
        self.base = fill.BiosCpuSetFillTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)
        self.original_data_image = self.base.base.data_image

    def data_image(self, fixture):
        image = self.original_data_image(fixture)
        # The older synthetic builder emits a symbol per call. A real ELF has
        # one undefined global even when three relocations call that function.
        symbols, remap, names = [], {}, {}
        for index, symbol in enumerate(image['symbols']):
            if symbol['name'] not in names:
                names[symbol['name']] = len(symbols)
                symbols.append(symbol)
            remap[index] = names[symbol['name']]
        rels = bytearray(image['section_data'][2])
        for position in range(0, len(rels), 8):
            info = struct.unpack_from('<I', rels, position+4)[0]
            struct.pack_into('<I', rels, position+4, (remap[info >> 8] << 8) | (info & 255))
        image['symbols'], image['symbol_tables'][3] = symbols, symbols
        image['section_data'][2] = bytes(rels)
        return image

    def fixture(self, middle=()):
        tokens = [0xB520, 0xB081, ('load', 3, 'object'), 0x2000, 0x6018,
                  ('load', 1, 'mmio'), 0x8008, ('load', 5, 'saved'),
                  0x4668, 0x2100, 0x1C2A, 'bios', *middle,
                  0x4668, 0x2100, 0x1C2A, 'bios',
                  0x4668, 0x2100, ('load', 2, 'direct'), 'bios',
                  0xB001, 0xBC20, 0xBC01, 0x4700]
        body, calls, bindings, loads = bytearray(), {}, {}, []
        for token in tokens:
            if isinstance(token, int):
                body += struct.pack('<H', token)
            elif token == 'bios':
                site = A + len(body)
                calls[site], bindings[site] = bios.ADDRESS, bios.NAME
                body += fill.fixtures.fixtures.bl(site, bios.ADDRESS)
            else:
                loads.append((len(body), token[1], token[2]))
                body += b'\0\0'
        if len(body) % 4:
            body += b'\0\0'
        pools = {}
        for name, value in [('object', 0x03000020), ('mmio', 0x04000134),
                            ('saved', 0x05000001), ('direct', 0x05000056)]:
            pools[name] = len(body)
            body += struct.pack('<I', value)
        for site, register, name in loads:
            struct.pack_into('<H', body, site, 0x4800 | (register << 8) |
                             ((pools[name] - ((site+4)&~3)) // 4))
        rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(body):08X}',
                     mode='thumb', instrs=len(tokens)),
                dict(rom=f'0x{bios.ADDRESS:08X}', end=f'0x{bios.ADDRESS+4:08X}',
                     mode='thumb', instrs=2)]
        mapping, index = fill.fixtures.fixtures.indexes(rows)
        rom = bytearray(0x143000)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        at = bios.ADDRESS-match.ROM_BASE
        rom[at:at+4] = bios.WRAPPER
        return dict(data=bytes(body), address=A, rom=bytes(rom), mapping=mapping,
                    index=index, calls=calls, bindings=bindings,
                    selector=profile.BIOS_SAVED_SCALAR_MMIO_DATA_SELECTOR,
                    data_mapping=b'{"destination":"0x03000020"}',
                    data_bindings=[[pools['object'], 'destination', 0]])

    def test_two_cached_uses_and_direct_control_remain_distinct_from_objects_and_mmio(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        saved = manifest['bios_saved_scalar_control']['words']
        self.assertEqual(len(saved), 1)
        self.assertEqual(saved[0][1], 0x05000001)
        self.assertEqual(len(saved[0][2][0][1]), 2)
        self.assertEqual(manifest['bios_scalar_control']['words'][0][1], 0x05000056)
        self.assertEqual(manifest['numeric_mmio_literals']['words'][0][1], 0x04000134)
        self.assertNotIn(saved[0][0], {r[0] for r in manifest['data_bindings']})
        self.assertEqual(len(manifest['native_buffers']['bios_fill']['sites']), 3)
        self.assertIn('explicit ordinary ABI premise', manifest['bios_saved_scalar_control']['contract'])
        self.assertFalse(manifest['arithmetic_C_equivalence'])

    def test_memory_other_argument_arithmetic_overwrite_and_join_refuse(self):
        for middle in ((0x602D,), (0x1C29,), (0x682D,), (0x2D00,),
                       (0x3501,), (0x2500,), (0x2B00, 0xD000, 0x2301)):
            with self.subTest(middle=middle), self.assertRaises(ValueError):
                profile.verify(**self.fixture(middle))

    def test_old_selector_and_fabricated_object_stay_refused_and_manifest_is_exact(self):
        f = self.fixture()
        with self.assertRaisesRegex(ValueError, 'typed coverage'):
            profile.verify(**dict(f, selector=profile.BIOS_SCALAR_MMIO_DATA_SELECTOR))
        manifest, _ = profile.verify(**f)
        offset = manifest['bios_saved_scalar_control']['words'][0][0]
        with self.assertRaisesRegex(ValueError, 'also be a typed object'):
            profile.verify(**dict(f, data_mapping=b'{"destination":"0x03000020","fake":"0x05000001"}',
                data_bindings=f['data_bindings']+[[offset, 'fake', 0]]))
        forged = copy.deepcopy(manifest)
        forged['bios_saved_scalar_control']['words'][0][2][0][1].pop()
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            profile.verify(**f, manifest=forged)

    def test_existing_direct_scalar_mmio_selector_retains_positive_and_saved_boundary(self):
        case = numeric.BiosNumericMmioLiteralTests('runTest')
        case.setUp()
        self.addCleanup(case.doCleanups)
        f = case.fixture()
        manifest, _ = profile.verify(**f)
        self.assertNotIn('bios_saved_scalar_control', manifest)
        with self.assertRaisesRegex(ValueError, 'actual saved scalar-only'):
            profile.verify(**dict(f, selector=profile.BIOS_SAVED_SCALAR_MMIO_DATA_SELECTOR))

    def test_original_scalar_words_have_no_abs32_and_linker_must_preserve_them(self):
        f = self.fixture()
        helper = self.base.base
        original = self.data_image(f)
        linked = helper.linked_data_image(f, original)
        records = {}
        calls, _, targets = profile.original_bindings(original, A, f['rom'], f['mapping'],
            selector=f['selector'], data_mapping=f['data_mapping'], data_relocations=records)
        self.assertEqual(len(records), 1)
        self.assertEqual(profile.linked_bytes(original, linked, A, calls, targets,
            data_relocations=records), f['data'])
        bad = copy.deepcopy(linked)
        text = bytearray(bad['text'])
        struct.pack_into('<I', text, len(text)-8, 0x05000002)
        bad['text'] = bytes(text)
        with self.assertRaisesRegex(ValueError, 'outside call relocations'):
            profile.linked_bytes(original, bad, A, calls, targets, data_relocations=records)

    def test_cli_report_authenticates_cached_control_policy_source_and_runtime(self):
        f = self.fixture()
        with patch.object(self.base.base, 'data_image', side_effect=self.data_image), \
                self.base.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            evidence = fill.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertFalse(evidence.report_matches(report.replace(
                'Scalar aliases may be consumed only', 'forged aliases'), root, A))
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(evidence.report_matches(report, root, A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
