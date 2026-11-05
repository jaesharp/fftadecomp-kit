"""Distinct object and function identities under the existing BIOS source proof."""
from contextlib import redirect_stdout
import copy
import io
import json
import struct
import sys
import unittest
from unittest.mock import patch

import test_bios_cpuset_fill_profile as fill

profile, match, A, B = fill.profile, fill.match, fill.A, fill.B


class BiosFunctionLiteralTests(unittest.TestCase):
    def setUp(self):
        self.base = fill.BiosCpuSetFillTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self):
        f = self.base.fixture(data=True)
        body = bytearray(f['data'])
        body[6:6] = struct.pack('<HH', 0x4900, 0x6019)
        literal = len(body)
        body += struct.pack('<I', B | 1)
        object_offset = f['data_bindings'][0][0] + 4
        struct.pack_into('<H', body, 4, 0x4B00 | ((object_offset-8)//4))
        struct.pack_into('<H', body, 6, 0x4900 | ((literal-8)//4))
        f['calls'] = {site+4:target for site,target in f['calls'].items()}
        f['bindings'] = {site+4:name for site,name in f['bindings'].items()}
        for site,target in f['calls'].items():
            body[site-A:site-A+4] = fill.fixtures.fixtures.bl(site,target)
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        rows = json.loads(f['mapping'])
        rows[0].update(end=f'0x{A+len(body):08X}', instrs=rows[0]['instrs']+2)
        f['mapping'], f['index'] = fill.fixtures.fixtures.indexes(rows)
        f.update(data=bytes(body), rom=bytes(rom),
                 selector=profile.BIOS_FUNCTION_DATA_SELECTOR,
                 data_bindings=[[object_offset,'destination',0], [literal,f'func_{B:08X}',0]])
        return f

    def test_distinct_function_and_object_identities_keep_bounded_bios_source(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        self.assertEqual(manifest['function_literal_bindings'], [f['data_bindings'][-1][:2]])
        self.assertEqual(manifest['native_buffers']['bios_fill']['sites'][0][2], 2)
        self.assertIn('function literals are not objects', manifest['data_contract'])
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertFalse(manifest['original_formal_type_certainty'])
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, selector=profile.BIOS_DATA_SELECTOR))

    def test_original_and_linked_elf_keep_exact_function_types_and_thumb_bit(self):
        f = self.fixture()
        helper = self.base.base
        original = helper.data_image(f)
        linked = helper.linked_data_image(f, original)
        records = {}
        calls, bindings, targets = profile.original_bindings(original,A,f['rom'],f['mapping'],
            selector=f['selector'],data_mapping=f['data_mapping'],data_relocations=records)
        names = {f'func_{B:08X}'}
        self.assertEqual(profile.linked_bytes(original,linked,A,calls,targets,
            data_relocations=records,function_literals=names), f['data'])
        for kind in (1, 3):
            bad = copy.deepcopy(original)
            bad['symbols'][-1]['type'] = kind
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                profile.original_bindings(bad,A,f['rom'],f['mapping'],selector=f['selector'],
                    data_mapping=f['data_mapping'],data_relocations={})
        bad = copy.deepcopy(original)
        body = bytearray(bad['text'])
        struct.pack_into('<i',body,f['data_bindings'][-1][0],4)
        bad['text'] = bytes(body)
        with self.assertRaises(ValueError):
            profile.original_bindings(bad,A,f['rom'],f['mapping'],selector=f['selector'],
                data_mapping=f['data_mapping'],data_relocations={})
        for kind, value in ((1,B|1),(2,B)):
            bad = copy.deepcopy(linked)
            bad['symbols'][-1].update(type=kind,value=value)
            with self.subTest(kind=kind,value=value), self.assertRaises(ValueError):
                profile.linked_bytes(original,bad,A,calls,targets,
                    data_relocations=records,function_literals=names)

    def test_unknown_duplicate_arm_and_object_alias_entries_stay_refused(self):
        f = self.fixture()
        rows = json.loads(f['mapping'])
        target = next(row for row in rows if int(row['rom'],16)==B)
        for changed in ([row for row in rows if row is not target],
                        rows+[dict(target)],
                        [dict(row,mode='arm') if row is target else row for row in rows]):
            mapping,index = fill.fixtures.fixtures.indexes(changed)
            with self.subTest(rows=changed), self.assertRaises(ValueError):
                profile.verify(**dict(f,mapping=mapping,index=index))
        objects = json.loads(f['data_mapping'])
        objects[f'func_{B:08X}'] = f'0x{B:08X}'
        with self.assertRaises(ValueError):
            profile.verify(**dict(f,data_mapping=json.dumps(objects).encode()))
        records = copy.deepcopy(f['data_bindings'])
        records[-1][2] = 1
        with self.assertRaises(ValueError):
            profile.verify(**dict(f,data_bindings=records))

    def test_actual_boundaries_and_full_manifest_are_required(self):
        f = self.fixture()
        with self.assertRaises(ValueError):
            profile.verify(**dict(self.base.fixture(data=True),selector=f['selector']))
        manifest,_ = profile.verify(**f)
        with self.assertRaises(ValueError):
            profile.verify(**f,manifest=dict(manifest,function_literal_bindings=[]))
        rom = bytearray(f['rom'])
        rom[fill.bios.ADDRESS-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            profile.verify(**dict(f,rom=bytes(rom)))

    def test_cli_report_binds_original_types_source_runtime_and_producers(self):
        f = self.fixture()
        with self.base.base.build_boundary(f) as (root,_,_), patch.object(
                profile,'toolchain_fingerprint',return_value=[['synthetic','1'*64]]):
            with patch.object(sys,'argv',['match.py','--root',str(root),
                    '--addressed-runtime-profile',f['selector'],f'{A:08X}']),redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(),0)
            report = (root/'docs/match/08010000.md').read_text()
            evidence = fill.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report,root,A))
            with patch.object(profile,'runtime_fingerprint',return_value={'changed':True}):
                self.assertFalse(evidence.report_matches(report,root,A))
            pins = profile.data_producer_fingerprint(f['selector'])
            with patch.object(profile,'data_producer_fingerprint',return_value=dict(
                    pins,**{'addressed_signed_runtime_profile.py':'0'*64})):
                self.assertFalse(evidence.report_matches(report,root,A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report,root,A))


if __name__ == '__main__':
    unittest.main()
