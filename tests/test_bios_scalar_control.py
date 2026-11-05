"""BIOS control values have a closed scalar use, separate from typed objects."""
from contextlib import redirect_stdout
import copy
import io
import json
import struct
import sys
import unittest
from unittest.mock import patch

import test_bios_cpuset_fill_profile as fixtures

profile, match, A = fixtures.profile, fixtures.match, fixtures.A


class BiosScalarControlTests(unittest.TestCase):
    def setUp(self):
        self.fixture_case = fixtures.BiosCpuSetFillTests('runTest')
        self.fixture_case.setUp()
        self.addCleanup(self.fixture_case.doCleanups)

    def fixture(self, **changes):
        f = self.fixture_case.fixture(data=True, control=0x05000010, **changes)
        f['selector'] = profile.BIOS_SCALAR_DATA_SELECTOR
        return f

    def test_numeric_control_is_bound_without_a_fabricated_object(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        controls = manifest['bios_scalar_control']['words']
        self.assertEqual(len(controls), 1)
        self.assertEqual(controls[0][1], 0x05000010)
        self.assertEqual(len(controls[0][2]), 1)
        self.assertNotIn(controls[0][0], [r[0] for r in manifest['data_bindings']])
        self.assertEqual(manifest['native_buffers']['bios_fill']['sites'][0][2], 4)
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        with self.assertRaisesRegex(ValueError, 'typed coverage'):
            profile.verify(**dict(f, selector=profile.BIOS_DATA_SELECTOR))

    def test_control_use_cannot_escape_into_another_argument_or_register(self):
        with self.assertRaises(ValueError):
            profile.verify(**self.fixture(destination=0x1C11))  # r1 = r2
        f = self.fixture()
        data = bytearray(f['data'])
        load = next(i for i in range(0, len(data)-1, 2)
                    if struct.unpack_from('<H', data, i)[0] & 0xFF00 == 0x4A00)
        data[load+1] = 0x4B  # the same word loaded into r3, never a scalar control
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        with self.assertRaisesRegex(ValueError, 'actual literal control use'):
            profile.verify(**dict(f, data=bytes(data), rom=bytes(rom)))

    def test_scalar_control_cannot_be_relabelled_as_a_typed_object(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        offset = manifest['bios_scalar_control']['words'][0][0]
        objects = json.loads(f['data_mapping'])
        objects['fake_control'] = '0x05000010'
        with self.assertRaisesRegex(ValueError, 'also be a typed object'):
            profile.verify(**dict(f, data_mapping=json.dumps(objects).encode(),
                data_bindings=sorted(f['data_bindings']+[[offset,'fake_control',0]])))
        forged = copy.deepcopy(manifest)
        forged['bios_scalar_control']['words'][0][1] ^= 1
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            profile.verify(**f, manifest=forged)

    def test_native_cli_and_report_replay_keep_original_admission_guards(self):
        f = self.fixture()
        with self.fixture_case.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic','1'*64]]):
            with patch.object(sys, 'argv', ['match.py','--root',str(root),
                    '--addressed-runtime-profile',f['selector'],f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            evidence = fixtures.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertFalse(evidence.report_matches(report.replace(
                'scalar control identity', 'forged control identity'), root, A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
