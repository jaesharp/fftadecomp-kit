"""Ordinary BIOS calls without any object literal keep the same ABI limits."""
from contextlib import redirect_stdout
import io
import sys
import unittest
from unittest.mock import patch

import test_bios_cpuset_fill_profile as fill

profile, match, bios, A = fill.profile, fill.match, fill.bios, fill.A


class OrdinaryBiosTests(unittest.TestCase):
    def setUp(self):
        self.base = fill.BiosCpuSetFillTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, **changes):
        f = self.base.fixture(prefix=(), source=0x2000, **changes)
        f['selector'] = profile.BIOS_ORDINARY_SELECTOR
        return f

    def test_no_objects_have_their_own_explicit_ordinary_boundary(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        self.assertIn('bios_ordinary', manifest)
        self.assertNotIn('native_buffers', manifest)
        self.assertNotIn('data_bindings', manifest)
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, selector=profile.BIOS_ORDINARY_DATA_SELECTOR))
        data = self.fixture(data=True)
        data.pop('data_mapping')
        data.pop('data_bindings')
        with self.assertRaises(ValueError):
            profile.verify(**data)

    def test_local_aliases_and_wrapper_changes_remain_refused(self):
        for f in (self.fixture(destination=0x4669), self.fixture()):
            if f['data'] == self.fixture()['data']:
                rom = bytearray(f['rom'])
                rom[bios.ADDRESS-match.ROM_BASE] ^= 1
                f = dict(f, rom=bytes(rom))
            with self.assertRaises(ValueError):
                profile.verify(**f)
        local = self.base.fixture(prefix=(), source=0x4668)
        local['selector'] = profile.BIOS_ORDINARY_SELECTOR
        with self.assertRaises(ValueError):
            profile.verify(**local)

    def test_cli_and_source_runtime_report_replay_are_bound(self):
        f = self.fixture()
        f.update(data_bindings=[], data_mapping=b'{}')
        with self.base.base.build_boundary(f) as (root, _, _), patch.object(
                profile,'toolchain_fingerprint',return_value=[['synthetic','1'*64]]):
            with patch.object(sys,'argv',['match.py','--root',str(root),
                    '--addressed-runtime-profile',f['selector'],f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            evidence = fill.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report, root, A))
            with patch.object(profile,'runtime_fingerprint',return_value={'changed':True}):
                self.assertFalse(evidence.report_matches(report, root, A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
