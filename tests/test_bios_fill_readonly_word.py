"""Compose explicit incoming word0 with the bounded BIOS local source proof."""
from contextlib import redirect_stdout
import io
import sys
import unittest
from unittest.mock import patch

import test_bios_cpuset_fill_profile as fill

profile, match, bios, A = fill.profile, fill.match, fill.bios, fill.A


class BiosReadonlyWordTests(unittest.TestCase):
    def setUp(self):
        self.base = fill.BiosCpuSetFillTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, **options):
        options.setdefault('prefix', (0x9902, 0x2280, 0x0452))
        f = self.base.fixture(data=True, **options)
        f['selector'] = profile.BIOS_READONLY_DATA_SELECTOR
        return f

    def test_actual_word_read_and_bounded_source_have_distinct_premises(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        self.assertEqual(manifest['frame']['entry_stack']['words'], [0])
        self.assertTrue(manifest['frame']['entry_stack']['reads'])
        self.assertEqual(manifest['native_buffers']['bios_fill']['sites'][0][2], 2)
        self.assertIn('readonly_entry_stack_profile.py', manifest['producer_source_sha256'])
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertFalse(manifest['original_formal_type_certainty'])
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, selector=profile.BIOS_DATA_SELECTOR))
        with self.assertRaises(ValueError):
            profile.verify(**self.fixture(prefix=(0x2280, 0x0452)))

    def test_extra_words_writes_aliases_and_local_destinations_stay_refused(self):
        for prefix in ((0x9903, 0x2280, 0x0452),
                       (0x9102, 0x9902, 0x2280, 0x0452),
                       (0xA902, 0x8809, 0x2280, 0x0452)):
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                profile.verify(**self.fixture(prefix=prefix))
        for options in (dict(destination=0x4669), dict(source=0xA801),
                        dict(prefix=(0x9902, 0x2200))):
            with self.subTest(options=options), self.assertRaises(ValueError):
                profile.verify(**self.fixture(**options))

    def test_wrapper_and_exact_manifest_remain_authenticated(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        rom = bytearray(f['rom'])
        rom[bios.ADDRESS-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, rom=bytes(rom)))
        changed = dict(manifest, runtime_numeric_return_facts=[1])
        with self.assertRaises(ValueError):
            profile.verify(**f, manifest=changed)

    def test_cli_replay_binds_source_runtime_and_both_premises(self):
        f = self.fixture()
        with self.base.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            self.assertIn('* incoming stack ABI:', report)
            self.assertIn('* local buffer boundary:', report)
            evidence = fill.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report, root, A))
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(evidence.report_matches(report, root, A))
            pins = profile.data_producer_fingerprint(f['selector'])
            with patch.object(profile, 'data_producer_fingerprint', return_value=dict(
                    pins, **{'readonly_entry_stack_profile.py': '0'*64})):
                self.assertFalse(evidence.report_matches(report, root, A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
