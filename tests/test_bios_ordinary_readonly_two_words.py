"""Exactly two incoming words remain independent of the ordinary BIOS boundary."""
from contextlib import redirect_stdout
import io
import sys
import unittest
from unittest.mock import patch

import test_bios_cpuset_ordinary_data as ordinary

profile, match, bios, A = ordinary.profile, ordinary.match, ordinary.bios, ordinary.A


class OrdinaryBiosReadonlyTwoWordsTests(unittest.TestCase):
    setUp = ordinary.OrdinaryBiosDataTests.setUp

    def fixture(self, **options):
        options.setdefault('prefix', (0x9902, 0x9A03))
        f = ordinary.OrdinaryBiosDataTests.fixture(self, **options)
        f['selector'] = profile.BIOS_ORDINARY_READONLY_TWO_DATA_SELECTOR
        return f

    def test_actual_two_unknown_words_do_not_grant_bios_memory_effects(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        incoming = manifest['frame']['entry_stack']
        self.assertEqual(incoming['words'], [0, 1])
        self.assertEqual({row[1] for row in incoming['reads']}, {0, 4})
        self.assertEqual(incoming['loaded_value'], 'unknown scalar; no provenance facts')
        self.assertIn('readonly_entry_stack_words_profile.py', manifest['producer_source_sha256'])
        self.assertIn('no BIOS memory effects', manifest['bios_ordinary']['contract'])
        self.assertNotIn('native_buffers', manifest)
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertFalse(manifest['original_formal_type_certainty'])

    def test_missing_extra_written_or_addressed_words_and_local_aliases_refuse(self):
        for prefix in ((0x9902,), (0x9902, 0x9A03, 0x9904),
                       (0x9102, 0x9902, 0x9A03), (0xA902, 0x8809, 0x9A03)):
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                profile.verify(**self.fixture(prefix=prefix))
        f = self.fixture()
        for selector in (profile.BIOS_ORDINARY_DATA_SELECTOR, profile.BIOS_DATA_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**dict(f, selector=selector))
        for options in (dict(source=0x4668), dict(destination=0x4669),
                        dict(prefix=(0x9902, 0x9A03, 0x466A))):
            with self.subTest(options=options), self.assertRaises(ValueError):
                profile.verify(**self.fixture(**options))
        rom = bytearray(f['rom'])
        rom[bios.ADDRESS-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, rom=bytes(rom)))
        manifest, _ = profile.verify(**f)
        with self.assertRaises(ValueError):
            profile.verify(**f, manifest=dict(manifest, runtime_numeric_return_facts=[1]))

    def test_cli_replay_binds_both_boundaries_source_runtime_and_producers(self):
        f = self.fixture()
        with self.base.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            self.assertIn('* incoming stack ABI:', report)
            evidence = ordinary.fill.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report, root, A))
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(evidence.report_matches(report, root, A))
            pins = profile.data_producer_fingerprint(f['selector'])
            for name in ('readonly_entry_stack_words_profile.py', 'bios_cpuset_fill_profile.py'):
                with patch.object(profile, 'data_producer_fingerprint', return_value=dict(
                        pins, **{name: '0'*64})):
                    self.assertFalse(evidence.report_matches(report, root, A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
