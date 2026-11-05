"""Compose exactly three incoming ABI words with the bounded BIOS source proof."""
from contextlib import redirect_stdout
import io
import sys
import unittest
from unittest.mock import patch

import test_bios_fill_readonly_word as word

profile, match, bios, A = word.profile, word.match, word.bios, word.A


class BiosReadonlyThreeWordsTests(unittest.TestCase):
    setUp = word.BiosReadonlyWordTests.setUp

    def fixture(self, **options):
        options.setdefault('prefix', (0x9902, 0x9903, 0x9904, 0x2280, 0x0452))
        f = self.base.fixture(data=True, **options)
        f['selector'] = profile.BIOS_READONLY_THREE_DATA_SELECTOR
        return f

    def test_three_actual_unknown_words_remain_separate_from_bios_memory(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        incoming = manifest['frame']['entry_stack']
        self.assertEqual(incoming['words'], [0, 1, 2])
        self.assertEqual({row[1] for row in incoming['reads']}, {0, 4, 8})
        self.assertEqual(incoming['loaded_value'], 'unknown scalar; no provenance facts')
        self.assertIn('readonly_entry_stack_words_profile.py', manifest['producer_source_sha256'])
        self.assertEqual(manifest['native_buffers']['bios_fill']['sites'][0][2], 2)
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertFalse(manifest['original_formal_type_certainty'])

    def test_extra_missing_written_or_addressed_words_and_old_selectors_refuse(self):
        for prefix in ((0x9902, 0x9903, 0x2280, 0x0452),
                       (0x9902, 0x9903, 0x9904, 0x9905, 0x2280, 0x0452),
                       (0x9102, 0x9902, 0x9903, 0x9904, 0x2280, 0x0452),
                       (0xA902, 0x8809, 0x9903, 0x9904, 0x2280, 0x0452)):
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                profile.verify(**self.fixture(prefix=prefix))
        f = self.fixture()
        for selector in (profile.BIOS_DATA_SELECTOR, profile.BIOS_READONLY_DATA_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**dict(f, selector=selector))
        with self.assertRaises(ValueError):
            profile.verify(**self.fixture(destination=0x4669))
        manifest, _ = profile.verify(**f)
        with self.assertRaises(ValueError):
            profile.verify(**f, manifest=dict(manifest, runtime_numeric_return_facts=[1]))
        rom = bytearray(f['rom'])
        rom[bios.ADDRESS-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, rom=bytes(rom)))

    def test_cli_replay_binds_word_policy_source_runtime_and_bios_producer(self):
        f = self.fixture()
        with self.base.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            self.assertIn('* incoming stack ABI:', report)
            self.assertIn('* local buffer boundary:', report)
            evidence = word.fill.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report, root, A))
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(evidence.report_matches(report, root, A))
            pins = profile.data_producer_fingerprint(f['selector'])
            with patch.object(profile, 'data_producer_fingerprint', return_value=dict(
                    pins, **{'readonly_entry_stack_words_profile.py': '0'*64})):
                self.assertFalse(evidence.report_matches(report, root, A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
