"""Exact three-word incoming ABI premise, typed data and mixed runtime calls."""
from contextlib import redirect_stdout
import io
import sys
import unittest
from unittest.mock import patch

import test_addressed_unsigned_runtime_profile as unsigned

profile, match, A = unsigned.profile, unsigned.match, unsigned.A


class ThreeWordsDataTests(unittest.TestCase):
    def setUp(self):
        self.base = unsigned.AddressedUnsignedRuntimeTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, accesses=(0x9802, 0x9903, 0x9A04)):
        tokens = (0xB510, *accesses, 'udiv', 'div', 0x4C01,
                  0xBC10, 0xBC02, 0x4708, 0x0020, 0x0300)
        f = self.base.fixture(tokens)
        f.update(selector=profile.INTEGER_THREE_DATA_SELECTOR,
                 data_mapping=b'{"buffer":"0x03000020"}', data_bindings=[[24, 'buffer', 0]])
        return f

    def test_exact_three_reached_words_stay_unknown_and_boundaries_remain_closed(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        incoming = manifest['frame']['entry_stack']
        self.assertEqual(incoming['words'], [0, 1, 2])
        self.assertEqual([r[1] for r in incoming['reads']], [0, 4, 8])
        self.assertEqual(incoming['loaded_value'], 'unknown scalar; no provenance facts')
        self.assertEqual(manifest['data_bindings'], [[24, 'buffer', 0]])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        self.assertIn('readonly_entry_stack_words_profile.py', manifest['producer_source_sha256'])
        for accesses in ((0x9802, 0x9903, 0x9A05), (0x9802, 0x9903, 0x9A03),
                         (0x9802, 0x9903, 0x9204)):
            with self.subTest(accesses=accesses), self.assertRaises(ValueError):
                profile.verify(**self.fixture(accesses))
        for selector in (profile.INTEGER_DATA_SELECTOR, profile.READONLY_TWO_DATA_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**dict(f, selector=selector))
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, data_bindings=[]))

    def test_fresh_cli_report_discloses_premises_and_rejects_stale_inputs(self):
        f = self.fixture()
        with self.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                 '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            self.assertIn('* incoming stack ABI: ', report)
            self.assertIn('* named data binding: ', report)
            self.assertTrue(unsigned.fixtures.evidence.report_matches(report, root, A))
            for relative in ('config/data_symbols.json', 'src/08010000.c'):
                path = root/relative
                original = path.read_bytes()
                path.write_bytes(original+b' ')
                try:
                    self.assertFalse(unsigned.fixtures.evidence.report_matches(report, root, A))
                finally:
                    path.write_bytes(original)
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(unsigned.fixtures.evidence.report_matches(report, root, A))
