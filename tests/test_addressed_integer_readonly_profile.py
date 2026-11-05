"""One explicit incoming ABI word composed with mixed addressed runtime calls."""
from contextlib import redirect_stdout
import io
import sys
import unittest
from unittest.mock import patch

import test_addressed_unsigned_runtime_profile as unsigned

profile, match, A = unsigned.profile, unsigned.match, unsigned.A


class IntegerReadonlyTests(unittest.TestCase):
    def setUp(self):
        self.base = unsigned.AddressedUnsignedRuntimeTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, access=0x9802):
        return dict(self.base.fixture((0xB510, access, 'udiv', 'div',
                                      0xBC10, 0xBC02, 0x4708)),
                    selector=profile.INTEGER_READONLY_SELECTOR)

    def test_actual_read_is_unknown_and_undeclared_reads_writes_escapes_refuse(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        incoming = manifest['frame']['entry_stack']
        self.assertEqual(incoming['words'], [0])
        self.assertEqual(incoming['reads'], [[A+2, 0, 4, '0298']])
        self.assertEqual(incoming['loaded_value'], 'unknown scalar; no provenance facts')
        self.assertIn('readonly_entry_stack_profile.py', manifest['producer_source_sha256'])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        for access in (0x9803, 0x9002, 0xA802):
            with self.subTest(access=access), self.assertRaises(ValueError):
                profile.verify(**self.fixture(access))
        for selector in (profile.INTEGER_SELECTOR, profile.SELECTOR, profile.UNSIGNED_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**dict(f, selector=selector))
        no_read = self.base.fixture((0xB510, 'udiv', 'div', 0xBC10, 0xBC02, 0x4708))
        with self.assertRaisesRegex(ValueError, 'actual checked incoming reads'):
            profile.verify(**dict(no_read, selector=profile.INTEGER_READONLY_SELECTOR))

    def test_cli_report_discloses_premise_and_rejects_stale_runtime_or_policy(self):
        f = self.fixture()
        f.update(data_mapping=b'{}', data_bindings=[])
        with self.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                 '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            self.assertIn('* incoming stack ABI: ', report)
            self.assertTrue(unsigned.fixtures.evidence.report_matches(report, root, A))
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(unsigned.fixtures.evidence.report_matches(report, root, A))
            with patch.object(profile, 'toolchain_fingerprint', return_value=[['changed', '2'*64]]):
                self.assertFalse(unsigned.fixtures.evidence.report_matches(report, root, A))
            changed = report.replace(profile.INTEGER_READONLY_SELECTOR, profile.INTEGER_SELECTOR)
            self.assertFalse(unsigned.fixtures.evidence.report_matches(changed, root, A))
