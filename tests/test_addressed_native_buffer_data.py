"""Signed and typed-data compositions retain the existing native alias proof."""
import copy
from contextlib import redirect_stdout
import io
import json
import sys
import unittest
from unittest.mock import patch

import test_addressed_unsigned_native_buffer as native

profile, match, A = native.profile, native.match, native.A


class AddressedNativeBufferDataTests(unittest.TestCase):
    def setUp(self):
        self.base = native.AddressedUnsignedNativeBufferTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, signed=True, data=False):
        f = self.base.fixture()
        body, rom = bytearray(f['data']), bytearray(f['rom'])
        if signed:
            site = next(site for site, target in f['calls'].items()
                        if target == match.UDIVSI3_ADDRESS)
            target = profile.quotient.ADDRESS
            body[site-A:site-A+4] = native.unsigned.fixtures.bl(site, target)
            f['calls'][site], f['bindings'][site] = target, f'func_{target:08X}'
        rows = json.loads(f['mapping'])
        if data:
            body[18:18] = b'\x02\x4c'
            self.assertEqual(len(body), 28)
            body += b'\x20\x00\x00\x03'
            row = next(r for r in rows if int(r['rom'], 16) == A)
            row.update(end=f'0x{A+len(body):08X}', instrs=row['instrs']+1)
            f['mapping'], f['index'] = native.unsigned.fixtures.indexes(rows)
            f.update(data_mapping=b'{"buffer":"0x03000020"}',
                     data_bindings=[[28, 'buffer', 0]])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        selector = profile.BUFFER_DATA_SELECTOR if data else profile.BUFFER_SELECTOR
        if not signed:
            selector = profile.UNSIGNED_BUFFER_DATA_SELECTOR if data else profile.UNSIGNED_BUFFER_SELECTOR
        f.update(data=bytes(body), rom=bytes(rom), selector=selector)
        return f

    def test_explicit_compositions_require_both_buffer_and_typed_identity(self):
        for signed, data in ((True, False), (True, True), (False, True)):
            with self.subTest(signed=signed, data=data):
                f = self.fixture(signed, data)
                manifest, _ = profile.verify(**f)
                self.assertEqual(manifest['schema'], profile.SCHEMAS[f['selector']])
                self.assertEqual(manifest['native_buffers']['dependencies'][0][:2], [native.B, 8])
                self.assertEqual(manifest['runtime_numeric_return_facts'], [])
                old = profile.DATA_SELECTOR if signed and data else profile.SELECTOR if signed else profile.UNSIGNED_DATA_SELECTOR
                with self.assertRaises(ValueError):
                    profile.verify(**dict(f, selector=old))
                bad = dict(f)
                rom = bytearray(f['rom'])
                rom[native.B-match.ROM_BASE+3] = 0x71
                bad['rom'] = bytes(rom)
                with self.assertRaises(ValueError):
                    profile.verify(**bad)
                if data:
                    self.assertEqual(manifest['data_bindings'], f['data_bindings'])
                    for bindings in ([], [[28, 'buffer', 4]], [[24, 'buffer', 0]]):
                        with self.assertRaises(ValueError):
                            profile.verify(**dict(f, data_bindings=bindings))

    def test_data_cli_and_replay_pin_sources_native_helpers_and_runtime(self):
        for signed in (True, False):
            with self.subTest(signed=signed):
                f = self.fixture(signed, True)
                with self.base.base.build_boundary(f) as (root, _, _), patch.object(
                        profile, 'toolchain_fingerprint', return_value=[['synthetic', '1' * 64]]):
                    with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                         '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                        self.assertEqual(match.main(), 0)
                    report = (root / 'docs/match/08010000.md').read_text()
                    self.assertTrue(native.unsigned.fixtures.evidence.report_matches(report, root, A))
                    with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                        self.assertFalse(native.unsigned.fixtures.evidence.report_matches(report, root, A))
                    pins = profile.data_producer_fingerprint(f['selector'])
                    with patch.object(profile, 'data_producer_fingerprint',
                                      return_value=dict(pins, **{'match.py': '0' * 64})):
                        self.assertFalse(native.unsigned.fixtures.evidence.report_matches(report, root, A))
                    original = (root / 'baserom.bin').read_bytes()
                    changed = bytearray(original)
                    changed[native.B-match.ROM_BASE] ^= 1
                    (root / 'baserom.bin').write_bytes(changed)
                    self.assertFalse(native.unsigned.fixtures.evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
