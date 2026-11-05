"""Exact BIOS wrapper and canonical mapped R2 callback compose explicitly."""
from contextlib import redirect_stdout
import io
import json
import sys
import unittest
from unittest.mock import patch

import test_addressed_r2_callback as callback
import bios_cpuset_fill_profile as bios

profile, match, A = callback.profile, callback.match, callback.A


class BiosR2CallbackTests(unittest.TestCase):
    def setUp(self):
        self.base = callback.R2CallbackTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self):
        f = self.base.fixture()
        body = bytearray(f['data'])
        body[22:22] = callback.bl(A+22, bios.ADDRESS)
        body[2:4] = bytes.fromhex('074a')
        body[4:6] = bytes.fromhex('0748')
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        rom[bios.ADDRESS-match.ROM_BASE:bios.ADDRESS-match.ROM_BASE+4] = bios.WRAPPER
        rows = json.loads(f['mapping'])
        rows[0].update(end=f'0x{A+len(body):08X}', instrs=rows[0]['instrs']+1)
        rows.append(dict(rom=f'0x{bios.ADDRESS:08X}', end=f'0x{bios.ADDRESS+4:08X}', mode='thumb', instrs=2))
        f['mapping'], f['index'] = callback.indexes(rows)
        f.update(data=bytes(body), rom=bytes(rom),
                 data_bindings=[[offset+4, name, addend] for offset, name, addend in f['data_bindings']])
        f['calls'][A+22] = bios.ADDRESS
        f['bindings'][A+22] = bios.NAME
        return f

    def verify(self, f, **options):
        return profile.verify(**f, selector=profile.BIOS_R2_ORDINARY_DATA_SELECTOR, **options)

    def test_both_actual_boundaries_and_their_dependencies_are_recorded(self):
        f = self.fixture()
        manifest, _ = self.verify(f)
        self.assertEqual(manifest['bios_ordinary']['calls'], [22])
        self.assertEqual(len(manifest['callback']['sites']), 1)
        self.assertIn('no callback numeric', manifest['callback']['contract'])
        self.assertIn('bios_cpuset_fill_profile.py', manifest['producer_source_sha256'])
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertNotIn('native_buffers', manifest)

    def test_absent_bios_and_alias_escape_stay_refused(self):
        with self.assertRaises(ValueError):
            self.verify(self.base.fixture())
        f = self.fixture()
        # A genuine SP value cannot be smuggled through an ordinary call.
        f = self.base.mutate_body(f, 14, 0x4668)
        with self.assertRaises(ValueError):
            self.verify(f)
        with self.assertRaises(ValueError):
            profile.verify(**self.fixture(), selector=profile.BIOS_ORDINARY_DATA_SELECTOR)

    def test_wrapper_thunk_and_manifest_are_bound(self):
        f = self.fixture()
        manifest, _ = self.verify(f)
        for address in (bios.ADDRESS, match.function_thunk.ALIASES['_call_via_r2']):
            rom = bytearray(f['rom'])
            rom[address-match.ROM_BASE] ^= 1
            with self.subTest(address=address), self.assertRaises(ValueError):
                self.verify(dict(f, rom=bytes(rom)))
        with self.assertRaises(ValueError):
            self.verify(f, manifest=dict(manifest, runtime_numeric_return_facts=[1]))

    def test_cli_source_runtime_and_producer_replay_guards(self):
        f = self.fixture()
        with self.base.build_fixture(f) as (root, *_), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', profile.BIOS_R2_ORDINARY_DATA_SELECTOR,
                    f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            self.assertTrue(callback.evidence.report_matches(report, root, A))
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(callback.evidence.report_matches(report, root, A))
            pins = profile.data_producer_fingerprint(profile.BIOS_R2_ORDINARY_DATA_SELECTOR)
            with patch.object(profile, 'data_producer_fingerprint', return_value=dict(
                    pins, **{'bios_cpuset_fill_profile.py': '0'*64})):
                self.assertFalse(callback.evidence.report_matches(report, root, A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(callback.evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
