"""Mixed addressed integer entries retain separate conditional ABI admission."""
import copy
from contextlib import redirect_stdout
import io
import sys
import unittest
from unittest.mock import patch

import test_addressed_unsigned_runtime_profile as unsigned

profile, match, A = unsigned.profile, unsigned.match, unsigned.A


class AddressedIntegerRuntimeTests(unittest.TestCase):
    def setUp(self):
        self.base = unsigned.AddressedUnsignedRuntimeTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, *, data=False, signed_mod=False):
        tokens = (0xB510, 'udiv', 'div', 'umod', 0xBC10, 0xBC02, 0x4708)
        if data:
            tokens = (0xB510, 'udiv', 'div', 'umod', 0x4C02,
                      0xBC10, 0xBC02, 0x4708, 0x0000, 0x0020, 0x0300)
        f = self.base.fixture(tokens)
        if signed_mod:
            site = next(site for site, target in f['calls'].items()
                        if target == profile.quotient.ADDRESS)
            target = profile.remainder.ADDRESS
            body = bytearray(f['data'])
            body[site-A:site-A+4] = unsigned.fixtures.bl(site, target)
            rom = bytearray(f['rom'])
            rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
            f.update(data=bytes(body), rom=bytes(rom))
            f['calls'][site] = target
            f['bindings'][site] = f'func_{target:08X}'
        f['selector'] = profile.INTEGER_DATA_SELECTOR if data else profile.INTEGER_SELECTOR
        if data:
            f.update(data_mapping=b'{"buffer":"0x03000020"}',
                     data_bindings=[[24, 'buffer', 0]])
        return f

    def test_all_four_entries_and_both_selectors_authenticate_each_runtime(self):
        for data in (False, True):
            for signed_mod in (False, True):
                f = self.fixture(data=data, signed_mod=signed_mod)
                with self.subTest(data=data, signed_mod=signed_mod):
                    manifest, _ = profile.verify(**f)
                    self.assertEqual(manifest['schema'], profile.SCHEMAS[f['selector']])
                    self.assertEqual(manifest['runtime_numeric_return_facts'], [])
                    self.assertFalse(manifest['arithmetic_C_equivalence'])
                    self.assertFalse(manifest['original_formal_type_certainty'])
                    for address in set(f['calls'].values()) | {0x0814274C}:
                        bad = copy.deepcopy(f)
                        rom = bytearray(f['rom'])
                        rom[address-match.ROM_BASE] ^= 1
                        bad['rom'] = bytes(rom)
                        with self.assertRaises(ValueError):
                            profile.verify(**bad)

    def test_explicit_mixed_selector_does_not_relax_existing_or_default_admission(self):
        f = self.fixture()
        for selector in (profile.SELECTOR, profile.UNSIGNED_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**dict(f, selector=selector))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(f['data'], A, True, f['calls'])
        unsigned_only = self.base.fixture()
        with self.assertRaisesRegex(ValueError, 'actual signed and unsigned'):
            profile.verify(**dict(unsigned_only, selector=profile.INTEGER_SELECTOR))
        for data in (False, True):
            f = self.fixture(data=data)
            original = self.base.data_image(f) if data else self.base.image(f)
            options = dict(data_mapping=f['data_mapping'], data_relocations={}) if data else {}
            calls, bindings, _ = profile.original_bindings(
                original, A, f['rom'], f['mapping'], selector=f['selector'], **options)
            self.assertEqual((calls, bindings), (f['calls'], f['bindings']))
            for name in ('__divsi3', '__udivsi3', 'func_08142AB2'):
                bad = copy.deepcopy(original)
                bad['symbols'][1]['name'] = name
                with self.subTest(name=name), self.assertRaises(ValueError):
                    profile.original_bindings(bad, A, f['rom'], f['mapping'],
                                             selector=f['selector'], **options)

    def test_mixed_cli_source_replay_report_and_stale_runtime(self):
        for data in (False, True):
            f = self.fixture(data=data)
            f.setdefault('data_mapping', b'{}')
            f.setdefault('data_bindings', [])
            with self.subTest(data=data), self.base.build_boundary(f) as (root, _, _), patch.object(
                    profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
                with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                     '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                    self.assertEqual(match.main(), 0)
                report = (root/'docs/match/08010000.md').read_text()
                self.assertEqual(profile.selector_for_report(report), f['selector'])
                self.assertTrue(unsigned.fixtures.evidence.report_matches(report, root, A))
                with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                    self.assertFalse(unsigned.fixtures.evidence.report_matches(report, root, A))
                path = root/'src/08010000.c'
                path.write_text(path.read_text()+'\n')
                self.assertFalse(unsigned.fixtures.evidence.report_matches(report, root, A))
