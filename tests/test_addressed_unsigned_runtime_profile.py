"""Explicit conditional unsigned ABI admission; synthetic ELF/ROM, no compiler."""
import copy
from contextlib import redirect_stdout
import hashlib
import io
import json
import struct
import sys
import unittest
from unittest.mock import patch

import test_addressed_signed_runtime_profile as fixtures
import test_addressed_signed_runtime_two_words_data as data_fixtures

profile = fixtures.profile
match = fixtures.match
A, B = fixtures.A, fixtures.B


class AddressedUnsignedRuntimeTests(unittest.TestCase):
    image = fixtures.AddressedSignedRuntimeTests.image
    data_image = fixtures.AddressedSignedRuntimeTests.data_image
    linked_data_image = fixtures.AddressedSignedRuntimeTests.linked_data_image
    build_boundary = data_fixtures.TwoWordsDataTests.build_boundary

    def setUp(self):
        fixtures.AddressedSignedRuntimeTests.setUp(self)
        self.fixtures = self
        self.rom[0x142B20:0x142B24] = fixtures.bl(0x08142B20, 0x0814274C)
        self.rom[0x142BE0:0x142BE4] = fixtures.bl(0x08142BE0, 0x0814274C)
        for module, field in ((match, 'UDIVSI3_IDENTITIES'),
                              (profile.unsigned_remainder, 'IDENTITIES')):
            spans = tuple((lo, hi, hashlib.sha256(
                self.rom[lo-match.ROM_BASE:hi-match.ROM_BASE]).hexdigest())
                for lo, hi, _ in getattr(module, field))
            change = patch.object(module, field, spans)
            change.start()
            self.addCleanup(change.stop)

    def fixture(self, tokens=(0xB510, 0x2100, 'udiv', 'umod', 0xBC10, 0xBC02, 0x4708)):
        data, calls, bindings = bytearray(), {}, {}
        targets = dict(udiv=match.UDIVSI3_ADDRESS, umod=profile.unsigned_remainder.ADDRESS,
                       div=profile.quotient.ADDRESS, ordinary=B)
        for token in tokens:
            if isinstance(token, int):
                data += struct.pack('<H', token)
            else:
                target, site = targets[token], A + len(data)
                data += fixtures.bl(site, target)
                calls[site] = target
                if token != 'ordinary':
                    bindings[site] = f'func_{target:08X}'
        spans = set(match.UDIVSI3_IDENTITIES + profile.unsigned_remainder.IDENTITIES +
                    profile.quotient.IDENTITIES + profile.remainder.IDENTITIES)
        rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(data):08X}', mode='thumb',
                     instrs=len(tokens)),
                dict(rom=f'0x{B:08X}', end=f'0x{B+2:08X}', mode='thumb', instrs=1)]
        rows += [dict(rom=f'0x{lo:08X}', end=f'0x{hi:08X}', mode='thumb',
                      instrs=(hi-lo)//2) for lo, hi, _ in sorted(spans)]
        mapping, index = fixtures.indexes(rows)
        rom = bytearray(self.rom)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return dict(data=bytes(data), address=A, rom=bytes(rom), mapping=mapping,
                    index=index, calls=calls, bindings=bindings,
                    selector=profile.UNSIGNED_SELECTOR)

    def test_full_words_zero_mixed_entries_and_ordinary_calls(self):
        for tokens in [('udiv',), ('umod',), ('udiv', 'umod'), ('udiv', 'ordinary', 'umod')]:
            with self.subTest(tokens=tokens):
                f = self.fixture((0xB510, 0x2100, *tokens, 0xBC10, 0xBC02, 0x4708))
                manifest, instructions = profile.verify(**f)
                self.assertEqual(manifest['schema'], profile.UNSIGNED_SCHEMA)
                self.assertEqual(manifest['runtime_numeric_return_facts'], [])
                self.assertFalse(manifest['arithmetic_C_equivalence'])
                self.assertFalse(manifest['original_formal_type_certainty'])
                self.assertEqual(len(instructions), len(tokens)+5)
                self.assertIn('umodsi3_profile.py', manifest['producer_source_sha256'])

    def test_original_addressed_relocations_and_exact_linked_body(self):
        f = self.fixture()
        image = self.image(f)
        calls, bindings, targets = profile.original_bindings(
            image, A, f['rom'], f['mapping'], selector=f['selector'])
        self.assertEqual((calls, bindings), (f['calls'], f['bindings']))
        linked = copy.deepcopy(image)
        linked.update(type=2, text=f['data'], relocations=[])
        section = list(linked['sections'][1])
        section[3] = A
        linked['sections'][1] = tuple(section)
        for symbol in linked['symbols']:
            if symbol['section']:
                symbol['value'] = A | 1
            else:
                symbol.update(value=targets[symbol['name']] | 1, section=0xFFF1, type=2)
        self.assertEqual(profile.linked_bytes(image, linked, A, calls, targets), f['data'])
        for alias in ('__udivsi3', '__umodsi3', 'func_08142AB2', 'func_0814274C'):
            bad = copy.deepcopy(image)
            bad['symbols'][1]['name'] = alias
            with self.subTest(alias=alias), self.assertRaises(ValueError):
                profile.original_bindings(bad, A, f['rom'], f['mapping'], selector=f['selector'])
        linked['text'] = bytes([f['data'][0] ^ 1]) + f['data'][1:]
        with self.assertRaises(ValueError):
            profile.linked_bytes(image, linked, A, calls, targets)

    def test_signed_selectors_and_default_verifier_still_reject_unsigned(self):
        f = self.fixture()
        for selector in (profile.SELECTOR, profile.READONLY_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**dict(f, selector=selector))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(f['data'], A, True, f['calls'])
        with self.assertRaises(ValueError):
            profile.original_bindings(self.image(f), A, f['rom'], f['mapping'])
        mixed = self.fixture((0xB510, 'udiv', 'div', 0xBC10, 0xBC02, 0x4708))
        with self.assertRaises(ValueError):
            profile.verify(**mixed)

    def test_runtime_zero_hook_indexes_bindings_and_frame_remain_checked(self):
        f = self.fixture()
        for address in (match.UDIVSI3_ADDRESS, profile.unsigned_remainder.ADDRESS, 0x0814274C):
            bad = dict(f)
            rom = bytearray(f['rom'])
            rom[address-match.ROM_BASE] ^= 1
            bad['rom'] = bytes(rom)
            with self.subTest(address=address), self.assertRaises(ValueError):
                profile.verify(**bad)
        for change in ('missing', 'duplicate', 'overlap', 'text'):
            bad = dict(f)
            rows = json.loads(f['mapping'])
            if change == 'missing':
                rows = [r for r in rows if int(r['rom'], 16) != match.UDIVSI3_ADDRESS]
            elif change == 'duplicate':
                rows.append(rows[0].copy())
            elif change == 'overlap':
                rows.append(dict(rows[0], rom=f'0x{A+2:08X}'))
            bad['mapping'], bad['index'] = fixtures.indexes(rows)
            if change == 'text':
                bad['index'] = bad['index'].replace(b'08142AB0', b'08142AB2')
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile.verify(**bad)
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, bindings={}))
        with self.assertRaises(ValueError):
            profile.verify(**self.fixture((0xB510, 0xB081, 'udiv', 0xBC10, 0xBC02, 0x4708)))

    def test_unsigned_data_requires_exact_typed_reached_coverage(self):
        f = self.fixture((0xB510, 'udiv', 0x4C02, 0xBC10, 0xBC02, 0x4708,
                          0x0000, 0x0020, 0x0300))
        objects = json.dumps({'buffer': '0x03000020'}).encode()
        f.update(selector=profile.UNSIGNED_DATA_SELECTOR, data_mapping=objects,
                 data_bindings=[[16, 'buffer', 0]])
        manifest, _ = profile.verify(**f)
        self.assertEqual(manifest['data_bindings'], [[16, 'buffer', 0]])
        self.assertEqual(manifest['schema'], profile.UNSIGNED_DATA_SCHEMA)
        for bindings in ([], [[16, 'buffer', 4]], [[12, 'buffer', 0]]):
            with self.subTest(bindings=bindings), self.assertRaises(ValueError):
                profile.verify(**dict(f, data_bindings=bindings))
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, data_mapping=json.dumps({'buffer': f'0x{B:08X}'}).encode()))

    def data_fixture(self):
        f = self.fixture((0xB510, 'udiv', 0x4C02, 0xBC10, 0xBC02, 0x4708,
                          0x0000, 0x0020, 0x0300))
        f.update(selector=profile.UNSIGNED_DATA_SELECTOR,
                 data_mapping=b'{"buffer":"0x03000020"}', data_bindings=[[16, 'buffer', 0]])
        return f

    def test_data_original_ELF_binds_object_relocation_and_runtime_separately(self):
        f = self.data_fixture()
        original = self.data_image(f)
        linked = self.linked_data_image(f, original)
        records = {}
        calls, bindings, targets = profile.original_bindings(
            original, A, f['rom'], f['mapping'], selector=f['selector'],
            data_mapping=f['data_mapping'], data_relocations=records)
        self.assertEqual(records, {16: ('buffer', 0)})
        self.assertEqual(bindings, f['bindings'])
        self.assertEqual(profile.linked_bytes(original, linked, A, calls, targets,
                                             data_relocations=records), f['data'])
        bad = copy.deepcopy(original)
        bad['symbols'][-1]['name'] = 'unmapped'
        with self.assertRaises(ValueError):
            profile.original_bindings(bad, A, f['rom'], f['mapping'], selector=f['selector'],
                                      data_mapping=f['data_mapping'], data_relocations={})

    def test_fresh_cli_report_status_and_publisher_reject_stale_inputs(self):
        for selector in profile.UNSIGNED_SELECTORS:
            f = self.data_fixture() if selector == profile.UNSIGNED_DATA_SELECTOR else self.fixture()
            f.setdefault('data_mapping', b'{}')
            f.setdefault('data_bindings', [])
            with self.subTest(selector=selector), self.build_boundary(f) as (root, _, _), patch.object(
                    profile, 'toolchain_fingerprint', return_value=[['synthetic', '1' * 64]]):
                with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                     '--addressed-runtime-profile', selector, f'{A:08X}']), redirect_stdout(io.StringIO()):
                    self.assertEqual(match.main(), 0)
                report = (root / 'docs/match/08010000.md').read_text()
                self.assertEqual(profile.selector_for_report(report), selector)
                self.assertTrue(fixtures.evidence.report_matches(report, root, A))
                self.assertEqual(fixtures.status.collect(str(root), verify=False)[1], 1)
                with redirect_stdout(io.StringIO()):
                    self.assertTrue(fixtures.push.check_reports(str(root)))
                for relative in ('src/08010000.c', 'include/fixture.h', 'config/functions.json',
                                 'symbols/functions.txt', 'config/data_symbols.json', 'baserom.bin'):
                    path = root / relative
                    original = path.read_bytes()
                    path.write_bytes(original + b' ')
                    try:
                        self.assertFalse(fixtures.evidence.report_matches(report, root, A))
                    finally:
                        path.write_bytes(original)
                with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                    self.assertFalse(fixtures.evidence.report_matches(report, root, A))

    def test_fresh_build_checks_unsigned_producer_and_midrun_runtime(self):
        f = self.data_fixture()
        with self.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1' * 64]]):
            result = profile.build(root, A, selector=f['selector'])
            self.assertEqual(result['body'], f['data'])
            self.assertIn('umodsi3_profile.py', result['manifest']['producer_source_sha256'])
            with patch.object(profile, 'runtime_fingerprint',
                              side_effect=[result['runtime'], {'changed': True}]):
                with self.assertRaisesRegex(ValueError, 'changed during verification'):
                    profile.build(root, A, selector=f['selector'])
            pins = profile.data_producer_fingerprint(f['selector'])
            altered = dict(pins, **{'umodsi3_profile.py': '0' * 64})
            with patch.object(profile, 'data_producer_fingerprint', side_effect=[pins, pins, altered]):
                with self.assertRaisesRegex(ValueError, 'changed during verification'):
                    profile.build(root, A, selector=f['selector'])


if __name__ == '__main__':
    unittest.main()
