"""Compiler runtime aliases and literal-only MMIO retain separate identities."""
import copy
from contextlib import contextmanager, redirect_stdout
import io
import json
import struct
import sys
import unittest
from unittest.mock import patch

import test_compiler_signed_runtime_data as fixtures

profile, match, A = fixtures.profile, fixtures.match, fixtures.A
SELECTOR = profile.COMPILER_MMIO_DATA_SELECTOR


class CompilerSignedRuntimeNumericMmioTests(unittest.TestCase):
    def setUp(self):
        self.base = fixtures.CompilerSignedRuntimeDataTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, value=0x04000100, mixed=False):
        f = (self.base.base.fixtures.data_fixture() if mixed else self.base.fixture())
        offset = f['data_bindings'][0][0]
        body = bytearray(f['data'])
        struct.pack_into('<I', body, offset, value)
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        f.update(data=bytes(body), rom=bytes(rom), data_bindings=f['data_bindings'][1:])
        return f

    @contextmanager
    def build_boundary(self, f=None):
        helper = self.base.base.fixtures
        original_builder, linked_builder = helper.data_image, helper.linked_data_image

        def original(value):
            return self.base.rename(original_builder(value))

        def linked(value, image):
            canonical = self.base.rename(copy.deepcopy(image), reverse=True)
            return self.base.rename(linked_builder(value, canonical))

        with patch.object(helper, 'data_image', side_effect=original), \
                patch.object(helper, 'linked_data_image', side_effect=linked):
            with self.base.base.build_boundary(f or self.fixture()) as result:
                yield result

    def test_numeric_only_boundaries_and_old_selectors_remain_strict(self):
        for value in (0x04000000, 0x04000100, 0x040003FE):
            f = self.fixture(value)
            manifest, _ = profile.verify(**f, selector=SELECTOR)
            self.assertEqual(manifest['schema'], profile.COMPILER_MMIO_DATA_SCHEMA)
            self.assertEqual(manifest['data_bindings'], [])
            self.assertEqual(manifest['numeric_mmio_literals']['words'][0][1], value)
            self.assertEqual(manifest['runtime_numeric_return_facts'], [])
            self.assertFalse(manifest['arithmetic_C_equivalence'])
            self.assertNotIn('bios_scalar_control', manifest)
            self.assertNotIn('native_buffers', manifest)
        for selector in (profile.COMPILER_DATA_SELECTOR, profile.DATA_SELECTOR,
                         profile.BIOS_SCALAR_MMIO_DATA_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**self.fixture(), selector=selector)

    def test_numeric_and_actual_typed_words_coexist_without_role_overlap(self):
        f = self.fixture(mixed=True)
        manifest, _ = profile.verify(**f, selector=SELECTOR)
        self.assertEqual(manifest['data_bindings'], f['data_bindings'])
        self.assertTrue(manifest['data_bindings'])
        offsets = {row[0] for row in manifest['numeric_mmio_literals']['words']}
        self.assertFalse(offsets & {row[0] for row in manifest['data_bindings']})
        self.assertIn('hardware access validity', manifest['numeric_mmio_literals']['contract'])
        self.assertIn('no numeric result', manifest['compiler_runtime']['contract'])

    def test_missing_mmio_ram_odd_outside_and_bios_operations_refuse(self):
        for value in (0x03000100, 0x04000101, 0x03FFFFFE, 0x04000400, 0x05000010):
            with self.subTest(value=value), self.assertRaises(ValueError):
                profile.verify(**self.fixture(value), selector=SELECTOR)
        with self.assertRaises(ValueError):
            profile.verify(**self.base.fixture(), selector=SELECTOR)
        f = self.fixture()
        body = bytearray(f['data'])
        struct.pack_into('<H', body, 4, 0xDF0B)
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, data=bytes(body), rom=bytes(rom)), selector=SELECTOR)

    def test_fabricated_binding_and_forged_literal_manifest_refuse(self):
        f = self.fixture()
        offset = len(f['data'])-4
        objects = json.loads(f['data_mapping'])
        objects['fake_mmio'] = '0x04000100'
        with self.assertRaisesRegex(ValueError, 'also be a typed object'):
            profile.verify(**dict(f, data_mapping=json.dumps(objects).encode(),
                data_bindings=[[offset, 'fake_mmio', 0]]), selector=SELECTOR)
        manifest, _ = profile.verify(**f, selector=SELECTOR)
        forged = copy.deepcopy(manifest)
        forged['numeric_mmio_literals']['words'][0][1] += 2
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            profile.verify(**f, selector=SELECTOR, manifest=forged)
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, data_mapping=b'not json'), selector=SELECTOR)

    def test_original_elf_has_no_mmio_symbol_and_linked_word_is_immutable(self):
        for mixed in (False, True):
            f = self.fixture(mixed=mixed)
            original = self.base.image(f)
            before = copy.deepcopy(original)
            calls, _, targets, records = self.base.bindings(f, original, SELECTOR)
            self.assertEqual(original, before)
            offset = len(f['data'])-4 if not mixed else self.base.base.fixtures.data_fixture()['data_bindings'][0][0]
            self.assertNotIn(offset, records)
            self.assertNotIn(0x04000100, targets.values())
            self.assertEqual(struct.unpack_from('<I', original['text'], offset)[0], 0x04000100)
            linked = self.base.linked(f, original)
            options = dict(data_relocations=records) if records else {}
            self.assertEqual(profile.linked_bytes(original, linked, A, calls, targets, **options), f['data'])
            text = bytearray(linked['text'])
            struct.pack_into('<I', text, offset, 0x04000102)
            linked['text'] = bytes(text)
            with self.assertRaisesRegex(ValueError, 'outside call relocations'):
                profile.linked_bytes(original, linked, A, calls, targets, **options)

    def test_new_build_rejects_explicit_runtime_source_before_linking(self):
        with self.build_boundary() as (root, _, commands):
            read = match.Runner.read_binary

            def explicit_source(runner, path):
                return b'int __divsi3(int, int);' if path.endswith('f.i') else read(runner, path)

            with patch.object(match.Runner, 'read_binary', explicit_source), \
                    self.assertRaisesRegex(ValueError, 'preprocessed C'):
                profile.build(root, A, selector=SELECTOR)
            self.assertEqual(commands, [])

    def test_native_cli_report_guards_source_runtime_producer_and_literal_policy(self):
        with self.build_boundary() as (root, _, _):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', SELECTOR, f'{A:08X}']), \
                    redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            evidence = fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertFalse(evidence.report_matches(report.replace(
                'Literal identity only', 'forged literal policy'), root, A))
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(evidence.report_matches(report, root, A))
            pins = profile.data_producer_fingerprint(SELECTOR)
            with patch.object(profile, 'data_producer_fingerprint', return_value=dict(
                    pins, **{'addressed_signed_runtime_profile.py': '0'*64})):
                self.assertFalse(evidence.report_matches(report, root, A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
