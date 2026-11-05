"""Two actual incoming scalar words with a bounded local CpuSet fill source."""
import copy
from contextlib import redirect_stdout
import io
import sys
import unittest
from unittest.mock import patch

import test_bios_cpuset_fill_profile as fill

profile, match, bios, A = fill.profile, fill.match, fill.bios, fill.A


class BiosReadonlyTwoWordsTests(unittest.TestCase):
    def setUp(self):
        self.base = fill.BiosCpuSetFillTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, **options):
        options.setdefault('prefix', (0x9902, 0x9903, 0x2280, 0x0452))
        f = self.base.fixture(**options)
        f['selector'] = profile.BIOS_READONLY_TWO_SELECTOR
        return f

    def test_two_reached_words_and_local_source_keep_separate_premises(self):
        manifest, _ = profile.verify(**self.fixture())
        incoming = manifest['frame']['entry_stack']
        self.assertEqual(incoming['words'], [0, 1])
        self.assertEqual({row[1] for row in incoming['reads']}, {0, 4})
        self.assertEqual(incoming['loaded_value'], 'unknown scalar; no provenance facts')
        self.assertIn('readonly_entry_stack_words_profile.py', manifest['producer_source_sha256'])
        self.assertEqual(manifest['native_buffers']['bios_fill']['sites'][0][2], 2)
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertFalse(manifest['original_formal_type_certainty'])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        self.assertNotIn('data_bindings', manifest)

    def test_missing_extra_written_or_addressed_incoming_words_refuse(self):
        for prefix in ((0x9902, 0x2280, 0x0452),
                       (0x9903, 0x2280, 0x0452),
                       (0x9902, 0x9903, 0x9904, 0x2280, 0x0452),
                       (0x9102, 0x9902, 0x9903, 0x2280, 0x0452),
                       (0xA902, 0x8809, 0x9903, 0x2280, 0x0452)):
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                profile.verify(**self.fixture(prefix=prefix))

    def test_existing_selectors_and_mixed_contexts_stay_closed(self):
        f = self.fixture()
        for selector in (profile.BIOS_SELECTOR, profile.READONLY_TWO_SELECTOR,
                         profile.BIOS_ORDINARY_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**dict(f, selector=selector))
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, data_mapping=b'{}', data_bindings=[]))
        context = (f['rom'], f['mapping'], f['index'], f['bindings'], {}, f['selector'])
        for extra in ({'buffer_proof': object()}, {'function_thunk_context': {}},
                      {'modsi3_context': ()}):
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                match.verify_leaf_instructions(f['data'], A, True, f['calls'],
                    addressed_signed_runtime_context=context, **extra)

    def test_bios_mode_source_destination_wrapper_and_manifest_are_checked(self):
        for options in (dict(destination=0x4669), dict(source=0xA801),
                        dict(prefix=(0x9902, 0x9903, 0x2200))):
            with self.subTest(options=options), self.assertRaises(ValueError):
                profile.verify(**self.fixture(**options))
        f = self.fixture()
        rom = bytearray(f['rom'])
        rom[bios.ADDRESS-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, rom=bytes(rom)))
        manifest, _ = profile.verify(**f)
        changed = copy.deepcopy(manifest)
        changed['producer_source_sha256']['readonly_entry_stack_words_profile.py'] = '0'*64
        with self.assertRaises(ValueError):
            profile.verify(**f, manifest=changed)

    def test_original_relocations_require_actual_bios_identity(self):
        f = self.fixture()
        original = self.base.base.image(f)
        calls, bindings, targets = profile.original_bindings(
            original, A, f['rom'], f['mapping'], selector=f['selector'])
        self.assertEqual((calls, bindings), (f['calls'], f['bindings']))
        self.assertEqual(targets[bios.NAME], bios.ADDRESS)
        bad = copy.deepcopy(original)
        bad['symbols'][1]['type'] = 1
        with self.assertRaises(ValueError):
            profile.original_bindings(bad, A, f['rom'], f['mapping'], selector=f['selector'])

    def test_cli_report_replay_binds_source_runtime_and_both_proofs(self):
        f = dict(self.fixture(), data_mapping=b'{}', data_bindings=[])
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
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
