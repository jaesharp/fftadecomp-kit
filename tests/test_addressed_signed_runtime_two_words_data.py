"""Synthetic typed-data/incoming-word composition; no ROM or compiler required."""
import copy
from contextlib import contextmanager, redirect_stderr, redirect_stdout
import io
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'tools'))
import addressed_signed_runtime_profile as profile
import match
import match_evidence as evidence
import push
import status
import test_addressed_signed_runtime_profile as fixtures

A = fixtures.A
SELECTOR = 'addressed-signed-runtime-readonly-two-words-data-v1'
SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-readonly-two-words-data-v1'


class TwoWordsDataTests(unittest.TestCase):
    def setUp(self):
        # Reuse shipped fixture builders, never their test methods.
        self.fixtures = fixtures.AddressedSignedRuntimeTests()
        self.fixtures.setUp()
        self.addCleanup(self.fixtures.doCleanups)
        tools = patch.object(profile, 'toolchain_fingerprint',
                             return_value=[['synthetic compiler boundary', '1' * 64]])
        tools.start()
        self.addCleanup(tools.stop)
        for module in (profile, match, evidence, status, push):
            self.assertEqual(Path(module.__file__).resolve().parent, ROOT / 'tools')
        self.assertEqual(Path(fixtures.__file__).resolve().parent, ROOT / 'tests')

    def fixture(self, reads=(0x9802, 0x9903), extra=()):
        tokens = (0xB510, *reads, 0x4C00, 0x6820, 0x2100,
                  *extra, 'div', 'ordinary', 0xBC10, 0xBC02, 0x4708)
        f = self.fixtures.fixture(tokens)
        body = bytearray(f['data'])
        if len(body) % 4:
            body += b'\0\0'
        literal = len(body)
        load = 2 + 2 * len(reads)
        struct.pack_into('<H', body, load,
                         0x4C00 | ((literal - ((load + 4) & ~3)) // 4))
        body += struct.pack('<I', 0x03002810)
        f['data'] = bytes(body)
        rom = bytearray(f['rom'])
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(body)] = body
        f['rom'] = bytes(rom)
        rows = json.loads(f['mapping'])
        rows[0].update(end=f'0x{A + len(body):08X}', instrs=len(tokens))
        f['mapping'], f['index'] = fixtures.indexes(rows)
        f.update(data_mapping=b'{"state":"0x03002810"}',
                 data_bindings=[[literal, 'state', 0]])
        return f

    def verify(self, f, **options):
        return profile.verify(**f, selector=SELECTOR, **options)

    @contextmanager
    def build_boundary(self, f=None):
        f = f or self.fixture()
        original = self.fixtures.data_image(f)
        linked = self.fixtures.linked_data_image(f, original)
        scratch = ROOT / 'build'
        scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='two_words_data_', dir=scratch) as directory:
            root = Path(directory)
            for sub in ('src', 'include', 'config', 'symbols', 'docs/match'):
                (root / sub).mkdir(parents=True)
            (root / 'src/08010000.c').write_text('/* synthetic fingerprint input */\n')
            (root / 'include/fixture.h').write_text('/* synthetic header fingerprint */\n')
            for relative, data in [('config/functions.json', f['mapping']),
                                   ('symbols/functions.txt', f['index']),
                                   ('config/data_symbols.json', f['data_mapping']),
                                   ('baserom.bin', f['rom'])]:
                (root / relative).write_bytes(data)
            commands = []

            class SyntheticRunner:
                def __init__(self, *args, **kwargs):
                    self.root = kwargs['root']

                @contextmanager
                def workspace(self):
                    workspace = self.root / 'workspace'
                    workspace.mkdir()
                    yield str(workspace)

                def read_binary(self, path):
                    return f['data'] if path.endswith('f.linked.bin') else b'synthetic ELF boundary'

                def write_text(self, path, value):
                    Path(path).write_text(value)

                def sh(self, command):
                    commands.append(command)  # Never execute a compiler or linker.

            with (patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')),
                  patch.object(match, 'Runner', SyntheticRunner),
                  patch.object(match, 'compile_object',
                               return_value=(b'synthetic original ELF', None, original)),
                  patch.object(match, 'elf_image', return_value=linked),
                  patch.object(match, '_run_replay_process', return_value=None),
                  patch.object(match, 'plausibility_result', return_value=([], None))):
                yield root, f, commands

    def test_combined_admission_and_existing_selector_boundaries(self):
        f = self.fixture()
        manifest, instructions = self.verify(f)
        self.assertEqual(manifest['schema'], SCHEMA)
        incoming = manifest['frame']['entry_stack']
        self.assertEqual(incoming['words'], [0, 1])
        self.assertEqual({row[1] for row in incoming['reads']}, {0, 4})
        self.assertEqual(incoming['loaded_value'], 'unknown scalar; no provenance facts')
        self.assertEqual(manifest['data_bindings'], f['data_bindings'])
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        self.assertFalse(manifest['original_formal_type_certainty'])
        self.assertIn('readonly_entry_stack_words_profile.py', manifest['producer_source_sha256'])
        self.assertTrue(instructions)
        for selector in (profile.SELECTOR, profile.DATA_SELECTOR,
                         profile.READONLY_SELECTOR, profile.READONLY_TWO_SELECTOR):
            old = dict(f)
            if selector != profile.DATA_SELECTOR:
                old.pop('data_mapping')
                old.pop('data_bindings')
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**old, selector=selector)

    def test_combined_frame_rejects_wrong_words_writes_and_pointer_escape(self):
        cases = {'missing0': ((0x9903,), ()), 'missing4': ((0x9802,), ()),
                 'extra8': ((0x9802, 0x9903, 0x9A04), ()),
                 'write0': ((0x9802, 0x9903), (0x9002,)),
                 'overwrite_saved': ((0x9802, 0x9903), (0x9000,)),
                 'incoming_alias_call': ((0x9802, 0x9903), (0xA802,)),
                 'partial_read': ((0x9802, 0x9903), (0xA802, 0x8800))}
        for reason, (reads, extra) in cases.items():
            with self.subTest(reason=reason), self.assertRaises(ValueError):
                self.verify(self.fixture(reads, extra))

    def test_combined_ELF_relocations_linked_identity_and_integrity(self):
        f = self.fixture()
        original = self.fixtures.data_image(f)
        relocations = {}
        calls, bindings, targets = profile.original_bindings(original, A, f['rom'], f['mapping'],
            selector=SELECTOR, data_mapping=f['data_mapping'], data_relocations=relocations)
        linked = self.fixtures.linked_data_image(f, original)
        self.assertEqual(profile.linked_bytes(original, linked, A, calls, targets,
                                             data_relocations=relocations), f['data'])
        self.assertEqual(bindings, f['bindings'])
        for reason in ('object_type', 'duplicate_object', 'ABS32_kind', 'unmapped_object'):
            bad = copy.deepcopy(original)
            if reason == 'object_type':
                bad['symbols'][-1]['type'] = 2
            elif reason == 'duplicate_object':
                bad['symbols'].append(copy.deepcopy(bad['symbols'][-1]))
            elif reason == 'ABS32_kind':
                raw = bytearray(bad['section_data'][2])
                offset, info = struct.unpack_from('<II', raw, len(raw) - 8)
                struct.pack_into('<II', raw, len(raw) - 8, offset, (info & ~255) | 10)
                bad['section_data'][2] = bytes(raw)
            else:
                bad['symbols'][-1]['name'] = 'unmapped'
            with self.subTest(reason=reason), self.assertRaises(ValueError):
                profile.original_bindings(bad, A, f['rom'], f['mapping'], selector=SELECTOR,
                    data_mapping=f['data_mapping'], data_relocations={})
        for reason in ('pool_word', 'nonrelocated_byte', 'wrong_symbol_kind', 'extra_function'):
            bad = copy.deepcopy(linked)
            if reason in ('pool_word', 'nonrelocated_byte'):
                raw = bytearray(bad['text'])
                raw[f['data_bindings'][0][0] if reason == 'pool_word' else 0] ^= 1
                bad['text'] = bytes(raw)
            elif reason == 'wrong_symbol_kind':
                bad['symbols'][-1]['type'] = 2
            else:
                bad['symbols'].append(dict(name='extra', value=A | 1, size=2,
                                           type=2, bind=1, section=1))
            with self.subTest(reason=reason), self.assertRaises(ValueError):
                profile.linked_bytes(original, bad, A, calls, targets, data_relocations=relocations)

    def test_combined_manifest_and_typed_data_fail_closed(self):
        f = self.fixture()
        manifest, _ = self.verify(f)
        changes = [('words', [0]), ('producer', '0' * 64), ('binding', 4)]
        for reason, value in changes:
            bad = copy.deepcopy(manifest)
            if reason == 'words':
                bad['frame']['entry_stack']['words'] = value
            elif reason == 'producer':
                bad['producer_source_sha256']['readonly_entry_stack_words_profile.py'] = value
            else:
                bad['data_bindings'][0][2] = value
            with self.subTest(reason=reason), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.verify(f, manifest=bad)
        for reason in ('stale_mapping', 'wrong_addend', 'missing_binding', 'forged_context'):
            bad = copy.deepcopy(f)
            if reason == 'stale_mapping':
                bad['data_mapping'] = b'{"state":"0x03002814"}'
            elif reason == 'wrong_addend':
                bad['data_bindings'][0][2] = 4
            elif reason == 'missing_binding':
                bad['data_bindings'] = []
            else:
                with self.assertRaises(ValueError):
                    profile.context_selector((f['rom'], f['mapping'], f['index'],
                                              f['bindings'], {}, SELECTOR))
                continue
            with self.subTest(reason=reason), self.assertRaises(ValueError):
                self.verify(bad)

    def test_build_snapshots_both_policy_sources_and_rejects_midrun_mutation(self):
        with self.build_boundary() as (root, f, commands):
            result = profile.build(root, A, selector=SELECTOR)
            pins = result['manifest']['producer_source_sha256']
            self.assertEqual(pins, profile.data_producer_fingerprint(SELECTOR))
            self.assertIn('readonly_entry_stack_words_profile.py', pins)
            self.assertEqual(result['body'], f['data'])
            self.assertEqual(len(commands), 3)
            path = root / 'config/data_symbols.json'
            old = path.read_bytes()

            def change_mapping(*args, **kwargs):
                path.write_bytes(old + b' ')

            with patch.object(match, '_run_replay_process', side_effect=change_mapping):
                try:
                    with self.assertRaisesRegex(ValueError, 'changed during verification'):
                        profile.build(root, A, selector=SELECTOR)
                finally:
                    path.write_bytes(old)
            snapshots = [pins, pins, {**pins, 'readonly_entry_stack_words_profile.py': '0' * 64}]
            with patch.object(profile, 'data_producer_fingerprint', side_effect=snapshots):
                with self.assertRaisesRegex(ValueError, 'changed during verification'):
                    profile.build(root, A, selector=SELECTOR)

    def test_explicit_composition_rejects_aliases_callbacks_and_extra_contexts(self):
        f = self.fixture()
        original = self.fixtures.data_image(f)
        with self.assertRaisesRegex(ValueError, 'requires actual typed bindings'):
            profile.original_bindings(original, A, f['rom'], f['mapping'], selector=SELECTOR)
        for name in ('__divsi3', '_call_via_r2', 'func_0814274C'):
            bad = copy.deepcopy(original)
            bad['symbols'][1]['name'] = name
            with self.subTest(name=name), self.assertRaises(ValueError):
                profile.original_bindings(bad, A, f['rom'], f['mapping'], selector=SELECTOR,
                    data_mapping=f['data_mapping'], data_relocations={})
        for other in ({'buffer_proof': object()}, {'function_thunk_context': {}},
                      {'modsi3_context': ()}, {'preloaded_switch': True}):
            context = (f['rom'], f['mapping'], f['index'], f['bindings'], {},
                       SELECTOR, f['data_mapping'], f['data_bindings'])
            with self.subTest(extra=list(other)), self.assertRaisesRegex(ValueError, 'isolated explicit'):
                match.verify_leaf_instructions(f['data'], A, True, f['calls'],
                    addressed_signed_runtime_context=context, **other)

    def test_portable_CLI_status_publisher_and_freshness_roundtrip(self):
        with self.build_boundary() as (root, f, _):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                 '--addressed-signed-runtime-profile', SELECTOR, f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root / 'docs/match/08010000.md').read_text()
            self.assertEqual(profile.selector_for_report(report), SELECTOR)
            self.assertIn('* incoming stack ABI:', report)
            self.assertIn('* named data binding:', report)
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertEqual(status.collect(str(root), verify=False)[1], 1)
            completed = type('Completed', (), dict(returncode=0,
                stdout=f'extent    {len(f["data"])} bytes\nverdict MATCH - byte identical\n', stderr=''))()
            with patch.object(status.subprocess, 'run', return_value=completed) as run:
                self.assertEqual(status.collect(str(root), verify=True)[1], 1)
                self.assertIn(SELECTOR, run.call_args.args[0])
            with redirect_stdout(io.StringIO()):
                self.assertTrue(push.check_reports(str(root)))
            for relative in ('src/08010000.c', 'include/fixture.h', 'config/data_symbols.json',
                             'config/functions.json', 'symbols/functions.txt', 'baserom.bin'):
                path = root / relative
                old = path.read_bytes()
                path.write_bytes(old + b' ')
                try:
                    with self.subTest(stale=relative):
                        self.assertFalse(evidence.report_matches(report, root, A))
                finally:
                    path.write_bytes(old)
            with patch.object(profile, 'runtime_fingerprint', return_value={'stale': True}):
                self.assertFalse(evidence.report_matches(report, root, A))
            with patch.object(profile, 'build', side_effect=AssertionError('must reject before build')):
                with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                     '--addressed-signed-runtime-profile', SELECTOR,
                     '--owner-runtime-profile', 'restoring-owner-acyclic-v1', f'{A:08X}']):
                    with self.assertRaisesRegex(ValueError, 'isolated explicit'):
                        match.main()
                with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                     '--addressed-signed-runtime-profile', 'unknown-composition', f'{A:08X}']), \
                        redirect_stderr(io.StringIO()):
                    with self.assertRaises(SystemExit):
                        match.main()


if __name__ == '__main__':
    unittest.main()
