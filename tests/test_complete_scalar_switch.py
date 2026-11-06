"""Complete scalar switches have no external-padding or entry-word permission."""
import copy
import json
import os
from pathlib import Path
import struct
import tempfile
import unittest

import match
import owner_admission_profile as owner
from test_switch_constants import assemble, fixture_assembly, ordinary_link, fixed_args

A = 0x08010000


class CompleteScalarSwitchTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(dir=os.environ['FFTA_TEST_SCRATCH'])
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def fixture(self, access='', allocation=True):
        prefix = ('sub sp,#4\n' if allocation else '') + access
        assembly = fixture_assembly(call=True, prefix=prefix, first='', second='')
        assembly = assembly.replace('.Lconstant0:\n.word 0xFF00FF00\n'
                                    '.Lconstant1:\n.word 0x0F0F0F0F\n', '')
        assembly = assembly.replace('func_08000000', 'func_08010000')
        finish = ('add sp,#4\n' if allocation else '') + 'pop {pc}'
        assembly = assembly.replace('bl func_08001000\npop {r1}\nbx r1',
            '.balign 4,0\n' + ('' if allocation else 'movs r2,#0\n') +
            'bl func_08001000\n' + finish)
        original = assemble(self.root, assembly)
        linked, data = ordinary_link(self.root, original, A)
        rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(data):08X}', mode='thumb', instrs=0),
                dict(rom='0x08001000', end='0x08001002', mode='thumb', instrs=1)]
        rows[0]['instrs'] = owner.refine(data, A, json.dumps(rows).encode())['instrs']
        mapping = json.dumps(rows).encode()
        index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                        f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'
                        for r in rows).encode()
        rom = bytearray(A-match.ROM_BASE+len(data))
        rom[A-match.ROM_BASE:] = data
        rom[0x1000:0x1002] = b'\x70\x47'
        values = dict(data=data, address=A, rom=bytes(rom), mapping=mapping,
                      index=index, objects=b'{}', selector=owner.DIRECT_SWITCH_SELECTOR)
        bindings, _ = owner.original_bindings(match.elf_image(original), A,
            values['rom'], mapping, b'{}', selector=values['selector'], index=index)
        return original, linked, values, bindings

    def test_complete_original_frame_and_report(self):
        original, _, values, bindings = self.fixture()
        manifest, instructions = owner.verify(**values, bindings=bindings)
        self.assertEqual(manifest['profile'], owner.DIRECT_SWITCH_SCHEMA)
        inventory = manifest['proof']['ordinary_switch_inventory']
        self.assertEqual(inventory['stack_adjustments'], [[2, -4], [len(values['data'])-4, 4]])
        self.assertNotIn('entry_stack', inventory['frame'])
        self.assertNotIn('terminal_alignment_policy', manifest['proof'])
        self.assertFalse(inventory['termination_claim'])
        self.assertFalse(inventory['ordinary_callee_native_proof'])
        report = owner.render(A, (values['data'], manifest, 'synthetic-source',
            values['mapping'], values['index'], b'{}', values['rom'],
            len(instructions), original))
        self.assertEqual(owner.selector_for_report(report), owner.DIRECT_SWITCH_SELECTOR)
        self.assertIn(owner.DIRECT_SWITCH_CONTROL_FLOW, report)
        self.assertIn('original_elf_sha256', report)

    def test_original_object_link_preserves_complete_bytes(self):
        original, linked, values, bindings = self.fixture()
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            runner.write_text(workspace+'/f.i', '')
            Path(workspace+'/f.o').write_bytes(original)
            data, actual = owner.object_bytes(runner, workspace, fixed_args(),
                match.elf_image(original), A, values['rom'], values['mapping'], b'{}',
                selector=values['selector'], index=values['index'])
            self.assertEqual(data, values['data'])
            self.assertEqual(actual, bindings)
            self.assertEqual(runner.read_binary(workspace+'/f.o'), original)
            self.assertEqual(match.elf_image(runner.read_binary(workspace+'/f.elf'))['text'],
                             match.elf_image(linked)['text'])

    def test_padding_and_incoming_word_policies_stay_separate(self):
        original, _, values, bindings = self.fixture()
        for selector in (owner.ALIGNED_SELECTOR, owner.CYCLIC_SELECTOR):
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'external two-byte'):
                owner.original_bindings(match.elf_image(original), A, values['rom'],
                    values['mapping'], b'{}', selector=selector, index=values['index'])
        for selector in (owner.ENTRY_SWITCH_SELECTOR, owner.ENTRY_DATA_SWITCH_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                owner.verify(**dict(values, selector=selector), bindings=bindings)

    def test_allocation_entry_reads_saved_words_and_aliases_are_checked(self):
        _, _, values, bindings = self.fixture(allocation=False)
        with self.assertRaisesRegex(ValueError, 'nonzero fixed local'):
            owner.verify(**values, bindings=bindings)
        for access in ('ldr r2,[sp,#8]', 'str r2,[sp,#4]', 'mov r2,sp', 'ldmia r2!,{r3}'):
            _, _, values, bindings = self.fixture(access)
            with self.subTest(access=access), self.assertRaises(ValueError):
                owner.verify(**values, bindings=bindings)

    def test_exact_call_bindings_counts_and_manifest_are_required(self):
        _, _, values, bindings = self.fixture()
        changed = copy.deepcopy(bindings)
        changed['calls'] = []
        with self.assertRaises(ValueError):
            owner.verify(**values, bindings=changed)
        rows = json.loads(values['mapping'])
        rows[0]['instrs'] += 1
        with self.assertRaises(ValueError):
            owner.verify(**dict(values, mapping=json.dumps(rows).encode()), bindings=bindings)
        manifest, _ = owner.verify(**values, bindings=bindings)
        manifest['proof']['ordinary_switch_inventory']['termination_claim'] = True
        with self.assertRaises(ValueError):
            owner.verify(**values, bindings=bindings, manifest=manifest)

    def test_data_and_function_literals_cannot_gain_this_policy(self):
        _, _, values, bindings = self.fixture()
        for key, value in (('data', [[0, 'g_state', 0]]), ('functions', [[0, 'func_08001000']])):
            changed = copy.deepcopy(bindings)
            changed[key] = value
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'excludes named data'):
                owner.verify(**values, bindings=changed)

    def test_switch_table_target_and_guard_are_authenticated(self):
        _, _, values, bindings = self.fixture()
        switch = owner.refine(values['data'], A, values['mapping'])['word_switches'][0]
        for offset, replacement in ((switch['guard'], b'\xc0\x46'),
                                    (switch['table'], struct.pack('<I', A+switch['table']))):
            data = bytearray(values['data'])
            data[offset:offset+len(replacement)] = replacement
            rom = bytearray(values['rom'])
            rom[A-match.ROM_BASE:] = data
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                owner.verify(**dict(values, data=bytes(data), rom=bytes(rom)), bindings=bindings)

    def test_explicit_marker_and_unknown_selection_are_checked(self):
        marker = f'* verification: `{owner.DIRECT_SWITCH_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker), owner.DIRECT_SWITCH_SELECTOR)
        for report in (marker*2, marker+f'* verification: `{owner.ALIGNED_SCHEMA}`\n'):
            with self.subTest(report=report), self.assertRaises(ValueError):
                owner.selected(report)
        _, _, values, bindings = self.fixture()
        with self.assertRaises(ValueError):
            owner.verify(**dict(values, selector='unknown-complete-scalar-switch'), bindings=bindings)
