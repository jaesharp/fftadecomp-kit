"""Incoming-word permissions stay separate from ordinary guarded-switch policy."""
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest

import match
import owner_admission_profile as owner
import framed_switch_inventory as scalar
from test_switch_constants import assemble, fixture_assembly, ordinary_link, fixed_args

A = 0x08010000


class EntrySwitchTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(dir=os.environ['FFTA_TEST_SCRATCH'])
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def fixture(self, access='ldr r2,[sp,#4]', extra=''):
        assembly = fixture_assembly(call=True, prefix=access+'\n'+extra,
                                    first='', second='')
        assembly = assembly.replace('.Lconstant0:\n.word 0xFF00FF00\n'
                                    '.Lconstant1:\n.word 0x0F0F0F0F\n', '')
        assembly = assembly.replace('func_08000000', 'func_08010000')
        assembly = assembly.replace('pop {r1}\nbx r1', 'pop {pc}')
        original = assemble(self.root, assembly)
        linked, data = ordinary_link(self.root, original, A)
        rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(data):08X}',
                     mode='thumb', instrs=0),
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
                      index=index, objects=b'{}', selector=owner.ENTRY_SWITCH_SELECTOR)
        bindings, _ = owner.original_bindings(match.elf_image(original), A,
            values['rom'], mapping, b'{}', selector=owner.ENTRY_SWITCH_SELECTOR, index=index)
        return original, linked, values, bindings

    def test_original_binding_frame_unknown_word_and_report(self):
        original, _, values, bindings = self.fixture()
        manifest, instructions = owner.verify(**values, bindings=bindings)
        self.assertEqual(manifest['profile'], owner.ENTRY_SWITCH_SCHEMA)
        inventory = manifest['proof']['ordinary_switch_inventory']
        entry = inventory['frame']['entry_stack']
        self.assertEqual(entry['words'], [0])
        self.assertTrue(entry['reads'])
        self.assertEqual({row[1] for row in entry['reads']}, {0})
        self.assertIn('unknown scalar', entry['loaded_value'])
        self.assertFalse(inventory['termination_claim'])
        self.assertFalse(inventory['ordinary_callee_native_proof'])
        self.assertFalse(inventory['source_or_ELF_admission'])
        self.assertEqual(inventory['stack_adjustments'], [])
        report = owner.render(A, (values['data'], manifest, 'synthetic-source',
            values['mapping'], values['index'], b'{}', values['rom'],
            len(instructions), original))
        self.assertEqual(owner.selector_for_report(report), owner.ENTRY_SWITCH_SELECTOR)
        self.assertIn(owner.ENTRY_SWITCH_CONTROL_FLOW, report)
        self.assertIn('original_elf_sha256', report)

    def test_original_object_link_is_unchanged(self):
        original, linked, values, bindings = self.fixture()
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            runner.write_text(workspace+'/f.i', '')
            Path(workspace+'/f.o').write_bytes(original)
            data, actual = owner.object_bytes(runner, workspace, fixed_args(),
                match.elf_image(original), A, values['rom'], values['mapping'], b'{}',
                selector=owner.ENTRY_SWITCH_SELECTOR, index=values['index'])
            self.assertEqual(data, values['data'])
            self.assertEqual(actual, bindings)
            self.assertEqual(match.elf_image(runner.read_binary(workspace+'/f.elf'))['text'],
                             match.elf_image(linked)['text'])

    def test_old_switch_selectors_keep_actual_local_allocation_requirement(self):
        _, _, values, bindings = self.fixture()
        calls = {A+offset:int(name[5:],16) for offset,name in bindings['calls']}
        for selector in (scalar.SELECTOR, scalar.CYCLIC_SELECTOR):
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'nonzero fixed local'):
                scalar.verify(values['data'], A, values['rom'], values['mapping'],
                    values['index'], calls, {site:f'func_{target:08X}' for site,target in calls.items()},
                    selector=selector)

    def test_absent_incoming_read_does_not_gain_permission(self):
        _, _, values, bindings = self.fixture('movs r2,#0')
        with self.assertRaisesRegex(ValueError, 'actual incoming word0'):
            owner.verify(**values, bindings=bindings)

    def test_second_word_and_incoming_store_are_refused(self):
        for access in ('ldr r2,[sp,#8]', 'str r2,[sp,#4]', 'ldrh r2,[r1]'):
            _, _, values, bindings = self.fixture(access)
            with self.subTest(access=access), self.assertRaises(ValueError):
                owner.verify(**values, bindings=bindings)

    def test_sp_address_and_saved_word_corruption_are_refused(self):
        for access in ('mov r2,sp', 'str r2,[sp]'):
            _, _, values, bindings = self.fixture(access)
            with self.subTest(access=access), self.assertRaises(ValueError):
                owner.verify(**values, bindings=bindings)

    def test_exact_counts_bindings_and_fresh_manifest_are_required(self):
        _, _, values, bindings = self.fixture()
        manifest, _ = owner.verify(**values, bindings=bindings)
        changed = copy.deepcopy(manifest)
        changed['proof']['ordinary_switch_inventory']['frame']['entry_stack']['words'] = [0,1]
        with self.assertRaises(ValueError):
            owner.verify(**values, bindings=bindings, manifest=changed)
        changed = copy.deepcopy(bindings)
        changed['calls'] = []
        with self.assertRaises(ValueError):
            owner.verify(**values, bindings=changed)
        rows = json.loads(values['mapping'])
        rows[0]['instrs'] += 1
        with self.assertRaises(ValueError):
            owner.verify(**dict(values, mapping=json.dumps(rows).encode()), bindings=bindings)

    def test_explicit_selection_rejects_mixed_markers_and_unknown_inventory(self):
        marker = f'* verification: `{owner.ENTRY_SWITCH_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker), owner.ENTRY_SWITCH_SELECTOR)
        for report in (marker*2, marker+f'* verification: `{owner.CYCLIC_SCHEMA}`\n'):
            with self.assertRaises(ValueError):
                owner.selected(report)
        _, _, values, bindings = self.fixture()
        with self.assertRaises(ValueError):
            owner.verify(**dict(values, selector='unknown-entry-word'), bindings=bindings)
