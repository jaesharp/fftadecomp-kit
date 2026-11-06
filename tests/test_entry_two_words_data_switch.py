"""Typed data and two incoming ABI words require their own switch policy."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import match
import owner_admission_profile as owner
from test_switch_constants import assemble, fixture_assembly, fixed_args

A = 0x08010000


class EntryDataSwitchTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(dir=os.environ['FFTA_TEST_SCRATCH'])
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def fixture(self, access='ldr r2,[sp,#4]\nldr r3,[sp,#8]', extra=''):
        assembly = fixture_assembly(call=True, prefix=access+'\n'+extra,
                                    first='ldr r1,.Ldata', second='',
                                    tail='.balign 4,0\n.Ldata:\n.word g_state')
        assembly = assembly.replace('.Lconstant0:\n.word 0xFF00FF00\n'
                                    '.Lconstant1:\n.word 0x0F0F0F0F\n', '')
        assembly = assembly.replace('func_08000000', 'func_08010000')
        assembly = assembly.replace('pop {r1}\nbx r1', 'pop {pc}')
        original = assemble(self.root, assembly)
        (self.root/'known.s').write_text('.syntax unified\n.thumb\n'
            '.global func_08001000\n.type func_08001000,%function\n'
            '.thumb_set func_08001000,0x08001001\n'
            '.global g_state\n.type g_state,%object\n.set g_state,0x02000100\n')
        subprocess.run(['arm-none-eabi-as', str(self.root/'known.s'), '-o',
                        str(self.root/'known.o')], check=True, capture_output=True)
        subprocess.run(['arm-none-eabi-ld', '--no-undefined', '--no-relax',
                        f'-Ttext=0x{A:08X}', '-e', 'func_08010000',
                        str(self.root/'f.o'), str(self.root/'known.o'),
                        '-o', str(self.root/'f.elf')], check=True, capture_output=True)
        linked = match.elf_image((self.root/'f.elf').read_bytes())
        symbol, offset = match.function_record(linked, 'func_08010000', A, True)
        data = linked['text'][offset:offset+symbol['size']]
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
                      index=index, objects=b'{"g_state":"0x02000100"}',
                      selector=owner.ENTRY_DATA_SWITCH_SELECTOR)
        bindings, _ = owner.original_bindings(match.elf_image(original), A,
            values['rom'], mapping, values['objects'], selector=values['selector'], index=index)
        return original, values, bindings

    def test_unknown_two_words_typed_data_frame_and_report(self):
        original, values, bindings = self.fixture()
        manifest, instructions = owner.verify(**values, bindings=bindings)
        self.assertEqual(manifest['profile'], owner.ENTRY_DATA_SWITCH_SCHEMA)
        entry = manifest['proof']['ordinary_switch_inventory']['frame']['entry_stack']
        self.assertEqual(entry['words'], [0, 1])
        self.assertEqual({row[1] for row in entry['reads']}, {0, 4})
        self.assertIn('unknown scalar', entry['loaded_value'])
        self.assertEqual(manifest['bindings']['data'], bindings['data'])
        self.assertFalse(manifest['proof']['ordinary_switch_inventory']['termination_claim'])
        report = owner.render(A, (values['data'], manifest, 'synthetic-source',
            values['mapping'], values['index'], values['objects'], values['rom'],
            len(instructions), original))
        self.assertEqual(owner.selector_for_report(report), values['selector'])
        self.assertIn(owner.ENTRY_DATA_SWITCH_CONTROL_FLOW, report)
        self.assertIn('original_elf_sha256', report)

    def test_original_object_link_preserves_all_bytes_and_bindings(self):
        original, values, bindings = self.fixture()
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            runner.write_text(workspace+'/f.i', '')
            Path(workspace+'/f.o').write_bytes(original)
            data, actual = owner.object_bytes(runner, workspace, fixed_args(),
                match.elf_image(original), A, values['rom'], values['mapping'],
                values['objects'], selector=values['selector'], index=values['index'])
            self.assertEqual(data, values['data'])
            self.assertEqual(actual, bindings)
            self.assertEqual(runner.read_binary(workspace+'/f.o'), original)

    def test_one_word_and_legacy_selectors_keep_their_boundaries(self):
        _, values, bindings = self.fixture()
        for selector in (owner.ENTRY_SWITCH_SELECTOR, owner.ALIGNED_SELECTOR, owner.CYCLIC_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                owner.verify(**dict(values, selector=selector), bindings=bindings)

    def test_missing_or_third_word_incoming_store_and_saved_corruption_fail(self):
        for access in ('ldr r2,[sp,#4]', 'ldr r2,[sp,#4]\nldr r3,[sp,#12]',
                       'ldr r2,[sp,#4]\nstr r3,[sp,#8]',
                       'ldr r2,[sp,#4]\nldr r3,[sp,#8]\nstr r0,[sp]',
                       'mov r2,sp\nldr r3,[sp,#8]'):
            _, values, bindings = self.fixture(access)
            with self.subTest(access=access), self.assertRaises(ValueError):
                owner.verify(**values, bindings=bindings)

    def test_absent_data_or_function_literal_cannot_select_the_policy(self):
        _, values, bindings = self.fixture()
        for key, value in (('data', []), ('functions', [[0, 'func_08001000']])):
            changed = copy.deepcopy(bindings)
            changed[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                owner.verify(**values, bindings=changed)

    def test_typed_point_and_exact_call_and_count_are_bound(self):
        _, values, bindings = self.fixture()
        changed = copy.deepcopy(bindings)
        changed['calls'] = []
        with self.assertRaises(ValueError):
            owner.verify(**values, bindings=changed)
        with self.assertRaises(ValueError):
            owner.verify(**dict(values, objects=b'{"g_state":"0x02000104"}'), bindings=bindings)
        rows = json.loads(values['mapping'])
        rows[0]['instrs'] += 1
        with self.assertRaises(ValueError):
            owner.verify(**dict(values, mapping=json.dumps(rows).encode()), bindings=bindings)

    def test_manifest_and_mixed_markers_are_rejected(self):
        _, values, bindings = self.fixture()
        manifest, _ = owner.verify(**values, bindings=bindings)
        changed = copy.deepcopy(manifest)
        changed['proof']['ordinary_switch_inventory']['frame']['entry_stack']['words'] = [0, 1, 2]
        with self.assertRaises(ValueError):
            owner.verify(**values, bindings=bindings, manifest=changed)
        marker = f'* verification: `{owner.ENTRY_DATA_SWITCH_SCHEMA}`\n'
        for text in (marker*2, marker+f'* verification: `{owner.ENTRY_SWITCH_SCHEMA}`\n'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                owner.selected(text)

    def test_actual_named_data_relocation_is_required(self):
        original, values, _ = self.fixture()
        with self.assertRaisesRegex(ValueError, 'unmapped'):
            owner.original_bindings(match.elf_image(original), A, values['rom'],
                values['mapping'], b'{}', selector=values['selector'], index=values['index'])


if __name__ == '__main__':
    unittest.main()
