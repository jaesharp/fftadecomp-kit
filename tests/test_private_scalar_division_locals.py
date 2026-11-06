"""New source admission boundaries for scalar DIV and private byte locals."""
from contextlib import contextmanager
import copy
import hashlib
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import dynamic_division_actual_fixtures as actual
import private_scalar_division_locals_inventory as inventory
import private_float_pack_admission_profile as admission
import software_float_profile as runtime

A = 0x08010000
SELECTOR = admission.SCALAR_DIVISION_LOCALS_SELECTOR


def words(*values):
    return b''.join(value.to_bytes(2, 'little') for value in values)


def call(site, target):
    delta = target-site-4
    return words(0xF000|((delta>>12)&0x7FF), 0xF800|((delta>>1)&0x7FF))


def fixture(*, store=True, external=False):
    body = words(0xB500)+call(A+2, inventory.dynamic.DIV)+words(0x2001, 0x2101)
    body += call(A+10, inventory.dynamic.DIV)+words(0xB081, 0x466A, 0x2000)
    if store:
        body += words(0x7010)
    body += words(0x6820 if external else 0x5610, 0xB001, 0xBC02, 0x4708)
    rom = bytearray(inventory.dynamic.ZERO+len(actual.ZERO)-match.ROM_BASE)
    rows, lines = [], []
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    for address, data, count in ((A, body, len(list(decoder.disasm(body, A)))),
            (inventory.dynamic.DIV, actual.DIV, 72), (inventory.dynamic.ZERO, actual.ZERO, 1)):
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(data)] = data
        rows.append(dict(rom=f'0x{address:08X}', end=f'0x{address+len(data):08X}', mode='thumb', instrs=count))
        lines.append(f'{address:08X} {address+len(data):08X} {len(data)} {count} return\n')
    return body, bytes(rom), json.dumps(rows).encode(), ''.join(lines).encode()


def elf_pair(body):
    name = '__divsi3'
    symbols = [dict(name=f'func_{A:08X}', type=2, bind=1, section=1, value=1, size=len(body)),
               dict(name=name, type=0, bind=1, section=0, value=0, size=0)]
    original = bytearray(body)
    for site in (2, 10):
        original[site:site+4] = call(A+site, A+site)
    rels = b''.join(struct.pack('<II', site, 1<<8|10) for site in (2, 10))
    image = dict(type=1, text_index=1, text=bytes(original), symbols=symbols,
        sections=[(0,)*10, (0,1,6,0,0,len(body),0,0,4,0), (0,9,0,0,0,len(rels),3,1,4,8)],
        symbol_tables={3:symbols}, relocations=[2], section_data=[b'',bytes(original),rels])
    linked = copy.deepcopy(image)
    linked.update(type=2, text=body, relocations=[])
    linked['sections'][1] = (0,1,6,A,0,len(body),0,0,4,0)
    linked['symbols'][0]['value'] = A|1
    linked['symbols'][1].update(value=inventory.dynamic.DIV|1, section=0xFFF1, type=2)
    return image, linked


class ScalarDivisionLocalsTests(unittest.TestCase):
    @contextmanager
    def context(self, **options):
        selected = fixture(**options)
        with patch.object(runtime, 'ROM_SHA256', hashlib.sha256(selected[1]).hexdigest()):
            yield selected

    def test_private_byte_effects_and_real_zero_closure_are_explicit(self):
        with self.context() as (body, rom, mapping, index):
            proof, _ = inventory.verify(body, A, rom, mapping, index, selector=inventory.SELECTOR)
        native = proof['native_closure']
        self.assertEqual({row[0] for row in native['runtime_closure']},
                         {inventory.dynamic.DIV, inventory.dynamic.ZERO})
        self.assertTrue(native['residual_local_scratch'])
        self.assertEqual(proof['discarded_exit_scratch_policy'], inventory.dynamic.SCRATCH_POLICY)
        self.assertEqual(proof['external_reads'], [])
        self.assertEqual(proof['numeric_input_preconditions'], [])
        self.assertFalse(proof['source_or_ELF_admission'])
        self.assertFalse(proof['native_nonescape_proof'])
        self.assertFalse(proof['universal_termination_claim'])

    def test_uninitialized_byte_and_external_pointer_do_not_gain_permissions(self):
        for options, message in ((dict(store=False), 'uninitialized'),
                                 (dict(external=True), 'memory base')):
            with self.subTest(options=options), self.context(**options) as (body, rom, mapping, index):
                with self.assertRaisesRegex(ValueError, message):
                    inventory.verify(body, A, rom, mapping, index, selector=inventory.SELECTOR)

    def test_selector_immutable_inputs_and_actual_count_are_required(self):
        with self.context() as (body, rom, mapping, index):
            for selector in (None, True, inventory.dynamic.SELECTOR):
                with self.subTest(selector=selector), self.assertRaises(ValueError):
                    inventory.verify(body, A, rom, mapping, index, selector=selector)
            with self.assertRaisesRegex(ValueError, 'immutable'):
                inventory.verify(bytearray(body), A, rom, mapping, index, selector=inventory.SELECTOR)
            lines = index.decode().splitlines(); fields = lines[0].split()
            fields[3] = str(int(fields[3])+1); lines[0] = ' '.join(fields)
            changed = ('\n'.join(lines)+'\n').encode()
            with self.assertRaisesRegex(ValueError, 'count'):
                inventory.verify(body, A, rom, mapping, changed, selector=inventory.SELECTOR)

    def test_original_runtime_binding_and_relocation_only_link(self):
        with self.context() as (body, rom, mapping, index):
            original, linked = elf_pair(body); before = copy.deepcopy(original)
            calls, targets = admission.original_bindings(original, A, rom, mapping, index, selector=SELECTOR)
            self.assertEqual(calls, [[2, '__divsi3'], [10, '__divsi3']])
            self.assertEqual(admission.linked_bytes(original, linked, A, calls, targets, selector=SELECTOR), body)
            self.assertEqual(original, before)
            proof, _ = admission.verify(body, A, rom, mapping, index, calls, selector=SELECTOR)
            self.assertEqual(proof['schema'], admission.SCALAR_DIVISION_LOCALS_SCHEMA)
            self.assertIn('discarded-scratch', proof['contract'])
            changed = copy.deepcopy(linked); raw = bytearray(body); raw[-2] ^= 1; changed['text'] = bytes(raw)
            with self.assertRaisesRegex(ValueError, 'outside original BL'):
                admission.linked_bytes(original, changed, A, calls, targets, selector=SELECTOR)

    def test_other_runtime_names_defined_symbols_and_addends_refuse(self):
        with self.context() as (body, rom, mapping, index):
            original, _ = elf_pair(body)
            for kind in ('name', 'defined', 'addend', 'extra'):
                changed = copy.deepcopy(original)
                if kind == 'name': changed['symbols'][1]['name'] = '__modsi3'
                elif kind == 'defined': changed['symbols'][1]['section'] = 0xFFF1
                elif kind == 'extra': changed['symbols'].append(dict(name='unproved', type=0, bind=1, section=0, value=0, size=0))
                else: changed['text'] = changed['text'][:2]+call(A+2,A+4)+changed['text'][6:]
                with self.subTest(kind=kind), self.assertRaises(ValueError):
                    admission.original_bindings(changed, A, rom, mapping, index, selector=SELECTOR)
            with self.assertRaises(ValueError):
                admission.original_bindings(original, A, rom, mapping, index)

    def test_forged_call_binding_and_manifest_refuse(self):
        with self.context() as (body, rom, mapping, index):
            for calls in ([[[2,'__divsi3']]], [[2,'__divsi3']], [[2,'__modsi3'],[10,'__divsi3']]):
                with self.subTest(calls=calls), self.assertRaises(ValueError):
                    admission.verify(body, A, rom, mapping, index, calls, selector=SELECTOR)
            with self.assertRaisesRegex(ValueError, 'manifest differs'):
                inventory.verify(body, A, rom, mapping, index, selector=inventory.SELECTOR, manifest={})

    def test_report_and_cli_keep_new_selector_distinct(self):
        marker = f'* verification: `{admission.SCALAR_DIVISION_LOCALS_SCHEMA}`\n* private float pack: `{SELECTOR}`\n'
        self.assertEqual(admission.selector_for_report(marker), SELECTOR)
        for changed in (marker+marker, marker.replace(f'* private float pack: `{SELECTOR}`',
                f'* private float pack: `{admission.SELECTOR}`')):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                admission.selector_for_report(changed)
        with patch.object(admission, 'issue', return_value=379) as issue, \
                patch.object(sys, 'argv', ['match.py','08010000','--owner-runtime-profile',SELECTOR]):
            self.assertEqual(match.main(), 379)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile, SELECTOR)


if __name__ == '__main__':
    unittest.main(verbosity=2)
