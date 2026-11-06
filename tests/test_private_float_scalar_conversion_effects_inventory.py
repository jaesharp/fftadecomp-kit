"""Synthetic scalar conversion effects, without compiler or original ROM proofs."""
import copy
import hashlib
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import private_float_scalar_conversion_effects_inventory as inventory
import software_float_profile as runtime
import test_private_float_pack_effects_inventory as base

A, U, P = base.ADDRESS, base.UNPACK, base.PACK
words, call = base.words, base.call


def fixture(*, direction='unpack', pointer=4, literal=False):
    unpack = words(0x6802, 0x600A, 0x604A, 0x608A, 0x60CA, 0x4770)
    pack = words(0x6802, 0x6842, 0x6882, 0x68C0, 0x4770)
    if direction == 'unpack':
        caller = words(0xB500, 0xB085, 0x9004, 0xA800 | pointer, 0x4669)
        caller += call(A+10, U)
        if literal:
            caller += words(0x4801, 0xE002, 0, 0xFFFF, 0x7FFF)
        else:
            caller += words(0x9800)
        caller += words(0xB005, 0xBC02, 0x4708)
        count = 11 if literal else 10
    else:
        caller = words(0xB500, 0xB084, 0x9000, 0x9001, 0x9002, 0x9003,
                       0x4668 if pointer == 4 else 0xA800 | pointer)
        caller += call(A+14, P) + words(0xB004, 0xBC02, 0x4708)
        count = 11
    parts = {A: caller, U: unpack, P: pack}
    counts = {A: count, U: 6, P: 5}
    rom, rows, mapping, index = base.image(parts, counts)
    specs = tuple((role, (start, start+len(parts[start]), counts[start],
        hashlib.sha256(parts[start]).hexdigest()), bounds)
        for (role, _, bounds), start in zip(inventory.HELPERS, (U, P)))
    return caller, rom, rows, mapping, index, specs


class ScalarConversionEffectsTests(unittest.TestCase):
    def verify(self, selected=None, *, helpers=None, selector=inventory.SELECTOR, manifest=None):
        body, rom, _, mapping, index, specs = selected or fixture()
        with patch.object(inventory, 'HELPERS', helpers or specs), \
                patch.object(runtime, 'ROM_SHA256', hashlib.sha256(rom).hexdigest()), \
                patch.object(runtime, 'EDGES', ()):
            return inventory.verify(body, A, rom, mapping, index,
                selector=selector, manifest=manifest)

    def test_both_directions_discharge_finite_effects_into_locals(self):
        for direction in ('unpack', 'pack'):
            with self.subTest(direction=direction):
                proof, _ = self.verify(fixture(direction=direction))
                self.assertEqual(proof['external_reads'], [])
                self.assertEqual(proof['external_writes'], [])
                self.assertTrue(proof['caller_discharged_helper_effects_into_live_abstract_locals'])
                self.assertEqual(proof['numeric_return_facts'], [])
                self.assertFalse(proof['source_or_ELF_admission'])

    def test_reached_in_function_numeric_literal_has_exact_partition(self):
        proof, _ = self.verify(fixture(literal=True))
        self.assertEqual(proof['partition']['literal_and_table_bytes'], 4)
        self.assertEqual(proof['partition']['alignment_bytes'], 2)
        self.assertEqual(proof['partition']['words'][0]['value'], 0x7FFFFFFF)

    def test_reached_literal_cannot_escape_sized_symbol_into_alignment_tail(self):
        selected = fixture(literal=True)
        body = selected[0][:14]+words(0x4804)+selected[0][16:]
        parts = {A: body, U: selected[1][U-base.BASE:U-base.BASE+12],
                 P: selected[1][P-base.BASE:P-base.BASE+10]}
        rom, rows, mapping, index = base.image(parts, {A: 11, U: 6, P: 5})
        with self.assertRaises(ValueError):
            self.verify((body, rom, rows, mapping, index, selected[-1]))

    def test_saved_and_incoming_stack_are_not_local_buffers(self):
        for direction, pointer in (('unpack', 5), ('unpack', 6), ('pack', 1)):
            with self.subTest(direction=direction, pointer=pointer), self.assertRaises(ValueError):
                self.verify(fixture(direction=direction, pointer=pointer))

    def test_actual_helper_access_requires_its_finite_bound(self):
        selected = fixture()
        helpers = copy.deepcopy(list(selected[-1]))
        helpers[0][2]['writes'].pop()
        with self.assertRaisesRegex(ValueError, 'write'):
            self.verify(selected, helpers=helpers)

    def test_helper_identity_is_bound_even_for_the_other_direction(self):
        selected = fixture()
        helpers = list(selected[-1])
        role, (start, end, count, digest), bounds = helpers[1]
        helpers[1] = role, (start, end, count+1, digest), bounds
        with self.assertRaisesRegex(ValueError, 'identity'):
            self.verify(selected, helpers=helpers)

    def test_extra_helper_sequence_is_rejected(self):
        selected = fixture()
        body = selected[0][:14] + call(A+14, P) + selected[0][14:]
        parts = {A: body, U: selected[1][U-base.BASE:U-base.BASE+12],
                 P: selected[1][P-base.BASE:P-base.BASE+10]}
        rom, rows, mapping, index = base.image(parts, {A: 11, U: 6, P: 5})
        with self.assertRaisesRegex(ValueError, 'exactly one pinned'):
            self.verify((body, rom, rows, mapping, index, selected[-1]))

    def test_explicit_selector_and_exact_manifest_are_required(self):
        with self.assertRaisesRegex(ValueError, 'explicit inventory'):
            self.verify(selector='default')
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.verify(manifest={})


if __name__ == '__main__':
    unittest.main(verbosity=2)
