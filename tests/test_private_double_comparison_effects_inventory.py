"""Synthetic two-input comparison effects; no compiler or original ROM proof."""
import copy
import hashlib
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import private_double_comparison_effects_inventory as inventory
import software_float_profile as runtime
import test_private_float_pack_effects_inventory as fixtures

A, U, CMP = 0x08000100, 0x08000200, 0x08000300
words, call = fixtures.words, fixtures.call


def fixture(*, second_output=5, compare_offset=16, second_target=U, narrow_stack=False):
    caller = words(0xB500, 0xB08E, 0x900A, 0x910B, 0x920C, 0x930D, 0xA80A, 0x4669)
    caller += call(A + 16, U) + words(0xA80C, 0xA900 | second_output)
    caller += call(A + 24, second_target) + words(0x4668, 0xA905)
    caller += call(A + 32, CMP) + words(0xB00E, 0xBC02, 0x4708)
    unpack = words(0x6802, 0x6843, 0x600A, 0x604A, 0x608A, 0x60CA, 0x610A, 0x688A, 0x4770)
    if narrow_stack:
        unpack = words(0xB082, 0x6802, 0x6843, 0x9200, 0x466B, 0x781A, 0x881A,
                       0x600A, 0x604A, 0x608A, 0x60CA, 0x610A, 0x688A, 0xB002, 0x4770)
    comparison = words(0x6802, 0x6842, 0x6882, 0x68C2, 0x6902,
                       0x680A, 0x684A, 0x688A, 0x68CA,
                       0x680A | ((compare_offset // 4) << 6), 0x2000, 0x4770)
    parts = {A: caller, U: unpack, CMP: comparison}
    counts = {start: len(list(fixtures.Cs(fixtures.CS_ARCH_ARM,
        fixtures.CS_MODE_THUMB).disasm(body, start))) for start, body in parts.items()}
    rom, rows, mapping, index = fixtures.image(parts, counts)
    helpers = tuple((role, (start, start + len(parts[start]), counts[start],
        hashlib.sha256(parts[start]).hexdigest()), bounds)
        for (role, _, bounds), start in zip(inventory.HELPERS, (U, CMP)))
    return caller, rom, mapping, index, helpers


class DoubleComparisonEffectsTests(unittest.TestCase):
    def verify(self, selected=None, *, helpers=None, manifest=None,
               selector=inventory.SELECTOR):
        body, rom, mapping, index, specs = selected or fixture()
        with patch.object(inventory, 'HELPERS', specs if helpers is None else helpers), \
                patch.object(runtime, 'ROM_SHA256', hashlib.sha256(rom).hexdigest()), \
                patch.object(runtime, 'EDGES', ()):
            return inventory.verify(body, A, rom, mapping, index,
                selector=selector, manifest=manifest)

    def test_both_record_read_bounds_are_discharged_into_locals(self):
        result, instructions = self.verify()
        self.assertEqual(len(instructions), 18)
        self.assertEqual(result['external_reads'], [])
        self.assertEqual(result['external_writes'], [])
        self.assertEqual(result['helper_closure'][1]['native_proof']['argument_effects']['reads'],
                         [[register, offset, 4] for register in (0, 1)
                          for offset in range(0, 20, 4)])
        self.assertEqual(len(result['caller']['argument_accesses']), 26)
        self.assertEqual(result['numeric_return_facts'], [])
        self.assertFalse(result['source_or_ELF_admission'])

    def test_unpacker_narrow_stack_reads_keep_external_word_bounds(self):
        result, _ = self.verify(fixture(narrow_stack=True))
        proof = result['helper_closure'][0]['native_proof']
        self.assertEqual(proof['argument_effects']['reads'], [[0, 0, 4], [0, 4, 4], [1, 8, 4]])
        self.assertEqual(result['external_reads'], [])

    def test_unpacker_output_read_requires_its_own_finite_bound(self):
        selected = fixture()
        helpers = copy.deepcopy(list(selected[-1]))
        helpers[0][2]['reads'].pop()
        with self.assertRaisesRegex(ValueError, 'external read'):
            self.verify(selected, helpers=helpers)

    def test_second_output_cannot_overrun_live_allocation(self):
        with self.assertRaisesRegex(ValueError, 'saved|frame'):
            self.verify(fixture(second_output=13))

    def test_comparison_cannot_read_a_sixth_word(self):
        with self.assertRaisesRegex(ValueError, 'external read'):
            self.verify(fixture(compare_offset=20))

    def test_actual_second_formal_read_requires_its_bound(self):
        selected = fixture()
        helpers = copy.deepcopy(list(selected[-1]))
        helpers[1][2]['reads'].pop()
        with self.assertRaisesRegex(ValueError, 'external read'):
            self.verify(selected, helpers=helpers)

    def test_repeated_unpack_sequence_is_exact(self):
        with self.assertRaisesRegex(ValueError, 'two pinned unpacks'):
            self.verify(fixture(second_target=CMP))

    def test_helper_identity_and_complete_partition_are_bound(self):
        selected = fixture()
        helpers = list(selected[-1])
        role, (start, end, count, digest), bounds = helpers[1]
        helpers[1] = role, (start, end, count + 1, digest), bounds
        with self.assertRaisesRegex(ValueError, 'identity'):
            self.verify(selected, helpers=helpers)

    def test_explicit_selector_and_exact_manifest_required(self):
        with self.assertRaisesRegex(ValueError, 'explicit inventory'):
            self.verify(selector='default')
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.verify(manifest={})


if __name__ == '__main__':
    unittest.main(verbosity=2)
