"""Synthetic finite double-record effects, without original ROM or compiler calls."""
import copy
import hashlib
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import private_double_scalar_conversion_effects_inventory as inventory
import software_float_profile as runtime
import test_private_float_pack_effects_inventory as base

A, U, W = base.ADDRESS, base.UNPACK, base.PACK
words, call = base.words, base.call


def fixture(*, pointer=5, unpack=None, reverse=False):
    if unpack is None:
        unpack = words(0x6802, 0x6843, 0x600A, 0x604A, 0x608A, 0x60CA,
                       0x610A, 0x688A, 0x4770)
    wide = words(0x4770)
    caller = words(0xB500, 0xB087, 0x9005, 0x9106, 0xA800 | pointer, 0x4669)
    caller += call(A+12, W if reverse else U)
    caller += words(0x9803, 0x9904, 0x2201)
    caller += call(A+22, U if reverse else W)
    caller += words(0xB007, 0xBC02, 0x4708)
    parts = {A: caller, U: unpack, W: wide}
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    counts = {start: len(list(decoder.disasm(body, start))) for start, body in parts.items()}
    rom, rows, mapping, index = base.image(parts, counts)
    specs = tuple((role, (start, start+len(parts[start]), counts[start],
        hashlib.sha256(parts[start]).hexdigest()), bounds)
        for (role, _, bounds), start in zip(inventory.HELPERS, (U, W)))
    return caller, rom, rows, mapping, index, specs


class DoubleScalarConversionEffectsTests(unittest.TestCase):
    def verify(self, selected=None, *, helpers=None, selector=inventory.SELECTOR, manifest=None):
        body, rom, _, mapping, index, specs = selected or fixture()
        with patch.object(inventory, 'HELPERS', helpers or specs), \
                patch.object(runtime, 'ROM_SHA256', hashlib.sha256(rom).hexdigest()), \
                patch.object(runtime, 'EDGES', ()):
            return inventory.verify(body, A, rom, mapping, index, selector=selector, manifest=manifest)

    def test_exact_two_helpers_discharge_eight_and_twenty_byte_buffers(self):
        proof, _ = self.verify()
        self.assertEqual(proof['external_reads'], [])
        self.assertEqual(proof['external_writes'], [])
        effects = proof['helper_closure'][0]['native_proof']['argument_effects']
        self.assertEqual(effects['reads'], [[0, 0, 4], [0, 4, 4], [1, 8, 4]])
        self.assertEqual(effects['writes'], [[1, offset, 4] for offset in range(0, 20, 4)])
        self.assertTrue(all(access[-1][:2] == ['stack', 0]
                            for access in proof['caller']['argument_accesses']))
        self.assertEqual(proof['numeric_return_facts'], [])
        self.assertFalse(proof['source_or_ELF_admission'])
        self.assertFalse(proof['physical_memory_claim'])

    def test_input_second_word_cannot_reach_saved_or_incoming_stack(self):
        for pointer in (6, 7, 8):
            with self.subTest(pointer=pointer), self.assertRaises(ValueError):
                self.verify(fixture(pointer=pointer))

    def test_each_actual_read_and_write_requires_explicit_bound(self):
        selected = fixture()
        for kind in ('reads', 'writes'):
            for position in range(len(selected[-1][0][2][kind])):
                helpers = copy.deepcopy(selected[-1])
                helpers[0][2][kind].pop(position)
                with self.subTest(kind=kind, position=position), self.assertRaises(ValueError):
                    self.verify(selected, helpers=helpers)

    def test_narrow_helper_local_load_retains_finite_record_policy(self):
        unpack = words(0xB081, 0x9000, 0x9A00, 0x7802, 0x600A,
                       0x604A, 0x608A, 0x60CA, 0x610A, 0xB001, 0x4770)
        # Read the helper's own allocated word through SP, not the argument buffer.
        unpack = unpack[:6]+words(0x466A, 0x7812)+unpack[8:]
        proof, _ = self.verify(fixture(unpack=unpack))
        self.assertTrue(proof['complete_argument_effect_proof'])

    def test_pinned_leaf_identity_and_call_order_cannot_change(self):
        selected = fixture()
        helpers = list(selected[-1])
        role, (start, end, count, digest), bounds = helpers[1]
        helpers[1] = role, (start, end, count+1, digest), bounds
        with self.assertRaisesRegex(ValueError, 'identity'):
            self.verify(selected, helpers=helpers)
        with self.assertRaisesRegex(ValueError, 'exactly one pinned'):
            self.verify(fixture(reverse=True))
        with patch.object(runtime, 'EDGES', ((W, U),)), self.assertRaisesRegex(ValueError, 'closed leaf'):
            body, rom, _, mapping, index, specs = selected
            with patch.object(inventory, 'HELPERS', specs), \
                    patch.object(runtime, 'ROM_SHA256', hashlib.sha256(rom).hexdigest()):
                inventory.verify(body, A, rom, mapping, index, selector=inventory.SELECTOR)

    def test_explicit_selector_and_complete_manifest_are_required(self):
        with self.assertRaisesRegex(ValueError, 'explicit inventory'):
            self.verify(selector='default')
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.verify(manifest={})


if __name__ == '__main__':
    unittest.main(verbosity=2)
