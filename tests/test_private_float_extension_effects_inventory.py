"""Synthetic extension closure effects, including the real fifth-word boundary."""
import copy
import hashlib
import sys
from pathlib import Path
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import private_float_extension_effects_inventory as inventory
import software_float_profile as runtime
import test_private_float_pack_effects_inventory as fixtures

A, U, CMP, PACK, CONSTRUCT = (0x08000100, 0x08000200, 0x08000240,
                            0x08000280, 0x08000300)
words, call = fixtures.words, fixtures.call


def fixture(output_after_zero=False, external_pack=False):
    caller = bytearray(fixtures.PrivateFloatPackEffectsTests().fixture()[0])
    if output_after_zero:
        caller[8:10] = words(0xA901)  # Output starts at SP+4, leaving SP unwritten.
    unpack = words(0xB510, 0x6802, 0x600A, 0x604A, 0x608A, 0x60CA,
                   0xBC10, 0xBC01, 0x4700)
    pack = words(0x6801, 0x6841, 0x6881, 0x68C1,
                 0x6941 if external_pack else 0x6901, 0x4770)
    constructor = words(0xB500, 0xB085, 0x9906, 0x4668)
    constructor += call(CONSTRUCT + 8, PACK)
    constructor += words(0xB005, 0xBC02, 0x4708)
    parts = {A: bytes(caller), U: unpack, CMP: words(0x4770),
             PACK: pack, CONSTRUCT: constructor}
    counts = {start: len(list(fixtures.Cs(fixtures.CS_ARCH_ARM,
        fixtures.CS_MODE_THUMB).disasm(body, start))) for start, body in parts.items()}
    rom, rows, mapping, index = fixtures.image(parts, counts)
    helpers = tuple((role, (start, start + len(parts[start]), counts[start],
        hashlib.sha256(parts[start]).hexdigest()), bounds)
        for (role, _, bounds), start in zip(inventory.HELPERS, (U, CMP, PACK, CONSTRUCT)))
    return parts[A], rom, mapping, index, helpers


class ExtensionEffectsTests(unittest.TestCase):
    def verify(self, selected=None, *, helpers=None, manifest=None,
               selector=inventory.SELECTOR, edges=((CONSTRUCT + 8, PACK),)):
        body, rom, mapping, index, specs = selected or fixture()
        with patch.object(inventory, 'HELPERS', specs if helpers is None else helpers), \
                patch.object(runtime, 'ROM_SHA256', hashlib.sha256(rom).hexdigest()), \
                patch.object(runtime, 'EDGES', edges):
            return inventory.verify(body, A, rom, mapping, index,
                selector=selector, manifest=manifest)

    def test_complete_nested_effects_and_fifth_argument_stay_local(self):
        result, instructions = self.verify()
        self.assertEqual(len(instructions), 17)
        self.assertEqual(result['external_reads'], [])
        self.assertEqual(result['external_writes'], [])
        self.assertEqual(result['helper_closure'][-1]['native_proof']['stack_reads'], [(0, 4)])
        self.assertEqual(result['helper_closure'][2]['native_proof']['argument_effects']['reads'],
                         [[0, offset, 4] for offset in range(0, 20, 4)])
        self.assertFalse(result['source_or_ELF_admission'])
        self.assertEqual(result['numeric_return_facts'], [])

    def test_unwritten_fifth_argument_refuses(self):
        with self.assertRaisesRegex(ValueError, 'stack argument is not established'):
            self.verify(fixture(output_after_zero=True))

    def test_double_pack_read_cannot_exceed_twenty_bytes(self):
        with self.assertRaisesRegex(ValueError, 'external read'):
            self.verify(fixture(external_pack=True))

    def test_missing_completed_dependency_refuses(self):
        with self.assertRaisesRegex(ValueError, 'completed native dependency'):
            self.verify(edges=((CONSTRUCT + 8, 0x08000380),))

    def test_actual_read_requires_its_declared_bound(self):
        selected = fixture()
        helpers = copy.deepcopy(list(selected[-1]))
        helpers[2][2]['reads'].pop()
        with self.assertRaisesRegex(ValueError, 'external read'):
            self.verify(selected, helpers=helpers)

    def test_exact_manifest_and_explicit_selector_required(self):
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.verify(manifest={})
        with self.assertRaisesRegex(ValueError, 'explicit inventory'):
            self.verify(selector='default')


if __name__ == '__main__':
    unittest.main(verbosity=2)
