"""Original compiler symbol identity and complete relocation preservation."""
from contextlib import contextmanager
import copy
import hashlib
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import compiler_local_copy_elf_inventory as inventory
import test_private_float_pack_effects_inventory as fixtures

A, H = 0x08000100, 0x08000200


def fixture(repeated=False):
    if repeated:
        body = fixtures.words(0xB500, 0x4804, 0x4904) + fixtures.call(A+6, H)
        body += fixtures.words(0x4A04, 0x4B04, 0x3000, 0xBC02, 0x4708)
        body += struct.pack('<IIII', *inventory.DATA.values(), *inventory.DATA.values())
        sites = ((6, 1, 10), (20, 2, 2), (24, 3, 2), (28, 2, 2), (32, 3, 2))
    else:
        body = fixtures.words(0xB500, 0x4803, 0x4903) + fixtures.call(A+6, H)
        body += fixtures.words(0xBC02, 0x4708, 0x0000)
        body += struct.pack('<II', *inventory.DATA.values())
        sites = ((6, 1, 10), (16, 2, 2), (20, 3, 2))
    helper = fixtures.words(0x4770)
    rom, _, mapping, index = fixtures.image({A: body, H: helper}, {A: 9 if repeated else 6, H: 1})
    symbols = [dict(name=f'func_{A:08X}', type=2, bind=1, section=1, value=1, size=len(body))]
    symbols += [dict(name=name, type=0, bind=1, section=0, value=0, size=0)
                for name in ('memcpy', *inventory.DATA)]
    raw = bytearray(body)
    raw[6:10] = fixtures.call(A+6, A+6)
    for site, _, kind in sites:
        if kind == 2:
            raw[site:site+4] = bytes(4)
    rels = b''.join(struct.pack('<II', site, number << 8 | kind)
                   for site, number, kind in sites)
    original = dict(type=1, text_index=1, text=bytes(raw), symbols=symbols,
        sections=[(0,)*10, (0, 1, 6, 0, 0, len(body), 0, 0, 4, 0),
                  (0, 9, 0, 0, 0, len(rels), 3, 1, 4, 8)],
        symbol_tables={3: symbols}, relocations=[2], section_data=[b'', bytes(raw), rels])
    linked = copy.deepcopy(original)
    linked.update(type=2, text=body, relocations=[])
    linked['sections'][1] = (0, 1, 6, A, 0, len(body), 0, 0, 4, 0)
    linked['symbols'][0]['value'] = A | 1
    linked['symbols'][1].update(type=2, value=H | 1, section=0xFFF1)
    for symbol, point in zip(linked['symbols'][2:], inventory.DATA.values()):
        symbol.update(type=1, value=point, section=0xFFF1)
    objects = json.dumps({name: f'0x{point:08X}' for name, point in inventory.DATA.items()}).encode()
    return original, linked, rom, mapping, index, objects, helper


class CompilerCopyELFInventoryTests(unittest.TestCase):
    def verify(self, selected=None, **changes):
        original, linked, rom, mapping, index, objects, helper = fixture() if selected is None else selected
        with patch.object(inventory, 'HELPER', (H, H+len(helper), 1, hashlib.sha256(helper).hexdigest())):
            return inventory.verify(original, linked, A, rom, mapping, index, objects,
                selector=changes.pop('selector', inventory.SELECTOR), **changes)

    def test_genuine_compiler_copy_and_both_data_bindings_without_admission(self):
        result = self.verify()
        self.assertEqual(result['relocations'], [[6, 10, 'memcpy', H],
            [16, 2, 'data_03003860', 0x03003860], [20, 2, 'data_03003E68', 0x03003E68]])
        self.assertEqual(result['instructions'], 6)
        for field in ('source_or_ELF_admission', 'copy_effects_proved', 'frame_preservation_proved',
                      'memory_safety_claim', 'physical_memory_claim', 'initialized_contents_claim'):
            self.assertIs(result[field], False)

    def test_repeated_named_literals_are_individually_bound_and_cannot_be_omitted(self):
        result = self.verify(fixture(repeated=True))
        self.assertEqual(len(result['relocations']), 5)
        self.assertEqual(result['instructions'], 9)
        for site in (20, 24, 28, 32):
            with self.subTest(site=site):
                v = list(fixture(repeated=True)); image = v[0]
                raw = image['section_data'][2]
                raw = b''.join(raw[i:i+8] for i in range(0, len(raw), 8)
                               if struct.unpack_from('<I', raw, i)[0] != site)
                section = list(image['sections'][2]); section[5] = len(raw)
                image['sections'][2] = tuple(section); image['section_data'][2] = raw
                with self.assertRaisesRegex(ValueError, 'unrelocated bytes'):
                    self.verify(v)

    def test_explicit_selector_and_typed_inputs(self):
        with self.assertRaisesRegex(ValueError, 'explicit selector'):
            self.verify(selector='default')
        v = list(fixture()); v[3] = bytearray(v[3])
        with self.assertRaisesRegex(ValueError, 'immutable inputs'):
            self.verify(v)

    def test_original_compiler_name_cannot_be_replaced_by_source_helper_name(self):
        v = list(fixture()); v[0]['symbols'][1]['name'] = f'func_{H:08X}'
        v[1]['symbols'][1]['name'] = f'func_{H:08X}'
        with self.assertRaisesRegex(ValueError, 'genuine compiler memcpy'):
            self.verify(v)

    def test_nonzero_call_and_data_addends_refuse(self):
        for site, replacement in ((6, fixtures.call(A+6, A+8)), (16, bytes([1, 0, 0, 0]))):
            with self.subTest(site=site):
                v = list(fixture()); raw = bytearray(v[0]['text']); raw[site:site+4] = replacement
                v[0]['text'] = bytes(raw)
                with self.assertRaisesRegex(ValueError, 'genuine compiler|zero-addend'):
                    self.verify(v)

    def test_duplicate_missing_extra_and_overlapping_relocations_refuse(self):
        for mode in ('duplicate-symbol', 'missing', 'extra', 'overlap'):
            with self.subTest(mode=mode):
                v = list(fixture()); image = v[0]
                if mode == 'duplicate-symbol':
                    image['symbols'].append(dict(image['symbols'][1]))
                else:
                    raw = image['section_data'][2]
                    if mode == 'missing': raw = raw[:-8]
                    elif mode == 'extra': raw += raw[:8]
                    else: raw = raw[:8] + struct.pack('<II', 8, 2 << 8 | 2) + raw[16:]
                    section = list(image['sections'][2]); section[5] = len(raw)
                    image['sections'][2] = tuple(section); image['section_data'][2] = raw
                with self.assertRaisesRegex(ValueError, 'unique ELF symbol|exactly one compiler|overlapping original'):
                    self.verify(v)

    def test_data_definitions_and_actual_data_map_are_mandatory(self):
        for mode in ('type', 'value', 'map'):
            with self.subTest(mode=mode):
                v = list(fixture())
                if mode == 'type': v[1]['symbols'][2]['type'] = 2
                elif mode == 'value': v[1]['symbols'][2]['value'] += 4
                else: v[5] = b'{}'
                with self.assertRaisesRegex(ValueError, 'one unchanged complete|typed literal|explicit data map'):
                    self.verify(v)

    def test_copy_thumb_definition_and_complete_helper_count_are_mandatory(self):
        for mode in ('thumb', 'helper-count'):
            with self.subTest(mode=mode):
                v = list(fixture())
                if mode == 'thumb': v[1]['symbols'][1]['value'] &= ~1
                else:
                    rows = json.loads(v[3]); rows[1]['instrs'] = 2; v[3] = json.dumps(rows).encode()
                with self.assertRaisesRegex(ValueError, 'genuine compiler|index.*count|count.*index|identity/count|spans/counts'):
                    self.verify(v)

    def test_unrelocated_bytes_and_stale_manifest_refuse(self):
        v = list(fixture()); raw = bytearray(v[1]['text']); raw[0] ^= 1; v[1]['text'] = bytes(raw)
        with self.assertRaisesRegex(ValueError, 'unrelocated bytes'):
            self.verify(v)
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.verify(manifest={'source_or_ELF_admission': True})

    def test_owner_count_and_extent_are_mandatory(self):
        for mode in ('count', 'extent'):
            with self.subTest(mode=mode):
                v = list(fixture()); rows = json.loads(v[3])
                if mode == 'count': rows[0]['instrs'] += 1
                else: rows[0]['end'] = f'0x{A+26:08X}'
                v[3] = json.dumps(rows).encode()
                with self.assertRaisesRegex(ValueError, 'count|span|extent|bound|complete'):
                    self.verify(v)


if __name__ == '__main__':
    unittest.main()
