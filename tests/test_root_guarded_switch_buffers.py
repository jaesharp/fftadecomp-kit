"""Root switch composition retains complete frame and local-buffer checks."""
import copy
import json
import struct
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import named_data_buffer_profile as buffers
import owner_admission_profile as owner

A, B = 0x08010000, 0x08020000


def bl(site, target):
    displacement = target - site - 4
    return struct.pack('<HH', 0xF000 | ((displacement >> 12) & 0x7FF),
                       0xF800 | ((displacement >> 1) & 0x7FF))


def fixture(*, callee=(0x6001, 0x2000, 0x4770), callee_body=None, allocation=2, alias=True):
    body = bytearray()
    labels, branches = {}, []

    def emit(value):
        body.extend(struct.pack('<H', value))

    def branch(opcode, label):
        branches.append((len(body), opcode, label))
        emit(0)

    emit(0xB510)  # save R4 and entry LR
    emit(0xB080 | allocation)
    emit(0x2801)
    branch(0xD800, 'default')
    for value in (0x0080, 0x4902, 0x1840, 0x6800, 0x4687):
        emit(value)
    emit(0)
    body.extend(struct.pack('<III', A+24, 0, 0))
    labels['case0'] = len(body)
    emit(0x4668 if alias else 0x2000)
    call = A+len(body)
    body.extend(bl(call, B))
    emit(0x2000)
    branch(0xE000, 'finish')
    labels['case1'] = len(body)
    load = len(body)
    emit(0)
    emit(0x6800)
    branch(0xE000, 'finish')
    labels['default'] = len(body)
    emit(0x2000)
    labels['finish'] = len(body)
    for value in (0xB000 | allocation, 0xBC10, 0xBC02, 0x4708):
        emit(value)
    if len(body) % 4:
        emit(0)
    object_offset = len(body)
    body.extend(struct.pack('<I', 0x03000020))
    struct.pack_into('<H', body, load,
                     0x4800 | ((object_offset-((load+4)&~3))//4))
    for offset, opcode, label in branches:
        difference = (labels[label]-offset-4)//2
        struct.pack_into('<H', body, offset,
                         opcode | (difference & (0x7FF if opcode == 0xE000 else 0xFF)))
    for offset, label in ((24, 'case0'), (28, 'case1')):
        struct.pack_into('<I', body, offset, A+labels[label])
    helper = struct.pack('<'+'H'*len(callee), *callee) if callee_body is None else callee_body
    rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(body):08X}', mode='thumb', instrs=0),
            dict(rom=f'0x{B:08X}', end=f'0x{B+len(helper):08X}', mode='thumb', instrs=len(helper)//2)]
    mapping = json.dumps(rows).encode()
    rows[0]['instrs'] = owner.refine(bytes(body), A, mapping)['instrs']
    mapping = json.dumps(rows).encode()
    index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                    f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'
                    for r in rows).encode()
    rom = bytearray(B-match.ROM_BASE+len(helper))
    rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
    rom[B-match.ROM_BASE:B-match.ROM_BASE+len(helper)] = helper
    bindings = dict(calls=[[call-A, f'func_{B:08X}']],
                    data=[[object_offset, 'state', 0]], functions=[],
                    switches=[[20, 24], [24, labels['case0']], [28, labels['case1']]])
    return dict(data=bytes(body), address=A, rom=bytes(rom), mapping=mapping, index=index,
                objects=b'{"state":"0x03000020"}', bindings=bindings,
                selector=buffers.ROOT_SWITCH_SELECTOR)


class RootSwitchBufferTests(unittest.TestCase):
    def test_existing_guarded_callee_inventory_keeps_each_output_bound(self):
        prefix = struct.pack('<8H', 0xB500, 0x2901, 0xD80E,
                             0x008B, 0x4A01, 0x189B, 0x681B, 0x469F)
        table = struct.pack('<3I', B+20, B+28, B+32)
        suffix = struct.pack('<7H', 0x6002, 0xE001, 0x6042, 0xE7FF, 0x2000, 0xBC02, 0x4708)
        body = prefix+table+suffix
        manifest, _ = owner.verify(**fixture(callee_body=body))
        guarded = manifest['proof']['buffers']['root_guarded_switch']['guarded_callees']
        self.assertEqual([r['address'] for r in guarded], [B])
        with self.assertRaises(ValueError):
            owner.verify(**fixture(callee_body=body, allocation=1))

    def test_complete_guarded_paths_frame_and_output_bounds(self):
        f = fixture()
        manifest, instructions = owner.verify(**f)
        self.assertEqual(manifest['profile'], buffers.ROOT_SWITCH_SCHEMA)
        self.assertEqual(manifest['proof']['frame']['preserved'], 'r4-r11,sp,entry-lr')
        self.assertEqual(manifest['proof']['instructions'], len(instructions))
        self.assertEqual(manifest['proof']['buffers']['dependencies'][0]['address'], B)
        self.assertEqual(manifest['proof']['buffers']['root_guarded_switch']['switch']['bound'], 1)

    def test_alias_escape_saved_words_and_out_of_frame_writes_fail(self):
        for changes in (dict(callee=(0x6001, 0x4770)),
                        dict(callee=(0x6081, 0x2000, 0x4770)), dict(allocation=0)):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                owner.verify(**fixture(**changes))

    def test_root_return_must_restore_callee_saved_tokens(self):
        f = fixture()
        data = bytearray(f['data'])
        # Replace restoration of R4 with a scalar write while retaining balanced SP.
        offset = data.index(struct.pack('<H', 0xBC10))
        struct.pack_into('<H', data, offset, 0xBC08)
        struct.pack_into('<H', data, 38, 0x2400)  # actually destroy incoming R4
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        with self.assertRaises(ValueError):
            owner.verify(**dict(f, data=bytes(data), rom=bytes(rom)))

    def test_explicit_selector_and_actual_inspected_buffer_required(self):
        f = fixture()
        for selector in (buffers.SELECTOR, buffers.GUARDED_SWITCH_SELECTOR, owner.ALIGNED_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                owner.verify(**dict(f, selector=selector))
        with self.assertRaises(ValueError):
            owner.verify(**fixture(alias=False))

    def test_exact_typed_words_ROM_and_manifest_required(self):
        f = fixture()
        manifest, _ = owner.verify(**f)
        changed = copy.deepcopy(manifest)
        changed['proof']['buffers']['root_guarded_switch']['switch']['bound'] = 2
        with self.assertRaises(ValueError):
            owner.verify(**f, manifest=changed)
        for key in ('switches', 'data'):
            altered = copy.deepcopy(f)
            altered['bindings'][key] = []
            with self.subTest(key=key), self.assertRaises(ValueError):
                owner.verify(**altered)
        with self.assertRaises(ValueError):
            owner.verify(**dict(f, rom=f['rom'][:A-match.ROM_BASE]+bytes(len(f['rom'])-(A-match.ROM_BASE))))

    def test_closed_proof_type_root_binding_and_report_round_trip(self):
        f = fixture()
        calls = {A+site: B for site, _ in f['bindings']['calls']}
        words = dict(f['bindings']['switches'])
        proof = buffers.RootGuardedSwitchBufferProof(f['rom'], f['mapping'], f['index'], f['objects'])
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(f['data'], A, True, calls,
                buffer_proof=proof, switch_relocations=words)
        proof.bind_root(f['data'], A, calls, words)
        with self.assertRaises(ValueError):
            proof.bind_root(f['data'], A, calls, words)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(f['data'], A, True, {},
                buffer_proof=proof, switch_relocations=words)
        class Forged(buffers.RootGuardedSwitchBufferProof):
            pass
        forged = Forged(f['rom'], f['mapping'], f['index'], f['objects'])
        forged.bind_root(f['data'], A, calls, words)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(f['data'], A, True, calls,
                buffer_proof=forged, switch_relocations=words)
        report = f'* verification: `{buffers.ROOT_SWITCH_SCHEMA}`\n'
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), buffers.ROOT_SWITCH_SELECTOR)


if __name__ == '__main__':
    unittest.main(verbosity=2)
