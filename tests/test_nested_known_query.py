"""Nested query composition and actual scratch-consumer rejection cases."""
import copy
import json
from pathlib import Path
import struct
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import named_data_buffer_profile as named
import nested_known_query_profile as nested
import known_list_query_continuation_profile as query
import known_list_query_closure_profile as known
from test_known_list_query_continuation import raw_query

A, B, C, D = 0x08010000, 0x08011000, 0x08012000, 0x08013000


def bl(site, target):
    value = target-site-4
    return struct.pack('<HH', 0xf000 | ((value >> 12) & 0x7ff),
                       0xf800 | ((value >> 1) & 0x7ff))


def assemble(address, tokens):
    raw = bytearray()
    for token in tokens:
        raw += bl(address+len(raw), token) if token >= 0x08000000 else struct.pack('<H', token)
    return bytes(raw)


def query_body(address, callees=(), extra=()):
    tokens = [0xb530, 0xb083, 0x1c04, 0x1c0d, 0x9500, 0x2000, 0x9002,
              0x6920, 0, 0x466a, query.ITERATOR]
    for target in callees:
        tokens.extend((0x1c20, 0x1c29, target))
    tokens.extend((*extra, 0x9802, 0xb003, 0xbc30, 0xbc02, 0x4708))
    raw = bytearray(assemble(address, tokens))
    if len(raw) % 4:
        raw += b'\0\0'
    literal = len(raw)
    struct.pack_into('<H', raw, 16, 0x4900 | ((literal-20)//4))
    raw += struct.pack('<I', query.CALLBACK | 1)
    return bytes(raw), literal


def fixture(consumer=True, consumer_body=None, leaf=None, extra=()):
    root, literal = query_body(A, (B, C) if consumer else (B,), extra)
    helper, _ = query_body(B)
    bodies = {start: bytes.fromhex(raw) for start, (_, raw) in known.DEPENDENCIES.items()
              if start != 0x08022194}
    bodies.update({A: root, B: helper,
        C: assemble(C, consumer_body or (0xb500, D, 0xbc02, 0x4708)),
        D: assemble(D, leaf or (0x2200, 0x4770))})
    rom = bytearray(0x142260)
    rows = []
    for address, body in sorted(bodies.items()):
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(body)] = body
        count = known.DEPENDENCIES[address][0] if address in known.DEPENDENCIES else len(body)//2
        rows.append(dict(rom=f'0x{address:08X}', end=f'0x{address+len(body):08X}', mode='thumb', instrs=count))
    rom[0x14225e:0x142260] = bytes.fromhex('c046')
    mapping = json.dumps(rows).encode()
    for row in rows:
        address = int(row['rom'], 16)
        if address in (A, B, C, D):
            row['instrs'] = owner.refine(bodies[address], address, mapping)['instrs']
    mapping = json.dumps(rows).encode()
    refine = owner.refine(root, A, mapping)
    _, _, _, calls, _ = graph.graph(root, A, refine)
    return dict(data=root, address=A, rom=bytes(rom), mapping=mapping,
        index=''.join(f'{r["rom"][2:]} {r["end"][2:]} '
            f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode(),
        objects=b'{}', bindings=dict(calls=[[site-A, f'func_{target:08X}'] for site, target in calls.items()],
            functions=[[literal, f'func_{query.CALLBACK:08X}']], data=[], switches=[]), selector=nested.SELECTOR)


def alter(f, address, offset, halfword):
    f = copy.deepcopy(f)
    rom = bytearray(f['rom'])
    struct.pack_into('<H', rom, address-match.ROM_BASE+offset, halfword)
    f['rom'] = bytes(rom)
    if address == A:
        f['data'] = bytes(rom[A-match.ROM_BASE:A-match.ROM_BASE+len(f['data'])])
    return f


class NestedQueryTests(unittest.TestCase):
    def test_complete_nested_query_and_transitive_killing_write(self):
        manifest, _ = owner.verify(**fixture())
        self.assertEqual(manifest['profile'], nested.SCHEMA)
        receipt = manifest['proof']['nested_queries'][0]
        self.assertEqual(receipt['target'], B)
        self.assertEqual({x['address'] for x in receipt['consumer']}, {A, C, D})
        self.assertIn(D, {x['address'] for x in manifest['proof']['buffers']['dependencies']})

    def test_no_consumer_can_leave_only_nonresult_r2_at_normal_return(self):
        manifest, _ = owner.verify(**fixture(consumer=False))
        self.assertEqual(manifest['proof']['nested_queries'][0]['consumer'][0]['surviving_normal_returns'], [2])

    def test_independent_raw_oracle_empty_miss_and_found_nested_paths(self):
        f = fixture()
        for keys, found in [([], None), ([0x10], None), ([0x02004000], 0),
                            ([0x10, 0x02004000, 0x20], 1)]:
            with self.subTest(keys=keys):
                result, scratch, objects = raw_query(f['rom'], keys)
                self.assertEqual(result, 0 if found is None else objects[found])
                self.assertEqual(scratch, 0)

    def test_incoming_private_origin_cannot_be_read_as_key(self):
        with self.assertRaisesRegex(ValueError, 'prefix observes'):
            owner.verify(**alter(fixture(), B, 6, 0x1c15))

    def test_incoming_private_origin_cannot_be_spilled(self):
        with self.assertRaises(ValueError):
            owner.verify(**alter(fixture(), B, 8, 0x9200))

    def test_expired_nested_pointer_cannot_be_read(self):
        with self.assertRaisesRegex(ValueError, 'observed before'):
            owner.verify(**fixture(consumer=False, extra=(0x6810,)))

    def test_expired_nested_pointer_cannot_be_compared(self):
        with self.assertRaisesRegex(ValueError, 'observed before'):
            owner.verify(**fixture(consumer=False, extra=(0x2a00,)))

    def test_expired_nested_pointer_cannot_be_copied(self):
        with self.assertRaisesRegex(ValueError, 'observed before'):
            owner.verify(**fixture(consumer=False, extra=(0x1c13,)))

    def test_expired_nested_pointer_cannot_be_stored(self):
        with self.assertRaisesRegex(ValueError, 'observed before'):
            owner.verify(**fixture(consumer=False, extra=(0x9200,)))

    def test_transitive_callee_cannot_read_before_kill(self):
        with self.assertRaisesRegex(ValueError, 'observed before'):
            owner.verify(**fixture(leaf=(0x6810, 0x2200, 0x4770)))

    def test_transitive_callee_cannot_spill_before_kill(self):
        with self.assertRaisesRegex(ValueError, 'observed before'):
            owner.verify(**fixture(leaf=(0xb404, 0xbc04, 0x2200, 0x4770)))

    def test_recursive_observation_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'recursion|recursive'):
            owner.verify(**fixture(leaf=(0xb500, C, 0xbc02, 0x4708)))

    def test_indirect_call_cannot_use_arity_to_discard_scratch(self):
        f = fixture(consumer_body=(0xb500, 0x0814225C, 0xbc02, 0x4708))
        with self.assertRaises(ValueError):
            owner.verify(**f)

    def test_nested_query_callback_identity_is_required(self):
        body, literal = query_body(B)
        with self.assertRaises(ValueError):
            owner.verify(**alter(fixture(), B, literal, 0xab59))

    def test_nested_query_cannot_return_private_r0(self):
        with self.assertRaises(ValueError):
            owner.verify(**alter(fixture(), B, 24, 0x4668))

    def test_old_selector_still_rejects_nested_query_context(self):
        f = fixture(); f['selector'] = query.SELECTOR
        with self.assertRaisesRegex(ValueError, 'query replay differs'):
            owner.verify(**f)

    def test_unregistered_subclass_is_not_trusted(self):
        class Unregistered(nested.NestedKnownQueryProof):
            pass
        f = fixture()
        proof = Unregistered(f['rom'], f['mapping'], f['index'], f['objects'])
        self.assertFalse(named.conditional_thunk_replay(proof))

    def test_report_and_cli_preserve_explicit_new_selector(self):
        self.assertEqual(owner.selector_for_report(f'* verification: `{nested.SCHEMA}`'), nested.SELECTOR)
        run = subprocess.run([sys.executable, '-B', match.__file__, '--owner-runtime-profile',
                              nested.SELECTOR, '--help'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(nested.SELECTOR, run.stdout)

    def test_changed_saved_manifest_is_rejected(self):
        f = fixture(); manifest, _ = owner.verify(**f)
        manifest['proof']['nested_queries'][0]['target'] += 2
        with self.assertRaises(ValueError):
            owner.verify(**dict(f, manifest=manifest))

    def test_branch_that_does_not_kill_still_reaches_observation(self):
        with self.assertRaisesRegex(ValueError, 'observed before'):
            owner.verify(**fixture(consumer_body=(0x2800, 0xd000, 0x2200, 0x4770), extra=(0x6810,)))

    def test_observation_state_budget_is_enforced(self):
        with patch.object(nested, 'MAX_STATES', 1), self.assertRaisesRegex(ValueError, 'state budget'):
            owner.verify(**fixture())

    def test_observation_depth_budget_is_enforced(self):
        with patch.object(nested, 'MAX_DEPTH', 1), self.assertRaisesRegex(ValueError, 'depth bound'):
            owner.verify(**fixture())

    def test_old_and_new_report_markers_are_separate_choices(self):
        old = f'* verification: `{query.SCHEMA}`'
        new = f'* verification: `{nested.SCHEMA}`'
        self.assertEqual(owner.selector_for_report(old), query.SELECTOR)
        with self.assertRaises(ValueError):
            owner.selector_for_report(old+'\n'+new)


if __name__ == '__main__':
    unittest.main()
