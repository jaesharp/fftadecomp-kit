"""More small bodies require an aggregate bound and fresh actual effects."""
import copy
import json
import unittest

from test_r6_target_external_alignment import aligned_fixture, W, C, bl
import test_static_callback_r6_target as target
import static_callback_r6_frame_profile as policy
import owner_admission_profile as owner
import match


def add_bodies(values, bodies):
    rom = bytearray(values['rom'])
    rows = json.loads(values['mapping'])
    for address, body in bodies.items():
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(body)] = body
        rows.append(dict(rom=f'0x{address:08X}', end=f'0x{address+len(body):08X}',
                         mode='thumb', instrs=len(body)//2))
    values.update(rom=bytes(rom), mapping=json.dumps(rows).encode(),
        index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                      f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
                      for row in rows).encode())
    return values


def fixture():
    bodies = {C+0x1000+16*i: bytes.fromhex('00200021002200237047') for i in range(11)}
    worker = bytes.fromhex('70b50e1c151c')
    for address in bodies:
        worker += bl(W+len(worker), address)
    worker += bytes.fromhex('291c') + bl(W+len(worker)+2, target.THUNK)
    worker += bytes.fromhex('70bc01bc0047')
    values = add_bodies(aligned_fixture(worker=worker), bodies)
    values['selector'] = policy.COMPACT_CLOSURE_SELECTOR
    return values


def proof(values, selector=policy.COMPACT_CLOSURE_SELECTOR):
    return policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
                                      values['objects'], policy=selector)


class CompactClosureTests(unittest.TestCase):
    def test_complete_small_callees_have_actual_effects_and_bound_closure(self):
        values = fixture()
        manifest, _ = owner.verify(**values)
        evidence = manifest['proof']['buffers']['r6_restoration']
        closure = evidence['compact_dependency_closure']
        self.assertGreater(closure['owners'], 10)
        self.assertLessEqual(closure['aggregate_body_bytes'], 4096)
        self.assertEqual(closure['aggregate_body_bytes'], sum(row['bytes'] for row in closure['bodies']))
        self.assertEqual(manifest['proof']['buffers']['dependency_budget'], 32)
        with self.assertRaisesRegex(ValueError, 'dependency budget'):
            owner.verify(**dict(values, selector=policy.OPTIONAL_LOCAL_FRAME_SELECTOR))

    def test_aggregate_body_budget_applies_even_to_individually_small_owners(self):
        addresses = [C+0x3000, C+0x4000]
        values = add_bodies(aligned_fixture(),
            {address: bytes.fromhex('0020')*1024+bytes.fromhex('7047') for address in addresses})
        actual = proof(values)
        actual.span(addresses[0])
        with self.assertRaisesRegex(ValueError, 'aggregate body budget'):
            actual.span(addresses[1])

    def test_owner_count_budget_still_limits_tiny_bodies(self):
        addresses = [C+0x3000+4*i for i in range(33)]
        values = add_bodies(aligned_fixture(), {address: bytes.fromhex('7047') for address in addresses})
        actual = proof(values)
        for address in addresses[:32]:
            actual.span(address)
        with self.assertRaisesRegex(ValueError, 'dependency budget'):
            actual.span(addresses[32])

    def test_actual_out_of_bounds_effect_cannot_use_a_budget_allowance(self):
        values = fixture()
        rom = bytearray(values['rom'])
        address = C+0x1000
        rom[address-match.ROM_BASE:address-match.ROM_BASE+4] = bytes.fromhex('01209060')
        with self.assertRaisesRegex(ValueError, 'outside allocated'):
            owner.verify(**dict(values, rom=bytes(rom)))

    def test_closure_and_bound_policy_are_authenticated(self):
        values = fixture()
        manifest, _ = owner.verify(**values)
        for field in ('body', 'budget'):
            changed = copy.deepcopy(manifest)
            evidence = changed['proof']['buffers']['r6_restoration']
            if field == 'body':
                evidence['compact_dependency_closure']['bodies'][0]['body_sha256'] = '0'*64
            else:
                evidence['policy']['compact_dependency_closure']['aggregate_body_bytes'] = 8192
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'manifest differs'):
                owner.verify(**values, manifest=changed)


if __name__ == '__main__':
    unittest.main(verbosity=2)
