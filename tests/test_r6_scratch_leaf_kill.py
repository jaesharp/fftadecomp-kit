"""Discarded scratch may cross only a complete leaf that actually kills it."""
import copy
import json
import unittest

from test_r6_local_return_scratch import fixture as local_fixture
from test_r6_target_external_alignment import A, W, bl
import test_static_callback_r6_target as target
import static_callback_r6_frame_profile as policy
import owner_admission_profile as owner
import match

N = target.C + 0x1000
KILL = bytes.fromhex('0022002300207047')


def fixture(leaf=KILL):
    values = local_fixture()
    worker = bytes.fromhex('70b50e1c151c') + bl(W+6, target.L) + bl(W+10, N)
    worker += bytes.fromhex('291c') + bl(W+16, target.THUNK) + bytes.fromhex('70bc01bc0047')
    rom = bytearray(values['rom'])
    rom[W-match.ROM_BASE:W-match.ROM_BASE+len(worker)] = worker
    rom[N-match.ROM_BASE:N-match.ROM_BASE+len(leaf)] = leaf
    rows = json.loads(values['mapping'])
    for row in rows:
        if int(row['rom'], 16) == W:
            row['end'] = f'0x{W+len(worker):08X}'
    rows.append(dict(rom=f'0x{N:08X}', end=f'0x{N+len(leaf):08X}', mode='thumb', instrs=0))
    index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                    f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
                    for row in rows).encode()
    values.update(rom=bytes(rom), mapping=json.dumps(rows).encode(), index=index,
                  selector=policy.QUARANTINE_SELECTOR)
    return values


def proof(values):
    return policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
                                      values['objects'], policy=policy.QUARANTINE_SELECTOR)


class ScratchLeafKillTests(unittest.TestCase):
    def test_complete_leaf_kills_scratch_before_every_observation(self):
        values = fixture()
        manifest, _ = owner.verify(**values)
        evidence = manifest['proof']['buffers']['r6_restoration']
        kills = [kill for row in evidence['normal_return_scratch']
                 for kill in row.get('scratch_leaf_kills', [])]
        self.assertTrue(kills)
        self.assertTrue(all(row['address'] == N and row['killed_before_observation'] for row in kills))
        self.assertEqual(evidence['policy']['scratch_leaf_kill']['registers'], [2, 3])
        with self.assertRaisesRegex(ValueError, 'consumer observes'):
            owner.verify(**dict(values, selector=policy.LOCAL_SCRATCH_SELECTOR))

    def test_leaf_cannot_read_or_return_an_incoming_alias(self):
        for body in ('111c0022002300207047', '002300207047', '002200207047'):
            values = fixture(bytes.fromhex(body))
            with self.subTest(body=body), self.assertRaises(ValueError):
                proof(values)._scratch_leaf_kill(N, {match.ARM_REG_R0+2, match.ARM_REG_R0+3})

    def test_leaf_excludes_calls_frames_and_preserved_register_writes(self):
        for body in (bytes.fromhex('00b50022002301bc0047'),
                     bytes.fromhex('0024002200237047'),
                     bl(N, target.C)+bytes.fromhex('002200237047'),
                     bytes.fromhex('6a4600237047')):
            values = fixture(body)
            with self.subTest(body=body.hex()), self.assertRaisesRegex(ValueError, 'no-call no-frame'):
                proof(values)._scratch_leaf_kill(N, {match.ARM_REG_R0+2})

    def test_a_loop_or_return_path_without_killing_is_refused(self):
        for body in ('002800d0fce7002200237047', '002800d000227047'):
            values = fixture(bytes.fromhex(body))
            with self.subTest(body=body), self.assertRaises(ValueError):
                proof(values)._scratch_leaf_kill(N, {match.ARM_REG_R0+2})

    def test_changed_kill_receipt_cannot_authenticate_a_manifest(self):
        values = fixture()
        manifest, _ = owner.verify(**values)
        changed = copy.deepcopy(manifest)
        rows = changed['proof']['buffers']['r6_restoration']['normal_return_scratch']
        row = next(row for row in rows if row.get('scratch_leaf_kills'))
        row['scratch_leaf_kills'][0]['body_sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**values, manifest=changed)
        result = (values['data'], manifest, 'synthetic source', values['mapping'], values['index'],
                  values['objects'], values['rom'], 0, b'synthetic original identity')
        report = owner.render(A, result)
        self.assertEqual(owner.selector_for_report(report), policy.QUARANTINE_SELECTOR)
        with self.assertRaises(ValueError):
            owner.selected(report+f'* verification: `{policy.LOCAL_SCRATCH_SCHEMA}`\n')


if __name__ == '__main__':
    unittest.main(verbosity=2)
