"""Exact scalar service6 preserves bounded outgoing slots without alias inputs."""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))

import match
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import guarded_bios_division_profile as policy

A, B = 0x08010000, 0x08010100


def halfwords(*values):
    return struct.pack('<' + 'H' * len(values), *values)


def call(site, target):
    delta = target - site - 4
    return halfwords(0xF000 | ((delta >> 12) & 0x7FF),
                     0xF800 | ((delta >> 1) & 0x7FF))


def fixture():
    # Write one bounded word, kill the register result, retain an outgoing
    # pointer slot and saved R4 alias across an otherwise scalar BIOS call.
    body = (halfwords(0xB510, 0xB082, 0x4668) + call(A + 6, B) +
            halfwords(0x2007, 0x2102, 0x2200, 0x2300, 0x466C,
                      0x466B, 0x9300, 0x2300) + call(A + 26, policy.ADDRESS) +
            halfwords(0xB002, 0xBC10, 0xBC01, 0x4700))
    helper = halfwords(0x6001, 0x4770)
    rom = bytearray(policy.ADDRESS + 4 - match.ROM_BASE)
    for address, data in ((A, body), (B, helper), (policy.ADDRESS, policy.WRAPPER)):
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(data)] = data
    rows = [dict(rom=f'0x{address:08X}', end=f'0x{address+len(data):08X}',
                 mode='thumb', instrs=0)
            for address, data in ((A, body), (B, helper), (policy.ADDRESS, policy.WRAPPER))]
    index = ''.join(f'{int(row["rom"], 16):08X} {int(row["end"], 16):08X} '
                    f'{int(row["end"], 16)-int(row["rom"], 16)} 0 return\n'
                    for row in rows).encode()
    return dict(data=body, address=A, rom=bytes(rom), mapping=json.dumps(rows).encode(),
        index=index, objects=b'{}\n', selector=policy.SELECTOR,
        bindings=dict(calls=[[6, f'func_{B:08X}'], [26, f'func_{policy.ADDRESS:08X}']],
                      data=[], functions=[], switches=[]))


class GuardedBiosDivisionTests(unittest.TestCase):
    def test_complete_owner_and_manifest_bind_actual_scalar_call(self):
        f = fixture()
        manifest, _ = owner.verify(**f)
        self.assertEqual(manifest['profile'], policy.SCHEMA)
        proof = manifest['proof']['buffers']
        self.assertEqual(proof['dependency_budget'], 32)
        row = proof['bios_division']['observations'][0]
        self.assertEqual(row['site'], A + 26)
        self.assertEqual(row['untouched_incoming_slots'], [(0, -16)])
        self.assertIn('No division/remainder numerical equivalence', proof['bios_division']['conditional_ABI'])
        changed = copy.deepcopy(manifest)
        changed['proof']['buffers']['bios_division']['observations'][0]['consumer_body_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**dict(f, manifest=changed))

    def test_old_profile_and_actual_buffer_bounds_stay_closed(self):
        f = fixture()
        with self.assertRaisesRegex(ValueError, 'interrupts require linked CFG'):
            owner.verify(**dict(f, selector=buffers.GUARDED_ALIAS_SELECTOR))
        rom = bytearray(f['rom'])
        rom[B-match.ROM_BASE:B-match.ROM_BASE+2] = halfwords(0x6081)  # str r1,[r0,#8]
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            owner.verify(**dict(f, rom=bytes(rom)))

    def test_wrapper_mapping_call_site_and_scalar_inputs_are_required(self):
        f = fixture()
        stack = [(False, False, True)] * 2
        def proof(**changes):
            actual = dict(f, **changes)
            return policy.GuardedBiosDivisionProof(actual['rom'], actual['mapping'],
                actual['index'], actual['objects'])
        for register in range(match.ARM_REG_R0, match.ARM_REG_R0 + 4):
            with self.subTest(register=register), self.assertRaisesRegex(ValueError, 'without register aliases'):
                proof().check_arguments(policy.ADDRESS, {register: -8}, stack, {},
                    frozenset(), site=A+26)
        for site in (None, A, A+6, A+28, B):
            with self.subTest(site=site), self.assertRaises(ValueError):
                proof().check_arguments(policy.ADDRESS, {}, stack, {}, frozenset(), site=site)
        for wrapper in (halfwords(0xDF08, 0x4770), halfwords(0xDF06, 0x4700)):
            rom = bytearray(f['rom']);rom[policy.ADDRESS-match.ROM_BASE:] = wrapper
            with self.subTest(wrapper=wrapper), self.assertRaisesRegex(ValueError, 'exact complete'):
                proof(rom=bytes(rom)).check_arguments(policy.ADDRESS, {}, stack, {}, frozenset(), site=A+26)
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            proof().check_arguments(policy.ADDRESS, {}, stack, {0: -12}, frozenset(), site=A+26)
        for change in ('duplicate', 'mode', 'extent'):
            rows = json.loads(f['mapping'])
            if change == 'duplicate': rows.append(rows[-1].copy())
            if change == 'mode': rows[-1]['mode'] = 'arm'
            if change == 'extent': rows[-1]['end'] = f'0x{policy.ADDRESS+2:08X}'
            with self.subTest(change=change), self.assertRaises(ValueError):
                proof(mapping=json.dumps(rows).encode()).check_arguments(policy.ADDRESS,
                    {}, stack, {}, frozenset(), site=A+26)

    def test_new_policy_dispatches_and_strict_reports_remain_canonical(self):
        marker = f'* verification: `{policy.SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker), policy.SELECTOR)
        for report in (marker*2, marker+f'* verification: `{owner.SCHEMA}`\n'):
            with self.assertRaises(ValueError): owner.selected(report)
        with patch.object(sys, 'argv', ['match.py', '0x08010000', '--root', str(Path.cwd()),
                '--owner-runtime-profile', policy.SELECTOR]), \
                patch.object(match, 'repo_root', return_value=str(Path.cwd())), \
                patch.object(owner, 'issue', return_value=17) as issue:
            self.assertEqual(match.main(), 17)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile, policy.SELECTOR)


if __name__ == '__main__':
    unittest.main(verbosity=2)
