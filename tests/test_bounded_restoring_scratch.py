"""Bounded ordinary outputs retain R0/R1 and exact root-only scratch checks."""
import copy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

from test_descriptor_restoring_leaf import fixture as leaf_fixture
from test_guarded_bios_division import halfwords,A,B
import descriptor_disjunctive_alias_profile as policy
import match
import owner_admission_profile as owner


def fixture(register=2):
    f=leaf_fixture()
    body=bytearray(f['data'])
    body[14:16]=halfwords(0x4668+register)  # mov rN,sp after actual bounded output
    if register==1:
        body[20:24]=halfwords(0xBC08,0x4718)  # return through R3, retaining R1 alias
    rom=bytearray(f['rom']);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body
    return dict(f,data=bytes(body),rom=bytes(rom),selector=policy.BOUNDED_SELECTOR)


class BoundedRestoringScratchTests(unittest.TestCase):
    def test_complete_ordinary_owner_and_tampered_return_manifest(self):
        f=fixture()
        manifest,_=owner.verify(**f)
        self.assertEqual(manifest['profile'],policy.BOUNDED_SCHEMA)
        self.assertEqual(manifest['proof']['schema'],policy.BOUNDED_SCHEMA)
        buffers=manifest['proof']['buffers']
        self.assertTrue(buffers['restoring_leaf_aliases']['observations'])
        scratch=buffers['root_discarded_scratch']
        self.assertEqual(scratch['registers'],[2,3])
        self.assertEqual(scratch['address'],A)
        self.assertTrue(scratch['observations'])
        self.assertTrue(all(row[1]in(2,3)for row in scratch['observations']))
        altered=copy.deepcopy(manifest)
        altered['proof']['buffers']['root_discarded_scratch']['body_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            owner.verify(**dict(f,manifest=altered))

    def test_result_registers_and_existing_selector_remain_closed(self):
        for register in (0,1):
            with self.subTest(register=register),self.assertRaisesRegex(ValueError,'escapes through a return register'):
                owner.verify(**fixture(register))
        with self.assertRaisesRegex(ValueError,'escapes through a return register'):
            owner.verify(**dict(fixture(),selector=policy.CALLEE_SELECTOR))

    def test_all_actual_output_bounds_remain_enforced(self):
        f=fixture();rom=bytearray(f['rom'])
        rom[B-match.ROM_BASE+4:B-match.ROM_BASE+6]=halfwords(0x8114)
        with self.assertRaisesRegex(ValueError,'outside allocated local words|outside the tracked frame'):
            owner.verify(**dict(f,rom=bytes(rom)))

    def test_root_projection_cannot_apply_to_another_body_or_active_callee(self):
        f=fixture()
        proof=policy.BoundedRestoringScratchProof(f['rom'],f['mapping'],f['index'],f['objects'])
        aliases={match.ARM_REG_R2:-16}
        with self.assertRaisesRegex(ValueError,'bound root context'):
            policy.root_return_aliases(proof,f['data'],A,A+len(f['data'])-2,aliases)
        proof.bind_root(A,f['data'])
        for data,address,site in ((f['data'],B,B),(f['data']+b'\0\0',A,A+len(f['data'])-2),
                                  (f['data'],A,A)):
            with self.subTest(address=address,site=site),self.assertRaises(ValueError):
                policy.root_return_aliases(proof,data,address,site,aliases)
        proof.active.add(B)
        with self.assertRaises(ValueError):
            policy.root_return_aliases(proof,f['data'],A,A+len(f['data'])-2,aliases)
        class Arbitrary(policy.BoundedRestoringScratchProof):pass
        other=Arbitrary(f['rom'],f['mapping'],f['index'],f['objects'])
        self.assertEqual(policy.root_return_aliases(other,f['data'],A,A,aliases),aliases)

    def test_explicit_selector_and_canonical_report(self):
        marker=f'* verification: `{policy.BOUNDED_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker),policy.BOUNDED_SELECTOR)
        for text in (marker*2,marker+f'* verification: `{policy.SCHEMA}`\n'):
            with self.assertRaises(ValueError):owner.selected(text)
        with patch.object(sys,'argv',['match.py','0x08010000','--root',str(Path.cwd()),
                '--owner-runtime-profile',policy.BOUNDED_SELECTOR]), \
                patch.object(match,'repo_root',return_value=str(Path.cwd())), \
                patch.object(owner,'issue',return_value=17)as issue:
            self.assertEqual(match.main(),17)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile,policy.BOUNDED_SELECTOR)


if __name__=='__main__':unittest.main(verbosity=2)
