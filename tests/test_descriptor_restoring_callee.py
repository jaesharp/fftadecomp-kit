"""Nested actual effects remain mandatory after saved-entry restoration proof."""
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

from test_descriptor_restoring_leaf import fixture as root_fixture
from test_guarded_bios_division import halfwords,call,A,B
import descriptor_disjunctive_alias_profile as policy
import match
import owner_admission_profile as owner

C=B+0x100


def fixture(*,early=False,child=halfwords(0x4770),bad_return=False):
    push=halfwords(0xB550)
    writes=halfwords(0x2407,0x2608,0x8014)
    middle=(call(B+2,C)+writes) if early else (writes+call(B+8,C))
    leaf=push+middle+halfwords(0xBC50,0xBC02,0x4700 if bad_return else 0x4708)
    f=root_fixture(leaf)
    rom=bytearray(f['rom']);rom.extend(b'\0'*(C-match.ROM_BASE+len(child)-len(rom)))
    rom[C-match.ROM_BASE:]=child
    rows=json.loads(f['mapping']);rows.append(dict(rom=f'0x{C:08X}',
        end=f'0x{C+len(child):08X}',mode='thumb',instrs=0))
    f.update(rom=bytes(rom),mapping=json.dumps(rows).encode(),
        index=f['index']+f'{C:08X} {C+len(child):08X} {len(child)} 0 return\n'.encode(),
        selector=policy.CALLEE_SELECTOR)
    return f


def run(f):
    proof=policy.RestoringCalleeDisjunctiveProof(f['rom'],f['mapping'],f['index'],f['objects'])
    result=proof.check_arguments(B,{match.ARM_REG_R2:-8},[(False,False,True)]*2,
        {},frozenset(),site=A+8,words={},frame_base=-8,root_frame=A,
        watched=(match.ARM_REG_R0+4,match.ARM_REG_R0+6))
    return proof,result


class RestoringCalleeTests(unittest.TestCase):
    def test_complete_call_restoration_and_nested_effects(self):
        proof,_=run(fixture())
        manifest=proof.restoring_leaf_manifest()
        self.assertEqual(manifest['schema'],policy.CALLEE_SCHEMA)
        record=manifest['observations'][0]['restoration']
        self.assertEqual(record['registers'],[4,6])
        self.assertEqual(record['calls'],[(B+8,C)])
        self.assertIn('Existing compatible returning ordinary ABI',record['conditional_ABI'])
        self.assertTrue(record['frame'])
        self.assertIn(B,proof.native_frames)
        self.assertIn(C,proof.native_frames)

    def test_call_before_overwriting_entry_alias_refuses(self):
        with self.assertRaisesRegex(ValueError,'unoverwritten opaque entry alias'):
            run(fixture(early=True))

    def test_nested_actual_pointer_escape_refuses(self):
        with self.assertRaisesRegex(ValueError,'pointer use or escape|stored or spilled'):
            run(fixture(child=halfwords(0x6002,0x4770)))

    def test_wrong_return_cannot_export_restoration(self):
        with self.assertRaises(ValueError):run(fixture(bad_return=True))

    def test_closed_report_selector_and_cli(self):
        marker=f'* verification: `{policy.CALLEE_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker),policy.CALLEE_SELECTOR)
        for text in (marker*2,marker+f'* verification: `{policy.RESTORING_SCHEMA}`\n'):
            with self.assertRaises(ValueError):owner.selected(text)
        with patch.object(sys,'argv',['match.py','0x08010000','--root',str(Path.cwd()),
                '--owner-runtime-profile',policy.CALLEE_SELECTOR]), \
                patch.object(match,'repo_root',return_value=str(Path.cwd())), \
                patch.object(owner,'issue',return_value=17)as issue:
            self.assertEqual(match.main(),17)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile,policy.CALLEE_SELECTOR)


if __name__=='__main__':unittest.main(verbosity=2)
