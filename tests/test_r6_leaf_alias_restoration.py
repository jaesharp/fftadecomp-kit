"""Opaque caller aliases may be privately saved/restored, never observed."""
import copy
import hashlib
import unittest

from test_r6_target_external_alignment import aligned_fixture, A, W, C, bl
import match
import owner_admission_profile as owner
import static_callback_r6_frame_profile as policy
import test_static_callback_r6_target as target

L = target.L
LEAF = bytes.fromhex('30b50024002530bc01bc0047')


def fixture(leaf=LEAF):
    worker = bytes.fromhex('70b50e1c151c') + bl(W+6,L)
    worker += bytes.fromhex('0022291c') + bl(W+14,target.THUNK) + bytes.fromhex('70bc01bc0047')
    values = aligned_fixture(worker=worker, leaf=leaf)
    values['selector'] = policy.LEAF_ALIAS_SELECTOR
    return values


def proof(values):
    return policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
                                      values['objects'],policy=policy.LEAF_ALIAS_SELECTOR)


class LeafAliasTests(unittest.TestCase):
    def test_fresh_complete_effects_and_native_leaf_frame_preserve_hidden_alias(self):
        values = fixture()
        manifest, instructions = owner.verify(**values)
        self.assertTrue(instructions)
        self.assertEqual(manifest['profile'],policy.LEAF_ALIAS_SCHEMA)
        evidence = manifest['proof']['buffers']['r6_restoration']
        leaves = [row['leaf_alias_restoration'] for row in evidence['observations']
                  if 'leaf_alias_restoration' in row]
        self.assertTrue(leaves)
        self.assertTrue(any(row['address']==L and row['registers']==[5] for row in leaves))
        self.assertTrue(all(row['nested_calls'] is False for row in leaves))
        self.assertTrue(evidence['callback_observations'])
        self.assertIn('terminal_alignment', evidence['policy'])
        self.assertIn('leaf_alias_restoration', evidence['policy'])
        for selector in (policy.TARGET_SELECTOR,policy.ALIGNED_TARGET_SELECTOR):
            with self.subTest(selector=selector),self.assertRaisesRegex(ValueError,'live alias register'):
                owner.verify(**dict(values,selector=selector))

    def test_initial_alias_read_copy_and_stack_save_reload_escape_are_rejected(self):
        for leaf in (
                '30b5281c0024002530bc01bc0047',
                '30b528680024002530bc01bc0047',
                '30b500980024002530bc01bc0047',
                '30b568460024002530bc01bc0047',
                '30b50024002510bc01bc201c02bc0847'):
            values = fixture(bytes.fromhex(leaf))
            with self.subTest(leaf=leaf),self.assertRaises(ValueError):
                proof(values)._restore_leaf_aliases(L,(match.ARM_REG_R0+5,),{})

    def test_missing_restoration_and_explicit_pointer_argument_are_rejected(self):
        values = fixture(bytes.fromhex('002500207047'))
        with self.assertRaises(ValueError):
            proof(values)._restore_leaf_aliases(L,(match.ARM_REG_R0+5,),{})
        values = fixture()
        with self.assertRaisesRegex(ValueError,'explicit pointer argument'):
            proof(values)._restore_leaf_aliases(L,(match.ARM_REG_R0+5,),{match.ARM_REG_R0+5:-4})

    def test_nested_calls_and_target_or_guard_registers_receive_no_relaxation(self):
        leaf = bytes.fromhex('30b5')+bl(L+2,C)+bytes.fromhex('002530bc01bc0047')
        values = fixture(leaf)
        watches = (match.ARM_REG_R0+5,)
        self.assertEqual(proof(values)._restore_leaf_aliases(L,watches,{}),(watches,None))
        for register,body in ((6,'40b5002640bc01bc0047'),(11,'002083467047')):
            values = fixture(bytes.fromhex(body)); watches=(match.ARM_REG_R0+register,)
            self.assertEqual(proof(values)._restore_leaf_aliases(L,watches,{}),(watches,None))

    def test_leaf_restoration_receipt_tampering_is_not_a_fresh_manifest(self):
        values=fixture();manifest,_=owner.verify(**values)
        changed=copy.deepcopy(manifest)
        rows=changed['proof']['buffers']['r6_restoration']['observations']
        row=next(row for row in rows if 'leaf_alias_restoration' in row)
        row['leaf_alias_restoration']['body_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            owner.verify(**values,manifest=changed)
        result=(values['data'],manifest,'synthetic source',values['mapping'],values['index'],
                values['objects'],values['rom'],0,b'synthetic original identity')
        report=owner.render(A,result)
        self.assertEqual(owner.selector_for_report(report),policy.LEAF_ALIAS_SELECTOR)
        with self.assertRaises(ValueError):
            owner.selected(report+f'* verification: `{policy.ALIGNED_TARGET_SCHEMA}`\n')

    def test_changed_leaf_effects_are_still_checked_after_restoration(self):
        # The new gate proves register origins, never a buffer output bound.
        bad = bytes.fromhex('30b50024002501209060002030bc01bc0047')
        with self.assertRaisesRegex(ValueError,'outside allocated'):
            owner.verify(**fixture(bad))


if __name__=='__main__':unittest.main(verbosity=2)
