"""One reached ROM word beside an exact guarded buffer-callee table."""
import copy
import struct
import unittest
import test_guarded_callee_return_aliases as base
buffers, owner = base.buffers, base.owner
match = buffers.match

class GuardedOneWordBufferTests(unittest.TestCase):
    setUp = base.GuardedCalleeReturnAliasTests.setUp
    fixture = base.GuardedCalleeReturnAliasTests.fixture

    def one_word(self, *, load='ldr r2, object', guard='bls dispatch', store='str r0, [r4, #4]', object_value='0x02001234'):
        body = ('push {r4, lr}\nadds r4, r3, #0\n'+load+'\n'
          'cmp r0, #1\n'+guard+'\nb default\ndispatch: lsls r0, r0, #2\n'
          'ldr r1, pointer\nadds r0, r0, r1\nldr r0, [r0]\nmov pc, r0\n.balign 4, 0\n'
          'object: .word '+object_value+'\npointer: .word table\ntable: .word case0, case1\n'
          'case0: movs r0, #7\nstr r0, [r4]\nb done\n'
          'case1: movs r0, #8\n'+store+'\nb done\n'
          'default: movs r0, #0\ndone: adds r3, r4, #0\n'
          'pop {r4}\npop {r1}\nbx r1')
        return dict(self.fixture(callee=body, after='movs r0, #9\nstr r0, [r3]\nmovs r3, #0'), selector=buffers.GUARDED_ALIAS_SELECTOR)

    def test_reached_one_word_inventory_preserves_actual_return_alias(self):
        f=self.one_word();manifest,_=owner.verify(**f)
        rows=manifest['proof']['buffers']['guarded_switches']['observations']
        self.assertEqual(len(rows),1)
        self.assertEqual(rows[0]['structure']['switch']['interposed_words'],1)
        self.assertIn('interposed_ROM_word',rows[0]['structure'])
        self.assertNotIn('normal_return_scratch',manifest['proof']['buffers'])
        with self.assertRaises(ValueError):
            owner.verify(**dict(f, selector=buffers.GUARDED_SWITCH_SELECTOR))

    def test_guard_bounds_saved_words_and_unused_pool_remain_rejected(self):
        for change in (dict(guard='blo dispatch'),dict(store='str r0, [r4, #8]'),dict(load='movs r2, #0'),dict(object_value='case0')):
            with self.subTest(change=change), self.assertRaises(ValueError):owner.verify(**self.one_word(**change))

    def test_both_indexes_and_exact_observation_are_bound(self):
        f=self.one_word();manifest,_=owner.verify(**f)
        forged=copy.deepcopy(manifest);forged['proof']['buffers']['guarded_switches']['observations'][0]['structure']['interposed_ROM_word']['value']^=4
        with self.assertRaises(ValueError):owner.verify(**f,manifest=forged)
        with self.assertRaises(ValueError):owner.verify(**dict(f,index=f['index']+b'08010100 08010102 2 0 return\n'))

if __name__=='__main__':unittest.main(verbosity=2)
