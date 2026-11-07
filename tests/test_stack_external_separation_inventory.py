"""Aligned integer separation boundaries and exact interval complements."""
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import stack_external_separation_inventory as inventory


class StackSeparationTests(unittest.TestCase):
    def derive(self, frame=(-8,4), spans=(('external',100,120),), **options):
        return inventory.derive(frame,spans,selector=options.pop('selector',inventory.SELECTOR),**options)

    def permitted(self, proof, sp):
        return sp % proof['alignment'] == 0 and any(
            a <= sp//proof['alignment'] <= b
            for a,b in proof['admissible_aligned_entry_SP_quotients_inclusive'])

    def test_touching_exclusive_endpoints_are_allowed_but_overlap_refuses(self):
        proof=self.derive()
        self.assertTrue(self.permitted(proof,96))
        self.assertFalse(self.permitted(proof,100))
        self.assertFalse(self.permitted(proof,124))
        self.assertTrue(self.permitted(proof,128))
        self.assertEqual(proof['forbidden_aligned_entry_SP_quotients_inclusive'],[[25,31]])

    def test_small_domain_exhaustive_comparison_with_direct_halfopen_intersection(self):
        for frame in ((-1,0),(-8,4),(-12,8),(0,16)):
            for alignment in (1,2,4,8,16):
                spans=(('a',20,23),('b',28,43),('c',65,70))
                proof=self.derive(frame,spans,alignment=alignment)
                for sp in range(100):
                    expected=(sp % alignment == 0 and sp+frame[0] >= 0 and
                              sp+frame[1] <= inventory.SPACE and all(
                                  sp+frame[1] <= start or end <= sp+frame[0]
                                  for _,start,end in spans))
                    self.assertEqual(self.permitted(proof,sp),expected,(frame,alignment,sp))

    def test_nonwrapping_boundaries_and_complete_exclusion(self):
        proof=self.derive()
        self.assertFalse(self.permitted(proof,4))
        self.assertTrue(self.permitted(proof,8))
        self.assertTrue(self.permitted(proof,inventory.SPACE-4))
        self.assertFalse(self.permitted(proof,inventory.SPACE))
        excluded=self.derive(spans=(('all',0,inventory.SPACE),))
        self.assertEqual(excluded['admissible_aligned_entry_SP_quotients_inclusive'],[])
        self.assertEqual(excluded['admissible_entry_SP_count'],0)

    def test_overlapping_adjacent_and_duplicate_span_geometry_merge_once(self):
        proof=self.derive(spans=(('a',100,110),('b',108,120),('c',100,120)))
        self.assertEqual(proof['forbidden_aligned_entry_SP_quotients_inclusive'],[[25,31]])
        quotient=proof['nonwrapping_aligned_entry_SP_quotients_inclusive']
        self.assertEqual(proof['admissible_entry_SP_count'],quotient[1]-quotient[0]+1-7)

    def test_alignment_can_skip_a_forbidden_integer_interval(self):
        proof=self.derive((-1,0),(('one-byte',101,102),),alignment=16)
        self.assertEqual(proof['derivations'][0]['forbidden_entry_SP_inclusive'],[102,102])
        self.assertEqual(proof['forbidden_aligned_entry_SP_quotients_inclusive'],[])

    def test_invalid_inputs_never_become_address_or_frame_authority(self):
        for frame in ((True,4),(-8,False),(1,4),(-4,-1),(0,0),(-inventory.SPACE,4)):
            with self.subTest(frame=frame),self.assertRaisesRegex(ValueError,'frame'):
                self.derive(frame)
        for alignment in (True,0,3,32):
            with self.subTest(alignment=alignment),self.assertRaisesRegex(ValueError,'alignment'):
                self.derive(alignment=alignment)
        for spans in ((),(('bad',1,1),),(('bad',-1,2),),(('bad',0,True),),
                      (('bad',0,inventory.SPACE+1),),(('same',1,2),('same',3,4))):
            with self.subTest(spans=spans),self.assertRaises(ValueError):
                self.derive(spans=spans)
        with self.assertRaisesRegex(ValueError,'explicit inventory selector'):
            self.derive(selector='default')

    def test_closed_manifest_and_conditional_claims_survive_json_roundtrip(self):
        proof=self.derive()
        self.assertEqual(self.derive(manifest=json.loads(json.dumps(proof))),proof)
        for field in ('actual_entry_SP_established','physical_memory_permission',
                      'object_extent_or_lifetime_established','initialized_contents_established',
                      'asynchronous_noninterference_established','source_or_ELF_admission'):
            self.assertIs(proof[field],False)
        changed=dict(proof,actual_entry_SP_established=True)
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            self.derive(manifest=changed)


if __name__ == '__main__':
    unittest.main()
