"""Closed synthetic loop controls, including clobbered carried successor cases."""
from pathlib import Path
import hashlib
import struct
import sys
import unittest

sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import narrowed_counter_loop_prerequisite as loops

A=0x08002000


def encode(items,changes=None):
    labels={name:A+2*i for i,(name,_) in enumerate(items)}
    words=[]
    for name,word in items:
        word=(changes or {}).get(name,word)
        if isinstance(word,tuple):
            kind,target=word;delta=(labels[target]-labels[name]-4)//2
            word=(0xe000|(delta&2047)) if kind=='b' else ({'ls':0xd900,'hi':0xd800}[kind]|(delta&255))
        words.append(word)
    data=b''.join(struct.pack('<H',word) for word in words)
    return loops.Graph(data,A,set(labels.values())),labels,data


def inner_fixture(changes=None):
    graph,labels,data=encode([('init',0x2200),('header',0x2007),('body',0x2100),('tail',0x1c50),
        ('left',0x0400),('right',0x0c02),('compare',0x2a02),('back',('ls','header')),('exit',0x4770)],changes)
    spec={key:labels[key] for key in ('header','init','tail')};spec.update(counter=2,ceiling=2)
    return graph,spec,labels,data


def nested_fixture(changes=None,bound=8):
    graph,labels,data=encode([('guard',0x4544),('guard_branch',('hi','exit')),
        ('header',0x1c60),('capture',0x4684),('row_index',0x2407),('init',0x2200),
        ('inner_header',0x2007),('inner_tail',0x1c50),('inner_left',0x0400),('inner_right',0x0c02),
        ('inner_compare',0x2a02),('inner_back',('ls','inner_header')),('after_inner',0x2300),
        ('tail',0x4661),('left',0x0408),('right',0x0c04),('compare',0x4544),('back',('ls','header')),
        ('exit',0x4770)],changes)
    inner={'header':labels['inner_header'],'init':labels['init'],'tail':labels['inner_tail'],'counter':2,'ceiling':2}
    outer={'header':labels['header'],'counter':4,'limit_register':bound,'carry':12,
           'capture':labels['header'],'tail':labels['tail'],'guard':labels['guard']}
    ranges=[[0,0xffffffff] for _ in range(13)];ranges[4]=[0,3];ranges[bound]=[0,3]
    return graph,inner,outer,{labels['header']:ranges},labels,data


class NarrowedLoopTests(unittest.TestCase):
    def test_inner_exact_three_iterations(self):
        graph,spec,_,_=inner_fixture();proof=loops.inner_loop(graph,spec)
        self.assertEqual(proof['iterations'],3)
        self.assertTrue(proof['increment_wrap_impossible'])

    def test_outer_allows_index_reuse_after_capture(self):
        graph,inner,outer,numeric,_,_=nested_fixture()
        inside=loops.inner_loop(graph,inner);proof=loops.outer_loop(graph,outer,numeric,[inside])
        self.assertEqual(proof['maximum_iterations'],4)
        self.assertEqual(proof['summarized_inner_headers'],[inner['header']])
        self.assertTrue(proof['carried_successor_and_limit_preserved'])

    def test_nonzero_inner_initializer_refuses(self):
        graph,spec,_,_=inner_fixture({'init':0x2201})
        with self.assertRaisesRegex(ValueError,'zero initialization'):loops.inner_loop(graph,spec)

    def test_inner_counter_body_write_refuses(self):
        graph,spec,_,_=inner_fixture({'header':0x2201})
        with self.assertRaisesRegex(ValueError,'induction counter'):loops.inner_loop(graph,spec)

    def test_missing_unsigned_narrowing_refuses(self):
        graph,spec,_,_=inner_fixture({'right':0x1402})
        with self.assertRaisesRegex(ValueError,'unsigned right16'):loops.inner_loop(graph,spec)

    def test_wrong_step_refuses(self):
        graph,spec,_,_=inner_fixture({'tail':0x1c90})
        with self.assertRaisesRegex(ValueError,r'counter\+1'):loops.inner_loop(graph,spec)

    def test_wrong_inclusive_bound_refuses(self):
        graph,spec,_,_=inner_fixture({'compare':0x2a03})
        with self.assertRaisesRegex(ValueError,'immediate ceiling'):loops.inner_loop(graph,spec)

    def test_unconditional_backedge_refuses(self):
        graph,spec,_,_=inner_fixture({'back':('b','header')})
        with self.assertRaisesRegex(ValueError,'unsigned inclusive'):loops.inner_loop(graph,spec)

    def test_unsummarized_body_cycle_refuses(self):
        graph,spec,_,_=inner_fixture({'body':('b','body')})
        with self.assertRaisesRegex(ValueError,'cycle'):loops.inner_loop(graph,spec)

    def test_body_return_before_update_refuses(self):
        graph,spec,_,_=inner_fixture({'header':0x4770})
        with self.assertRaisesRegex(ValueError,'before its update'):loops.inner_loop(graph,spec)

    def test_carried_successor_clobber_refuses(self):
        graph,inner,outer,numeric,_,_=nested_fixture({'after_inner':0x4684})
        proof=loops.inner_loop(graph,inner)
        with self.assertRaisesRegex(ValueError,'clobbers carried successor'):loops.outer_loop(graph,outer,numeric,[proof])

    def test_invariant_limit_clobber_refuses(self):
        graph,inner,outer,numeric,_,_=nested_fixture({'after_inner':0x4680})
        proof=loops.inner_loop(graph,inner)
        with self.assertRaisesRegex(ValueError,'invariant limit'):loops.outer_loop(graph,outer,numeric,[proof])

    def test_capture_cannot_repurpose_limit_as_temporary(self):
        changes={'guard':0x429c,'header':0x1c63,'capture':0x469c,'after_inner':0x2000,'compare':0x429c}
        graph,inner,outer,numeric,_,_=nested_fixture(changes,bound=3)
        proof=loops.inner_loop(graph,inner)
        with self.assertRaisesRegex(ValueError,'capture overwrites invariant limit'):loops.outer_loop(graph,outer,numeric,[proof])

    def test_outer_refuses_missing_inner_summary(self):
        graph,_,outer,numeric,_,_=nested_fixture()
        with self.assertRaisesRegex(ValueError,'unsummarized cycle'):loops.outer_loop(graph,outer,numeric,[])

    def test_outer_requires_range_excluding_wrap(self):
        graph,inner,outer,numeric,labels,_=nested_fixture()
        numeric[labels['header']][4]=[0,65535]
        proof=loops.inner_loop(graph,inner)
        with self.assertRaisesRegex(ValueError,'prevent16bit wrap'):loops.outer_loop(graph,outer,numeric,[proof])

    def test_outer_requires_guard_polarity(self):
        graph,inner,outer,numeric,_,_=nested_fixture({'guard_branch':0xd000})
        proof=loops.inner_loop(graph,inner)
        with self.assertRaisesRegex(ValueError,'unsigned <='):loops.outer_loop(graph,outer,numeric,[proof])

    def test_tail_cannot_read_a_different_carry(self):
        graph,inner,outer,numeric,_,_=nested_fixture({'tail':0x4659})
        proof=loops.inner_loop(graph,inner)
        with self.assertRaisesRegex(ValueError,'carried successor MOV'):loops.outer_loop(graph,outer,numeric,[proof])

    def test_role_overlap_refuses(self):
        graph,inner,outer,numeric,_,_=nested_fixture();outer['carry']=outer['limit_register']
        proof=loops.inner_loop(graph,inner)
        with self.assertRaisesRegex(ValueError,'roles overlap'):loops.outer_loop(graph,outer,numeric,[proof])

    def test_all_palette_rank_values_decrease_without_wrap(self):
        for limit in range(512):
            for index in range(limit+1):
                successor=(index+1)&65535
                self.assertEqual(successor,index+1)
                rank=limit-index+1
                self.assertGreater(rank,0)
                self.assertEqual(limit-successor+1,rank-1)
                self.assertEqual(successor<=limit,rank>1)

    def test_full_certificate_composition_keeps_conditions(self):
        _,inner,outer,numeric,labels,data=nested_fixture()
        common={'address':A,'end':A+len(data),'body_sha256':hashlib.sha256(data).hexdigest(),
                'ROM_sha256':'0'*64,'partition':{'synthetic_complete_owner':True}}
        frame=dict(common,continuation={'continuation_sites':list(labels.values())},
                   required_unproved_conditions=['Independent synthetic frame premise.'])
        ranges=dict(common,fixed_point_states=[{'site':site,'ranges':values} for site,values in numeric.items()])
        authority={'independently_established_frozen_certificates':True,
                   'frame_sha256':loops.digest(frame),'numeric_sha256':loops.digest(ranges)}
        proof=loops.verify(data,A,frame,ranges,[inner],[outer],selector=loops.SELECTOR,reuse_authority=authority)
        self.assertFalse(proof['unconditional_termination'])
        self.assertFalse(proof['source_or_ELF_admission'])
        self.assertIn('Independent synthetic frame premise.',proof['required_unproved_conditions'])

    def test_missing_certificate_authority_refuses(self):
        with self.assertRaisesRegex(ValueError,'independent retained proof authority'):
            loops.verify(b'',A,{}, {},[],[],selector=loops.SELECTOR,reuse_authority={})

    def test_unjustified_owner_digest_refuses(self):
        with self.assertRaisesRegex(ValueError,'differs from exact owner'):
            loops.verify(b'',A,{}, {},[],[],selector=loops.SELECTOR,
                         reuse_authority={'independently_established_frozen_certificates':True})

    def test_update_middle_cannot_have_another_entry(self):
        graph,spec,labels,data=inner_fixture()
        extra=A+len(data);delta=(labels['right']-extra-4)//2
        data+=struct.pack('<H',0xe000|(delta&2047))
        graph=loops.Graph(data,A,set(labels.values())|{extra})
        with self.assertRaisesRegex(ValueError,'update sequence can be bypassed'):
            loops.inner_loop(graph,spec)

    def test_outer_index_changed_before_capture_refuses(self):
        graph,inner,outer,numeric,labels,_=nested_fixture()
        # Move the requested capture after the real R4 overwrite. The earlier
        # prefix must be rejected before accepting any later pattern.
        outer['capture']=labels['init']
        proof=loops.inner_loop(graph,inner)
        with self.assertRaisesRegex(ValueError,'overwrites its index before'):
            loops.outer_loop(graph,outer,numeric,[proof])


if __name__=='__main__':unittest.main()
