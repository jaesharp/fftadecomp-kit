"""New whole-state scenarios; no previous test methods or binds are replayed."""
from dataclasses import replace
from pathlib import Path
import copy as pythoncopy
import hashlib
import itertools
import unittest

import scheduler_whole_state as whole
import scheduler_copy_state as word
import scheduler_callback_state as suffix
import scheduler_return_state as ret
import scheduler_allocator_state as state
import allocator_search_relation as search
import allocator_remove_relation as remove
import allocator_insert_relation as insert
import allocator_split_relation as split
import allocator_wrapper_relation as wrapper
# Only independent raw decoders and byte fixtures are reused on NEW states.
# Their old test methods and old bind/derive calls are never invoked.
import test_scheduler_entry_state as entry_oracle
import test_scheduler_callback_state as callback_oracle
import test_scheduler_return_state as return_oracle

BASE=0x02000000
POINT=BASE+2048
E=-512
S=1600
D=1280
C=0x08100000
H=0x08110000
INPUTS=Path(__file__).resolve().parents[1]/'inputs'
Z12=(INPUTS/'retained-zero12.json').read_bytes()
Z92=(INPUTS/'retained-zero92.json').read_bytes()
SEEDS=itertools.count(1)


def sha(b):return hashlib.sha256(b).hexdigest()


def layout(point=POINT):
    a=0x08060000
    s,r,m,i,c,w,t,cb=[a+n*0x1000 for n in [3,4,5,6,2,1,7,8]]
    sl=search.Layout(s,sha(search.SHAPE))
    ml=remove.Layout(r,m,sha(remove.REMOVE_HEAD+remove._bl(r+124,m)+remove.REMOVE_TAIL),sha(remove.MEDIAN))
    il=insert.Layout(i,sha(insert.HEAD+remove._bl(i+22,s)+insert.MIDDLE+remove._bl(i+138,m)+insert.TAIL),sl,ml)
    al=split.Layout(c,sha(split._encoded(c,il,t,0x08304000)),il,t,0x08304000)
    wl=wrapper.Layout(w,sha(wrapper.HEAD+remove._bl(w+34,c)+wrapper.TAIL),al)
    st=state.Layout(a,sha(state._encoded(a,wl,cb)),wl,cb)
    w=a-0x1000;outer=ret.Layout(w,sha(ret._wrapper(w,st,point)),point,st)
    b,h=callback_oracle.bodies(C,H)
    return whole.Layout(outer,suffix.Layout(C,H,b,h),b'\x18\x47')


def put(m,a,w):m.update({a+i:v for i,v in enumerate(w)})
def half(m,a,v):m[a]=v&255;m[a+1]=v>>8&255
def opaque(name):return tuple(('opaque-byte',name,i) for i in range(4))


def fixture(*,parent=None,chain=(),option=None,descriptor=D,point=POINT,e=E):
    seed=next(SEEDS);memory={}
    for at,value in [(0,32),(2,32),(4,1),(130,0),(134,43),(136,0),(138,0)]:half(memory,at,value)
    put(memory,S,word._pointer(0));put(memory,S+4,word._constant(0));half(memory,S+12,seed*13)
    put(memory,S+4 if parent is None else parent+16,word._pointer(chain[0]) if chain else word._constant(0))
    for n,node in enumerate(chain):put(memory,node+8,word._pointer(chain[n+1]) if n+1<len(chain) else word._constant(0))
    for i in range(28):memory[descriptor+i]=('opaque-byte','whole source '+str(seed),i)
    half(memory,descriptor+20,158);half(memory,descriptor+22,option if option is not None else seed*2+1)
    put(memory,descriptor+4,word._pointer(6000+seed*4))
    put(memory,point-BASE,word._pointer(S))
    regs={i:opaque('whole entry '+str(seed)+' R'+str(i)) for i in range(15)}
    regs.update({0:word._constant(C|1),1:word._constant(0xabc00040),2:word._pointer(descriptor),
        3:word._constant(0) if parent is None else word._pointer(parent),10:word._pointer(e-188),
        13:word._pointer(e),14:word._constant(0x08012345+seed*2)})
    return dict(layout=layout(point),arena_base=BASE,cells=memory,registers=regs,selector=whole.SELECTOR,
        zero12_receipt=Z12,zero92_receipt=Z92,observed_zero_target=0x03005e79)


def run(f=None,**kw):return whole.derive(**dict(fixture() if f is None else f,**kw))


def raw_copy_and_entry(f,report):
    """Independently decode copy and callback first12B after retained069 effects."""
    outer=f['layout'].outer;c=outer.callee.address;effect=f['layout'].effect
    regs,memory,_=entry_oracle.raw(dict(layout=outer,arena_base=BASE,cells=f['cells'],registers=f['registers']))
    assert regs==report['stages']['entry']['registers']
    pr=report['stages']['allocator-copy']['prefix'];memory.update({int(k):v for k,v in pr['changed_cells'].items()})
    low,high=report['unmodeled_retired_allocator_spans'][0]
    for at in range(low,high):memory[at]=('opaque-byte','unmodeled retired allocator',at-low)
    for name,value in pr['conditional_cutpoint_registers'].items():
        reg=13 if name=='SP' else int(name[1:])
        regs[reg]=word._pointer(value) if name=='SP' else word._constant(value) if type(value)is int else word._pointer(value[1])
    def addr(reg):
        v=regs[reg];assert v==word._pointer(v[0][1]);return v[0][1]
    b=state._encoded(c,outer.callee.allocator,outer.callee.callback_thunk)
    for pc in range(154,180,2):
        op=int.from_bytes(b[pc:pc+2],'little')
        if op&0xff00==0x4600:regs[(op&7)|((op>>4)&8)]=regs[(op>>3)&15]
        elif op&0xf800==0x2000:regs[(op>>8)&7]=word._constant(op&255)
        elif op&0xf000==0xc000:
            base=(op>>8)&7;selected=[i for i in range(8) if op&(1<<i)];start=addr(base)
            values=[tuple(memory[start+4*j+n] for n in range(4)) for j in range(len(selected))] if op&0x800 else [regs[i] for i in selected]
            for j,(r,value) in enumerate(zip(selected,values)):
                if op&0x800:regs[r]=value
                else:put(memory,start+4*j,value)
            regs[base]=word._pointer(start+4*len(selected))
        elif op&0xf800 in (0x6000,0x6800):
            r=op&7;at=addr((op>>3)&7)+4*((op>>6)&31)
            if op&0x800:regs[r]=tuple(memory[at+i] for i in range(4))
            else:put(memory,at,regs[r])
        elif op&0xf800==0x8000:
            at=addr((op>>3)&7)+2*((op>>6)&31);put(memory,at,regs[op&7][:2])
        elif op&0xfe00==0x1c00:
            assert (op>>6)&7==0;regs[op&7]=regs[(op>>3)&7]
        else:raise AssertionError(hex(op))
    regs[14]=word._constant((c+184)|1)
    assert regs==report['stages']['allocator-copy']['callback_registers']
    assert regs[3]==word._constant(effect.callback|1)
    for pc in range(0,12,2):
        op=int.from_bytes(effect.callback_data[pc:pc+2],'little')
        if op&0xfe00==0xb400:
            selected=[i for i in range(8) if op&(1<<i)]+([14] if op&256 else [])
            start=addr(13)-4*len(selected);values=[regs[i] for i in selected]
            for i,value in enumerate(values):put(memory,start+4*i,value)
            regs[13]=word._pointer(start)
        elif op&0xff80==0xb080:regs[13]=word._pointer(addr(13)-4*(op&127))
        elif op&0xfe00==0x1c00:
            assert (op>>6)&7==0;regs[op&7]=regs[(op>>3)&7]
        elif op&0xf800==0x8800:
            at=addr((op>>3)&7)+2*((op>>6)&31);regs[op&7]=(memory[at],memory[at+1],0,0)
        else:raise AssertionError(hex(op))
    return regs,memory


class WholeStateTests(unittest.TestCase):
    def test_whole_chain_materializes_saves_and_restores_actual_entry(self):
        f=fixture();r=run(f)
        self.assertTrue(r['reaches_outer_return_thunk'],r['boundary']);self.assertTrue(r['materialized_entry_saves'])
        self.assertFalse(r['fabricated_saved_words']);self.assertEqual(r['allocation_coordinate'],140)
        for reg in (4,5,6,7,8,9):self.assertEqual(r['registers'][reg],f['registers'][reg])
        self.assertEqual(r['registers'][13],f['registers'][13]);self.assertEqual(r['outer_return_word'],f['registers'][14])
        self.assertEqual(r['stages']['allocator-copy']['descriptor_phase_under_conditions'],0)
        self.assertFalse(r['actual_reaching_state_proved']);self.assertFalse(r['native_admission'])

    def test_preexisting_fake_saved_bytes_are_overwritten_by_real_entry_stores(self):
        f=fixture()
        for at in range(E-80,E):f['cells'][at]=0xaa
        r=run(f);self.assertTrue(r['reaches_outer_return_thunk'],r['boundary'])
        self.assertEqual(tuple(r['post_cells'][str(E-4+i)] for i in range(4)),f['registers'][14])

    def test_retired_allocator_bytes_are_not_resurrected(self):
        f=fixture()
        for at in range(E-156,E-80):f['cells'][at]=99
        r=run(f);self.assertTrue(r['reaches_outer_return_thunk'],r['boundary'])
        self.assertEqual(r['post_cells'][str(E-150)][0],'opaque-byte')
        self.assertEqual(r['retired_spans'],[(E-188,E)])
        self.assertEqual(r['known_retired_alias_registers']['10'],E-188)

    def test_parent_and_nonempty_tail_effects_feed_actual_callback(self):
        f=fixture(parent=2600,chain=(2800,2900));r=run(f)
        self.assertTrue(r['reaches_outer_return_thunk'],r['boundary'])
        self.assertEqual(tuple(r['post_cells'][str(2908+i)] for i in range(4)),word._pointer(140))
        self.assertEqual(tuple(r['post_cells'][str(152+i)] for i in range(4)),word._pointer(2600))

    def test_pre_entry_save_changes_fixed_pointer_observation(self):
        f=fixture(point=BASE+E-16);f['registers'][4]=word._pointer(S)
        r=run(f);self.assertFalse(r['reaches_outer_return_thunk'])
        self.assertEqual(r['stages']['entry']['observed_scheduler_word'],word._pointer(S))
        self.assertEqual(r['stage'],'return-consumer');self.assertIn('frame',r['boundary']['reason'])

    def test_post_read_parent_alias_can_change_later_global_pointer(self):
        f=fixture(point=BASE+E-24);r=run(f)
        self.assertEqual(r['stages']['entry']['observed_scheduler_word'],word._pointer(S))
        self.assertEqual(tuple(r['post_cells'][str(E-24+i)] for i in range(4)),(0,)*4)
        self.assertEqual(r['stage'],'return-consumer');self.assertFalse(r['reaches_outer_return_thunk'])

    def test_opaque_scheduler_stops_after_actual_saves(self):
        f=fixture();put(f['cells'],POINT-BASE,opaque('unknown scheduler'));r=run(f)
        self.assertEqual(r['stage'],'count-argument-adapter');self.assertEqual(r['boundary']['site'],f['layout'].outer.callee.address+20)
        self.assertTrue(r['materialized_entry_saves']);self.assertNotIn('allocator-copy',r['stages'])

    def test_numeric_descriptor_does_not_become_pointer(self):
        f=fixture();f['registers'][2]=word._constant(BASE+D);r=run(f)
        self.assertEqual(r['stage'],'count-argument-adapter');self.assertIn('descriptor',r['boundary']['reason'])

    def test_opaque_low_count_refuses_without_initializing_bits(self):
        f=fixture();f['registers'][1]=opaque('size unknown');r=run(f)
        self.assertEqual(r['stage'],'count-argument-adapter');self.assertIn('size',r['boundary']['reason'])

    def test_retained_count92_refusal_preserves_executed_allocator_effects(self):
        f=fixture();f['registers'][1]=word._constant(68);r=run(f)
        self.assertEqual(r['stage'],'allocator-copy');self.assertIn('count',r['boundary']['reason'])
        self.assertIsNone(r['registers']);self.assertNotIn('callback-entry',r['stages'])

    def test_zero_target_permission_is_not_inferred_from_literal_identity(self):
        f=fixture();f['observed_zero_target']=None;r=run(f)
        self.assertEqual(r['stage'],'allocator-copy');self.assertFalse(r['reaches_outer_return_thunk'])
        self.assertNotIn('callback-thunk',r['stages'])

    def test_descriptor_private_frame_refusal_is_not_bypassed_by_entry_saves(self):
        f=fixture(descriptor=E-40);r=run(f)
        self.assertEqual(r['stage'],'allocator-copy');self.assertFalse(r['reaches_outer_return_thunk'])

    def test_descriptor_alias_of_wrapper_saves_copies_actual_saved_origins(self):
        f=fixture(descriptor=E-16);r=run(f)
        self.assertTrue(r['reaches_outer_return_thunk'],r['boundary'])
        source=r['stages']['allocator-copy']['descriptor_bytes']
        self.assertEqual(source[4:8],f['registers'][5])
        self.assertEqual(r['outer_return_word'],f['registers'][14])

    def test_actual_reloaded_wrong_callback_stops_before_prefix(self):
        f=fixture();f['registers'][0]=word._constant(C+5);r=run(f)
        self.assertEqual(r['stage'],'callback-thunk');self.assertEqual(r['boundary']['site'],f['layout'].outer.callee.callback_thunk)
        self.assertNotIn('callback-entry',r['stages'])

    def test_opaque_callback_transports_until_actual_thunk_observation(self):
        f=fixture();f['registers'][0]=opaque('unknown callback');r=run(f)
        self.assertEqual(r['stage'],'callback-thunk');self.assertFalse(r['reaches_outer_return_thunk'])

    def test_zero_option_retains_nested_helper_actual_prologue_and_cutpoint(self):
        f=fixture(option=0);r=run(f)
        self.assertEqual(r['stage'],'callback-suffix');self.assertEqual(r['boundary']['site'],H+30)
        self.assertEqual(r['registers'][13],word._pointer(E-188));self.assertNotIn('return-consumer',r['stages'])

    def test_tag_mismatch_retains_actual_alternative_branch(self):
        f=fixture();half(f['cells'],D+20,23);r=run(f)
        self.assertEqual(r['stage'],'callback-suffix');self.assertEqual(r['boundary']['site'],C+76)

    def test_protected_entry_store_stops_before_allocator(self):
        f=fixture();f['protected_spans']=((E-16,E-12),);r=run(f)
        self.assertEqual(r['stage'],'entry');self.assertEqual(r['changed_cells'],{})

    def test_missing_fixed_pointer_word_does_not_get_initialized(self):
        f=fixture();del f['cells'][POINT-BASE+2];r=run(f)
        self.assertEqual(r['stage'],'entry');self.assertEqual(len(r['changed_cells']),20)

    def test_unknown_high_size_bits_remain_explicit071_limitation(self):
        f=fixture();f['registers'][1]=(64,0,('opaque-byte','size high',2),('opaque-byte','size high',3));r=run(f)
        self.assertEqual(r['stage'],'return-consumer');self.assertIn('discarded opaque high',r['boundary']['reason'])

    def test_input_state_immutable(self):
        f=fixture();before=pythoncopy.deepcopy(f);run(f);self.assertEqual(f,before)

    def test_three_new_raw_entry_copy_callback_return_chains(self):
        for parent,chain in [(None,()),(None,(3000,)),(2700,(3100,3200))]:
            f=fixture(parent=parent,chain=chain);r=run(f);self.assertTrue(r['reaches_outer_return_thunk'],r['boundary'])
            regs,memory=raw_copy_and_entry(f,r)
            self.assertEqual(regs,r['stages']['callback-entry']['registers'])
            got,memory,_,trace,cut=callback_oracle.raw(dict(layout=f['layout'].effect,registers=regs,cells=memory,entry_sp=E-80))
            self.assertIsNone(cut);self.assertEqual(trace,r['stages']['callback-suffix']['trace'])
            self.assertEqual(got,r['stages']['callback-suffix']['registers'])
            final,memory,_=return_oracle.raw_continuation(dict(layout=f['layout'].outer,post_registers=got,post_cells=memory,
                arena_base=BASE,entry_registers=f['registers']))
            self.assertEqual(final,r['registers']);self.assertEqual(memory,{int(k):v for k,v in r['post_cells'].items()})


class BindingTests(unittest.TestCase):
    def test_new_context_binding_reuses_layouts_and_exact_thunk(self):
        l=layout();self.assertEqual(whole.bind(l.outer,l.effect,l.thunk_data,selector=whole.SELECTOR),l)

    def test_changed_thunk_or_old_layout_cannot_join(self):
        l=layout()
        for bad in [replace(l,thunk_data=b'\x10\x47'),replace(l,outer=replace(l.outer,wrapper_sha256='0'*64))]:
            with self.assertRaises(ValueError):whole._validate(bad)
        with self.assertRaises(ValueError):whole.bind(l.outer,l.effect,l.thunk_data,selector='default')

    def test_cross_owner_callback_alias_refuses(self):
        l=layout();c=l.outer.callee.address;b,h=callback_oracle.bodies(c,H)
        with self.assertRaisesRegex(ValueError,'overlaps'):whole._validate(replace(l,effect=suffix.Layout(c,H,b,h)))


class BoundaryCompositionTests(unittest.TestCase):
    def test_fresh_allocator_zero_overwrites_aliased_descriptor_tag_before_copy(self):
        f=fixture(descriptor=140,option=37);r=run(f)
        self.assertEqual(r['stage'],'callback-suffix');self.assertEqual(r['boundary']['site'],C+76)
        self.assertEqual(r['stages']['allocator-copy']['descriptor_bytes'][20:22],(0,0))

    def test_retired_namespace_does_not_equate_unrelated_incoming_opaque_bytes(self):
        f=fixture(option=39);f['registers'][11]=opaque('unmodeled retired allocator');r=run(f)
        self.assertTrue(r['reaches_outer_return_thunk'],r['boundary'])
        self.assertEqual(r['post_cells'][str(E-150)][1],'unmodeled retired allocator:1')
        self.assertEqual(r['registers'][11],f['registers'][11])

    def test_byte_budget_exhaustion_stops_before_callback_entry_kernel(self):
        f=fixture(option=41)
        at=100000
        while len(f['cells'])<3950:f['cells'][at]=0;at+=1
        r=run(f)
        self.assertEqual(r['stage'],'callback-entry');self.assertIn('4096',r['boundary']['reason'])
        self.assertNotIn('callback-entry',r['stages']);self.assertTrue(r['stages']['allocator-copy']['reaches_callback_thunk'])

    def test_nested_coordinate_limit_stops_before_callback_suffix_kernel(self):
        e=-(2**31)+176;f=fixture(e=e,option=43);f['arena_base']=0x80000000
        f['registers'][10]=word._pointer(e)
        l=f['layout'].outer;put(f['cells'],l.scheduler_point-f['arena_base'],word._pointer(S))
        r=run(f)
        self.assertEqual(r['stage'],'callback-suffix');self.assertIn('coordinate bounds',r['boundary']['reason'])
        self.assertNotIn('callback-suffix',r['stages']);self.assertEqual(r['registers'][13],word._pointer(e-116))


class FrameLifecycleTests(unittest.TestCase):
    def test_callback_branch_cutpoint_keeps_current_callback_frame_live(self):
        f=fixture(option=47);half(f['cells'],D+20,99);r=run(f)
        self.assertEqual(r['boundary']['site'],C+76)
        self.assertEqual(r['retired_spans'],[(E-156,E-116)])
        self.assertEqual(r['frame_reactivations'][0]['span'],[E-116,E-80])

    def test_nested_cutpoint_does_not_mark_reused_live_helper_frame_retired(self):
        f=fixture(option=512);f['registers'][10]=word._pointer(E-150);r=run(f)
        self.assertEqual(r['boundary']['site'],H+30);self.assertEqual(r['retired_spans'],[])
        self.assertNotIn('10',r['known_retired_alias_registers'])
        self.assertEqual([e['span'] for e in r['frame_reactivations']],
                         [[E-116,E-80],[E-136,E-116],[E-188,E-136]])

    def test_fresh_success_retires_reactivated_frames_after_both_returns(self):
        f=fixture(option=49,parent=3400);r=run(f)
        self.assertTrue(r['reaches_outer_return_thunk'],r['boundary'])
        self.assertEqual(r['retired_spans'],[(E-188,E)])
        self.assertTrue(all(not e['old_initialization_granted'] for e in r['frame_reactivations']))
        self.assertEqual(r['registers'][13],f['registers'][13])


if __name__=='__main__':unittest.main()
