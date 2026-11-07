"""New079 state cases and an independent concrete Thumb mnemonic oracle."""
from dataclasses import replace
import copy
import hashlib
import os
from pathlib import Path
import unittest
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

import scheduler_zero40_state as zero
import scheduler_small_entry_state as small
import test_scheduler_small_entry_state as prior_fixtures

words = zero.words
BASE,E,NODE,SCHED,SUBJECT = 0x02000000,2048,256,5000,6000
IMAGE_PATH = Path(os.environ.get('FFTA_ZERO40_IMAGE', str(Path(__file__).resolve().parents[1]/'inputs/source-image.bin')))
if not IMAGE_PATH.is_file():
    raise unittest.SkipTest('Set FFTA_ZERO40_IMAGE to the external retained176B image fixture')
IMAGE = IMAGE_PATH.read_bytes()


def put(m,at,w):m.update({at+i:v for i,v in enumerate(w)})
def integer(n):return words._constant(n)
def pointer(n):return words._pointer(n)
def opaque(n):return tuple(('opaque-byte',n,i) for i in range(4))
def half(m,at,n):put(m,at,tuple(n.to_bytes(2,'little')))
def byte(v,base=BASE):
    if type(v) is int:return v
    if v[0]=='base-plus-byte':return ((base+v[1])>>(8*v[2]))&255
    return hashlib.sha256((v[1]+':'+str(v[2])).encode()).digest()[0]
def number(w,base=BASE):return int.from_bytes(bytes(byte(v,base) for v in w),'little')
def memory(r):return {int(k):v for k,v in r['post_cells'].items()}


def fixture(*,node=NODE,parent=None,list_head=None):
    p=prior_fixtures.layout();l=zero.Layout(p,IMAGE,zero.IMAGE_BASE)
    r={i:opaque('079 R'+str(i)) for i in range(15)}
    r.update({0:pointer(node),1:integer(40),2:integer(zero.IMAGE_BASE|1),4:integer(40),
        5:pointer(SCHED),6:integer(0) if parent is None else pointer(parent),7:pointer(node),
        8:integer(p.callback|1),9:pointer(E+4),13:pointer(E-56),14:integer((p.scheduler.address+52)|1)})
    m={}
    for i in range(28):m[E-56+i]=('opaque-byte','078 uninitialized local',i)
    for off,reg in [(-28,8),(-24,9),(-20,4),(-16,5),(-12,6),(-8,7)]:put(m,E+off,opaque('caller saved R'+str(reg)))
    put(m,E-4,integer((p.coordinate.helper.helper+270)|1))
    for i in range(28):m[E+4+i]=('opaque-byte','uninterpreted descriptor tail',i)
    put(m,E+8,pointer(SUBJECT));half(m,E+4,257)
    half(m,SCHED+12,42)
    head=0 if list_head is None else list_head
    put(m,SCHED+4,integer(0) if head==0 else pointer(head))
    if parent is not None:put(m,parent+16,integer(0) if head==0 else pointer(head))
    if head:put(m,head+8,integer(0))
    half(m,SUBJECT,0x1234);m[SUBJECT+2]=0x56;put(m,SUBJECT+4,opaque('subject payload pointer or opaque'))
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,scheduler_entry_sp=E,selector=zero.SELECTOR)


def raw(f, stop_before=None):
    """Independent numeric decoder/oracle, no production execution helpers.

    Complete immutable body validation is shared; effect decode, concrete memory,
    ALU flags, branching, transfer order and returns are separately implemented.
    """
    l,base=f['layout'],f['arena_base'];p=l.prior;s=p.scheduler.address
    owners=small._validate(p)
    thunk=p.scheduler.allocator.allocator.thunk;cb=p.callback
    bodies={s:owners[s],cb:owners[cb],thunk:b'\x10\x47',p.scheduler.callback_thunk:b'\x18\x47',l.image_base:l.image[:50]}
    regs={i:number(w,base) for i,w in f['registers'].items()}
    m={base+k:byte(v,base) for k,v in f['cells'].items()}
    pc,trace,events,comparison=thunk,[],[],None
    decoder=Cs(CS_ARCH_ARM,CS_MODE_THUMB);decoder.detail=True
    names=dict(sp=13,lr=14,pc=15,sb=9,sl=10,fp=11,ip=12)
    def reg(op):
        n=decoder.reg_name(op.reg);return names.get(n,int(n[1:]) if n.startswith('r') else -1)
    def num(op):return op.imm if op.type==2 else regs[reg(op)]
    def load(at,width):
        v=tuple(m[at+i] for i in range(width));events.append((pc,'read'+str(width*8),at-base,v))
        return int.from_bytes(bytes(v),'little')
    def store(at,width,value):
        v=tuple(((value&0xffffffff).to_bytes(4,'little'))[:width]);m.update({at+i:b for i,b in enumerate(v)})
        events.append((pc,'write'+str(width*8),at-base,v))
    for _ in range(1024):
        if pc==stop_before:
            trace.append(pc);return regs,m,trace,events,pc
        owner=next((a for a,b in bodies.items() if a<=pc<a+len(b)),None)
        if owner is None:return regs,m,trace,events,pc
        ins=next(decoder.disasm(bodies[owner][pc-owner:],pc,1));ops,name,nxt=ins.operands,ins.mnemonic,pc+ins.size
        trace.append(pc)
        if name=='push':
            selected=[reg(o) for o in ops];at=regs[13]-4*len(selected);values=[regs[n] for n in selected]
            for i,v in enumerate(values):store(at+4*i,4,v)
            regs[13]=at
        elif name=='pop':
            at=regs[13];values=[load(at+4*i,4) for i in range(len(ops))]
            for op,v in zip(ops,values):regs[reg(op)]=v
            regs[13]=at+4*len(ops)
        elif name in ('mov','movs'):regs[reg(ops[0])]=num(ops[1])
        elif name in ('add','adds','sub','subs'):
            d=reg(ops[0]);a=num(ops[1]) if len(ops)==3 else regs[d];b=num(ops[-1])
            regs[d]=(a-b if name.startswith('sub') else a+b)&0xffffffff
        elif name=='lsls':regs[reg(ops[0])]=(num(ops[1])<<num(ops[2]))&0xffffffff
        elif name=='ands':regs[reg(ops[0])]&=num(ops[1])
        elif name=='cmp':comparison=(num(ops[0]),num(ops[1]))
        elif name in ('beq','bne','bhi','bls','bgt','ble'):
            a,b=comparison;aa=a-2**32 if a&0x80000000 else a;bb=b-2**32 if b&0x80000000 else b
            if dict(beq=a==b,bne=a!=b,bhi=a>b,bls=a<=b,bgt=aa>bb,ble=aa<=bb)[name]:nxt=ops[0].imm
        elif name=='b':nxt=ops[0].imm
        elif name=='bl':regs[14]=nxt|1;nxt=ops[0].imm
        elif name=='bx':nxt=regs[reg(ops[0])]&~1
        elif name in ('ldm','stm'):
            bn=reg(ops[0]);at=regs[bn];selected=[reg(o) for o in ops[1:]]
            if name=='ldm':
                values=[load(at+4*i,4) for i in range(len(selected))]
                for n,v in zip(selected,values):regs[n]=v
            else:
                values=[regs[n] for n in selected]
                for i,v in enumerate(values):store(at+4*i,4,v)
            regs[bn]=at+4*len(selected)
        elif name in ('ldr','ldrb','ldrh','str','strb','strh'):
            bn=decoder.reg_name(ops[1].mem.base);width=1 if name.endswith('b') else 2 if name.endswith('h') else 4
            at=regs[names.get(bn,int(bn[1:]) if bn.startswith('r') else -1)]+ops[1].mem.disp
            if name.startswith('ldr'):regs[reg(ops[0])]=load(at,width)
            else:store(at,width,regs[reg(ops[0])])
        else:raise AssertionError((hex(pc),name,ins.op_str))
        pc=nxt
    raise AssertionError('independent raw budget exceeded')


class Zero40Tests(unittest.TestCase):
    def assert_raw(self,f,r,stop_before=None):
        regs,m,trace,events,pc=raw(f,stop_before)
        self.assertEqual(r['trace'],trace)
        self.assertEqual(r['final_PC'],pc)
        self.assertEqual({i:number(v,f['arena_base']) for i,v in r['registers'].items()},regs)
        self.assertEqual({f['arena_base']+k:byte(v,f['arena_base']) for k,v in memory(r).items()},m)
        got=[(v['site'],v['operation'],v['coordinate'],tuple(byte(b,f['arena_base']) for b in v['bytes'])) for v in r['memory_events'] if 'coordinate' in v]
        self.assertEqual(got,events)

    def test_new_complete_phase0_returns_match_raw_machine(self):
        f=fixture();r=zero.derive(**f)
        self.assertIsNone(r['boundary']);self.assertEqual(r['conditional_returns'],dict(zero40=True,callback=True,scheduler=True))
        self.assertEqual(r['callback_observed_phase'],0);self.assertEqual(r['registers'][0],pointer(NODE))
        self.assertEqual(tuple(memory(r)[NODE+20+i] for i in range(2)),(0,1))
        self.assertEqual(tuple(memory(r)[NODE+24+i] for i in range(3)),(0x34,0x12,0x56))
        self.assertEqual(tuple(memory(r)[NODE+28+i] for i in range(4)),opaque('subject payload pointer or opaque'))
        self.assert_raw(f,r)

    def test_new_parent_empty_list_real_writes_match_raw(self):
        f=fixture(parent=7000);r=zero.derive(**f);self.assertIsNone(r['boundary'])
        self.assertEqual(tuple(memory(r)[7000+16+i] for i in range(4)),pointer(NODE));self.assert_raw(f,r)

    def test_new_parent_chain_walk_and_tail_link_match_raw(self):
        f=fixture(parent=7000,list_head=7200);put(f['cells'],7208,pointer(7300));put(f['cells'],7308,integer(0))
        r=zero.derive(**f);self.assertIsNone(r['boundary']);self.assert_raw(f,r)
        self.assertEqual(tuple(memory(r)[NODE+4+i] for i in range(4)),pointer(7300))

    def test_new_scheduler_chain_tail_link_match_raw(self):
        f=fixture(list_head=7200);r=zero.derive(**f);self.assertIsNone(r['boundary']);self.assert_raw(f,r)

    def test_new_phase0_payload_source_alias_observes_store_order(self):
        # First callback byte write changes the subsequent word load at node+24.
        f=fixture();put(f['cells'],E+8,pointer(NODE+20));r=zero.derive(**f)
        self.assertIsNone(r['boundary']);self.assert_raw(f,r)
        self.assertEqual(tuple(memory(r)[NODE+28+i] for i in range(4)),(0,0,42,0))

    def test_new_zero_unaligned_one_byte_path_is_exact_then_scheduler_refuses(self):
        f=fixture(node=NODE+1);r=zero.derive(**f)
        self.assertTrue(r['conditional_returns']['zero40']);self.assertIn('unaligned',r['boundary']['reason'])
        writes=[v for v in r['memory_events'] if v['operation']=='write8']
        self.assertEqual([v['coordinate'] for v in writes],list(range(NODE+1,NODE+41)))
        self.assertEqual(r['registers'][2],pointer(NODE+41))

    def test_new_zero_unaligned_two_byte_path_retains_exact_registers(self):
        f=fixture(node=NODE+2);r=zero.derive(**f)
        self.assertTrue(r['conditional_returns']['zero40']);self.assertEqual(r['registers'][1],integer(0))
        self.assertEqual(len([v for v in r['memory_events'] if v['operation']=='write8']),40)

    def test_new_zero_unaligned_three_byte_path_retains_exact_span(self):
        f=fixture(node=NODE+3);r=zero.derive(**f)
        self.assertTrue(r['conditional_returns']['zero40']);self.assertEqual([memory(r)[i] for i in range(NODE+3,NODE+43)],[0]*40)

    def test_new_zero_save_alias_observes_corrupted_return(self):
        f=fixture(node=E-60);r=zero.derive(**f)
        self.assertEqual(r['boundary']['site'],zero.IMAGE_BASE+48)
        self.assertIn('reloaded return',r['boundary']['reason']);self.assertFalse(r['conditional_returns']['zero40'])
        self.assertEqual(r['registers'][0],integer(0))

    def test_new_zero_overwrites_source_descriptor_no_pointer_invented(self):
        f=fixture(node=E+4);r=zero.derive(**f)
        self.assertTrue(r['conditional_returns']['zero40']);self.assertTrue(r['callback_entered'])
        self.assertIn('provenance',r['boundary']['reason']);self.assertEqual(r['boundary']['site'],f['layout'].prior.callback+42)

    def test_new_zero_overwrites_scheduler_saved_LR_later_return_refuses(self):
        f=fixture(node=E-4);r=zero.derive(**f)
        self.assertTrue(r['conditional_returns']['zero40'])
        self.assertFalse(r['conditional_returns']['scheduler']);self.assertIsNotNone(r['boundary'])

    def test_new_list_cycle_has_bounded_refusal_no_termination_fact(self):
        f=fixture(list_head=7200);put(f['cells'],7208,pointer(7200));f['max_steps']=240
        r=zero.derive(**f);self.assertIn('bound exhausted',r['boundary']['reason']);self.assertFalse(r['actual_termination_proved'])

    def test_new_missing_tag_read_refuses_at_actual_load(self):
        f=fixture();del f['cells'][SCHED+12];r=zero.derive(**f)
        self.assertEqual(r['boundary']['site'],f['layout'].prior.scheduler.address+56);self.assertIn('reaching',r['boundary']['reason'])

    def test_new_protected_zero_write_is_not_granted(self):
        f=fixture();f['protected_spans']=((NODE+12,NODE+16),);r=zero.derive(**f)
        self.assertIn('protected',r['boundary']['reason']);self.assertNotIn(str(NODE+12),r['changed_cells'])

    def test_new_retired_destination_is_not_reactivated_as_heap(self):
        f=fixture();f['retired_spans']=((NODE,NODE+40),);r=zero.derive(**f)
        self.assertIn('retired',r['boundary']['reason'])

    def test_new_actual_push_reactivates_only_its_four_byte_save(self):
        f=fixture();f['retired_spans']=((E-64,E-56),);r=zero.derive(**f)
        self.assertIsNone(r['boundary']);self.assertTrue(r['conditional_returns']['scheduler'])

    def test_new_immutable_image_overlap_refuses_without_installation_claim(self):
        f=fixture(node=zero.IMAGE_BASE-BASE);r=zero.derive(**f)
        self.assertIn('immutable executable',r['boundary']['reason']);self.assertFalse(r['actual_installed_identity_proved'])

    def test_new_wrapping_destination_refuses_actual_store(self):
        f=fixture(node=12);f['arena_base']=2**32-4096;f['registers'][0]=f['registers'][7]=pointer(4096-20);r=zero.derive(**f)
        self.assertIn('wraps',r['boundary']['reason']);self.assertFalse(r['conditional_returns']['zero40'])

    def test_new_null_allocator_value_does_not_gain_pointer_provenance(self):
        f=fixture();f['registers'][0]=f['registers'][7]=integer(0);r=zero.derive(**f)
        self.assertIn('provenance',r['boundary']['reason']);self.assertFalse(r['conditional_returns']['zero40'])

    def test_new_opaque_subject_is_refused_only_when_used_as_address(self):
        f=fixture();put(f['cells'],E+8,opaque('unknown subject'));r=zero.derive(**f)
        self.assertEqual(r['boundary']['site'],f['layout'].prior.callback+42);self.assertIn('provenance',r['boundary']['reason'])

    def test_new_subject_word_is_copied_with_pointer_origin_intact(self):
        f=fixture();put(f['cells'],SUBJECT+4,pointer(8000));r=zero.derive(**f)
        self.assertIsNone(r['boundary']);self.assertEqual(tuple(memory(r)[NODE+28+i] for i in range(4)),pointer(8000))

    def test_new_callback_target_reload_observes_descriptor_alias(self):
        f=fixture(node=E-56);r=zero.derive(**f)
        self.assertIn('scalar/control observation',r['boundary']['reason']);self.assertFalse(r['callback_entered'])
        self.assertEqual(r['boundary']['site'],f['layout'].prior.scheduler.callback_thunk)

    def test_new_caller_save_alias_is_reloaded_not_restored_from_snapshot(self):
        f=fixture();# Write payload word through the callback into saved R4.
        node=E-48;f=fixture(node=node)
        r=zero.derive(**f)
        self.assertFalse(r['fabricated_saved_words']);self.assertIsNotNone(r['boundary'])

    def test_new_rejects_changed_complete_image_even_unexecuted_tail(self):
        f=fixture();b=bytearray(IMAGE);b[-1]^=1;f['layout']=replace(f['layout'],image=bytes(b))
        with self.assertRaisesRegex(ValueError,'complete actual176B'):zero.derive(**f)

    def test_new_rejects_shifted_image_destination(self):
        f=fixture();f['layout']=replace(f['layout'],image_base=zero.IMAGE_BASE+4)
        with self.assertRaisesRegex(ValueError,'complete actual176B'):zero.derive(**f)

    def test_new_rejects_false_count92_interface(self):
        f=fixture();f['registers'][1]=integer(92);r=zero.derive(**f)
        self.assertEqual(r['trace'],[]);self.assertIn('interface',r['boundary']['reason'])

    def test_new_rejects_wrong_descriptor_reaching_pointer(self):
        f=fixture();f['registers'][9]=pointer(E-52);r=zero.derive(**f)
        self.assertEqual(r['trace'],[]);self.assertIn('interface',r['boundary']['reason'])

    def test_new_explicit_selector_is_required(self):
        f=fixture();f['selector']='default'
        with self.assertRaisesRegex(ValueError,'explicit'):zero.derive(**f)

    def test_new_fresh078_composition_preserves_all_prior_conditions(self):
        # New end-to-end state, no previously successful producer input repeated.
        f=prior_fixtures.fixture(entry=E+128);e=E+128;p=f['layout'];m=f['cells']
        put(m,e,integer(0));put(m,e+8,pointer(SUBJECT));half(m,SCHED+12,0x77);put(m,SCHED+4,integer(0))
        half(m,SUBJECT,0x2244);m[SUBJECT+2]=0x66;put(m,SUBJECT+4,pointer(9000))
        before=small.derive(**f)
        l=zero.bind(p,IMAGE,zero.IMAGE_BASE,selector=zero.SELECTOR)
        r=zero.continue_from_078(l,BASE,before,selector=zero.SELECTOR)
        self.assertIsNone(r['boundary']);self.assertTrue(r['conditional_returns']['scheduler'])
        self.assertEqual(r['inherited_078_obligations'],before['obligations'])
        self.assertFalse(r['actual_078_reaching_authentication_proved'])
        f2=dict(layout=l,arena_base=BASE,cells=prior_fixtures.mem(before),registers=before['registers'],scheduler_entry_sp=e,selector=zero.SELECTOR)
        self.assert_raw(f2,r)
        # Mutate only the supplied report; no producer replay.
        broken=copy.deepcopy(before);broken['nested_call_cutpoint']['call_site']+=2
        with self.assertRaisesRegex(ValueError,'interface differs'):zero.continue_from_078(l,BASE,broken,selector=zero.SELECTOR)

    def test_new_conditional_returns_never_grant_actual_or_native_authority(self):
        f=fixture();f['cells'][SUBJECT+2]=0x91;r=zero.derive(**f)
        self.assertIsNone(r['boundary'])
        for k in ['actual_reaching_state_proved','actual_heap_or_SP_proved','physical_access_proved',
                  'actual_lifetime_proved','actual_installed_identity_proved','actual_code_execution_proved',
                  'actual_termination_proved','full_CFG_closed','Sqrt_effect_proved','post_Sqrt_executed',
                  'returns_to_root','source_or_ELF_admission','native_admission']:
            self.assertFalse(r[k],k)
        self.assertEqual(len(r['obligations']),6)


    def test_new_numeric_unknown_callback_cutpoint_retains_actual_arguments(self):
        f=fixture(node=E-56);put(f['cells'],E+4,integer(0x08030001));r=zero.derive(**f)
        self.assertIn('callback identity',r['boundary']['reason'])
        self.assertEqual(r['nested_call_cutpoint']['target_word'],0x08030000)
        self.assertFalse(r['nested_call_cutpoint']['callee_executed'])
        self.assertEqual(r['nested_call_cutpoint']['register_arguments'][1],pointer(E-56))

    def test_new_payload_aliases_saved_registers_and_real_epilogue_observes_it(self):
        f=fixture(node=E-48);put(f['cells'],E+12,integer(f['layout'].prior.callback|1))
        put(f['cells'],SUBJECT+4,pointer(8120));r=zero.derive(**f)
        self.assertIsNone(r['boundary']);self.assert_raw(f,r)
        self.assertEqual(r['registers'][4],pointer(8120))
        self.assertEqual(r['registers'][8],integer(0x2a0100))
        self.assertEqual(r['registers'][9][:3],(0x34,0x12,0x56))

    def test_new_image_word_writeback_wrap_is_refused_after_last_valid_store(self):
        f=fixture();f['arena_base']=2**32-4096
        f['registers'][0]=f['registers'][7]=pointer(4096-40)
        r=zero.derive(**f)
        self.assertIn('pointer arithmetic wraps',r['boundary']['reason'])
        self.assertEqual(r['boundary']['site'],zero.IMAGE_BASE+22)
        self.assertEqual(sum(v['operation']=='write32' and v['site']==zero.IMAGE_BASE+22 for v in r['memory_events']),10)
        self.assertFalse(r['conditional_returns']['zero40'])

    def test_new_unaligned_raw_zero_one_mod_four_has_identical_events(self):
        f=fixture(node=NODE+9);r=zero.derive(**f)
        self.assertTrue(r['conditional_returns']['zero40']);self.assert_raw(f,r,r['boundary']['site'])

    def test_new_unaligned_raw_zero_two_mod_four_has_identical_events(self):
        f=fixture(node=NODE+10);r=zero.derive(**f)
        self.assertTrue(r['conditional_returns']['zero40']);self.assert_raw(f,r,r['boundary']['site'])

    def test_new_unaligned_raw_zero_three_mod_four_has_identical_events(self):
        f=fixture(node=NODE+11);r=zero.derive(**f)
        self.assertTrue(r['conditional_returns']['zero40']);self.assert_raw(f,r,r['boundary']['site'])

    def test_new_zero_destination_crossing_callback_save_observes_corruption(self):
        # Descriptor points to callback's real save. Its PUSH supplies the data.
        f=fixture();put(f['cells'],E+8,pointer(E-72))
        r=zero.derive(**f)
        self.assertTrue(r['callback_entered']);self.assertIn('scalar field',r['boundary']['reason'])
        self.assertEqual(r['boundary']['site'],f['layout'].prior.callback+42)

    def test_new_exact_scheduler_saved_return_overwritten_by_callback(self):
        # Node near saved LR; source descriptor restores a real subject pointer
        # after zero, but callback's opaque word reaches LR and is observed.
        f=fixture(node=E-32);p=f['layout'].prior
        put(f['cells'],E+28,integer(p.callback|1))
        r=zero.derive(**f)
        self.assertFalse(r['conditional_returns']['scheduler'])
        self.assertIsNotNone(r['boundary'])

    def test_new_callback_entry_save_can_be_protected_independently(self):
        f=fixture();f['protected_spans']=((E-72,E-68),);r=zero.derive(**f)
        self.assertTrue(r['conditional_returns']['zero40']);self.assertEqual(r['boundary']['site'],f['layout'].prior.callback)
        self.assertIn('protected',r['boundary']['reason'])

    def test_new_all_opaque_descriptor_tail_bytes_remain_distinct(self):
        f=fixture();r=zero.derive(**f);m=memory(r)
        for off in range(8,28):
            self.assertEqual(m[E-56+off],('opaque-byte','uninterpreted descriptor tail',off))
        self.assertIsNone(r['boundary'])


    def test_new_callback_written_wrong_LR_stops_at_real_scheduler_BX(self):
        f=fixture(node=E-32);p=f['layout'].prior
        put(f['cells'],E+28,integer(p.callback|1));put(f['cells'],SUBJECT+4,integer(0x08012345))
        r=zero.derive(**f)
        self.assertEqual(r['boundary']['site'],p.scheduler.address+204)
        self.assertEqual(r['boundary']['target_word'],0x08012345)
        self.assertEqual(r['conditional_returns'],dict(zero40=True,callback=True,scheduler=False))
        self.assert_raw(f,r,r['boundary']['site'])

    def test_new_callback_written_opaque_LR_stops_at_real_control_observation(self):
        f=fixture(node=E-32);p=f['layout'].prior
        put(f['cells'],E+28,integer(p.callback|1));put(f['cells'],SUBJECT+4,opaque('new opaque return'))
        r=zero.derive(**f)
        self.assertEqual(r['boundary']['site'],p.scheduler.address+204)
        self.assertIn('scalar/control',r['boundary']['reason']);self.assertTrue(r['conditional_returns']['callback'])
        self.assertEqual(r['registers'][1],opaque('new opaque return'))

    def test_new_truncated_callback_pointer_word_is_not_nominal_identity(self):
        f=fixture(node=E-56);put(f['cells'],E+4,pointer(8000));r=zero.derive(**f)
        self.assertFalse(r['callback_entered']);self.assertIn('scalar/control',r['boundary']['reason'])
        self.assertEqual(r['boundary']['site'],f['layout'].prior.scheduler.callback_thunk)

    def test_new_sixteenth_parent_node_uses_each_live_link_no_list_summary(self):
        f=fixture(parent=7100,list_head=7200)
        for i in range(16):put(f['cells'],7200+32*i+8,pointer(7200+32*(i+1)) if i<15 else integer(0))
        r=zero.derive(**f);self.assertIsNone(r['boundary']);self.assert_raw(f,r)
        self.assertEqual(tuple(memory(r)[NODE+4+i] for i in range(4)),pointer(7680))
