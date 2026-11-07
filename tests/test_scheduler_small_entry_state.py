"""New direct scheduler states and one fresh076 composition, no old tests."""
from dataclasses import replace
import copy
import hashlib
import json
from pathlib import Path
import unittest

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
import scheduler_small_entry_state as small
import scheduler_allocator_state as state
import scheduler_copy_state as words
import scheduler_coordinate_common_state as coordinate
import test_scheduler_coordinate_common_state as layouts

BASE, E, SCHED = 0x02000000, 2048, 5000


def digest(b):return hashlib.sha256(b).hexdigest()
def put(m,at,w):m.update({at+i:v for i,v in enumerate(w)})
def half(m,at,n):put(m,at,tuple((n & 65535).to_bytes(2,'little')))
def opaque(name):return tuple(('opaque-byte',name,i) for i in range(4))
def mem(r):return {int(k):v for k,v in r['post_cells'].items()}


def layout():
    c = layouts.layout()
    s = coordinate._validate(c)['prior']['calls'][c.helper.helper+266]
    w,a,search,remove,median,insert,thunk,cbthunk = [s+0x1000*i for i in range(1,9)]
    sl = state.split.insert.search.Layout(search,digest(state.split.insert.search.SHAPE))
    md = state.remove.REMOVE_HEAD+state.remove._bl(remove+124,median)+state.remove.REMOVE_TAIL
    ml = state.remove.Layout(remove,median,digest(md),digest(state.remove.MEDIAN))
    idata = state.split.insert.HEAD+state.remove._bl(insert+22,search)+state.split.insert.MIDDLE+state.remove._bl(insert+138,median)+state.split.insert.TAIL
    il = state.split.insert.Layout(insert,digest(idata),sl,ml)
    al = state.split.Layout(a,digest(state.split._encoded(a,il,thunk,0x08300000)),il,thunk,0x08300000)
    wl = state.wrapper.Layout(w,digest(state.wrapper._identity(w,al)),al)
    sched = state.Layout(s,digest(state._encoded(s,wl,cbthunk)),wl,cbthunk)
    cb = int.from_bytes(c.helper.helper_data[288:292],'little') & ~1
    data = bytearray(small.CALLBACK)
    for offset in (56,84,108):data[offset:offset+4] = state.remove._bl(cb+offset,0x08020000+offset)
    return small.Layout(c,sched,cb,bytes(data),(0x03005e79).to_bytes(4,'little'))


def heap(*,size=10,empty=False):
    m = {}
    for at,value in [(0,0 if empty else 32),(2,0 if empty else 32),(4,0 if empty else 1),
                     (130,0),(134,size),(136,0),(138,0)]:half(m,at,value)
    return m


def fixture(*,size=10,empty=False,entry=E):
    l = layout()
    r = {i:opaque('078 R'+str(i)) for i in range(15)}
    r.update({0:words._pointer(SCHED),1:words._constant(l.callback|1),2:words._constant(12),
              3:words._pointer(entry+4),13:words._pointer(entry),14:words._constant((l.coordinate.helper.helper+270)|1)})
    m = heap(size=size,empty=empty)
    put(m,SCHED,words._pointer(0));put(m,entry,words._pointer(7000))
    for i in range(28):m[entry+4+i] = ('opaque-byte','live source descriptor',i)
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=small.SELECTOR)


def concrete_byte(v,base=BASE):
    if type(v) is int:return v
    if v[0] == 'base-plus-byte':return ((base+v[1])>>(8*v[2])) & 255
    return hashlib.sha256((v[1]+':'+str(v[2])).encode()).digest()[0]


def concrete_word(w,base=BASE):
    return int.from_bytes(bytes(concrete_byte(v,base) for v in w),'little')


def raw(f, *, zero12=False):
    """Concrete independent Thumb execution; stack allocation writes no bits."""
    l,base = f['layout'],f['arena_base']
    allowners = small._validate(l)  # only complete immutable shapes, no effects
    s,a = l.scheduler.address,l.scheduler.allocator.allocator
    bodies = {p:b for p,b in allowners.items() if p not in (l.callback,l.scheduler.callback_thunk,a.insertion.address)}
    if zero12:bodies[a.insertion.address]=allowners[a.insertion.address]
    regs = {i:concrete_word(w,base) for i,w in f['registers'].items()}
    m = {base+k:concrete_byte(v,base) for k,v in f['cells'].items()}
    pc,trace,events,cmp = s,[],[],None
    decoder = Cs(CS_ARCH_ARM,CS_MODE_THUMB);decoder.detail = True
    names = dict(sp=13,lr=14,pc=15,sb=9,sl=10,fp=11,ip=12)

    def reg(op):
        name=decoder.reg_name(op.reg)
        return names.get(name,int(name[1:]) if name.startswith('r') else -1)
    def num(op):return op.imm if op.type == 2 else regs[reg(op)]
    def load(at,width):
        v = tuple(m[at+i] for i in range(width));events.append((pc,'read'+str(width*8),at-base,v))
        return int.from_bytes(bytes(v),'little')
    def store(at,width,value):
        v = tuple(((value & 0xffffffff).to_bytes(4,'little'))[:width]);m.update({at+i:b for i,b in enumerate(v)})
        events.append((pc,'write'+str(width*8),at-base,v))
    for _ in range(1024):
        owner=next((p for p,b in bodies.items() if p <= pc < p+len(b)),None)
        assert owner is not None,hex(pc)
        ins=next(decoder.disasm(bodies[owner][pc-owner:],pc,1));ops,name,nxt=ins.operands,ins.mnemonic,pc+ins.size
        trace.append(pc)
        if name=='push':
            selected=[reg(o) for o in ops];at=regs[13]-4*len(selected)
            for i,n in enumerate(selected):store(at+4*i,4,regs[n])
            regs[13]=at
        elif name=='pop':
            selected=[reg(o) for o in ops];at=regs[13];vals=[load(at+4*i,4) for i in range(len(selected))]
            for n,v in zip(selected,vals):regs[n]=v
            regs[13]=at+4*len(selected)
        elif name=='mov':regs[reg(ops[0])]=num(ops[1])
        elif name=='movs':regs[reg(ops[0])]=num(ops[1])
        elif name in ('add','adds','sub','subs'):
            dst=reg(ops[0]);x=num(ops[1]) if len(ops)==3 else regs[dst];y=num(ops[-1])
            regs[dst]=(x-y if name.startswith('sub') else x+y)&0xffffffff
        elif name in ('lsls','lsrs','asrs'):
            x,shift=num(ops[1]),num(ops[2])
            if name=='lsls':v=x<<shift
            elif name=='lsrs':v=x>>shift
            else:v=(x-2**32 if x&0x80000000 else x)>>shift
            regs[reg(ops[0])]=v&0xffffffff
        elif name in ('ands','orrs'):
            x,y=regs[reg(ops[0])],num(ops[1]);regs[reg(ops[0])]=x&y if name=='ands' else x|y
        elif name=='rsbs':regs[reg(ops[0])]=(-num(ops[1]))&0xffffffff
        elif name=='cmp':cmp=(num(ops[0]),num(ops[1]))
        elif name in ('beq','bne','bhi','bls','bgt','ble','bge','blt','bhs','blo'):
            x,y=cmp;xx=x-2**32 if x&0x80000000 else x;yy=y-2**32 if y&0x80000000 else y
            cond=dict(beq=x==y,bne=x!=y,bhi=x>y,bls=x<=y,bgt=xx>yy,ble=xx<=yy,bge=xx>=yy,blt=xx<yy,bhs=x>=y,blo=x<y)
            if cond[name]:nxt=ops[0].imm
        elif name=='b':nxt=ops[0].imm
        elif name=='bl':regs[14]=nxt|1;nxt=ops[0].imm
        elif name=='bx':
            if owner==a.thunk:
                if not zero12 or regs[1]!=12:return regs,m,trace,events
                # Reuse the retained conditional relation, not its old producer.
                dest,top,lr=regs[0],regs[13],regs[14]
                store(top-4,4,lr)
                for offset in range(0,12,4):store(dest+offset,4,0)
                regs[0]=load(top-4,4);regs[1]=0;regs[2]=dest+12
                nxt=regs[0]&~1;cmp=None
            else:nxt=regs[reg(ops[0])]&~1
        elif name in ('ldr','ldrb','ldrh','str','strb','strh'):
            bn=decoder.reg_name(ops[1].mem.base);width=1 if name.endswith('b') else 2 if name.endswith('h') else 4
            if bn=='pc':
                at=((pc+4)&~3)+ops[1].mem.disp
                regs[reg(ops[0])]=int.from_bytes(bodies[owner][at-owner:at-owner+4],'little')
            else:
                at=regs[names.get(bn,int(bn[1:]) if bn.startswith('r') else -1)]+ops[1].mem.disp
                if pc in (s+42,a.address+92):regs[reg(ops[0])]=int.from_bytes(l.zero_pointer_data,'little')
                elif name.startswith('ldr'):regs[reg(ops[0])]=load(at,width)
                else:store(at,width,regs[reg(ops[0])])
        else:raise AssertionError((hex(pc),name,ins.op_str))
        pc=nxt
    raise AssertionError('independent raw budget exceeded')


class EntryTests(unittest.TestCase):
    def test_no_split_materializes_all_nested_saves_and_reaches_zero40(self):
        f=fixture();r=small.derive(**f);s=f['layout'].scheduler
        self.assertTrue(r['reaches_unproved_installed_call'],r['boundary'])
        self.assertEqual(r['nested_call_cutpoint']['call_site'],s.address+48)
        self.assertEqual(r['registers'][0],words._pointer(140))
        self.assertEqual(r['registers'][1],words._constant(40))
        self.assertEqual(r['registers'][3],words._constant(f['layout'].callback|1))
        self.assertEqual(r['registers'][13],words._pointer(E-56))
        self.assertEqual(r['allocation_count'],40)
        self.assertEqual(len(r['actual_returns']),5)
        self.assertFalse(r['callback_executed'])

    def test_split_stops_at_real_zero12_before_insertion_or_scheduler_zero(self):
        f=fixture(size=40);r=small.derive(**f);a=f['layout'].scheduler.allocator.allocator
        self.assertTrue(r['reaches_unproved_installed_call'],r['boundary'])
        self.assertEqual(r['nested_call_cutpoint']['call_site'],a.address+98)
        self.assertEqual(r['registers'][0],words._pointer(180))
        self.assertEqual(r['registers'][1],words._constant(12))
        self.assertEqual(len(r['actual_returns']),3)
        self.assertNotIn(f['layout'].scheduler.address+38,r['trace'])

    def test_empty_heap_follows_real_null_return_and_does_not_grant_destination(self):
        f=fixture(empty=True);r=small.derive(**f)
        self.assertTrue(r['reaches_unproved_installed_call'],r['boundary'])
        self.assertEqual(r['registers'][0],words._constant(0))
        self.assertEqual(r['registers'][1],words._constant(40))
        self.assertFalse(r['physical_access_proved'])

    def test_parent_argument_is_read_after_the_real_scheduler_saves(self):
        f=fixture();r=small.derive(**f);s=f['layout'].scheduler.address
        e=next(e for e in r['memory_events'] if e['site']==s+18)
        self.assertEqual(e['coordinate'],E)
        self.assertEqual(e['bytes'],words._pointer(7000))
        self.assertEqual(r['registers'][6],words._pointer(7000))
        self.assertEqual(r['registers'][9],words._pointer(E+4))

    def test_opaque_parent_is_transported_without_inventing_a_pointer(self):
        f=fixture();put(f['cells'],E,opaque('opaque parent'))
        r=small.derive(**f)
        self.assertTrue(r['reaches_unproved_installed_call'],r['boundary'])
        self.assertEqual(r['registers'][6],opaque('opaque parent'))

    def test_heap_word_aliases_real_scheduler_saved_R4(self):
        f=fixture();f['registers'][0]=words._pointer(E-20);f['registers'][4]=words._pointer(0)
        r=small.derive(**f)
        self.assertTrue(r['reaches_unproved_installed_call'],r['boundary'])
        e=next(e for e in r['memory_events'] if e['site']==f['layout'].scheduler.address+30)
        self.assertEqual(e['bytes'],words._pointer(0))

    def test_heap_word_over_opaque_saved_R4_refuses_at_actual_heap_field_use(self):
        f=fixture();f['registers'][0]=words._pointer(E-20)
        r=small.derive(**f)
        self.assertFalse(r['reaches_unproved_installed_call'])
        self.assertIn('provenance',r['boundary']['reason'])
        self.assertEqual(r['boundary']['site'],f['layout'].scheduler.allocator.allocator.insertion.search.address+18)

    def test_heap_fields_overwritten_by_real_stack_saves_do_not_reuse_initial_bytes(self):
        f=fixture(entry=24)
        r=small.derive(**f)
        self.assertFalse(r['reaches_unproved_installed_call'])
        self.assertIn('opaque',r['boundary']['reason'])

    def test_missing_heap_byte_stops_at_exact_search_read(self):
        f=fixture();del f['cells'][3]
        r=small.derive(**f)
        self.assertEqual(r['boundary']['site'],f['layout'].scheduler.allocator.allocator.insertion.search.address+20)
        self.assertIn('reaching',r['boundary']['reason'])

    def test_pointer_bytes_are_not_scalar_heap_header(self):
        f=fixture();f['cells'][3]=('base-plus-byte',20,0)
        r=small.derive(**f)
        self.assertIn('scalar field',r['boundary']['reason'])

    def test_protected_heap_write_preserves_reads_and_stops_before_mutation(self):
        f=fixture();f['protected_spans']=((136,137),)
        r=small.derive(**f)
        self.assertFalse(r['reaches_unproved_installed_call'])
        self.assertIn('protected',r['boundary']['reason'])
        self.assertEqual(r['boundary']['coordinate'],136)

    def test_protected_push_is_rejected_before_any_word_write(self):
        f=fixture();f['protected_spans']=((E-4,E),)
        r=small.derive(**f)
        self.assertEqual(r['changed_cells'],{})
        self.assertEqual(r['memory_events'],[])

    def test_fifth_word_in_retired_caller_region_is_not_reactivated(self):
        f=fixture();f['retired_spans']=((E,E+4),)
        r=small.derive(**f)
        self.assertEqual(r['boundary']['site'],f['layout'].scheduler.address+18)
        self.assertIn('retired',r['boundary']['reason'])

    def test_nested_stack_reallocation_and_final_retired_aliases_are_visible(self):
        f=fixture();f['retired_spans']=((E-200,E),);f['registers'][10]=words._pointer(E-100)
        r=small.derive(**f)
        self.assertTrue(r['reaches_unproved_installed_call'],r['boundary'])
        self.assertEqual(r['known_retired_alias_registers']['10'],E-100)
        self.assertEqual(r['registers'][10],f['registers'][10])

    def test_missing_parent_stops_after_actual_local_forgetting(self):
        f=fixture();del f['cells'][E]
        r=small.derive(**f)
        self.assertEqual(r['boundary']['site'],f['layout'].scheduler.address+18)
        for i in range(E-56,E-28):self.assertEqual(mem(r)[i][0],'opaque-byte')

    def test_wrong_count_callback_descriptor_and_return_are_entry_refusals(self):
        for reg,value in [(2,words._constant(64)),(1,words._constant(0x080e5f51)),
                          (3,words._pointer(E+8)),(14,words._constant(0x08012345))]:
            f=fixture();f['registers'][reg]=value;r=small.derive(**f)
            self.assertEqual(r['changed_cells'],{})
            self.assertEqual(r['trace'],[])

    def test_budget_is_a_refusal_without_fabricated_returns(self):
        f=fixture();f['max_steps']=24
        r=small.derive(**f)
        self.assertIn('instruction bound',r['boundary']['reason'])
        self.assertFalse(r['reaches_unproved_installed_call'])
        self.assertEqual(r['actual_returns'],[])

    def test_byte_budget_blocks_initial_push_atomically(self):
        f=fixture();n=100000
        while len(f['cells'])<4096:f['cells'][n]=0;n+=1
        r=small.derive(**f)
        self.assertEqual(r['changed_cells'],{})
        self.assertEqual(r['memory_events'],[])

    def test_input_immutable_and_external_claims_false(self):
        f=fixture();saved=copy.deepcopy(f);r=small.derive(**f);self.assertEqual(f,saved)
        for key in ('fabricated_callee_effects','fabricated_saved_words','ABI_preservation_assumed',
                    'old_count92_effect_used','callback_executed','Sqrt_effect_proved','actual_reaching_state_proved',
                    'actual_heap_or_SP_proved','physical_access_proved','actual_lifetime_proved',
                    'actual_code_execution_proved','actual_termination_proved','full_CFG_closed','returns_to_root',
                    'source_or_ELF_admission','native_admission'):
            self.assertFalse(r[key],key)

    def test_independent_concrete_instruction_oracle_on_six_new_paths(self):
        cases=[fixture(size=10),fixture(size=11),fixture(size=13),fixture(size=14),fixture(size=40),fixture(empty=True)]
        for f in cases:
            r=small.derive(**f);rr,mm,tt,ee=raw(f)
            self.assertTrue(r['reaches_unproved_installed_call'],r['boundary'])
            self.assertEqual({i:concrete_word(w) for i,w in r['registers'].items()},rr)
            self.assertEqual(r['trace'],tt)
            actual=[(e['site'],e['operation'],e['coordinate'],tuple(concrete_byte(v) for v in e['bytes']))
                    for e in r['memory_events'] if e['operation'] in ('read8','read16','read32','write8','write16','write32')]
            self.assertEqual(actual,ee)
            model=mem(r)
            for at,value in mm.items():self.assertEqual(concrete_byte(model[at-BASE]),value)
            for at in set(model)-{at-BASE for at in mm}:self.assertEqual(model[at][0],'opaque-byte')

    def test_one_new076_state_consumed_once_and_sqrt_report_rejected(self):
        l=layout()
        fresh,_=layouts.fixture(x=77,y=43,z=-19,dx=211,dy=109)
        newmem={int(k):v for k,v in fresh['report']['post_cells'].items()}
        newmem.update(heap(size=13));put(newmem,SCHED,words._pointer(0))
        put(newmem,layouts.prior_oracle.POINT-BASE,words._pointer(SCHED))
        fresh['report']['post_cells']={str(k):v for k,v in newmem.items()}
        report=coordinate.continue_from_075(**fresh)
        self.assertTrue(report['reaches_helper_scheduler_call'],report['boundary'])
        saved=copy.deepcopy(report)
        r=small.continue_from_076(l,BASE,report,selector=small.SELECTOR)
        self.assertTrue(r['reaches_unproved_installed_call'],r['boundary'])
        self.assertEqual(report,saved)
        altered=copy.deepcopy(report);altered['reaches_helper_scheduler_call']=False
        with self.assertRaises(ValueError):small.continue_from_076(l,BASE,altered,selector=small.SELECTOR)
        altered=copy.deepcopy(report);altered['nested_call_cutpoint']['register_arguments'][0]=words._constant(0)
        with self.assertRaises(ValueError):small.continue_from_076(l,BASE,altered,selector=small.SELECTOR)


def zero12_receipt():
    return (Path(__file__).resolve().parents[1]/'inputs/retained-zero12.json').read_bytes()


class Zero12Tests(unittest.TestCase):
    def test_conditional_split_insertion_and_real_returns_match_raw_state(self):
        f=fixture(size=40)
        r=small.derive(**f,zero12_receipt=zero12_receipt())
        self.assertTrue(r['reaches_unproved_installed_call'],r['boundary'])
        self.assertEqual(r['nested_call_cutpoint']['call_site'],f['layout'].scheduler.address+48)
        self.assertEqual(len(r['retained_zero12_compositions']),1)
        self.assertIn(f['layout'].scheduler.allocator.allocator.insertion.address,r['trace'])
        rr,mm,tt,ee=raw(f,zero12=True)
        self.assertEqual({i:concrete_word(v) for i,v in r['registers'].items()},rr)
        self.assertEqual(r['trace'],tt)
        actual=[(e['site'],e['operation'],e['coordinate'],tuple(concrete_byte(v) for v in e['bytes']))
                for e in r['memory_events'] if e['operation'] in ('read8','read16','read32','write8','write16','write32')]
        self.assertEqual(actual,ee)
        modeled=mem(r)
        self.assertEqual({at:concrete_byte(modeled[at-BASE]) for at in mm},mm)
        self.assertEqual(r['registers'][0],words._pointer(140))
        self.assertEqual(r['registers'][1],words._constant(40))
        self.assertFalse(r['callback_executed'])

    def test_certificate_corruption_refuses_before_conditional_effect(self):
        f=fixture(size=41)
        r=small.derive(**f,zero12_receipt=zero12_receipt()+b' ')
        self.assertIn('certificate bytes changed',r['boundary']['reason'])
        self.assertEqual(r['retained_zero12_compositions'],[])
        self.assertFalse(any(e.get('effect_origin') for e in r['memory_events']))

    def test_actual_target_word_must_match_retained_entry(self):
        f=fixture(size=42)
        f['layout']=replace(f['layout'],zero_pointer_data=(0x03005e7b).to_bytes(4,'little'))
        r=small.derive(**f,zero12_receipt=zero12_receipt())
        self.assertIn('R2 target differs',r['boundary']['reason'])
        self.assertEqual(r['retained_zero12_compositions'],[])

    def test_no_count40_effect_is_inferred_from_count12_receipt(self):
        f=fixture(size=12)
        r=small.derive(**f,zero12_receipt=zero12_receipt())
        self.assertTrue(r['reaches_unproved_installed_call'],r['boundary'])
        self.assertEqual(r['registers'][1],words._constant(40))
        self.assertEqual(r['retained_zero12_compositions'],[])
        self.assertFalse(r['callback_executed'])

    def test_zero_destination_protection_is_checked_before_certificate_writes(self):
        f=fixture(size=43)
        r=small.derive(**f,zero12_receipt=zero12_receipt(),protected_spans=((180,184),))
        self.assertIn('protected',r['boundary']['reason'])
        self.assertEqual(r['retained_zero12_compositions'],[])
        self.assertFalse(any(e.get('effect_origin') for e in r['memory_events']))

    def test_retired_zero_destination_is_not_reactivated_as_heap(self):
        f=fixture(size=44)
        r=small.derive(**f,zero12_receipt=zero12_receipt(),retired_spans=((180,192),))
        self.assertIn('retired',r['boundary']['reason'])
        self.assertEqual(r['retained_zero12_compositions'],[])

    def test_explicit_code_access_and_interference_conditions_remain_open(self):
        f=fixture(size=45);before=copy.deepcopy(f)
        r=small.derive(**f,zero12_receipt=zero12_receipt())
        self.assertEqual(f,before)
        c=r['retained_zero12_compositions'][0]
        self.assertEqual(c['unproved_premises'],json.loads(zero12_receipt())['unproved_premises'])
        self.assertFalse(c['actual_installed_identity_proved'])
        for key in ('physical_access_proved','actual_reaching_state_proved','actual_heap_or_SP_proved',
                    'actual_lifetime_proved','actual_code_execution_proved','actual_termination_proved',
                    'full_CFG_closed','source_or_ELF_admission','native_admission'):
            self.assertFalse(r[key])

    def test_zero_over_live_source_descriptor_is_ordered_not_separated(self):
        # Entry164 puts its source at168; the zero180..192 overlaps that source.
        # Earlier actual stack writes may also alias heap fields: no stale reuse.
        f=fixture(size=46,entry=164)
        r=small.derive(**f,zero12_receipt=zero12_receipt())
        self.assertIsNotNone(r['boundary'])
        self.assertFalse(r['callback_executed'])
        self.assertFalse(r['actual_heap_or_SP_proved'])
        for e in r['memory_events']:
            if e.get('effect_origin') and e['operation'].startswith('write') and e['coordinate']==180:
                self.assertEqual(e['bytes'],(0,0,0,0))

    def test_optional_receipt_requires_exact_bytes(self):
        f=fixture(size=47)
        for invalid in ({},True,bytearray(zero12_receipt())):
            with self.assertRaises(ValueError):small.derive(**f,zero12_receipt=invalid)


class BindingTests(unittest.TestCase):
    def test_new_synthetic_binding_uses_exact_retained_layouts(self):
        l=layout()
        self.assertEqual(small.bind(l.coordinate,l.scheduler,l.callback_data,l.callback,l.zero_pointer_data,selector=small.SELECTOR),l)

    def test_callback_complete_extent_and_selected_data_are_guarded(self):
        l=layout()
        for offset in (0,8,40,132,134):
            data=bytearray(l.callback_data);data[offset]^=1
            with self.assertRaises(ValueError):small._validate(replace(l,callback_data=bytes(data)))
        with self.assertRaises(ValueError):small._validate(replace(l,zero_pointer_data=b'\0'*3))

    def test_scheduler_and_callback_identity_cannot_be_swapped(self):
        l=layout()
        with self.assertRaises(ValueError):small._validate(replace(l,scheduler=replace(l.scheduler,sha256='0'*64)))
        with self.assertRaises(ValueError):small._validate(replace(l,callback=l.callback+2))

    def test_invalid_shapes_and_selector_refuse(self):
        f=fixture()
        for change in [dict(selector='default'),dict(max_steps=1025),dict(max_steps=True),dict(registers={}),
                       dict(cells={1:True}),dict(arena_base=True),dict(retired_spans=[(0,4)])]:
            with self.assertRaises(ValueError):small.derive(**dict(f,**change))


if __name__=='__main__':unittest.main()
