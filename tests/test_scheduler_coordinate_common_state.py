"""New075->076 states, ordered aliases and independent Thumb comparisons."""
from dataclasses import replace
import copy
import unittest

from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_coordinate_common_state as continuation
import scheduler_helper_common_state as prior
import scheduler_copy_state as words
import allocator_remove_relation as branch
import test_scheduler_helper_common_state as prior_oracle

BASE=prior_oracle.BASE
H,G,I,C=prior_oracle.H,prior_oracle.G,prior_oracle.I,prior_oracle.C
E=prior_oracle.E
T=prior_oracle.EXTERNAL+0x1000
P=prior_oracle.EXTERNAL+214*4
B=0x08110000
SQRT=0x08120000
GLOBAL=10000
put,half,opaque=prior_oracle.put,prior_oracle.half,prior_oracle.opaque


def layout(*,point=BASE+GLOBAL,motion_point=None):
    if motion_point is None:motion_point=point
    old=prior_oracle.layout()
    transform=continuation.TRANSFORM[:68]+point.to_bytes(4,'little')
    predicate=continuation.PREDICATE[:18]+branch._bl(P+18,B)+continuation.PREDICATE[22:]
    motion=bytearray(continuation.MOTION)
    motion[76:80]=(motion_point+52).to_bytes(4,'little');motion[252:256]=motion_point.to_bytes(4,'little')
    for offset,target in [(128,SQRT),(206,SQRT+0x1000),(226,SQRT+0x1000)]:motion[offset:offset+4]=branch._bl(B+offset,target)
    return continuation.Layout(old,T,transform,P,predicate,B,bytes(motion))


def signed16(v):
    v&=65535
    return v-65536 if v&32768 else v


def fixture(*,x=-123,y=234,z=-300,dx=1000,dy=2000,match=True,point=BASE+GLOBAL,motion_point=None):
    l=layout(point=point,motion_point=motion_point)
    f=prior_oracle.fixture(mode=5,dispatch=0);f['layout']=l.helper
    for offset,value in [(8,x),(10,y),(12,z)]:half(f['cells'],prior_oracle.FIELDS+offset,value)
    g=point-BASE;mg=(point if motion_point is None else motion_point)-BASE
    half(f['cells'],g+32,dx);half(f['cells'],g+34,dy)
    outx=signed16(((signed16(x)-signed16(z))>>1)+dx-120)
    outy=signed16(((signed16(x)+signed16(z))>>2)-(signed16(y)>>1)+dy-96)
    half(f['cells'],mg+36,outx if match else outx+1);half(f['cells'],mg+38,outy)
    report=prior.derive(**f)
    assert report['nested_call_cutpoint']['target']==T,report['boundary']
    return dict(layout=l,arena_base=BASE,report=report,selector=continuation.SELECTOR),f


def run(f):return continuation.continue_from_075(**f)
def mem(r):return {int(k):v for k,v in r['post_cells'].items()}
def direct(f):
    report=f['report']
    return dict(layout=f['layout'],arena_base=BASE,cells=mem(report),registers=dict(report['registers']),
                helper_entry_sp=E,selector=continuation.SELECTOR,
                retired_spans=tuple(tuple(v) for v in report['retired_spans']))


def raw(f):
    """Independent Capstone decoding from the actual conditional C918 entry."""
    l=f['layout'];r=dict(f['registers']);m=dict(f['cells']);pc=l.transform;trace=[];events=[];comparison=None
    owners={l.transform:l.transform_data,l.helper.coordinates:l.helper.coordinates_data,
            l.helper.helper:l.helper.helper_data,l.predicate:l.predicate_data,l.motion:l.motion_data}
    md=Cs(CS_ARCH_ARM,CS_MODE_THUMB);md.detail=True
    def reg(op):
        n=md.reg_name(op.reg)
        return {'sp':13,'lr':14,'pc':15,'sb':9,'sl':10,'fp':11,'ip':12}.get(n,int(n[1:]) if n.startswith('r') else -1)
    def scalar(w):
        assert all(type(v)is int for v in w)
        return sum(v<<(8*i) for i,v in enumerate(w))
    def coord(w):
        assert w==words._pointer(w[0][1]);return w[0][1]
    def forget(lo,hi):
        names={v[1] for v in [*m.values(),*(v for w in r.values() for v in w)] if type(v)is tuple and v[0]=='opaque-byte'}
        name='unmodeled coordinate local';n=0
        while name in names:n+=1;name='unmodeled coordinate local:'+str(n)
        for at in range(lo,hi):m[at]=('opaque-byte',name,at-lo)
    def read(at,width,signed=False):
        value=tuple(m[at+i] for i in range(width));events.append((pc,'read'+str(width*8),at,value))
        if width==4:return value
        n=scalar(value)
        if signed and n&(1<<(width*8-1)):n-=1<<(width*8)
        return words._constant(n&0xffffffff)
    def write(at,width,value):
        value=value[:width];put(m,at,value);events.append((pc,'write'+str(width*8),at,value))
    def location(op):
        base=md.reg_name(op.mem.base)
        if base=='pc':return ((pc+4)&~3)+op.mem.disp,True
        nr={'sp':13}.get(base,int(base[1:]) if base.startswith('r') else -1)
        offset=op.mem.disp
        if op.mem.index:offset+=scalar(r[int(md.reg_name(op.mem.index)[1:])])
        value=r[nr]
        return (scalar(value)-f['arena_base'] if all(type(v)is int for v in value) else coord(value))+offset,False
    for _ in range(220):
        owner=next((a for a,b in owners.items() if a<=pc<a+len(b)),None)
        if owner is None:return r,m,trace,events,pc
        ins=next(md.disasm(owners[owner][pc-owner:],pc,1));ops=ins.operands;name=ins.mnemonic
        trace.append(pc);nxt=pc+ins.size
        if name=='push':
            selected=[reg(v) for v in ops];at=coord(r[13])-4*len(selected)
            for i,n in enumerate(selected):write(at+4*i,4,r[n])
            r[13]=words._pointer(at)
        elif name=='pop':
            selected=[reg(v) for v in ops];at=coord(r[13]);values=[read(at+4*i,4) for i in range(len(selected))]
            for n,value in zip(selected,values):r[n]=value
            r[13]=words._pointer(at+4*len(selected))
        elif name in ('add','sub') and len(ops)==2 and reg(ops[0])==13:
            old=coord(r[13]);new=old+(-1 if name=='sub' else 1)*ops[1].imm
            if name=='sub':forget(new,old)
            r[13]=words._pointer(new)
        elif name=='mov':r[reg(ops[0])]=r[reg(ops[1])]
        elif name=='movs':r[reg(ops[0])]=words._constant(ops[1].imm)
        elif name in ('lsls','lsrs','asrs'):
            value=scalar(r[reg(ops[1])]);shift=ops[2].imm
            if name=='lsls':value<<=shift
            elif name=='lsrs':value>>=shift
            else:
                if value&0x80000000:value-=2**32
                value>>=shift
            r[reg(ops[0])]=words._constant(value&0xffffffff)
        elif name in ('adds','subs'):
            dst=reg(ops[0])
            if len(ops)==3:
                if ops[2].type==2 and ops[2].imm==0 and name=='adds':r[dst]=r[reg(ops[1])];pc=nxt;continue
                a=scalar(r[reg(ops[1])]);v=ops[2].imm if ops[2].type==2 else scalar(r[reg(ops[2])])
            else:a=scalar(r[dst]);v=ops[1].imm
            r[dst]=words._constant((a+v if name=='adds' else a-v)&0xffffffff)
        elif name=='muls':r[reg(ops[0])]=words._constant((scalar(r[reg(ops[1])])*scalar(r[reg(ops[2])]))&0xffffffff)
        elif name=='rsbs':r[reg(ops[0])]=words._constant((-scalar(r[reg(ops[1])]))&0xffffffff)
        elif name=='cmp':comparison=scalar(r[reg(ops[0])])==scalar(r[reg(ops[1])])
        elif name in ('beq','bne'):
            if comparison if name=='beq' else not comparison:nxt=ops[0].imm
        elif name=='b':nxt=ops[0].imm
        elif name=='bl':r[14]=words._constant(nxt|1);nxt=ops[0].imm
        elif name=='bx':nxt=scalar(r[reg(ops[0])])&~1
        elif name=='add':r[reg(ops[0])]=words._pointer(coord(r[reg(ops[1])])+ops[2].imm)
        elif name in ('ldr','ldrh','ldrsh'):
            at,rom=location(ops[1]);width=4 if name=='ldr' else 2
            r[reg(ops[0])]=tuple(owners[owner][at-owner:at-owner+4]) if rom else read(at,width,name=='ldrsh')
        elif name in ('str','strh'):
            at,rom=location(ops[1]);assert not rom;write(at,4 if name=='str' else 2,r[reg(ops[0])])
        else:raise AssertionError((hex(pc),name,ins.op_str))
        pc=nxt
    raise AssertionError('raw path exceeded acyclic bound')


class CoordinateTests(unittest.TestCase):
    def test_new075_state_closes_real_returns_to_distinct_scheduler_entry(self):
        f,_=fixture();r=run(f)
        self.assertTrue(r['reaches_helper_scheduler_call'],r['boundary'])
        self.assertTrue(all(r['conditional_returns'].values()))
        self.assertEqual(r['nested_call_cutpoint']['call_site'],H+266)
        self.assertEqual(r['registers'][2],words._constant(12))
        self.assertEqual(r['registers'][13],words._pointer(E-72))
        self.assertEqual(tuple(mem(r)[E-40+i] for i in range(2)),tuple((1088).to_bytes(2,'little')))

    def test_fresh_c918_reads_follow_each_prior_output_store(self):
        f,_=fixture(point=BASE+E-72,motion_point=BASE+GLOBAL);r=run(f)
        # The globals+32/+34 are the actual x/y output slots.
        self.assertTrue(r['conditional_returns']['transform'])
        m=mem(r);self.assertEqual(m[E-40]|m[E-39]<<8,176)
        self.assertEqual(m[E-38]|m[E-37]<<8,(-446)&65535)
        relevant=[e for e in r['memory_events'] if e['site'] in (T+24,T+28,T+32,T+46,T+48,T+54)]
        self.assertEqual([e['operation'] for e in relevant],['write16','read16','write16','write16','read16','write16'])

    def test_nonmatching_motion_reaches_real_sqrt_call_without_return(self):
        f,_=fixture(match=False);r=run(f)
        self.assertEqual(r['boundary']['site'],SQRT)
        self.assertEqual(r['nested_call_cutpoint']['call_site'],B+128)
        self.assertEqual(r['registers'][0],words._constant(256))
        self.assertFalse(r['conditional_returns']['motion_early'])
        self.assertFalse(r['conditional_returns']['predicate'])

    def test_missing_first_global_read_preserves_first_coordinate_write(self):
        f,_=fixture();del f['report']['post_cells'][str(GLOBAL+32)];r=run(f)
        self.assertEqual(r['boundary']['site'],T+28)
        self.assertEqual(mem(r)[E-40]|mem(r)[E-39]<<8,88)
        self.assertFalse(r['conditional_returns']['transform'])

    def test_missing_second_global_preserves_first_output_and_initial_second_output(self):
        f,_=fixture();del f['report']['post_cells'][str(GLOBAL+35)];r=run(f)
        self.assertEqual(r['boundary']['site'],T+48)
        self.assertEqual(mem(r)[E-40]|mem(r)[E-39]<<8,1088)
        self.assertEqual(mem(r)[E-38]|mem(r)[E-37]<<8,(-223)&65535)

    def test_output_over_c918_saved_return_corrupts_actual_BX_word(self):
        f,_=fixture();d=direct(f);d['registers'][3]=words._pointer(E-104)
        r=continuation.derive(**d)
        self.assertEqual(r['boundary']['site'],T+66)
        self.assertIn('return word',r['boundary']['reason'])
        self.assertFalse(r['conditional_returns']['transform'])

    def test_output_over_saved_R4_is_observed_by_the_helper_consumer(self):
        f,_=fixture();d=direct(f);d['registers'][3]=words._pointer(E-92)
        r=continuation.derive(**d)
        self.assertTrue(r['conditional_returns']['transform']);self.assertTrue(r['conditional_returns']['coordinate'])
        self.assertEqual(r['boundary']['site'],H+134)
        self.assertIn('provenance',r['boundary']['reason'])

    def test_overlapping_output_pointers_use_real_ordered_halfword_writes(self):
        f,_=fixture();d=direct(f);put(d['cells'],E-100,words._pointer(E-40))
        r=continuation.derive(**d)
        self.assertTrue(r['conditional_returns']['transform'])
        self.assertEqual(mem(r)[E-40]|mem(r)[E-39]<<8,1777)
        self.assertEqual(r['boundary']['site'],H+142)
        self.assertIn('opaque',r['boundary']['reason'])

    def test_opaque_output_pointer_never_becomes_address(self):
        f,_=fixture();d=direct(f);put(d['cells'],E-100,opaque('unknown y output'))
        r=continuation.derive(**d);self.assertEqual(r['boundary']['site'],T+46)
        self.assertIn('provenance',r['boundary']['reason'])

    def test_numeric_output_pointer_never_becomes_address(self):
        f,_=fixture();d=direct(f);d['registers'][3]=words._constant(BASE+E-40)
        r=continuation.derive(**d);self.assertEqual(r['boundary']['site'],T+24)
        self.assertIn('provenance',r['boundary']['reason'])

    def test_protected_first_output_store_stops_before_global_read(self):
        f,_=fixture();f['protected_spans']=((E-40,E-38),);r=run(f)
        self.assertEqual(r['boundary']['site'],T+24)
        self.assertFalse(any(e['site']==T+28 for e in r['memory_events']))

    def test_retired_output_target_refuses_even_if_old_scalar_bytes_exist(self):
        f,_=fixture();d=direct(f);d['retired_spans']=((E-40,E-38),)
        r=continuation.derive(**d);self.assertEqual(r['boundary']['site'],T+24)
        self.assertIn('retired',r['boundary']['reason'])

    def test_byte_budget_refuses_before_new_push_writes(self):
        f,_=fixture();d=direct(f);at=100000
        while len(d['cells'])<4096:d['cells'][at]=0;at+=1
        r=continuation.derive(**d);self.assertEqual(r['boundary']['site'],T)
        self.assertEqual(r['changed_cells'],{});self.assertEqual(r['memory_events'],[])

    def test_partial_c918_save_alias_makes_reloaded_high_register_explicit(self):
        f,_=fixture();d=direct(f);d['registers'][3]=words._pointer(E-124)
        r=continuation.derive(**d)
        self.assertTrue(r['conditional_returns']['transform'])
        self.assertNotEqual(r['registers'][8],d['registers'][8])
        self.assertFalse(r['ABI_preservation_assumed'])

    def test_real_callee_stack_words_are_read_after_actual_pushes(self):
        f,_=fixture();r=run(f)
        reads=[e for e in r['memory_events'] if e['site'] in (T+6,T+10)]
        self.assertEqual([e['coordinate'] for e in reads],[E-100,E-96])
        self.assertEqual(reads[0]['bytes'],words._pointer(E-38))
        self.assertEqual(reads[1]['bytes'],words._pointer(E-36))

    def test_motion_unknown_comparison_global_does_not_force_early_return(self):
        f,_=fixture();f['report']['post_cells'][str(GLOBAL+36)]=('opaque-byte','unknown motion x',0)
        r=run(f);self.assertEqual(r['boundary']['site'],B+52)
        self.assertFalse(r['conditional_returns']['motion_early'])

    def test_motion_second_comparison_is_a_fresh_distinct_read(self):
        f,_=fixture();del f['report']['post_cells'][str(GLOBAL+39)]
        r=run(f);self.assertEqual(r['boundary']['site'],B+64)
        self.assertFalse(r['conditional_returns']['motion_early'])

    def test_predicate_frame_reuses_retired_coordinates_without_old_initialization(self):
        f,_=fixture();r=run(f)
        self.assertTrue(r['reaches_helper_scheduler_call'])
        self.assertTrue(any(e['operation']=='allocate-frame' and e['coordinates']==[E-128,E-112] for e in r['memory_events']))
        self.assertEqual(mem(r)[E-128][0],'opaque-byte')
        self.assertTrue(any(lo<=E-128<hi for lo,hi in r['retired_spans']))

    def test_adapter_rejects_mixed_context_without_replaying075(self):
        f,_=fixture();f['report']['complete_owner_pins'][0]['sha256']='0'*64
        with self.assertRaises(ValueError):run(f)
        f,_=fixture();f['report']['nested_call_cutpoint']['register_arguments'][0]=words._constant(7)
        with self.assertRaises(ValueError):run(f)

    def test075_report_and_initial_state_remain_immutable(self):
        f,_=fixture();saved=copy.deepcopy(f);r=run(f);self.assertEqual(f,saved)
        for key in ['fabricated_callee_effects','fabricated_saved_words','output_initialization_assumed',
                    'role_separation_assumed','ABI_preservation_assumed','actual_reaching_state_proved',
                    'physical_access_proved','actual_heap_or_SP_proved','actual_lifetime_proved',
                    'actual_code_execution_proved','actual_termination_proved','returns_to_root',
                    'full_CFG_closed','source_or_ELF_admission','native_admission']:
            self.assertFalse(r[key],key)

    def test_six_new_raw_post075_return_and_motion_paths(self):
        cases=[dict(),dict(match=False),dict(x=-32768,y=-1,z=32767,dx=65535,dy=65534),
               dict(x=32767,y=-32768,z=-32768,dx=0,dy=0),dict(x=5,y=7,z=9,dx=120,dy=96),
               dict(x=-17,y=-19,z=-21,dx=31,dy=47,match=False)]
        for options in cases:
            with self.subTest(options=options):
                f,_=fixture(**options);d=direct(f);r=run(f)
                regs,memory,trace,events,pc=raw(d)
                self.assertEqual(r['registers'],regs);self.assertEqual(mem(r),memory)
                self.assertEqual(r['trace'],trace);self.assertEqual(r['boundary']['site'],pc)
                actual=[(e['site'],e['operation'],e['coordinate'],e['bytes']) for e in r['memory_events'] if e['operation'].startswith(('read16','read32','write'))]
                self.assertEqual(actual,events)

    def test_large_motion_differences_wrap_before_actual_sqrt_entry(self):
        for global_x,global_y in [(-32768,32767),(32767,-32768),(0,0)]:
            f,_=fixture()
            state=mem(f['report']);half(state,GLOBAL+36,global_x);half(state,GLOBAL+38,global_y)
            f['report']['post_cells']={str(k):v for k,v in state.items()}
            r=run(f);dx=signed16(global_x-968);dy=signed16(1681-global_y)
            self.assertEqual(r['boundary']['site'],SQRT)
            self.assertEqual(r['registers'][0],words._constant(((dx*dx+dy*dy)<<8)&0xffffffff))
            regs,memory,trace,_,pc=raw(direct(f))
            self.assertEqual(r['registers'],regs);self.assertEqual(mem(r),memory)
            self.assertEqual(r['trace'],trace);self.assertEqual(r['boundary']['site'],pc)


class BindingTests(unittest.TestCase):
    def test_new_complete_owner_composition_binding(self):
        l=layout();self.assertEqual(continuation.bind(l.helper,l.transform_data,l.transform,l.predicate_data,l.predicate,
            l.motion_data,l.motion,selector=continuation.SELECTOR),l)

    def test_actual_literals_bodies_calls_and_returns_are_guarded(self):
        l=layout()
        for name,offset in [('transform_data',24),('transform_data',66),('predicate_data',18),('predicate_data',34),
                            ('motion_data',76),('motion_data',236),('motion_data',250)]:
            data=bytearray(getattr(l,name));data[offset]^=1
            with self.assertRaises(ValueError):continuation._validate(replace(l,**{name:bytes(data)}))

    def test_complete_owner_overlap_is_rejected(self):
        l=layout()
        with self.assertRaisesRegex(ValueError,'overlap'):continuation._validate(replace(l,transform=l.helper.helper))

    def test_selector_and_coordinate_input_shapes_remain_explicit(self):
        l=layout()
        with self.assertRaises(ValueError):continuation.bind(l.helper,l.transform_data,l.transform,l.predicate_data,l.predicate,l.motion_data,l.motion,selector='default')
        f,_=fixture();d=direct(f)
        for changes in [dict(registers={}),dict(arena_base=True),dict(helper_entry_sp=E+2),dict(cells={0:True})]:
            with self.assertRaises(ValueError):continuation.derive(**dict(d,**changes))


if __name__=='__main__':unittest.main()
