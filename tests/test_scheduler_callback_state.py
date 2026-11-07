"""New shared-memory suffix states and independent raw Thumb comparisons."""
from dataclasses import replace
import hashlib
import unittest

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm import ARM_OP_IMM, ARM_OP_REG

import scheduler_callback_state as flow
import scheduler_callback_entry_state as prefix
import scheduler_copy_state as word
import allocator_remove_relation as branch
import scheduler_return_state as ret
import allocator_search_relation as search
import allocator_insert_relation as insert
import allocator_split_relation as split
import allocator_wrapper_relation as wrapper
import scheduler_allocator_state as state

C=0x08080000
H=0x08090000
E=2048
D=2304
P=4096
LR=0x080051b9


def bodies(c=C,h=H):
    b=bytearray(658);d=bytearray(292);s=flow.shapes
    b[:52]=s.DISPATCH;b[52:56]=(257).to_bytes(4,'little');b[56:76]=s.PHASE
    b[92:108]=s.COPY_FIELDS;b[116:138]=s.CALL_SETUP;b[138:142]=branch._bl(c+138,h)
    b[142:144]=b'\x68\x63';b[144:146]=(0xe000|((648-144-4)//2)).to_bytes(2,'little')
    b[148:152]=(0x08397280).to_bytes(4,'little');b[648:]=s.RETURN
    d[:30]=s.HELPER_GATE;d[270:278]=s.HELPER_RETURN
    return bytes(b),bytes(d)


def layout(c=C,h=H):
    b,d=bodies(c,h)
    return flow.Layout(c,h,b,d)


def opaque(name):return tuple(('opaque-byte',name,i) for i in range(4))


def put(m,at,value):m.update({at+i:v for i,v in enumerate(value)})


def half(m,at,value):m[at]=value&255;m[at+1]=value>>8&255


def fixture(*,payload=P,descriptor=D,phase=0,tag=158,option=1,e=E):
    saved={4:opaque('incoming4'),5:opaque('incoming5'),6:opaque('incoming6'),
           7:word._pointer(payload-24),14:word._constant(LR)}
    r={i:opaque('postprefix'+str(i)) for i in range(15)}
    r.update({0:word._pointer(payload-24),1:word._constant(phase),3:word._constant(C|1),
              4:saved[4],5:word._pointer(payload),6:word._pointer(payload-24),7:word._pointer(descriptor),
              8:word._constant(C|1),9:word._pointer(descriptor+128),10:word._pointer(e-36),
              13:word._pointer(e-36),14:saved[14]})
    m={descriptor+i:('opaque-byte','descriptor byte',i) for i in range(28)}
    half(m,descriptor,phase);half(m,descriptor+20,tag);half(m,descriptor+22,option)
    put(m,descriptor+4,word._pointer(3300))
    for i,reg in enumerate([4,5,6,7,14]):put(m,e-20+4*i,saved[reg])
    return dict(layout=layout(),registers=r,cells=m,entry_sp=e,selector=flow.SELECTOR)


def run(f=None,**kw):
    f=fixture() if f is None else f
    return flow.derive(**dict(f,**kw))


def raw(f):
    """Capstone-decoded independent execution, including actual nested saves."""
    l=f['layout'];c,h=l.callback,l.helper;r=dict(f['registers']);m=dict(f['cells']);e=f['entry_sp']
    for at in range(e-36,e-20):m[at]=('opaque-byte','unmodeled callback local',at-(e-36))
    decoder=Cs(CS_ARCH_ARM,CS_MODE_THUMB);decoder.detail=True
    pc=c+12;trace=[];written=set();comparison=None
    allowed_c=set(range(12,52,2))|set(range(56,76,2))|set(range(92,108,2))|set(range(116,140,2))|{142,144}|set(range(648,658,2))
    allowed_h=set(range(30))|set(range(270,278,2))
    def reg(operand):
        n=decoder.reg_name(operand.reg)
        return {'sp':13,'lr':14,'pc':15,'sb':9,'sl':10,'fp':11,'ip':12}.get(n,int(n[1:]) if n.startswith('r') else -1)
    def num(value):
        assert all(type(b)is int for b in value),value
        return sum(b<<(8*i) for i,b in enumerate(value))
    def addr(value):
        assert value==word._pointer(value[0][1]),value
        return value[0][1]
    def read(at,n,signed=False):
        v=tuple(m[at+i] for i in range(n))
        if n==4:return v
        x=sum(b<<(8*i) for i,b in enumerate(v))
        if signed and x&(1<<(8*n-1)):x-=1<<(8*n)
        return word._constant(x&0xffffffff)
    def write(at,n,value):
        for i in range(n):m[at+i]=value[i];written.add(at+i)
    def address(op):
        name=decoder.reg_name(op.mem.base)
        if name=='pc':return ((pc+4)&~3)+op.mem.disp
        base={'sp':13,'lr':14}.get(name,int(name[1:]) if name.startswith('r') else -1)
        out=addr(r[base])+op.mem.disp
        if op.mem.index:
            q=decoder.reg_name(op.mem.index);out+=num(r[int(q[1:])])
        return out
    for _ in range(128):
        if c<=pc<c+658:
            if pc-c not in allowed_c:return r,m,written,trace,pc
            b=l.callback_data;owner=c
        else:
            if pc-h not in allowed_h:return r,m,written,trace,pc
            b=l.helper_data;owner=h
        ins=next(decoder.disasm(b[pc-owner:pc-owner+4],pc,count=1));op=ins.operands;n=ins.mnemonic;trace.append(pc);nextpc=pc+ins.size
        if n=='movs':r[reg(op[0])]=word._constant(op[1].imm)
        elif n in ['lsls','lsrs']:
            value=num(r[reg(op[1])]);shift=op[2].imm
            r[reg(op[0])]=word._constant((value<<shift if n=='lsls' else value>>shift)&0xffffffff)
        elif n=='adds':
            if len(op)==3:
                assert op[2].imm==0;r[reg(op[0])]=r[reg(op[1])]
            else:r[reg(op[0])]=word._constant((num(r[reg(op[0])])+op[1].imm)&0xffffffff)
        elif n=='cmp':
            a=num(r[reg(op[0])]);z=op[1].imm if op[1].type==ARM_OP_IMM else num(r[reg(op[1])]);comparison=(a,z)
        elif n in ['beq','bne','bgt']:
            a,z=comparison;signed=lambda x:x-2**32 if x&0x80000000 else x
            take=(a==z) if n=='beq' else (a!=z) if n=='bne' else signed(a)>signed(z)
            if take:nextpc=op[0].imm
        elif n=='b':nextpc=op[0].imm
        elif n=='bl':r[14]=word._constant((pc+4)|1);nextpc=op[0].imm
        elif n in ['ldr','ldrb','ldrh','ldrsh']:
            at=address(op[1]);width=4 if n=='ldr' else 1 if n=='ldrb' else 2
            if decoder.reg_name(op[1].mem.base)=='pc':r[reg(op[0])]=word._constant(int.from_bytes(b[at-owner:at-owner+4],'little'))
            else:r[reg(op[0])]=read(at,width,n=='ldrsh')
        elif n in ['str','strb','strh']:write(address(op[1]),4 if n=='str' else 1 if n=='strb' else 2,r[reg(op[0])])
        elif n=='push':
            regs=[reg(x) for x in op];start=addr(r[13])-4*len(regs);values=[r[x] for x in regs]
            for i,value in enumerate(values):write(start+4*i,4,value)
            r[13]=word._pointer(start)
        elif n in ['sub','add']:
            assert reg(op[0])==13;r[13]=word._pointer(addr(r[13])+(-op[1].imm if n=='sub' else op[1].imm))
        elif n=='pop':
            nums=[reg(x) for x in op];start=addr(r[13]);values=[read(start+4*i,4) for i in range(len(nums))]
            r.update(zip(nums,values));r[13]=word._pointer(start+4*len(nums))
        elif n=='bx':
            if owner==c:return r,m,written,trace,None
            nextpc=num(r[reg(op[0])])&~1
        else:raise AssertionError((hex(pc),n,ins.op_str))
        pc=nextpc
    raise AssertionError('raw step bound')


class BindingTests(unittest.TestCase):
    def test_complete_relocated_binding(self):
        b,d=bodies(C+0x20000,H+0x20000)
        l=flow.bind(b,C+0x20000,d,H+0x20000,selector=flow.SELECTOR)
        self.assertEqual((len(l.callback_data),len(l.helper_data)),(658,292))

    def test_full_extents_selected_opcodes_and_owned_literal_refuse_mutation(self):
        b,d=bodies()
        for at in [0,12,52,56,64,92,116,138,142,144,648,656]:
            changed=bytearray(b);changed[at]^=1
            with self.subTest(at=at),self.assertRaises(ValueError):flow.bind(bytes(changed),C,d,H,selector=flow.SELECTOR)
        for at in [0,8,20,28,270,276]:
            changed=bytearray(d);changed[at]^=1
            with self.subTest(helper_at=at),self.assertRaises(ValueError):flow.bind(b,C,bytes(changed),H,selector=flow.SELECTOR)
        with self.assertRaises(ValueError):flow.bind(b[:-2],C,d,H,selector=flow.SELECTOR)

    def test_selector_and_owner_overlap_refuse(self):
        b,d=bodies()
        with self.assertRaises(ValueError):flow.bind(b,C,d,H,selector='default')
        with self.assertRaises(ValueError):flow.bind(b,C,d,C+4,selector=flow.SELECTOR)


class SharedStateTests(unittest.TestCase):
    def test_normal_path_actual_payload_and_nested_argument_effects(self):
        r=run();self.assertTrue(r['returns_to_input_continuation_under_conditions'],r['boundary'])
        self.assertEqual([r['changed_cells'][str(P+i)] for i in [2,3,4]], [1,1,0])
        self.assertEqual(tuple(r['changed_cells'][str(P+12+i)] for i in range(4)),word._pointer(3300))
        self.assertEqual(tuple(r['changed_cells'][str(P+52+i)] for i in range(4)),(0,)*4)
        self.assertTrue(r['nested_helper_early_returned']);self.assertEqual(r['registers'][7],word._pointer(P-24))
        self.assertEqual(r['registers'][13],word._pointer(E));self.assertFalse(r['actual_R7_survival_proved'])
        arg=[x for x in r['memory_events'] if x['site']==H+8][0]
        self.assertEqual((arg['coordinate'],arg['bytes']),(E-36,(0,)*4))

    def test_payload_write_changes_later_signed_tag_and_stops_real_branch(self):
        r=run(fixture(payload=D+16));self.assertFalse(r['returns_to_input_continuation_under_conditions'])
        self.assertEqual(r['boundary']['site'],C+76);self.assertEqual(r['changed_cells'][str(D+20)],0)
        self.assertFalse(r['nested_helper_entered'])

    def test_payload_write_changes_option_high_byte_before_actual_load(self):
        r=run(fixture(payload=D+20));self.assertTrue(r['returns_to_input_continuation_under_conditions'],r['boundary'])
        read=[x for x in r['memory_events'] if x['site']==C+98][0]
        self.assertEqual(read['value'],257)

    def test_payload_alias_taints_subject_pointer_without_promoting_it(self):
        r=run(fixture(payload=D+4));self.assertTrue(r['returns_to_input_continuation_under_conditions'],r['boundary'])
        value=tuple(r['changed_cells'][str(D+16+i)] for i in range(4))
        self.assertEqual(value,(('base-plus-byte',3300,0),('base-plus-byte',3300,1),1,1))
        self.assertEqual(word.observe(value)['kind'],'opaque-or-partial')

    def test_final_write_changes_saved_R7_without_ABI_repair(self):
        r=run(fixture(payload=E-60));self.assertTrue(r['returns_to_input_continuation_under_conditions'],r['boundary'])
        self.assertEqual(r['registers'][7],(0,)*4);self.assertFalse(r['register_origin_equalities']['7'])

    def test_final_write_changes_saved_return_word_and_retains_thunk_cutpoint(self):
        r=run(fixture(payload=E-56));self.assertFalse(r['returns_to_input_continuation_under_conditions'])
        self.assertTrue(r['reaches_return_thunk']);self.assertEqual(r['observed_return_word'],(0,)*4)
        self.assertEqual(r['boundary']['site'],C+656);self.assertIn('saved return word',r['boundary']['reason'])

    def test_zero_option_executes_real_helper_prologue_before_unhandled_branch(self):
        r=run(fixture(option=0));self.assertFalse(r['returns_to_input_continuation_under_conditions'])
        self.assertEqual(r['boundary']['site'],H+30);self.assertTrue(r['nested_helper_entered'])
        self.assertFalse(r['nested_helper_early_returned']);self.assertEqual(r['registers'][13],word._pointer(E-108))
        self.assertEqual(r['registers'][2],word._constant(5));self.assertIsNone(r['observed_return_word'])

    def test_option256_is_zero_after_actual_byte_truncation(self):
        r=run(fixture(option=256));self.assertEqual(r['boundary']['site'],H+30)
        self.assertEqual(r['changed_cells'][str(P+2)],0)

    def test_signed_tag_negative_stops_before_alternative_tag_body(self):
        r=run(fixture(tag=65535));self.assertEqual(r['boundary']['site'],C+76)
        self.assertEqual(r['registers'][1],word._constant(0xffffffff))

    def test_nonzero_phases_retain_actual_dispatch_cutpoints(self):
        for phase,target in [(1,152),(2,648),(256,158),(257,512),(258,584),(65535,648)]:
            with self.subTest(phase=phase):
                r=run(fixture(phase=phase));self.assertEqual(r['boundary']['site'],C+target)
                self.assertEqual(r['changed_cells'],{});self.assertFalse(r['phase0_entered'])

    def test_opaque_observed_phase_refuses_only_at_actual_CMP(self):
        f=fixture();f['registers'][1]=(('opaque-byte','observed phase',0),0,0,0);r=run(f)
        self.assertEqual(r['boundary']['site'],C+16);self.assertEqual(r['registers'][0],word._constant(256))
        self.assertEqual(r['trace'],[C+12,C+14,C+16])

    def test_observed_phase_is_not_reread_after_descriptor_bytes_change(self):
        f=fixture();half(f['cells'],D,258);r=run(f)
        self.assertTrue(r['returns_to_input_continuation_under_conditions'],r['boundary'])
        self.assertFalse(any(x.get('coordinate')==D and x['operation'].startswith('read') for x in r['memory_events']))

    def test_unknown_tag_bytes_are_not_scalar_facts(self):
        f=fixture();f['cells'][D+20]=('opaque-byte','tag',0);r=run(f)
        self.assertEqual(r['boundary']['site'],C+64);self.assertIn('opaque',r['boundary']['reason'])

    def test_numeric_descriptor_value_does_not_gain_address_provenance(self):
        f=fixture();f['registers'][7]=word._constant(D);r=run(f)
        self.assertEqual(r['boundary']['site'],C+64);self.assertIn('provenance',r['boundary']['reason'])

    def test_missing_subject_byte_does_not_get_initialized(self):
        f=fixture();del f['cells'][D+5];r=run(f)
        self.assertEqual(r['boundary']['site'],C+102);self.assertIn('missing',r['boundary']['reason'])

    def test_unmodeled_local_tag_refuses_stale_preexisting_scalar(self):
        r=run(fixture(descriptor=E-56));self.assertEqual(r['boundary']['site'],C+64)
        self.assertIn('opaque',r['boundary']['reason'])

    def test_unmodeled_local_word_transports_opaque_without_pointer_authority(self):
        f=fixture(descriptor=E-40);put(f['cells'],E-20,word._constant(0x0001009e));f['registers'][4]=word._constant(0x0001009e)
        r=run(f);self.assertTrue(r['returns_to_input_continuation_under_conditions'],r['boundary'])
        value=tuple(r['changed_cells'][str(P+12+i)] for i in range(4))
        self.assertEqual(value,tuple(('opaque-byte','unmodeled callback local',i) for i in range(4)))
        self.assertEqual(word.observe(value)['kind'],'opaque-or-partial')

    def test_unknown_local_namespace_does_not_alias_supplied_origin_name(self):
        f=fixture(descriptor=E-40);put(f['cells'],E-20,word._constant(0x0001009e));f['registers'][4]=word._constant(0x0001009e)
        f['cells'][8000]=('opaque-byte','unmodeled callback local',0);r=run(f)
        self.assertTrue(r['returns_to_input_continuation_under_conditions'],r['boundary'])
        self.assertEqual(r['changed_cells'][str(P+12)],('opaque-byte','unmodeled callback local:1',0))

    def test_explicit_protection_stops_actual_write_after_prior_effects(self):
        r=run(protected_spans=((P+12,P+16),));self.assertEqual(r['boundary']['site'],C+104)
        self.assertEqual(r['changed_cells'][str(P+3)],1);self.assertNotIn(str(P+12),r['changed_cells'])

    def test_nested_save_protection_is_checked_at_real_PUSH(self):
        r=run(protected_spans=((E-56,E-52),));self.assertEqual(r['boundary']['site'],H)
        self.assertTrue(r['nested_helper_entered']);self.assertFalse(r['nested_helper_early_returned'])

    def test_all_ambient_origins_and_SP_are_explicit(self):
        f=fixture();del f['registers'][12]
        with self.assertRaises(ValueError):run(f)
        f=fixture();f['registers'][13]=word._pointer(E-32);r=run(f)
        self.assertEqual(r['boundary']['site'],C+12);self.assertEqual(r['trace'],[])

    def test_ambient_dead_local_alias_retained_without_nonescape_claim(self):
        r=run();self.assertTrue(r['returns_to_input_continuation_under_conditions'])
        self.assertEqual(r['known_retired_alias_registers']['10'],E-36)
        self.assertFalse(r['nonescape_proved']);self.assertFalse(r['dead_bytes_erased'])

    def test_six_independent_raw_Thumb_shared_alias_executions(self):
        for i,payload in enumerate([P,D,D+4,D+20,E-60,E-56]):
            with self.subTest(i=i,payload=payload):
                f=fixture(payload=payload,option=3+2*i);f['registers'][12]=opaque('fresh raw ambient'+str(i))
                result=run(f);regs,memory,written,trace,cut=raw(f)
                self.assertEqual(regs,result['registers']);self.assertEqual(trace,result['trace'])
                self.assertEqual({str(k):memory[k] for k in written},result['changed_cells'])
                if payload==E-56:self.assertEqual(result['boundary']['site'],C+656)
                else:self.assertTrue(result['returns_to_input_continuation_under_conditions'],result['boundary'])

    def test_raw_Thumb_zero_option_cutpoint_preserves_actual_nested_state(self):
        f=fixture(option=512);result=run(f);regs,memory,written,trace,cut=raw(f)
        self.assertEqual(cut,H+30);self.assertEqual(regs,result['registers']);self.assertEqual(trace,result['trace'])
        self.assertEqual({str(k):memory[k] for k in written},result['changed_cells'])


class PrefixCompositionTests(unittest.TestCase):
    def test_two_new_primary_prefix_states_merge_changed_bytes_before_suffix(self):
        for option in [9,259]:
            with self.subTest(option=option):
                f=fixture(descriptor=E,option=option);incoming={i:opaque('fresh full entry'+str(i)) for i in range(15)}
                incoming.update({0:word._pointer(P-24),1:word._pointer(E),2:word._pointer(P),3:word._constant(C|1),
                                 7:word._pointer(P-24),10:word._pointer(E),13:word._pointer(E),14:word._constant(LR)})
                binding=prefix.Binding(C,f['layout'].callback_data,hashlib.sha256(f['layout'].callback_data).hexdigest())
                first=prefix.derive(binding,f['cells'],incoming,selector=prefix.SELECTOR)
                self.assertTrue(first['reaches_phase_comparison'],first['boundary'])
                memory=dict(f['cells']);memory.update({int(k):v for k,v in first['changed_cells'].items()})
                result=flow.derive(f['layout'],first['registers'],memory,entry_sp=first['entry_SP'],selector=flow.SELECTOR)
                self.assertTrue(result['returns_to_input_continuation_under_conditions'],result['boundary'])
                for reg in [4,5,6,7]:self.assertEqual(result['registers'][reg],incoming[reg])
                self.assertEqual(result['registers'][1],incoming[14]);self.assertEqual(result['registers'][13],incoming[13])


def return_layout():
    # Reconstruct a fresh synthetic071 identity; no old bind/derive replay.
    a=0x080a0000;s,r,m,i,c,w,t,cb=[a+n*0x1000 for n in [3,4,5,6,2,1,7,8]]
    sha=lambda b:hashlib.sha256(b).hexdigest()
    sl=search.Layout(s,sha(search.SHAPE))
    ml=branch.Layout(r,m,sha(branch.REMOVE_HEAD+branch._bl(r+124,m)+branch.REMOVE_TAIL),sha(branch.MEDIAN))
    il=insert.Layout(i,sha(insert.HEAD+branch._bl(i+22,s)+insert.MIDDLE+branch._bl(i+138,m)+insert.TAIL),sl,ml)
    al=split.Layout(c,sha(split._encoded(c,il,t,0x08304000)),il,t,0x08304000)
    wl=wrapper.Layout(w,sha(wrapper.HEAD+branch._bl(w+34,c)+wrapper.TAIL),al)
    st=state.Layout(a,sha(state._encoded(a,wl,cb)),wl,cb)
    w=a-0x1000;point=0x02008ff0
    return ret.Layout(w,sha(ret._wrapper(w,st,point)),point,st)


def through_return(payload,option):
    l=return_layout();e=E+80;f=fixture(descriptor=E,payload=payload,option=option)
    entry={i:opaque('wrapper entry'+str(i)) for i in list(range(13))+[14]}
    entry.update({0:word._constant(C|1),1:word._constant(64),2:word._pointer(2800),3:word._constant(0),
                  10:word._pointer(E),14:word._constant(0x08012345)})
    cells=dict(f['cells'])
    # These are explicit synthetic cutpoint conditions. Primary owns the real
    # entry-save transport; this test does not execute or claim that prefix.
    for at,value in ret._saved(l,entry,e).items():put(cells,at,value)
    put(cells,l.scheduler_point-0x02000000,word._pointer(7000));half(cells,7012,23)
    incoming={i:opaque('new callback entry'+str(i)) for i in range(15)}
    incoming.update({0:word._pointer(payload-24),1:word._pointer(E),2:word._pointer(payload),3:word._constant(C|1),
                     4:tuple(cells[E+16+i] for i in range(4)),5:tuple(cells[E+20+i] for i in range(4)),6:word._constant(0),
                     7:word._pointer(payload-24),8:word._constant(C|1),9:word._pointer(2800),10:word._pointer(E),
                     11:entry[11],12:entry[12],13:word._pointer(E),14:word._constant((l.callee.address+184)|1)})
    pb=prefix.Binding(C,f['layout'].callback_data,hashlib.sha256(f['layout'].callback_data).hexdigest())
    first=prefix.derive(pb,cells,incoming,selector=prefix.SELECTOR)
    assert first['reaches_phase_comparison'],first['boundary']
    cells.update({int(k):v for k,v in first['changed_cells'].items()})
    middle=flow.derive(f['layout'],first['registers'],cells,entry_sp=E,selector=flow.SELECTOR)
    assert middle['returns_to_input_continuation_under_conditions'],middle['boundary']
    post={int(k):v for k,v in middle['post_cells'].items()}
    final=ret.derive(l,0x02000000,e,payload-24,entry,middle['registers'],post,selector=ret.SELECTOR,
                     protected_spans=tuple(middle['retired_spans']))
    return middle,final,entry


class ConsumerTests(unittest.TestCase):
    def test_full_poststate_does_not_resurrect_unmodeled_local_bytes(self):
        f=fixture(option=17)
        for at in range(E-36,E-20):f['cells'][at]=255
        r=run(f);self.assertTrue(r['returns_to_input_continuation_under_conditions'],r['boundary'])
        self.assertEqual(tuple(r['post_cells'][str(E-36+i)] for i in range(4)),(0,)*4)
        self.assertEqual(r['post_cells'][str(E-28)],('opaque-byte','unmodeled callback local',8))
        self.assertNotIn(str(E-28),r['changed_cells'])

    def test_saved_origins_report_actual_corruption_separately_from_working_registers(self):
        r=run(fixture(payload=E-60,option=19))
        self.assertEqual(r['initial_saved_words']['7'],word._pointer(E-84))
        self.assertFalse(r['saved_origin_equalities']['7'])
        self.assertEqual(r['registers'][7],(0,)*4)

    def test_new_prefix_suffix_and071_consumer_restore_both_outer_frames(self):
        middle,final,entry=through_return(P+128,21)
        self.assertTrue(final['reaches_outer_return_thunk'],final['boundary'])
        for reg in [4,5,6,7,8,9]:self.assertEqual(final['registers'][reg],entry[reg])
        self.assertEqual(final['registers'][13],word._pointer(E+80))
        self.assertEqual(final['outer_return_word'],entry[14])
        self.assertFalse(final['actual_callback_return_proved']);self.assertFalse(final['native_admission'])

    def test071_consumer_rejects_actual_suffix_R7_corruption(self):
        middle,final,_=through_return(E-60,23)
        self.assertTrue(middle['returns_to_input_continuation_under_conditions'])
        self.assertFalse(final['reaches_outer_return_thunk']);self.assertIn('R7',final['boundary']['reason'])


if __name__=='__main__':unittest.main()
