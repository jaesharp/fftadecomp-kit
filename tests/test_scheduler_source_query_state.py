"""New082 source/predicate states and independent concrete Thumb oracle."""
from dataclasses import replace
import unittest,hashlib,json
from pathlib import Path
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_source_query_state as model


def artifact(name, value):
    out = Path(__file__).resolve().parents[1] / 'build'
    if out.is_dir():
        (out / name).write_text(json.dumps(value, indent=2) + '\n')


BASE,R,REQUEST,PAYLOAD,SUBJECT,PARENT=0x02000000,10000,11000,12000,13000,14000
I=model.words._constant;P=model.words._pointer

def O(name):return tuple(('opaque-byte',name,i) for i in range(4))
def put(m,a,w):m.update({a+i:v for i,v in enumerate(w)})
def half(m,a,v):put(m,a,tuple((v&65535).to_bytes(2,'little')))
def memory(r):return {int(k):v for k,v in r['post_cells'].items()}
def byte(v,base=BASE):
    if type(v) is int:return v
    if v[0]=='base-plus-byte':return ((base+v[1])>>(8*v[2]))&255
    return hashlib.sha256((v[1]+':'+str(v[2])).encode()).digest()[0]
def number(w,base=BASE):return int.from_bytes(bytes(byte(v,base) for v in w),'little')
def at(l,name,off=0):
    return next(a for n,a,b in (*l.prior.owners,*l.dependencies) if n==name)+off

def layout(shift=0):
    addresses={n:0x08160000+shift+i*0x400 for i,n in enumerate(sorted(model.phase081.SHAPES))}
    deps={n:0x08168000+shift+i*0x400 for i,n in enumerate(sorted(model.SHAPES))};owners=[];extra=[]
    for name,shape in model.phase081.SHAPES.items():
        a=addresses[name];b=bytearray(shape)
        for off,target in model.phase081.EDGES.get(name,{}).items():
            t=addresses[target] if target else 0x08172000+shift+off
            if name=='next':t=deps['predicate' if off==16 else 'wrapper']
            b[off:off+4]=model.removal._bl(a+off,t)
        owners.append((name,a,bytes(b)))
    for name,shape in model.SHAPES.items():
        a=deps[name];b=bytearray(shape)
        for off,target in model.EDGES.get(name,{}).items():
            b[off:off+4]=model.removal._bl(a+off,deps[target] if target else 0x08005954)
        extra.append((name,a,bytes(b)))
    return model.Layout(model.phase081.Layout(tuple(owners)),tuple(extra))

def fixture(flags=0,value=0,subject=SUBJECT):
    l=layout();regs={i:O('082 source R'+str(i)) for i in range(15)}
    regs.update({0:P(subject),1:I(5),2:I(0),3:P(PAYLOAD+3),4:P(PAYLOAD),5:P(REQUEST),6:P(PARENT),13:P(R-52),14:I(at(l,'root',124)|1)})
    m={};half(m,subject+4,flags);m[subject+704]=value;half(m,REQUEST,256);put(m,R-52,P(PARENT))
    for a,w in [(R-16,O('082 root incoming R4')),(R-12,O('082 root incoming R5')),(R-8,O('082 root incoming R6')),(R-4,I(0x08024681))]:put(m,a,w)
    return dict(layout=l,arena_base=BASE,cells=m,registers=regs,root_entry_sp=R,root_return_word=I(0x08024681),selector=model.SELECTOR)

def raw(f,stop_before=None):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for _,a,b in (*f['layout'].prior.owners,*f['layout'].dependencies)};regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
    mem={f['arena_base']+k:byte(v,f['arena_base']) for k,v in f['cells'].items()};pc=at(f['layout'],'next');events=[];trace=[]
    decoder=Cs(CS_ARCH_ARM,CS_MODE_THUMB);decoder.detail=True;flags=(False,False,False,False)
    names=dict(sp=13,lr=14,pc=15,sb=9,sl=10,fp=11,ip=12)
    def reg(o):
        n=decoder.reg_name(o.reg);return names.get(n,int(n[1:]) if n.startswith('r') else -1)
    def val(o):return o.imm if o.type==2 else regs[reg(o)]
    def read(a,w):
        v=tuple(mem[a+i] for i in range(w));events.append((pc,'read'+str(8*w),a-f['arena_base'],v));return int.from_bytes(bytes(v),'little')
    def write(a,w,v):
        b=tuple((v&0xffffffff).to_bytes(4,'little')[:w]);mem.update({a+i:x for i,x in enumerate(b)});events.append((pc,'write'+str(8*w),a-f['arena_base'],b))
    def arithmetic(a,b,sub):
        v=(a-b if sub else a+b)&0xffffffff
        return v,(bool(v&0x80000000),v==0,a>=b if sub else a+b>0xffffffff,bool(((a^b) if sub else ~(a^b))&(a^v)&0x80000000))
    for _ in range(4096):
        if pc==stop_before:trace.append(pc);break
        owner=next((a for a,b in bodies.items() if a<=pc<a+len(b)),None)
        if owner is None:break
        i=next(decoder.disasm(bodies[owner][pc-owner:],pc,1));ops,n,nxt=i.operands,i.mnemonic,pc+i.size;trace.append(pc)
        if n=='push':
            selected=[reg(o) for o in ops];a=regs[13]-4*len(ops);values=[regs[j] for j in selected]
            for j,v in enumerate(values):write(a+4*j,4,v)
            regs[13]=a
        elif n=='pop':
            a=regs[13];values=[read(a+4*j,4) for j in range(len(ops))]
            for o,v in zip(ops,values):regs[reg(o)]=v
            regs[13]=a+4*len(ops)
        elif n in ('mov','movs'):
            d=reg(ops[0]);regs[d]=val(ops[1]);v=regs[d]
            if n=='movs':flags=(bool(v&0x80000000),v==0,flags[2],flags[3])
        elif n in ('add','adds','sub','subs'):
            d=reg(ops[0]);a=val(ops[1]) if len(ops)==3 else regs[d];b=val(ops[-1]);v,newflags=arithmetic(a,b,n.startswith('sub'));regs[d]=v
            if n.endswith('s'):flags=newflags
        elif n=='cmp':_,flags=arithmetic(val(ops[0]),val(ops[1]),True)
        elif n in ('lsls','lsrs'):
            d=reg(ops[0]);v=val(ops[1]);count=val(ops[2]);c=flags[2]
            if n=='lsls':
                if count:c=bool(v&(1<<(32-count)))
                v=(v<<count)&0xffffffff
            else:
                count=count or 32;c=bool(v&(1<<(count-1)));v>>=count
            regs[d]=v;flags=(bool(v&0x80000000),v==0,c,flags[3])
        elif n in ('orrs','ands'):
            d=reg(ops[0]);b=val(ops[1]);v=regs[d]|b if n=='orrs' else regs[d]&b;regs[d]=v;flags=(bool(v&0x80000000),v==0,flags[2],flags[3])
        elif n in ('beq','bne','bhi','bls','bge','bgt'):
            nf,z,c,v=flags
            if dict(beq=z,bne=not z,bhi=c and not z,bls=not c or z,bge=nf==v,bgt=not z and nf==v)[n]:nxt=ops[0].imm
        elif n=='b':nxt=ops[0].imm
        elif n=='bl':regs[14]=nxt|1;nxt=ops[0].imm
        elif n=='bx':nxt=regs[reg(ops[0])]&~1
        elif n in ('ldr','str','ldrb','strb','ldrh','strh'):
            width=1 if n.endswith('b') else 2 if n.endswith('h') else 4;bn=decoder.reg_name(ops[1].mem.base)
            if bn=='pc':
                a=((pc+4)&~3)+ops[1].mem.disp;regs[reg(ops[0])]=int.from_bytes(bodies[owner][a-owner:a-owner+4],'little')
            else:
                index=names.get(bn,int(bn[1:]) if bn.startswith('r') else -1);a=regs[index]+ops[1].mem.disp
                if n.startswith('ldr'):regs[reg(ops[0])]=read(a,width)
                else:write(a,width,regs[reg(ops[0])])
        else:raise AssertionError((hex(pc),n,i.op_str))
        pc=nxt
    else:raise AssertionError('raw oracle bound exhausted')
    return regs,mem,trace,events,pc


class SourceQueryTests(unittest.TestCase):
    def assert_raw(self,f,result,stop_before=None):
        regs,mem,trace,events,pc=raw(f,stop_before)
        self.assertEqual(result['trace'],trace);self.assertEqual(result['final_PC'],pc)
        self.assertEqual({k:number(v,f['arena_base']) for k,v in result['registers'].items()},regs)
        got=memory(result)
        for a,v in mem.items():self.assertEqual(byte(got[a-f['arena_base']],f['arena_base']),v,(hex(a),v))
        actual=[(e['site'],e['operation'],e['coordinate'],tuple(byte(v,f['arena_base']) for v in e['bytes'])) for e in result['memory_events'] if 'coordinate' in e]
        self.assertEqual(actual,events)
    def derive(self,f):return model.derive(**f)
    def returned(self,f,r):
        self.assertIsNone(r['boundary']);self.assertTrue(r['conditional_root_return']);self.assert_raw(f,r)
        self.assertEqual(r['registers'][13],P(R))
    def wrapper(self,f,r):
        self.assertEqual(r['final_PC'],at(f['layout'],'wrapper'));self.assertIn('independent composition',r['boundary']['reason']);self.assert_raw(f,r,r['final_PC'])

    def test_all_query_conditions_clear_returns_root_and_sets_phase_two(self):
        f=fixture();r=self.derive(f);self.returned(f,r);m=memory(r)
        self.assertEqual(tuple(m[PAYLOAD+8+i] for i in range(4)),I(0));self.assertEqual((m[REQUEST],m[REQUEST+1]),(2,0))
        self.assertEqual(r['registers'][4],O('082 root incoming R4'))

    def test_flag8_short_circuit_builds_actual84_request(self):
        f=fixture(flags=8);del f['cells'][SUBJECT+704];r=self.derive(f);self.wrapper(f,r)
        self.assertNotIn(at(f['layout'],'mask'),r['trace']);self.assertNotIn(at(f['layout'],'byte_getter'),r['trace'])
        self.assertEqual(r['registers'][1],I(84));self.assertEqual(r['registers'][2],P(R-100));self.assertEqual(r['registers'][3],P(PARENT))
        self.assertEqual(r['registers'][14],I(at(f['layout'],'next',48)|1))
        m=memory(r);self.assertEqual(tuple(m[R-96+i] for i in range(4)),P(SUBJECT));self.assertEqual(tuple(m[R-92+i] for i in range(4)),P(PAYLOAD+3))
        self.assertEqual((m[R-80],m[R-79],m[R-78],m[R-77]),(5,0,0,0))
        self.assertTrue(all(type(m[R-100+i]) is tuple and m[R-100+i][0]=='opaque-byte' for i in range(2)))

    def test_flag32_short_circuit_uses_second_real_read(self):
        f=fixture(flags=32);del f['cells'][SUBJECT+704];r=self.derive(f);self.wrapper(f,r)
        reads=[e for e in r['memory_events'] if e.get('coordinate')==SUBJECT+4 and e['operation']=='read16']
        self.assertEqual(len(reads),2);self.assertNotIn(at(f['layout'],'byte_getter'),r['trace'])

    def test_nonzero_subject_byte_uses_real_getter_chain(self):
        f=fixture(value=255);r=self.derive(f);self.wrapper(f,r)
        self.assertIn(at(f['layout'],'byte_getter'),r['trace']);self.assertEqual(r['registers'][0],I(0x080FDB99))

    def test_unrelated_flag_bits_do_not_become_blocking_effect(self):
        f=fixture(flags=0xFFD7);r=self.derive(f);self.returned(f,r)

    def test_source_push_alias_is_observed_by_predicate(self):
        f=fixture(subject=R-64);f['registers'][7]=I(8)
        r=self.derive(f);self.wrapper(f,r)
        self.assertEqual(memory(r)[R-60],8)

    def test_unknown_halfword_after_real_saved_word_alias_stops(self):
        f=fixture(subject=R-68);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'predicate',8));self.assertIn('opaque',r['boundary']['reason'])

    def test_private_stack_reuse_preserves_known_phase_bytes(self):
        f=fixture(flags=8);half(f['cells'],R-100,0xAA55);f['retired_stack_spans']=((R-120,R-52),)
        r=self.derive(f);self.wrapper(f,r)
        self.assertEqual((memory(r)[R-100],memory(r)[R-99]),(0x55,0xAA))

    def test_stack_movement_does_not_revive_released_payload(self):
        f=fixture();f['released_payload_spans']=((R-72,R-52),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'next'));self.assertIn('retired',r['boundary']['reason'])

    def test_subject_field_on_released_payload_stays_dead(self):
        f=fixture();f['released_payload_spans']=((SUBJECT,SUBJECT+800),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'predicate',8));self.assertIn('retired',r['boundary']['reason'])

    def test_uninitialized_subject_byte_is_precise_getter_boundary(self):
        f=fixture();f['cells'][SUBJECT+704]=('opaque-byte','uninitialized property',0);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'byte_getter',6));self.assertIn('opaque',r['boundary']['reason'])

    def test_missing_subject_flag_byte_is_not_initialized(self):
        f=fixture();del f['cells'][SUBJECT+5];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'predicate',8));self.assertIn('reaching',r['boundary']['reason'])

    def test_wrapper_parent_reload_uses_actual_stack_word(self):
        f=fixture(flags=8);put(f['cells'],R-52,O('actual unknown parent'));r=self.derive(f);self.wrapper(f,r)
        self.assertEqual(r['registers'][3],O('actual unknown parent'))

    def test_missing_parent_stack_argument_stops_at_source_reload(self):
        f=fixture(flags=8);del f['cells'][R-51];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'next',42));self.assertIn('reaching',r['boundary']['reason'])

    def test_descriptor_write_overlaps_protected_bytes(self):
        f=fixture(flags=8);f['protected_spans']=((R-96,R-92),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'next',32));self.assertIn('protected',r['boundary']['reason'])

    def test_root_payload_write_changes_real_saved_R4(self):
        f=fixture();f['registers'][4]=P(R-24);r=self.derive(f);self.returned(f,r)
        self.assertEqual(r['registers'][4],I(0))

    def test_root_payload_write_corrupts_real_return_word(self):
        f=fixture();f['registers'][4]=P(R-12);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'root',228));self.assertIn('Thumb tagged',r['boundary']['reason']);self.assert_raw(f,r,r['final_PC'])

    def test_root_phase_write_modifies_saved_R5_byte_tokens(self):
        f=fixture();f['registers'][5]=P(R-12);r=self.derive(f);self.returned(f,r)
        self.assertEqual(r['registers'][5][:2],(2,0));self.assertEqual(r['registers'][5][2:],O('082 root incoming R5')[2:])

    def test_root_phase_alias_to_retired_source_local_is_refused(self):
        f=fixture();f['registers'][5]=P(R-100);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'root',218));self.assertIn('retired',r['boundary']['reason'])

    def test_bad_enclosing_source_return_interface_is_rejected(self):
        f=fixture();f['registers'][14]=I(0x08000001);r=self.derive(f)
        self.assertIn('SP/LR differs',r['boundary']['reason']);self.assertEqual(r['trace'],[])

    def test_wrong_root_scalar_call_argument_is_not_assumed(self):
        f=fixture();f['registers'][1]=I(261);r=self.derive(f)
        self.assertIn('scalar arguments differ',r['boundary']['reason']);self.assertEqual(r['trace'],[])

    def test_unaligned_real_flags_read_stops(self):
        f=fixture(subject=SUBJECT+1);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'predicate',8));self.assertIn('unaligned',r['boundary']['reason'])

    def test_instruction_budget_keeps_pending_calls_and_state(self):
        f=fixture();f['max_steps']=20;r=self.derive(f)
        self.assertIn('budget',r['boundary']['reason']);self.assertEqual(len(r['trace']),20);self.assertTrue(r['pending_calls'])

    def test_changed_dependency_target_is_not_nominally_equivalent(self):
        l=layout();deps=list(l.dependencies);i=next(i for i,v in enumerate(deps) if v[0]=='predicate');n,a,b=deps[i];b=bytearray(b)
        b[4:8]=model.removal._bl(a+4,at(l,'byte_getter'));deps[i]=(n,a,bytes(b))
        with self.assertRaisesRegex(ValueError,'target'):model.bind(l.prior,tuple(deps),selector=model.SELECTOR)

    def test_complete_predicate_mutation_is_rejected(self):
        l=layout();deps=list(l.dependencies);i=next(i for i,v in enumerate(deps) if v[0]=='predicate');n,a,b=deps[i];b=bytearray(b);b[10]^=1;deps[i]=(n,a,bytes(b))
        with self.assertRaisesRegex(ValueError,'shape'):model.bind(l.prior,tuple(deps),selector=model.SELECTOR)

    def test_fresh_relocated_layout_is_generic(self):
        f=fixture();l=layout(0x20000);f['layout']=model.bind(l.prior,l.dependencies,selector=model.SELECTOR)
        f['registers'][14]=I(at(l,'root',124)|1);r=self.derive(f);self.returned(f,r)

    def test_explicit_selector_and_frame_witness_required(self):
        f=fixture();f['selector']='default'
        with self.assertRaises(ValueError):self.derive(f)
        f=fixture();f['root_entry_sp']=True
        with self.assertRaises(ValueError):self.derive(f)

    def test_new_root081_then_source082_composition_preserves_all_state(self):
        l=layout(0x30000);m={};regs={i:O('082 fresh chain R'+str(i)) for i in range(15)}
        regs.update({0:P(PARENT),1:P(REQUEST),2:P(PAYLOAD),13:P(R),14:I(0x08024681)})
        half(m,REQUEST,256);put(m,PAYLOAD+20,I(0));put(m,PAYLOAD+16,P(SUBJECT));half(m,SUBJECT+4,0);m[SUBJECT+704]=0
        before=model.phase081.derive(l.prior,BASE,m,regs,selector=model.phase081.SELECTOR)
        self.assertEqual(before['final_PC'],at(l,'next'))
        result=model.continue_from_081(l,BASE,before,R,I(0x08024681),selector=model.SELECTOR)
        self.assertTrue(result['conditional_root_return']);self.assertIsNone(result['boundary']);self.assertFalse(result['actual_081_reaching_authentication_proved'])
        self.assertEqual(result['registers'][4],regs[4]);self.assertEqual(result['registers'][5],regs[5])
        artifact('new-composed-source-return.json', result)

class InheritedStateTests(unittest.TestCase):
    assert_raw=SourceQueryTests.assert_raw

    def test_new_freed_node_source_composition_reuses_only_actual_stack(self):
        l=layout(0x40000);node,heap,scheduler,global_point=15000,14800,16000,0x8ff0
        m={};regs={i:O('082 freed chain R'+str(i)) for i in range(15)}
        regs.update({0:P(PARENT),1:P(REQUEST),2:P(PAYLOAD),13:P(R),14:I(0x08024681)})
        half(m,REQUEST,256);put(m,PAYLOAD+20,P(node));put(m,PAYLOAD+16,P(SUBJECT))
        half(m,SUBJECT+4,8);put(m,global_point,P(scheduler));put(m,scheduler,P(heap));put(m,scheduler+4,P(node))
        for a in range(heap,heap+12):m[a]=0
        for a in range(node-12,node+24):m[a]=0
        half(m,node-8,0x7373);half(m,node-6,35);half(m,node+20,2);put(m,node,I(at(l,'callback')|1))
        before=model.phase081.derive(l.prior,BASE,m,regs,selector=model.phase081.SELECTOR,
            literal_points=(BASE+global_point,),release_spans=((node,node+128),))
        self.assertEqual(before['final_PC'],at(l,'next'))
        r=model.continue_from_081(l,BASE,before,R,I(0x08024681),selector=model.SELECTOR)
        self.assertEqual(r['final_PC'],at(l,'wrapper'));self.assertIn('independent composition',r['boundary']['reason'])
        self.assertEqual(r['conditional_released_payloads'],[(node,node+128)])
        f=dict(layout=l,arena_base=BASE,cells=memory(before),registers=before['registers'])
        self.assert_raw(f,r,r['final_PC'])
        artifact('new-freed-source-entry.json', r)

    def test_new_081_adapter_rejects_missing_payload_retirement_event(self):
        l=layout();pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(model.phase081._validate(l.prior).items())]
        report=dict(schema=model.phase081.SELECTOR,complete_owner_pins=pins,final_PC=at(l,'next'),
            boundary=dict(reason='next source helper entry requires independent closure'),conditional_root_return=False,
            pending_calls=[dict(role='next',return_pc=at(l,'root',124),entry_sp=R-52)],
            conditional_released_payloads=[(15000,15128)],retired_spans=[(15000,15128)],memory_events=[])
        with self.assertRaisesRegex(ValueError,'payload retirement'):model.continue_from_081(l,BASE,report,R,I(0x08024681),selector=model.SELECTOR)

    def test_new_081_adapter_does_not_reclassify_unknown_retired_bytes(self):
        l=layout();pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(model.phase081._validate(l.prior).items())]
        report=dict(schema=model.phase081.SELECTOR,complete_owner_pins=pins,final_PC=at(l,'next'),
            boundary=dict(reason='next source helper entry requires independent closure'),conditional_root_return=False,
            pending_calls=[dict(role='next',return_pc=at(l,'root',124),entry_sp=R-52)],
            conditional_released_payloads=[],retired_spans=[(123,127)],memory_events=[])
        with self.assertRaisesRegex(ValueError,'unclassified'):model.continue_from_081(l,BASE,report,R,I(0x08024681),selector=model.SELECTOR)

if __name__=='__main__':unittest.main()
