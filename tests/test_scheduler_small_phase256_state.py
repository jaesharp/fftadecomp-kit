"""New086 phase256 helper/requester cases and independent raw oracle."""
from dataclasses import replace
import unittest,hashlib,json,os
from pathlib import Path
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_small_phase256_state as model
upstream=model.returns085.source083
BASE,E,NODE,SCHED,PAYLOAD,DESC=0x02000000,10000,140,5000,164,3000
RETURN=0x081FFFF1
I=model.words._constant;P=model.words._pointer
DEFAULT_IMAGE=Path(__file__).resolve().parents[2]/'kit-source-scheduler-candidate/inputs/source-image.bin'
IMAGE_PATH=Path(os.environ.get('FFTA_SOURCE84_IMAGE',str(DEFAULT_IMAGE)))
IMAGE=IMAGE_PATH.read_bytes() if IMAGE_PATH.is_file() else None

def artifact(name,value):
    out=Path(__file__).resolve().parents[1]/'build'
    if out.is_dir():(out/name).write_text(json.dumps(value,indent=2)+'\n')
def O(name):return tuple(('opaque-byte',name,i) for i in range(4))
def put(m,a,w):m.update({a+i:v for i,v in enumerate(w)})
def memory(r):return {int(k):v for k,v in r['post_cells'].items()}
def byte(v,base=BASE):
    if type(v) is int:return v
    if v[0]=='base-plus-byte':return ((base+v[1])>>(8*v[2]))&255
    return hashlib.sha256((v[1]+':'+str(v[2])).encode()).digest()[0]
def number(w,base=BASE):return int.from_bytes(bytes(byte(v,base) for v in w),'little')
def at(l,name,off=0):return model._validate(l)[name][0]+off

def source_layout(shift=0):
    source=upstream.source082;phase=source.phase081;state=upstream.scheduler069
    addresses={n:0x08160000+shift+i*0x400 for i,n in enumerate(sorted(phase.SHAPES))}
    deps={n:0x08168000+shift+i*0x400 for i,n in enumerate(sorted(source.SHAPES))}
    sched,aw,core,zth,cb=0x08180000+shift,0x08181000+shift,0x08182000+shift,0x08183000+shift,0x08190000+shift
    owners=[];extra=[]
    for name,shape in phase.SHAPES.items():
        a=addresses[name];b=bytearray(shape)
        for off,target in phase.EDGES.get(name,{}).items():
            t=addresses[target] if target else 0x08172000+shift+off
            if name=='next':t=deps['predicate' if off==16 else 'wrapper']
            b[off:off+4]=upstream.removal._bl(a+off,t)
        if name=='next':b[52:56]=(cb|1).to_bytes(4,'little')
        owners.append((name,a,bytes(b)))
    for name,shape in source.SHAPES.items():
        a=deps[name];b=bytearray(shape)
        for off,target in source.EDGES.get(name,{}).items():b[off:off+4]=upstream.removal._bl(a+off,deps[target] if target else sched)
        extra.append((name,a,bytes(b)))
    prior=source.Layout(phase.Layout(tuple(owners)),tuple(extra));byname={n:(a,b) for n,a,b in owners}
    sha=lambda b:hashlib.sha256(b).hexdigest()
    sl=state.split.insert.search.Layout(addresses['search'],sha(byname['search'][1]))
    ml=state.remove.Layout(addresses['remove'],addresses['median'],sha(byname['remove'][1]),sha(byname['median'][1]))
    il=state.split.insert.Layout(addresses['insert'],sha(byname['insert'][1]),sl,ml)
    al=state.split.Layout(core,sha(state.split._encoded(core,il,zth,0x0836D4BC)),il,zth,0x0836D4BC)
    wl=state.wrapper.Layout(aw,sha(state.wrapper._identity(aw,al)),al)
    schedl=state.Layout(sched,sha(state._encoded(sched,wl,addresses['thunk'])),wl,addresses['thunk'])
    data=bytearray(upstream.CALLBACK)
    for off,target in ((120,0x0814186C),(138,0x080E03F8)):data[off:off+4]=upstream.removal._bl(cb+off,target)
    return upstream.Layout(prior,schedl,cb,bytes(data),IMAGE,(upstream.image079.IMAGE_BASE|1).to_bytes(4,'little'))

def prior_layout(shift=0):
    p=source_layout(shift);h=0x081C0000+shift;g=h+0x400;coord=h+0x800;bios=0x0814186C+shift
    identity=upstream._validate(p)['identity'][0]
    b=bytearray(model.returns085.suffix084.helper075.HELPER)
    for off in model.returns085.suffix084.helper075.CALL_OFFSETS:
        target=g if off==114 else coord if off==130 else p.scheduler.address if off==266 else h+0x1000+off
        b[off:off+4]=model.removal._bl(h+off,target)
    b[80:84]=(h+84).to_bytes(4,'little')
    for i,off in enumerate(model.returns085.suffix084.helper075.TABLE_OFFSETS):b[84+4*i:88+4*i]=(h+off).to_bytes(4,'little')
    b[288:292]=(upstream._validate(p)['callback'][0]|1).to_bytes(4,'little')
    getter=model.returns085.suffix084.helper075.GETTER[:2]+model.removal._bl(g+2,identity)+model.returns085.suffix084.helper075.GETTER[6:]
    cd=model.returns085.suffix084.helper075.COORDINATES[:28]+model.removal._bl(coord+28,h+0x2000)+model.returns085.suffix084.helper075.COORDINATES[32:]
    helper=model.returns085.suffix084.helper075.Layout(h,bytes(b),g,getter,identity,b'\x70\x47',coord,cd)
    cb=bytearray(p.callback_data);cb[120:124]=model.removal._bl(p.callback+120,bios);cb[138:142]=model.removal._bl(p.callback+138,h)
    p=replace(p,callback_data=bytes(cb))
    return model.returns085.Layout(model.returns085.suffix084.Layout(p,helper,bios,b'\x0b\xdf\x70\x47'))

def layout(shift=0):
    prior=prior_layout(shift);p84=prior.prior;p83=p84.prior;p82=p83.prior;p81=p82.prior
    predicate,getter,requester=0x081D0000+shift,0x081D0400+shift,0x081D0800+shift
    owners=[]
    for n,a,b in p81.owners:
        if n=='callback':
            b=bytearray(b)
            for off,t in ((56,predicate),(84,requester)):b[off:off+4]=model.removal._bl(a+off,t)
            b=bytes(b)
        owners.append((n,a,b))
    prior=replace(prior,prior=replace(p84,prior=replace(p83,prior=replace(p82,prior=replace(p81,owners=tuple(owners))))))
    predicate_data=model.PREDICATE[:2]+model.removal._bl(predicate+2,getter)+model.PREDICATE[6:]
    requester_data=model.REQUESTER[:24]+model.removal._bl(requester+24,p83.scheduler.address)+model.REQUESTER[28:]
    return model.Layout(prior,predicate,predicate_data,getter,model.GETTER,requester,requester_data)

def half(m,a,v):put(m,a,tuple((v&65535).to_bytes(2,'little')))
def fixture(flag=0,payload_word=None,mode=2,entry_sp=E,shift=0):
    l=layout(shift);m={entry_sp-64+i:('opaque-byte','086 live stack origin',i) for i in range(64)}
    half(m,DESC,256);m[PAYLOAD+2]=mode;put(m,PAYLOAD+4,I(0x0839D7E4) if payload_word is None else payload_word)
    m[0x7F74]=flag;put(m,0xF430,P(SCHED))
    r={i:O('086 actual R'+str(i)) for i in range(15)}
    r.update({0:P(NODE),1:P(DESC),2:P(PAYLOAD),13:P(entry_sp),14:I(RETURN)})
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR,literal_points=(0x02007F74,0x0200F430))

def raw(f,stop_before=None):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for a,b in model._validate(f['layout']).values()};regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
    mem={f['arena_base']+k:byte(v,f['arena_base']) for k,v in f['cells'].items()};pc=at(f['layout'],'callback');events=[];trace=[]
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
        if pc==at(f['layout'],'scheduler'):break
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
        elif n in ('lsls','lsrs','asrs'):
            d=reg(ops[0]);v=val(ops[1]);count=val(ops[2]);c=flags[2]
            if n=='lsls':
                if count:c=bool(v&(1<<(32-count)))
                v=(v<<count)&0xffffffff
            else:
                count=count or 32;c=bool(v&(1<<(count-1)));v=(v-2**32 if v&0x80000000 else v)>>count if n=='asrs' else v>>count;v&=0xffffffff
            regs[d]=v;flags=(bool(v&0x80000000),v==0,c,flags[3])
        elif n in ('orrs','ands','eors'):
            d=reg(ops[0]);b=val(ops[1]);v=regs[d]|b if n=='orrs' else regs[d]&b if n=='ands' else regs[d]^b;regs[d]=v;flags=(bool(v&0x80000000),v==0,flags[2],flags[3])
        elif n=='rsbs':
            d=reg(ops[0]);v,flags=arithmetic(0,val(ops[1]),True);regs[d]=v
        elif n in ('beq','bne','bhi','bls','bge','bgt','blt','ble','bhs','blo'):
            nf,z,c,v=flags
            if dict(beq=z,bne=not z,bhi=c and not z,bls=not c or z,bge=nf==v,bgt=not z and nf==v,blt=nf!=v,ble=z or nf!=v,bhs=c,blo=not c)[n]:nxt=ops[0].imm
        elif n=='b':nxt=ops[0].imm
        elif n=='bl':regs[14]=nxt|1;nxt=ops[0].imm
        elif n=='bx':nxt=regs[reg(ops[0])]&~1
        elif n in ('ldm','stm'):
            rn=reg(ops[0]);a=regs[rn]
            if n=='ldm':
                values=[read(a+4*j,4) for j in range(len(ops)-1)]
                for o,v in zip(ops[1:],values):regs[reg(o)]=v
            else:
                values=[regs[reg(o)] for o in ops[1:]]
                for j,v in enumerate(values):write(a+4*j,4,v)
            regs[rn]=a+4*(len(ops)-1)
        elif n in ('ldr','str','ldrb','strb','ldrh','strh'):
            width=1 if n.endswith('b') else 2 if n.endswith('h') else 4;bn=decoder.reg_name(ops[1].mem.base)
            if bn=='pc':
                a=((pc+4)&~3)+ops[1].mem.disp;regs[reg(ops[0])]=int.from_bytes(bodies[owner][a-owner:a-owner+4],'little')
            else:
                index=names.get(bn,int(bn[1:]) if bn.startswith('r') else -1);a=regs[index]+ops[1].mem.disp
                if n.startswith('ldr'):
                    regs[reg(ops[0])]=read(a,width)
                else:write(a,width,regs[reg(ops[0])])
        else:raise AssertionError((hex(pc),n,i.op_str))
        pc=nxt
    else:raise AssertionError('raw oracle bound exhausted')
    return regs,mem,trace,events,pc


@unittest.skipIf(IMAGE is None,'set FFTA_SOURCE84_IMAGE to the private authenticated176B source')
class SmallPhase256Tests(unittest.TestCase):
    def assert_raw(self,f,r,stop_before=None):
        regs,mem,trace,events,pc=raw(f,stop_before)
        self.assertEqual(r['trace'],trace);self.assertEqual(r['final_PC'],pc)
        self.assertEqual({k:number(v,f['arena_base']) for k,v in r['registers'].items()},regs)
        got=memory(r)
        for a,v in mem.items():self.assertEqual(byte(got[a-f['arena_base']],f['arena_base']),v,(hex(a),v))
        actual=[(e['site'],e['operation'],e['coordinate'],tuple(byte(v,f['arena_base']) for v in e['bytes'])) for e in r['memory_events'] if 'coordinate' in e]
        self.assertEqual(actual,events)
    def derive(self,f):return model.derive(**f)
    def returned(self,f,r):
        self.assertTrue(r['conditional_callback_return'],r['boundary']);self.assertIsNone(r['boundary']);self.assertEqual(r['pending_calls'],[])
        self.assertEqual(r['final_PC'],RETURN&~1);self.assertEqual(r['registers'][13],f['registers'][13]);self.assert_raw(f,r)
    def requested(self,f,r):
        self.assertEqual(r['final_PC'],at(f['layout'],'scheduler'),r['boundary']);self.assertEqual(r['new_scheduler_count'],40)
        self.assertFalse(r['nested_call_cutpoint']['callee_executed']);self.assert_raw(f,r)

    def test_real_predicate_nonzero_restores_callback_without_phase_write(self):
        f=fixture(flag=7);r=self.derive(f);self.returned(f,r)
        self.assertEqual((memory(r)[DESC],memory(r)[DESC+1]),(0,1));self.assertEqual(r['registers'][0],I(0))
        artifact('new-predicate-return.json',r)

    def test_zero_predicate_null_payload_word_increments_reloaded_phase(self):
        f=fixture(payload_word=I(0));r=self.derive(f);self.returned(f,r)
        self.assertEqual((memory(r)[DESC],memory(r)[DESC+1]),(1,1))

    def test_zero_mode_skips_requester_with_nonzero_literal_payload(self):
        f=fixture(mode=0);r=self.derive(f);self.returned(f,r)
        self.assertNotIn(at(f['layout'],'requester256'),r['trace']);self.assertEqual(memory(r)[DESC],1)

    def test_actual_requester_transports_sparse_descriptor_and_parent(self):
        f=fixture();r=self.derive(f);self.requested(f,r);m=memory(r)
        self.assertEqual(r['registers'][0],P(SCHED));self.assertEqual(r['registers'][1],I(0x080D791D));self.assertEqual(r['registers'][2],I(40))
        self.assertEqual(r['registers'][3],P(E-48));self.assertEqual(r['registers'][13],P(E-52));self.assertEqual(r['registers'][14],I(at(f['layout'],'requester256',28)|1))
        self.assertEqual(tuple(m[E-52+i] for i in range(4)),P(NODE));self.assertEqual(tuple(m[E-44+i] for i in range(4)),I(0x0839D7E4));self.assertEqual((m[E-28],m[E-27]),(2,0))
        self.assertEqual(tuple(m[E-48+i] for i in range(4)),tuple(f['cells'][E-48+i] for i in range(4)))
        self.assertFalse(r['physical_access_proved']);artifact('new-count40-request.json',r)

    def test_query_aliases_actual_callback_saved_return_byte(self):
        f=fixture(entry_sp=0x7F78);r=self.derive(f);self.returned(f,r)
        self.assertEqual(memory(r)[0x7F74],RETURN&255);self.assertEqual(memory(r)[DESC],0)

    def test_query_aliases_actual_nested_predicate_return_byte(self):
        f=fixture(entry_sp=0x7F88);r=self.derive(f);self.returned(f,r)
        self.assertEqual(memory(r)[0x7F74],(at(f['layout'],'callback',60)|1)&255)

    def test_phase_alias_to_nested_save_is_reloaded_before_increment(self):
        f=fixture(payload_word=I(0));f['registers'][1]=P(E-20);half(f['cells'],E-20,256)
        r=self.derive(f);m=memory(r)
        self.assertEqual(r['callback_observed_phase'],256)
        # The actual reload observes a retired callee frame, not a phase snapshot.
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback',90));self.assertIn('retired',r['boundary']['reason'])
        self.assertEqual(m[E-20]+256*m[E-19],(at(f['layout'],'callback',60)|1)&65535)
        self.assert_raw(f,r,stop_before=at(f['layout'],'callback',90))

    def test_phase_store_alias_changes_actual_restored_r6(self):
        f=fixture(payload_word=I(0));f['registers'][1]=P(E-8);f['registers'][6]=I(256)
        r=self.derive(f);self.returned(f,r);self.assertEqual(r['registers'][6],I(257))
        self.assertFalse(r['ABI_preservation_assumed'])

    def test_nonzero_predicate_never_observes_opaque_node_or_payload(self):
        f=fixture(flag=255);f['registers'][0]=O('unknown node');f['registers'][2]=O('unknown payload')
        r=self.derive(f);self.returned(f,r)

    def test_null_payload_word_skips_missing_mode_byte(self):
        f=fixture(payload_word=I(0));del f['cells'][PAYLOAD+2];r=self.derive(f);self.returned(f,r)
        self.assertFalse(any(e.get('coordinate')==PAYLOAD+2 for e in r['memory_events']))

    def test_intact_pointer_payload_is_transported_without_dereference(self):
        f=fixture(payload_word=P(9000));r=self.derive(f);self.requested(f,r)
        self.assertEqual(tuple(memory(r)[E-44+i] for i in range(4)),P(9000))
        self.assertFalse(any(e.get('coordinate')==9000 for e in r['memory_events']))

    def test_mode255_is_stored_as_actual_zero_extended_halfword(self):
        f=fixture(mode=255);r=self.derive(f);self.requested(f,r)
        self.assertEqual((memory(r)[E-28],memory(r)[E-27]),(255,0))

    def test_requester_source_alias_to_its_local_descriptor_retains_origins(self):
        f=fixture();f['registers'][2]=P(E-48);f['cells'][E-46]=2;put(f['cells'],E-44,P(9000))
        r=self.derive(f);self.requested(f,r);self.assertEqual(tuple(memory(r)[E-44+i] for i in range(4)),P(9000))

    def test_fixed_getter_point_requires_explicit_numeric_identity(self):
        f=fixture();f['literal_points']=(0x0200F430,);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'getter256',4));self.assertIn('provenance',r['boundary']['reason'])

    def test_getter_base_point_does_not_grant_adjacent_offset_permission(self):
        f=fixture();f['literal_points']=(0x02007F40,0x0200F430);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'getter256',4));self.assertIn('provenance',r['boundary']['reason'])

    def test_missing_getter_byte_stops_at_actual_load(self):
        f=fixture();del f['cells'][0x7F74];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'getter256',4));self.assertIn('reaching',r['boundary']['reason'])

    def test_opaque_getter_byte_does_not_become_boolean(self):
        f=fixture();f['cells'][0x7F74]=('opaque-byte','unknown query byte',0);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'getter256',4));self.assertIn('narrow read',r['boundary']['reason'])

    def test_retired_getter_byte_is_not_revived_by_unrelated_stack(self):
        f=fixture();f['retired_stack_spans']=((0x7F74,0x7F75),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'getter256',4));self.assertIn('retired',r['boundary']['reason'])

    def test_unknown_payload_word_stops_at_actual_null_comparison(self):
        f=fixture(payload_word=O('unknown payload word'));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback',68));self.assertIn('opaque',r['boundary']['reason'])

    def test_unknown_mode_stops_only_when_nonzero_word_path_reads_it(self):
        f=fixture();f['cells'][PAYLOAD+2]=('opaque-byte','unknown mode',0);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback',72));self.assertIn('narrow read',r['boundary']['reason'])

    def test_requester_global_pointer_load_has_its_own_literal_condition(self):
        f=fixture();f['literal_points']=(0x02007F74,);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'requester256',16));self.assertIn('provenance',r['boundary']['reason'])

    def test_missing_scheduler_pointer_origin_is_not_initialized(self):
        f=fixture();del f['cells'][0xF431];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'requester256',16));self.assertIn('reaching',r['boundary']['reason'])

    def test_wrong_phase_is_refused_after_real_save_and_phase_read(self):
        f=fixture();half(f['cells'],DESC,257);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback',8));self.assertIn('exact256',r['boundary']['reason'])
        self.assertTrue(any(e['operation']=='write32' for e in r['memory_events']))

    def test_callback_save_alias_cannot_hide_unknown_phase(self):
        f=fixture();f['registers'][1]=P(E-8);f['registers'][6]=O('unknown saved R6')
        r=self.derive(f);self.assertEqual(r['boundary']['site'],at(f['layout'],'callback',8));self.assertIn('narrow read',r['boundary']['reason'])

    def test_protected_callback_save_stops_before_query(self):
        f=fixture();f['protected_spans']=((E-16,E-12),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback'));self.assertIn('protected',r['boundary']['reason'])

    def test_released_frame_cannot_be_reactivated_by_push(self):
        f=fixture();f['released_payload_spans']=((E-16,E),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback'));self.assertIn('retired',r['boundary']['reason'])

    def test_actual_stack_reuse_preserves_live_known_local_words(self):
        f=fixture();f['retired_stack_spans']=((E-64,E),);put(f['cells'],E-48,P(8100))
        r=self.derive(f);self.requested(f,r);self.assertEqual(tuple(memory(r)[E-48+i] for i in range(4)),P(8100))

    def test_requester_sparse_store_respects_protection(self):
        f=fixture();f['protected_spans']=((E-28,E-26),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'requester256',10));self.assertIn('protected',r['boundary']['reason'])

    def test_explicit_budget_retains_partial_state_without_success_claim(self):
        f=fixture();f['max_steps']=12;r=self.derive(f)
        self.assertEqual(len(r['trace']),12);self.assertIn('budget',r['boundary']['reason']);self.assertFalse(r['conditional_callback_return'])

    def test_relocated_helpers_are_validated_by_complete_bytes_and_edges(self):
        f=fixture(shift=0x10000);l=f['layout']
        f['layout']=model.bind(l.prior,l.predicate,l.predicate_data,l.getter,l.getter_data,l.requester,l.requester_data,selector=model.SELECTOR)
        r=self.derive(f);self.requested(f,r)

    def test_changed_getter_literal_is_not_an_alias_for_current_point(self):
        f=fixture();b=bytearray(f['layout'].getter_data);b[8]^=4;f['layout']=replace(f['layout'],getter_data=bytes(b))
        with self.assertRaisesRegex(ValueError,'getter identity'):self.derive(f)

    def test_changed_requester_count_does_not_select_current_contract(self):
        f=fixture();b=bytearray(f['layout'].requester_data);b[22]=12;f['layout']=replace(f['layout'],requester_data=bytes(b))
        with self.assertRaisesRegex(ValueError,'requester identity'):self.derive(f)

    def test_selector_is_explicit_and_closed(self):
        f=fixture();f['selector']='default'
        with self.assertRaisesRegex(ValueError,'explicit086'):self.derive(f)
