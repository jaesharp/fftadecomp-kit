"""New084 post-SVC suffix states; BIOS execution is deliberately absent."""
from dataclasses import replace
import unittest,hashlib,json,os
from pathlib import Path
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_source_callback_suffix as model
upstream=model.source083
BASE,T,PAYLOAD,SUBJECT,PARENT,SCHED=0x02000000,10000,140,6000,8000,5000
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

def layout(shift=0):
    p=source_layout(shift);h=0x081C0000+shift;g=h+0x400;coord=h+0x800;bios=0x0814186C+shift
    identity=upstream._validate(p)['identity'][0]
    b=bytearray(model.helper075.HELPER)
    for off in model.helper075.CALL_OFFSETS:
        target=g if off==114 else coord if off==130 else p.scheduler.address if off==266 else h+0x1000+off
        b[off:off+4]=model.removal._bl(h+off,target)
    b[80:84]=(h+84).to_bytes(4,'little')
    for i,off in enumerate(model.helper075.TABLE_OFFSETS):b[84+4*i:88+4*i]=(h+off).to_bytes(4,'little')
    b[288:292]=(upstream._validate(p)['callback'][0]|1).to_bytes(4,'little')
    getter=model.helper075.GETTER[:2]+model.removal._bl(g+2,identity)+model.helper075.GETTER[6:]
    cd=model.helper075.COORDINATES[:28]+model.removal._bl(coord+28,h+0x2000)+model.helper075.COORDINATES[32:]
    helper=model.helper075.Layout(h,bytes(b),g,getter,identity,b'\x70\x47',coord,cd)
    cb=bytearray(p.callback_data);cb[120:124]=model.removal._bl(p.callback+120,bios);cb[138:142]=model.removal._bl(p.callback+138,h)
    p=replace(p,callback_data=bytes(cb))
    return model.Layout(p,helper,bios,b'\x0b\xdf\x70\x47')

def fixture():
    l=layout();m={T-72+i:('opaque-byte','084 actual prior local',i) for i in range(52)}
    put(m,PAYLOAD+72,P(SUBJECT));point=int.from_bytes(l.helper.helper_data[284:288],'little');put(m,point-BASE,P(SCHED))
    r={i:O('084 explicitly supplied post-SVC R'+str(i)) for i in range(15)}
    r.update({6:P(PAYLOAD),8:P(PARENT),13:P(T),14:I(l.prior.callback+124|1)})
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR,literal_points=(point,))

def raw(f,stop_before=None):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for a,b in model._validate(f['layout']).values()};regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
    mem={f['arena_base']+k:byte(v,f['arena_base']) for k,v in f['cells'].items()};pc=f['layout'].bios+2;events=[];trace=[]
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
        if pc==f['layout'].prior.scheduler.address:break
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
class PostSvcSuffixTests(unittest.TestCase):
    def assert_raw(self,f,r,stop_before=None):
        regs,mem,trace,events,pc=raw(f,stop_before)
        self.assertEqual(r['trace'],trace);self.assertEqual(r['final_PC'],pc)
        self.assertEqual({k:number(v,f['arena_base']) for k,v in r['registers'].items()},regs)
        got=memory(r)
        for a,v in mem.items():self.assertEqual(byte(got[a-f['arena_base']],f['arena_base']),v,(hex(a),v))
        actual=[(e['site'],e['operation'],e['coordinate'],tuple(byte(v,f['arena_base']) for v in e['bytes'])) for e in r['memory_events'] if 'coordinate' in e]
        self.assertEqual(actual,events)
    def derive(self,f):return model.derive_postsvc(**f)
    def scheduler(self,f,r):
        self.assertEqual(r['final_PC'],f['layout'].prior.scheduler.address,r['boundary']);self.assert_raw(f,r)
        self.assertTrue(r['observed_wrapper_BX_return']);self.assertFalse(r['actual_BIOS_effects_executed']);self.assertFalse(r['actual_BIOS_poststate_proved'])

    def test_explicit_postsvc_unknown_volatile_words_reach_real_count12(self):
        f=fixture();r=self.derive(f);self.scheduler(f,r);m=memory(r);l=f['layout']
        self.assertEqual(r['registers'][0],P(SCHED));self.assertEqual(r['registers'][1],I(upstream._validate(l.prior)['callback'][0]|1));self.assertEqual(r['registers'][2],I(12));self.assertEqual(r['registers'][3],P(T-68))
        self.assertEqual(r['registers'][13],P(T-72));self.assertEqual(r['registers'][14],I(l.helper.helper+270|1))
        self.assertEqual(tuple(m[T-64+i] for i in range(4)),P(T-28));self.assertEqual(tuple(m[T-72+i] for i in range(4)),P(PARENT))
        self.assertEqual(tuple(m[T-28+i] for i in range(3)),(0,0,2));self.assertEqual(m[T-25],f['cells'][T-25])
        self.assertEqual(tuple(m[T+i] for i in range(4)),f['registers'][4]);self.assertEqual(tuple(m[T-20+i] for i in range(4)),f['registers'][4])
        self.assertFalse(r['ABI_preservation_assumed']);self.assertFalse(r['native_admission'])
        artifact('new-postsvc-suffix.json',r)

    def test_postsvc_payload_and_sp_changes_are_observed_without_preservation(self):
        f=fixture();delta=200;f['registers'][6]=P(PAYLOAD+1000);f['registers'][13]=P(T+delta)
        put(f['cells'],PAYLOAD+1072,O('changed actual subject'))
        for i in range(52):f['cells'][T+delta-72+i]=('opaque-byte','new post-BIOS frame',i)
        r=self.derive(f);self.scheduler(f,r)
        self.assertEqual(r['registers'][6],O('changed actual subject'));self.assertEqual(r['postsvc_entry_SP'],T+delta)
        self.assertEqual(r['registers'][3],P(T+delta-68))

    def test_opaque_postsvc_payload_register_does_not_use_presvc_alias(self):
        f=fixture();f['registers'][6]=O('clobbered payload');r=self.derive(f)
        self.assertEqual(r['boundary']['site'],f['layout'].prior.callback+124);self.assertIn('provenance',r['boundary']['reason'])
        self.assertTrue(r['observed_wrapper_BX_return']);self.assertFalse(r['actual_BIOS_poststate_proved'])

    def test_unknown_postsvc_lr_does_not_assume_ordinary_return(self):
        f=fixture();f['registers'][14]=O('clobbered BIOS LR');r=self.derive(f)
        self.assertEqual(r['boundary']['site'],f['layout'].bios+2);self.assertFalse(r['observed_wrapper_BX_return']);self.assertIn('scalar',r['boundary']['reason'])

    def test_wrong_tagged_postsvc_return_target_is_refused(self):
        f=fixture();f['registers'][14]=I(f['layout'].prior.callback+126|1);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],f['layout'].bios+2);self.assertIn('LR',r['boundary']['reason'])

    def test_nonzero_postsvc_r4_is_transported_without_phase_assumption(self):
        f=fixture();f['registers'][4]=I(0xA1B2C3D4);r=self.derive(f);self.scheduler(f,r)
        self.assertEqual(tuple(memory(r)[T+i] for i in range(4)),I(0xA1B2C3D4));self.assertEqual(r['registers'][5],I(0xA1B2C3D4))

    def test_opaque_postsvc_parent_is_forwarded_without_pointer_facts(self):
        f=fixture();f['registers'][8]=O('clobbered parent');r=self.derive(f);self.scheduler(f,r)
        self.assertEqual(tuple(memory(r)[T-72+i] for i in range(4)),O('clobbered parent'))

    def test_payload_read_precedes_aliasing_stack_argument_store(self):
        f=fixture();f['registers'][6]=P(T-72);put(f['cells'],T,P(SUBJECT));r=self.derive(f);self.scheduler(f,r)
        self.assertEqual(r['registers'][6],P(SUBJECT));self.assertEqual(tuple(memory(r)[T+i] for i in range(4)),f['registers'][4])

    def test_helper_push_alias_changes_later_fixed_scheduler_load(self):
        f=fixture();point=f['literal_points'][0]-BASE;f['registers'][13]=P(point+20)
        for i in range(52):f['cells'][point+20-72+i]=('opaque-byte','aliased helper local',i)
        r=self.derive(f);self.scheduler(f,r)
        self.assertEqual(r['registers'][0],f['registers'][4]);self.assertFalse(r['physical_access_proved'])

    def test_known_private_record_bytes_preserve_unmasked_high_byte(self):
        f=fixture();put(f['cells'],T-28,I(0xAABBCCDD));r=self.derive(f);self.scheduler(f,r)
        self.assertEqual(tuple(memory(r)[T-28+i] for i in range(4)),I(0xAA020000))

    def test_pointer_fragments_in_private_record_remain_fragments(self):
        f=fixture();put(f['cells'],T-28,P(SUBJECT));r=self.derive(f);self.scheduler(f,r)
        self.assertEqual(tuple(memory(r)[T-28+i] for i in range(4)),(0,0,2,P(SUBJECT)[3]))
        self.assertEqual(model.words.observe(tuple(memory(r)[T-28+i] for i in range(4)))['kind'],'opaque-or-partial')

    def test_missing_private_bytes_stay_unknown_except_executed_mask_bits(self):
        f=fixture()
        for i in range(52):del f['cells'][T-72+i]
        r=self.derive(f);self.assertEqual(r['final_PC'],f['layout'].prior.scheduler.address,r['boundary']);m=memory(r)
        self.assertEqual(tuple(m[T-28+i] for i in range(3)),(0,0,2));self.assertEqual(m[T-25][0],'opaque-byte')
        self.assertTrue(all(type(m[T-68+i]) is tuple for i in range(4)))

    def test_literal_point_permission_is_not_inferred(self):
        f=fixture();f['literal_points']=();r=self.derive(f)
        self.assertEqual(r['boundary']['site'],f['layout'].helper.helper+254);self.assertIn('provenance',r['boundary']['reason'])

    def test_missing_actual_scheduler_point_byte_stops(self):
        f=fixture();del f['cells'][f['literal_points'][0]-BASE+1];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],f['layout'].helper.helper+254);self.assertIn('reaching',r['boundary']['reason'])

    def test_callback_argument_store_observes_protected_span(self):
        f=fixture();f['protected_spans']=((T,T+4),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],f['layout'].prior.callback+128);self.assertIn('protected',r['boundary']['reason'])

    def test_helper_mask_store_observes_protected_record(self):
        f=fixture();f['protected_spans']=((T-28,T-24),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],f['layout'].helper.helper+40);self.assertIn('protected',r['boundary']['reason'])

    def test_retired_stack_is_reused_only_by_actual_allocations(self):
        f=fixture();f['retired_stack_spans']=((T-72,T),);r=self.derive(f);self.scheduler(f,r)
        self.assertEqual(r['retired_spans'],[])

    def test_released_payload_cannot_be_reactivated_as_helper_local(self):
        f=fixture();f['released_payload_spans']=((T-72,T-20),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],f['layout'].helper.helper+2);self.assertIn('retired',r['boundary']['reason'])

    def test_missing_payload_word_does_not_get_bios_copy_initialization(self):
        f=fixture();del f['cells'][PAYLOAD+73];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],f['layout'].prior.callback+124);self.assertIn('reaching',r['boundary']['reason'])

    def test_numeric_sp_wrap_is_refused_before_memory(self):
        f=fixture();f['registers'][13]=P(-BASE-4);r=self.derive(f)
        self.assertIn('wraps',r['boundary']['reason']);self.assertEqual(r['trace'],[])

    def test_bounded_suffix_stops_without_claiming_scheduler(self):
        f=fixture();f['max_steps']=3;r=self.derive(f)
        self.assertIn('budget',r['boundary']['reason']);self.assertEqual(len(r['trace']),3);self.assertIsNone(r['nested_call_cutpoint'])

    def test_mutable_bios_body_is_not_immutable_binding(self):
        f=fixture();f['layout']=replace(f['layout'],bios_data=bytearray(b'\x0b\xdf\x70\x47'))
        with self.assertRaisesRegex(ValueError,'complete SVC'):self.derive(f)

    def test_changed_bios_instruction_is_not_accepted_by_address(self):
        f=fixture();f['layout']=replace(f['layout'],bios_data=b'\x0c\xdf\x70\x47')
        with self.assertRaisesRegex(ValueError,'complete SVC'):self.derive(f)

    def test_changed_complete_helper_body_is_rejected(self):
        f=fixture();b=bytearray(f['layout'].helper.helper_data);b[200]^=1;f['layout']=replace(f['layout'],helper=replace(f['layout'].helper,helper_data=bytes(b)))
        with self.assertRaisesRegex(ValueError,'shape'):self.derive(f)

    def test_generic_relocated_binding_and_suffix(self):
        f=fixture();l=layout(0x60000);f['layout']=model.bind(l.prior,l.helper,l.bios,l.bios_data,selector=model.SELECTOR);f['registers'][14]=I(l.prior.callback+124|1)
        r=self.derive(f);self.scheduler(f,r)

    def interface_shape(self):
        # Synthetic pre-call interface only; it is not a fabricated BIOS result.
        l=layout();r={i:O('083 pre-call R'+str(i)) for i in range(15)};c=l.prior.callback
        r.update({0:I(0x03003920),1:P(PAYLOAD+16),2:I(16),6:P(PAYLOAD),13:P(T),14:I(c+124|1)})
        owners=upstream._validate(l.prior);pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(owners.items())]
        report=dict(schema=upstream.SELECTOR,complete_owner_pins=pins,final_PC=l.bios,registers=r,obligations=['retained conditional BIOS gap'],
            nested_call_cutpoint=dict(call_site=c+120,target=l.bios,callee_executed=False,SP=T,return_word=I(c+124|1),register_arguments={i:r[i] for i in range(4)}))
        return l,report

    def test_interface_reports_numeric_spans_but_supplies_no_poststate(self):
        l,report=self.interface_shape();r=model.requirements_from_083(l,BASE,report,selector=model.SELECTOR)
        self.assertEqual(r['source_numeric_span'],[0x03003920,0x03003940]);self.assertEqual(r['destination_numeric_span'],[BASE+156,BASE+188]);self.assertIsNone(r['poststate']);self.assertIsNone(r['BIOS_effects']);self.assertIsNone(r['register_preservation']);self.assertFalse(r['BIOS_copy_proved'])
        artifact('open-bios-interface.json',r)

    def test_interface_rejects_changed_control_even_with_consistent_arguments(self):
        l,report=self.interface_shape();report['registers'][2]=I(8);report['nested_call_cutpoint']['register_arguments'][2]=I(8)
        with self.assertRaisesRegex(ValueError,'32-byte'):model.requirements_from_083(l,BASE,report,selector=model.SELECTOR)

    def test_interface_does_not_accept_shifted_payload_destination(self):
        l,report=self.interface_shape();report['registers'][1]=P(PAYLOAD+20);report['nested_call_cutpoint']['register_arguments'][1]=P(PAYLOAD+20)
        with self.assertRaisesRegex(ValueError,'32-byte'):model.requirements_from_083(l,BASE,report,selector=model.SELECTOR)

    def test_interface_does_not_promote_numeric_overlap_to_separation(self):
        l,report=self.interface_shape();p=0x03003920-BASE-16;report['registers'][6]=P(p);report['registers'][1]=P(p+16);report['nested_call_cutpoint']['register_arguments'][1]=P(p+16)
        r=model.requirements_from_083(l,BASE,report,selector=model.SELECTOR);self.assertTrue(r['numeric_overlap']);self.assertFalse(r['source_readability_proved']);self.assertFalse(r['destination_writability_proved'])

    def test_interface_rejects_stale_owner_pin(self):
        l,report=self.interface_shape();report['complete_owner_pins'][0]['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'CpuSet-entry'):model.requirements_from_083(l,BASE,report,selector=model.SELECTOR)

    def test_old_selector_cannot_enable_suffix(self):
        f=fixture();f['selector']=upstream.SELECTOR
        with self.assertRaisesRegex(ValueError,'084'):self.derive(f)
