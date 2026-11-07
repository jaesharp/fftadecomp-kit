"""New083 conditional states and independent Capstone concrete Thumb oracle."""
from dataclasses import replace
import unittest,hashlib,json,os
from pathlib import Path
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_source_scheduler_state as model

BASE,E,SCHED,SUBJECT,TAG,PARENT,NODE=0x02000000,10000,5000,6000,7000,8000,140
I=model.words._constant;P=model.words._pointer
IMAGE_PATH=Path(os.environ.get('FFTA_SOURCE84_IMAGE',str(Path(__file__).resolve().parents[1]/'inputs/source-image.bin')))
IMAGE=IMAGE_PATH.read_bytes() if IMAGE_PATH.is_file() else None
def artifact(name,value):
    out=Path(__file__).resolve().parents[1]/'build'
    if out.is_dir():(out/name).write_text(json.dumps(value,indent=2)+'\n')
def O(name):return tuple(('opaque-byte',name,i) for i in range(4))
def put(m,a,w):m.update({a+i:v for i,v in enumerate(w)})
def half(m,a,v):put(m,a,tuple((v&65535).to_bytes(2,'little')))
def memory(r):return {int(k):v for k,v in r['post_cells'].items()}
def byte(v,base=BASE):
    if type(v) is int:return v
    if v[0]=='base-plus-byte':return ((base+v[1])>>(8*v[2]))&255
    return hashlib.sha256((v[1]+':'+str(v[2])).encode()).digest()[0]
def number(w,base=BASE):return int.from_bytes(bytes(byte(v,base) for v in w),'little')
def at(l,name,off=0):return model._validate(l)[name][0]+off

def layout(shift=0):
    source=model.source082;phase=source.phase081;state=model.scheduler069
    addresses={n:0x08160000+shift+i*0x400 for i,n in enumerate(sorted(phase.SHAPES))}
    deps={n:0x08168000+shift+i*0x400 for i,n in enumerate(sorted(source.SHAPES))}
    sched,aw,core,zth,cb=0x08180000+shift,0x08181000+shift,0x08182000+shift,0x08183000+shift,0x08190000+shift
    owners=[];extra=[]
    for name,shape in phase.SHAPES.items():
        a=addresses[name];b=bytearray(shape)
        for off,target in phase.EDGES.get(name,{}).items():
            t=addresses[target] if target else 0x08172000+shift+off
            if name=='next':t=deps['predicate' if off==16 else 'wrapper']
            b[off:off+4]=model.removal._bl(a+off,t)
        if name=='next':b[52:56]=(cb|1).to_bytes(4,'little')
        owners.append((name,a,bytes(b)))
    for name,shape in source.SHAPES.items():
        a=deps[name];b=bytearray(shape)
        for off,target in source.EDGES.get(name,{}).items():b[off:off+4]=model.removal._bl(a+off,deps[target] if target else sched)
        extra.append((name,a,bytes(b)))
    prior=source.Layout(phase.Layout(tuple(owners)),tuple(extra));byname={n:(a,b) for n,a,b in owners}
    sha=lambda b:hashlib.sha256(b).hexdigest()
    sl=state.split.insert.search.Layout(addresses['search'],sha(byname['search'][1]))
    ml=state.remove.Layout(addresses['remove'],addresses['median'],sha(byname['remove'][1]),sha(byname['median'][1]))
    il=state.split.insert.Layout(addresses['insert'],sha(byname['insert'][1]),sl,ml)
    al=state.split.Layout(core,sha(state.split._encoded(core,il,zth,0x0836D4BC)),il,zth,0x0836D4BC)
    wl=state.wrapper.Layout(aw,sha(state.wrapper._identity(aw,al)),al)
    schedl=state.Layout(sched,sha(state._encoded(sched,wl,addresses['thunk'])),wl,addresses['thunk'])
    data=bytearray(model.CALLBACK)
    for off,target in ((120,0x0814186C),(138,0x080E03F8)):data[off:off+4]=model.removal._bl(cb+off,target)
    return model.Layout(prior,schedl,cb,bytes(data),IMAGE,(model.image079.IMAGE_BASE|1).to_bytes(4,'little'))

def fixture(size=28,parent=None,head=None):
    l=layout();m={}
    for a,n in ((0,32),(2,32),(4,1),(130,0),(134,size),(136,0),(138,0)):half(m,a,n)
    put(m,0x8FF0,P(SCHED));put(m,SCHED,P(0));put(m,SCHED+4,I(0) if head is None else P(head));half(m,SCHED+12,1)
    if parent is not None:put(m,parent+16,I(0) if head is None else P(head))
    if head is not None:put(m,head+8,I(0))
    for i in range(28):m[E+i]=('opaque-byte','083 original descriptor',i)
    put(m,E+4,P(SUBJECT));put(m,E+8,P(TAG));half(m,E+20,5);half(m,E+22,0)
    r={i:O('083 R'+str(i)) for i in range(15)}
    r.update({0:I(l.callback|1),1:I(84),2:P(E),3:I(0) if parent is None else P(parent),13:P(E),14:I(at(l,'next',48)|1)})
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR,literal_points=(0x02008FF0,))

def raw(f,stop_before=None):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for a,b in model._validate(f['layout']).values()};bodies[model.image079.IMAGE_BASE]=f['layout'].image[:50];regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
    mem={f['arena_base']+k:byte(v,f['arena_base']) for k,v in f['cells'].items()};pc=at(f['layout'],'wrapper');events=[];trace=[]
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
                    if a==f['layout'].scheduler.allocator.allocator.pointer_literal:regs[reg(ops[0])]=int.from_bytes(f['layout'].zero_pointer_data,'little')
                    else:regs[reg(ops[0])]=read(a,width)
                else:write(a,width,regs[reg(ops[0])])
        else:raise AssertionError((hex(pc),n,i.op_str))
        pc=nxt
    else:raise AssertionError('raw oracle bound exhausted')
    return regs,mem,trace,events,pc


@unittest.skipIf(IMAGE is None,'set FFTA_SOURCE84_IMAGE to the private authenticated176B source')
class SourceSchedulerTests(unittest.TestCase):
    def assert_raw(self,f,r,stop_before=None):
        regs,mem,trace,events,pc=raw(f,stop_before)
        self.assertEqual(r['trace'],trace);self.assertEqual(r['final_PC'],pc)
        self.assertEqual({k:number(v,f['arena_base']) for k,v in r['registers'].items()},regs)
        got=memory(r)
        for a,v in mem.items():self.assertEqual(byte(got[a-f['arena_base']],f['arena_base']),v,(hex(a),v))
        actual=[(e['site'],e['operation'],e['coordinate'],tuple(byte(v,f['arena_base']) for v in e['bytes'])) for e in r['memory_events'] if 'coordinate' in e]
        self.assertEqual(actual,events)
    def derive(self,f):return model.derive(**f)
    def cpuset(self,f,r):
        self.assertEqual(r['final_PC'],0x0814186C,r['boundary']);self.assertTrue(r['callback_entered']);self.assertEqual(r['callback_observed_phase'],0)
        self.assertEqual(r['registers'][0],I(0x03003920));self.assertEqual(r['registers'][1],P(NODE+40));self.assertEqual(r['registers'][2],I(16));self.assert_raw(f,r)

    def test_exact_fit112_zero_descriptor_phase_and_callback_cpuset_cutpoint(self):
        f=fixture();r=self.derive(f);self.cpuset(f,r)
        self.assertEqual([x['count'] for x in r['zero_calls']],[112]);self.assertEqual(r['wrapper_entry_SP'],E)
        m=memory(r);self.assertEqual(tuple(m[NODE+96+i] for i in range(4)),P(SUBJECT));self.assertEqual(tuple(m[NODE+36+i] for i in range(4)),P(TAG))
        self.assertEqual((m[NODE+30],m[NODE+31]),(5,0));self.assertEqual(tuple(m[E-80+i] for i in range(2)),(0,0))
        self.assertEqual(tuple(m[E+i] for i in range(2)),tuple(f['cells'][E+i] for i in range(2)))
        self.assertFalse(r['actual_installed_identity_proved']);self.assertFalse(r['native_admission'])
        artifact('new-exact-fit.json',r)

    def test_split_runs_actual_zero12_and_zero112_in_one_memory(self):
        f=fixture(size=48);r=self.derive(f);self.cpuset(f,r)
        self.assertEqual([x['count'] for x in r['zero_calls']],[12,112]);self.assertIn(at(f['layout'],'insert'),r['trace'])
        artifact('new-split.json',r)

    def test_parent_empty_child_list_uses_actual_parent_slot(self):
        f=fixture(parent=PARENT);r=self.derive(f);self.cpuset(f,r);m=memory(r)
        self.assertEqual(tuple(m[PARENT+16+i] for i in range(4)),P(NODE));self.assertEqual(tuple(m[NODE+12+i] for i in range(4)),P(PARENT))

    def test_parent_existing_child_tail_appends_in_order(self):
        f=fixture(parent=PARENT,head=9000);put(f['cells'],9008,P(9100));put(f['cells'],9108,I(0))
        r=self.derive(f);self.cpuset(f,r);m=memory(r)
        self.assertEqual(tuple(m[9108+i] for i in range(4)),P(NODE));self.assertEqual(tuple(m[NODE+4+i] for i in range(4)),P(9100))

    def test_scheduler_existing_global_tail_appends_in_order(self):
        f=fixture(head=9000);r=self.derive(f);self.cpuset(f,r)
        self.assertEqual(tuple(memory(r)[9008+i] for i in range(4)),P(NODE))

    def test_two_spare_units_follow_actual_no_split_branch(self):
        f=fixture(size=30);r=self.derive(f);self.cpuset(f,r)
        self.assertEqual([x['count'] for x in r['zero_calls']],[112]);self.assertNotIn(at(f['layout'],'insert'),r['trace'])

    def test_phase_reset_overwrites_known_source_phase_only_in_local_copy(self):
        f=fixture();half(f['cells'],E,0x0101);r=self.derive(f);self.cpuset(f,r);m=memory(r)
        self.assertEqual((m[E],m[E+1]),(1,1));self.assertEqual((m[E-80],m[E-79]),(0,0))

    def test_uninterpreted_descriptor_word_remains_opaque_after_copy(self):
        f=fixture();put(f['cells'],E+12,O('uninitialized untouched descriptor word'));r=self.derive(f);self.cpuset(f,r)
        self.assertEqual(tuple(memory(r)[E-68+i] for i in range(4)),O('uninitialized untouched descriptor word'))

    def test_unaligned_source_descriptor_entry_is_refused(self):
        f=fixture();f['registers'][13]=P(E+1);f['registers'][2]=P(E+1);r=self.derive(f)
        self.assertIn('exact84',r['boundary']['reason']);self.assertEqual(r['trace'],[])

    def test_wrong_count_is_not_substituted_from_old_scheduler_paths(self):
        f=fixture();f['registers'][1]=I(64);r=self.derive(f)
        self.assertIn('exact84',r['boundary']['reason']);self.assertEqual(r['trace'],[])

    def test_wrong_descriptor_or_source_return_is_not_repaired(self):
        f=fixture();f['registers'][2]=P(E+4);r=self.derive(f)
        self.assertIn('exact84',r['boundary']['reason']);self.assertEqual(r['trace'],[])

    def test_no_literal_point_authority_stops_at_real_global_load(self):
        f=fixture();f['literal_points']=();r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'wrapper',20));self.assertIn('provenance',r['boundary']['reason'])

    def test_global_pointer_without_reaching_bytes_is_not_initialized(self):
        f=fixture();del f['cells'][0x8FF2];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'wrapper',20));self.assertIn('reaching',r['boundary']['reason'])

    def test_null_allocator_return_cannot_authorize_zero_destination(self):
        f=fixture();half(f['cells'],0,0);half(f['cells'],2,0);half(f['cells'],4,0);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'zero_thunk'));self.assertIn('provenance',r['boundary']['reason'])
        self.assertFalse(r['callback_entered'])

    def test_zero_destination_write_protection_is_checked_per_real_store(self):
        f=fixture();f['protected_spans']=((NODE+8,NODE+12),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],model.image079.IMAGE_BASE+22);self.assertIn('protected',r['boundary']['reason'])
        self.assertFalse(r['callback_entered'])

    def test_released_payload_remains_dead_at_actual_zero_write(self):
        f=fixture();f['released_payload_spans']=((NODE,NODE+112),);r=self.derive(f)
        self.assertIn('retired',r['boundary']['reason']);self.assertFalse(r['callback_entered'])

    def test_stack_allocation_cannot_revive_released_payload(self):
        f=fixture();f['released_payload_spans']=((E-20,E),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'wrapper'));self.assertIn('retired',r['boundary']['reason'])

    def test_prior_retired_stack_reuse_preserves_live_source_and_actual_saves(self):
        f=fixture();f['retired_stack_spans']=((E-300,E),);r=self.derive(f);self.cpuset(f,r)
        self.assertTrue(r['retired_spans']);self.assertEqual(tuple(memory(r)[E+4+i] for i in range(4)),P(SUBJECT))

    def test_source_halfword_opaque_bits_stop_only_at_actual_callback_read(self):
        f=fixture();put(f['cells'],E+20,O('unknown scalar descriptor field'));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'large_callback',104));self.assertIn('opaque',r['boundary']['reason'])
        self.assertTrue(r['callback_entered']);self.assertEqual(r['callback_observed_phase'],0)

    def test_parent_list_alias_to_wrapper_saved_word_reads_that_word(self):
        f=fixture(parent=E-32);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'scheduler',66));self.assertIn('scalar observation',r['boundary']['reason'])
        self.assertFalse(r['callback_entered'])

    def test_cyclic_list_retains_precise_bounded_state(self):
        f=fixture(head=9000);put(f['cells'],9008,P(9000));f['max_steps']=800;r=self.derive(f)
        self.assertIn('budget',r['boundary']['reason']);self.assertEqual(len(r['trace']),800);self.assertFalse(r['callback_entered'])

    def test_parent_alias_to_retired_zero_return_save_is_refused(self):
        f=fixture(parent=E-100);put(f['cells'],E-84,I(0));r=self.derive(f)
        # Parent slot E-84 is also the real zero routine LR save. After
        # return it is retired; a parent read cannot grant it a live lifetime.
        self.assertEqual(r['boundary']['site'],at(f['layout'],'scheduler',64));self.assertIn('retired',r['boundary']['reason'])

    def test_bad_complete_source_image_is_not_installation_evidence(self):
        f=fixture();image=bytearray(IMAGE);image[175]^=1;f['layout']=replace(f['layout'],image=bytes(image))
        with self.assertRaisesRegex(ValueError,'176B'):self.derive(f)

    def test_wrong_original_zero_pointer_identity_is_rejected(self):
        f=fixture();f['layout']=replace(f['layout'],zero_pointer_data=(model.image079.IMAGE_BASE+3).to_bytes(4,'little'))
        with self.assertRaisesRegex(ValueError,'four-byte'):self.derive(f)

    def test_complete_callback_mutation_is_not_accepted_by_address(self):
        f=fixture();b=bytearray(f['layout'].callback_data);b[500]^=1;f['layout']=replace(f['layout'],callback_data=bytes(b))
        with self.assertRaisesRegex(ValueError,'callback instruction'):self.derive(f)

    def test_explicit_selector_required_and_old_policies_unchanged(self):
        f=fixture();f['selector']=model.image079.SELECTOR
        with self.assertRaisesRegex(ValueError,'083'):self.derive(f)

    def test_relocated_complete_owners_are_bound_by_shapes_and_edges(self):
        f=fixture();l=layout(0x40000);f['layout']=model.bind(l.prior,l.scheduler,l.callback,l.callback_data,l.image,l.zero_pointer_data,selector=model.SELECTOR)
        f['registers'][0]=I(l.callback|1);f['registers'][14]=I(at(l,'next',48)|1)
        r=self.derive(f);self.cpuset(f,r)

    def test_new082_source_entry_composes_into_actual84_then112_callback(self):
        f=fixture(size=44);l=f['layout'];root_sp=E+100;m=dict(f['cells']);half(m,SUBJECT+4,8);put(m,E+48,I(0))
        regs={i:O('083 new source composition R'+str(i)) for i in range(15)}
        regs.update({0:P(SUBJECT),1:I(5),2:I(0),3:P(TAG),13:P(E+48),14:I(at(l,'root',124)|1)})
        prior=model.source082.derive(l.prior,BASE,m,regs,root_sp,I(0x08024681),selector=model.source082.SELECTOR)
        self.assertEqual(prior['final_PC'],at(l,'wrapper'),prior['boundary'])
        result=model.continue_from_082(l,BASE,prior,selector=model.SELECTOR,literal_points=f['literal_points'])
        f.update(cells=memory(prior),registers=prior['registers']);self.cpuset(f,result)
        self.assertEqual([x['count'] for x in result['zero_calls']],[12,112]);self.assertTrue(result['inherited_082_obligations'])
        artifact('new-source-input.json',prior)
        artifact('new-source-composition.json',result)

    def adapter_shape(self):
        # Deliberately synthetic report shape for negative adapter guards only.
        f=fixture();l=f['layout'];owners=model.source082._validate(l.prior)
        pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(owners.items())]
        report=dict(schema=model.source082.SELECTOR,complete_owner_pins=pins,final_PC=at(l,'wrapper'),conditional_root_return=False,
            boundary=dict(reason='actual84-byte scheduler request requires independent composition'),root_entry_SP=E+100,
            pending_calls=[dict(role='next',return_pc=at(l,'root',124),entry_sp=E+48),dict(role='wrapper',return_pc=at(l,'next',48),entry_sp=E)],
            retired_spans=[],conditional_released_payloads=[],memory_events=[],post_cells={},registers=f['registers'])
        return f,report

    def test_adapter_rejects_changed_complete_owner_pin(self):
        f,report=self.adapter_shape();report['complete_owner_pins'][0]['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'wrapper-entry'):model.continue_from_082(f['layout'],BASE,report,selector=model.SELECTOR)

    def test_adapter_rejects_wrong_pending_wrapper_frame(self):
        f,report=self.adapter_shape();report['pending_calls'][1]['entry_sp']+=4
        with self.assertRaisesRegex(ValueError,'pending'):model.continue_from_082(f['layout'],BASE,report,selector=model.SELECTOR)

    def test_adapter_does_not_reclassify_unexplained_retired_bytes(self):
        f,report=self.adapter_shape();report['retired_spans']=[[E-20,E]]
        with self.assertRaisesRegex(ValueError,'unclassified'):model.continue_from_082(f['layout'],BASE,report,selector=model.SELECTOR)

    def test_direct_entry_rejects_wrong_original_source_return_word(self):
        f=fixture();f['registers'][14]=I(at(f['layout'],'next',50)|1);r=self.derive(f)
        self.assertIn('exact84',r['boundary']['reason']);self.assertEqual(r['trace'],[])

    def test_copy_reads_missing_untouched_source_byte_instead_of_inventing_it(self):
        f=fixture();del f['cells'][E+15];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'scheduler',162));self.assertIn('reaching',r['boundary']['reason']);self.assertFalse(r['callback_entered'])

    def test_real_callback_subject_field_write_keeps_opaque_pointer_uninterpreted(self):
        f=fixture();put(f['cells'],E+4,O('unknown subject token'));r=self.derive(f);self.cpuset(f,r)
        self.assertEqual(tuple(memory(r)[NODE+96+i] for i in range(4)),O('unknown subject token'))

    def test_complete_scheduler_digest_and_edge_are_not_nominal(self):
        f=fixture();s=replace(f['layout'].scheduler,sha256='0'*64);f['layout']=replace(f['layout'],scheduler=s)
        with self.assertRaisesRegex(ValueError,'scheduler identity'):self.derive(f)

    def test_state_bound_does_not_silently_drop_byte_origins(self):
        f=fixture();f['cells'].update({20000+i:0 for i in range(4097)})
        with self.assertRaisesRegex(ValueError,'bounded common'):self.derive(f)
