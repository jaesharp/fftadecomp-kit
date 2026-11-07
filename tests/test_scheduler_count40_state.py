"""New087 nested allocation cases and independent raw oracle."""
from dataclasses import replace
import unittest,hashlib,json,os
from pathlib import Path
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_count40_state as model
upstream=model.source083
BASE,E,NODE,SCHED,CALLER,DESC,POOLB=0x02000000,10000,140,5000,6000,7000,0x18000
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
    b=bytearray(model.phase086.returns085.suffix084.helper075.HELPER)
    for off in model.phase086.returns085.suffix084.helper075.CALL_OFFSETS:
        target=g if off==114 else coord if off==130 else p.scheduler.address if off==266 else h+0x1000+off
        b[off:off+4]=model.removal._bl(h+off,target)
    b[80:84]=(h+84).to_bytes(4,'little')
    for i,off in enumerate(model.phase086.returns085.suffix084.helper075.TABLE_OFFSETS):b[84+4*i:88+4*i]=(h+off).to_bytes(4,'little')
    b[288:292]=(upstream._validate(p)['callback'][0]|1).to_bytes(4,'little')
    getter=model.phase086.returns085.suffix084.helper075.GETTER[:2]+model.removal._bl(g+2,identity)+model.phase086.returns085.suffix084.helper075.GETTER[6:]
    cd=model.phase086.returns085.suffix084.helper075.COORDINATES[:28]+model.removal._bl(coord+28,h+0x2000)+model.phase086.returns085.suffix084.helper075.COORDINATES[32:]
    helper=model.phase086.returns085.suffix084.helper075.Layout(h,bytes(b),g,getter,identity,b'\x70\x47',coord,cd)
    cb=bytearray(p.callback_data);cb[120:124]=model.removal._bl(p.callback+120,bios);cb[138:142]=model.removal._bl(p.callback+138,h)
    p=replace(p,callback_data=bytes(cb))
    return model.phase086.returns085.Layout(model.phase086.returns085.suffix084.Layout(p,helper,bios,b'\x0b\xdf\x70\x47'))

def prior_phase_layout(shift=0):
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
    predicate_data=model.phase086.PREDICATE[:2]+model.removal._bl(predicate+2,getter)+model.phase086.PREDICATE[6:]
    requester_data=model.phase086.REQUESTER[:24]+model.removal._bl(requester+24,p83.scheduler.address)+model.phase086.REQUESTER[28:]
    return model.phase086.Layout(prior,predicate,predicate_data,getter,model.phase086.GETTER,requester,requester_data)

def layout(shift=0):
    prior=prior_phase_layout(shift);cb=0x080D791C;pw=0x081E0400+shift;gw=0x081E0800+shift
    owners=model.phase086._validate(prior);target=owners['allocator_wrapper'][0]
    data=bytearray(model.CALLBACK)
    for off,t in ((88,pw),(98,gw)):data[off:off+4]=model.removal._bl(cb+off,t)
    p=model.POOL_WRAPPER[:4]+model.removal._bl(pw+4,target)+model.POOL_WRAPPER[8:]
    g=model.GLOBAL_WRAPPER[:8]+model.removal._bl(gw+8,target)+model.GLOBAL_WRAPPER[12:]
    return model.Layout(prior,cb,bytes(data),pw,p,gw,g)

def half(m,a,v):put(m,a,tuple((v&65535).to_bytes(2,'little')))
def pool(m,base,size):
    for a,v in ((0,32 if size else 0),(2,32 if size else 0),(4,1 if size else 0),(130,0),(134,size),(136,0),(138,0)):half(m,base+a,v)
def fixture(size=8192,second=4096,parent=CALLER,shift=0):
    l=layout(shift);m={E-512+i:('opaque-byte','087 actual stack origin',i) for i in range(564)}
    pool(m,0,size);pool(m,POOLB,second)
    put(m,SCHED,P(0));put(m,SCHED+4,P(CALLER));half(m,SCHED+12,1);put(m,CALLER+8,I(0));put(m,CALLER+16,I(0))
    if parent is not None:put(m,parent+16,I(0))
    put(m,0xF430,P(SCHED));put(m,0x8FF4,P(POOLB))
    put(m,E,I(0) if parent is None else P(parent));put(m,E+8,I(0x0839D7E4));half(m,E+24,2)
    put(m,E+32,I(at(l,'callback',88)|1));put(m,E+36,O('entryR4'));put(m,E+40,O('entryR5'));put(m,E+44,O('entryR6'));put(m,E+48,I(RETURN))
    half(m,DESC,256)
    r={i:O('087 inputR'+str(i)) for i in range(15)}
    r.update({0:P(SCHED),1:I(l.callback|1),2:I(40),3:P(E+4),4:P(CALLER+24),5:P(DESC),6:P(CALLER),13:P(E),14:I(at(l,'requester256',28)|1)})
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR,callback_entry_sp=E+52,callback_return_word=I(RETURN),literal_points=(0x0200F430,0x02008FF4))

def raw(f,stop_before=None):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for a,b in model._validate(f['layout']).values()};bodies[model.image079.IMAGE_BASE]=f['layout'].prior.prior.prior.prior.image[:50];regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
    mem={f['arena_base']+k:byte(v,f['arena_base']) for k,v in f['cells'].items()};pc=at(f['layout'],'scheduler');events=[];trace=[]
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
                    if a==f['layout'].prior.prior.prior.prior.scheduler.allocator.allocator.pointer_literal:regs[reg(ops[0])]=int.from_bytes(f['layout'].prior.prior.prior.prior.zero_pointer_data,'little')
                    else:regs[reg(ops[0])]=read(a,width)
                else:write(a,width,regs[reg(ops[0])])
        else:raise AssertionError((hex(pc),n,i.op_str))
        pc=nxt
    else:raise AssertionError('raw oracle bound exhausted')
    return regs,mem,trace,events,pc


@unittest.skipIf(IMAGE is None,'set FFTA_SOURCE84_IMAGE to the private authenticated176B source')
class Count40Tests(unittest.TestCase):
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
        self.assertEqual(r['final_PC'],RETURN&~1);self.assertEqual(r['registers'][13],P(E+52));self.assert_raw(f,r)
    def test_complete_count40_two_actual_pool_allocations_and_returns(self):
        f=fixture();r=self.derive(f);artifact('new-count40-complete.json',r);self.returned(f,r)
        self.assertEqual([x['size_word'] for x in r['allocation_requests']],[I(68),I(0x3000),I(0x4000)])
        m=memory(r)
        self.assertEqual(tuple(m[NODE+24+i] for i in range(4)),I(0x0839D7E4))
        self.assertEqual(m[NODE+30],2)
        self.assertEqual(tuple(m[NODE+56+i] for i in range(4)),P(220))
        self.assertEqual(tuple(m[NODE+60+i] for i in range(4)),P(POOLB+140))
        self.assertEqual(tuple(m[CALLER+32+i] for i in range(4)),P(NODE))
        self.assertEqual((m[DESC],m[DESC+1]),(1,1))
        self.assertFalse(r['BIOS_prepost_gap_closed']);self.assertFalse(r['actual_installed_identity_proved'])
    def test_first_nested_allocation_can_return_null_without_invented_payload(self):
        f=fixture(size=17);r=self.derive(f);self.returned(f,r);m=memory(r)
        self.assertEqual(tuple(m[NODE+56+i] for i in range(4)),I(0))
        self.assertEqual(tuple(m[NODE+60+i] for i in range(4)),P(POOLB+140))
    def test_second_nested_pool_can_be_empty_and_null_is_stored(self):
        f=fixture(second=0);r=self.derive(f);self.returned(f,r)
        self.assertEqual(tuple(memory(r)[NODE+60+i] for i in range(4)),I(0))

    def test_initial_allocator_null_refuses_actual_zero_call(self):
        f=fixture(size=0);r=self.derive(f)
        self.assertEqual([x['size_word'] for x in r['allocation_requests']],[I(68)])
        # The actual scheduler has no null guard before the zero call.
        self.assertEqual(r['boundary']['site'],at(f['layout'],'zero_thunk'));self.assertIn('provenance',r['boundary']['reason'])
        self.assertFalse(r['callback_entered']);self.assertFalse(r['conditional_callback_return'])
        self.assert_raw(f,r,stop_before=at(f['layout'],'zero_thunk'))

    def test_both_nested_allocations_can_fail_independently(self):
        f=fixture(size=17,second=0);r=self.derive(f);self.returned(f,r)
        self.assertEqual(tuple(memory(r)[NODE+56+i] for i in range(8)),I(0)+I(0))

    def test_two_nominal_pools_may_be_the_same_ordered_allocator_state(self):
        f=fixture();put(f['cells'],0x8FF4,P(0));r=self.derive(f);self.returned(f,r)
        self.assertEqual([x['pool_word'] for x in r['allocation_requests']],[P(0)]*3)
        self.assertEqual(tuple(memory(r)[NODE+60+i] for i in range(4)),P(12520))

    def test_large_allocation_does_not_zero_or_initialize_buffer_contents(self):
        f=fixture();w=O('preexisting buffer contents');put(f['cells'],284,w)
        r=self.derive(f);self.returned(f,r);self.assertEqual(tuple(memory(r)[284+i] for i in range(4)),w)
        self.assertNotIn('300',r['post_cells'])
        self.assertEqual([c['count'] for c in r['zero_calls']],[12,68,12])

    def test_descriptor_word_is_copied_opaque_without_address_observation(self):
        f=fixture();w=O('unobserved descriptor payload');put(f['cells'],E+8,w)
        r=self.derive(f);self.returned(f,r);self.assertEqual(tuple(memory(r)[NODE+24+i] for i in range(4)),w)

    def test_phase_reload_aliases_real_zeroed_new_node_bytes(self):
        f=fixture();f['registers'][5]=P(NODE+32);r=self.derive(f);self.returned(f,r)
        self.assertEqual((memory(r)[NODE+32],memory(r)[NODE+33]),(1,0))

    def test_phase_increment_alias_changes_actual_saved_r6(self):
        f=fixture();f['registers'][5]=P(E+44);put(f['cells'],E+44,I(256))
        r=self.derive(f);self.returned(f,r);self.assertEqual(r['registers'][6],I(257))
        self.assertFalse(r['ABI_preservation_assumed'])

    def test_null_parent_uses_real_scheduler_list_branch(self):
        f=fixture(parent=None);r=self.derive(f);self.returned(f,r)
        self.assertEqual(tuple(memory(r)[NODE+12+i] for i in range(4)),I(0))

    def test_missing_scheduler_literal_authority_stops_real_callback_load(self):
        f=fixture();f['literal_points']=(0x02008FF4,);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',82));self.assertIn('provenance',r['boundary']['reason'])
        self.assert_raw(f,r,stop_before=at(f['layout'],'callback40',82))

    def test_global_pool_identity_is_separate_from_scheduler_identity(self):
        f=fixture();f['literal_points']=(0x0200F430,);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'global_wrapper',6));self.assertIn('provenance',r['boundary']['reason'])
        self.assert_raw(f,r,stop_before=at(f['layout'],'global_wrapper',6))

    def test_known_global_point_does_not_supply_missing_pointer_bytes(self):
        f=fixture();del f['cells'][0x8FF5];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'global_wrapper',6));self.assertIn('reaching',r['boundary']['reason'])

    def test_unknown_pool_pointer_does_not_become_allocated_memory(self):
        f=fixture();put(f['cells'],0x8FF4,O('unknown global pool'));r=self.derive(f)
        self.assertIn('provenance',r['boundary']['reason']);self.assertFalse(r['conditional_callback_return'])

    def test_retired_outer_phase_is_not_revived_by_nested_stack_reuse(self):
        f=fixture();f['retired_stack_spans']=((DESC,DESC+2),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback',90));self.assertIn('retired',r['boundary']['reason'])
        self.assert_raw(f,r,stop_before=at(f['layout'],'callback',90))

    def test_protected_root_save_stops_before_any_allocator(self):
        f=fixture();f['protected_spans']=((E-4,E),);r=self.derive(f)
        self.assertIn('protected',r['boundary']['reason']);self.assertEqual(r['allocation_requests'],[])

    def test_freed_enclosing_stack_cannot_be_revived_by_scheduler_push(self):
        f=fixture();f['released_payload_spans']=((E-24,E),);r=self.derive(f)
        self.assertIn('externally retired',r['boundary']['reason']);self.assertFalse(r['conditional_callback_return'])

    def test_corrupt_requester_saved_return_is_observed_on_real_pop(self):
        f=fixture();put(f['cells'],E+32,I(RETURN));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'requester256',32));self.assertIn('saved return',r['boundary']['reason'])
        self.assert_raw(f,r,stop_before=at(f['layout'],'requester256',32))

    def test_unknown_enclosing_return_is_not_replaced_by_expected_word(self):
        f=fixture();put(f['cells'],E+48,O('unknown enclosing return'));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback',134));self.assertIn('opaque',r['boundary']['reason'])
        self.assert_raw(f,r,stop_before=at(f['layout'],'callback',134))

    def test_explicit_execution_bound_retains_partial_state(self):
        f=fixture();f['max_steps']=8;r=self.derive(f)
        self.assertEqual(len(r['trace']),8);self.assertIn('budget',r['boundary']['reason']);self.assertFalse(r['conditional_callback_return'])

    def test_full_relocated_allocation_helpers_bind_only_their_actual_edges(self):
        f=fixture(shift=0x10000);l=f['layout']
        f['layout']=model.bind(l.prior,l.callback,l.callback_data,l.pool_wrapper,l.pool_wrapper_data,l.global_wrapper,l.global_wrapper_data,selector=model.SELECTOR)
        r=self.derive(f);self.returned(f,r)

    def test_complete_callback_suffix_mutation_is_rejected_even_if_unselected(self):
        f=fixture();b=bytearray(f['layout'].callback_data);b[280]^=1;f['layout']=replace(f['layout'],callback_data=bytes(b))
        with self.assertRaisesRegex(ValueError,'callback identity'):self.derive(f)

    def test_real_global_literal_cannot_be_replaced_with_nominal_alias(self):
        f=fixture();b=bytearray(f['layout'].global_wrapper_data);b[16]^=4;f['layout']=replace(f['layout'],global_wrapper_data=bytes(b))
        with self.assertRaisesRegex(ValueError,'global-pool wrapper identity'):self.derive(f)

    def test_count40_entry_rejects_different_count_without_effects(self):
        f=fixture();f['registers'][2]=I(12);r=self.derive(f)
        self.assertIn('entry differs',r['boundary']['reason']);self.assertEqual(r['memory_events'],[])

    def test_selector_is_explicit_and_closed(self):
        f=fixture();f['selector']='default'
        with self.assertRaisesRegex(ValueError,'explicit087'):self.derive(f)

    def preceding_report(self,f):
        l=f['layout'];old=model.phase086._validate(l.prior);r=f['registers']
        return dict(schema=model.phase086.SELECTOR,
            complete_owner_pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(old.items())],
            final_PC=at(l,'scheduler'),new_scheduler_count=40,conditional_callback_return=False,
            registers=r,callback_entry_SP=E+52,callback_return_word=I(RETURN),post_cells={str(k):v for k,v in f['cells'].items()},
            nested_call_cutpoint=dict(call_site=l.prior.requester+24,target=at(l,'scheduler'),SP=E,return_word=r[14],register_arguments={i:r[i] for i in range(4)},callee_executed=False),
            pending_calls=[dict(role='callback',return_pc=RETURN&~1,entry_sp=E+52),dict(role='requester256',return_pc=at(l,'callback',88),entry_sp=E+36)],
            retired_spans=[],conditional_released_payloads=[],obligations=['synthetic conditional entry only'])

    def test_transport_consumes_exact_conditional_state_without_prior_producer(self):
        f=fixture();prior=self.preceding_report(f)
        r=model.continue_from_086(f['layout'],BASE,prior,selector=model.SELECTOR,literal_points=f['literal_points'])
        self.returned(f,r);self.assertFalse(r['actual_086_report_authentication_proved'])
        self.assertEqual(r['inherited_086_obligations'],prior['obligations'])
        artifact('new-transported-count40.json',r)

    def test_transport_rejects_stale_owner_pins(self):
        f=fixture();prior=self.preceding_report(f);prior['complete_owner_pins'][0]['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'exact086'):model.continue_from_086(f['layout'],BASE,prior,selector=model.SELECTOR)

    def test_transport_rejects_fabricated_callee_execution(self):
        f=fixture();prior=self.preceding_report(f);prior['nested_call_cutpoint']['callee_executed']=True
        with self.assertRaisesRegex(ValueError,'interface'):model.continue_from_086(f['layout'],BASE,prior,selector=model.SELECTOR)

    def test_transport_preserves_retired_global_pool_pointer(self):
        f=fixture();prior=self.preceding_report(f);prior['retired_spans']=[(0x8FF4,0x8FF8)]
        r=model.continue_from_086(f['layout'],BASE,prior,selector=model.SELECTOR,literal_points=f['literal_points'])
        self.assertEqual(r['boundary']['site'],at(f['layout'],'global_wrapper',6));self.assertIn('retired',r['boundary']['reason'])
        self.assert_raw(f,r,stop_before=at(f['layout'],'global_wrapper',6))

    def test_nested_global_pointer_can_alias_scheduler_count_bytes(self):
        f=fixture();put(f['cells'],0x8FF4,P(SCHED));half(f['cells'],SCHED,0)
        # This overlapping pool header changes scheduler[0] itself. The actual
        # initial allocator sees the new complete word; no nominal role masks it.
        r=self.derive(f);self.assertIn('provenance',r['boundary']['reason'])
        self.assertFalse(r['callback_entered']);self.assertFalse(r['conditional_callback_return'])

    def test_unknown_mode_is_not_silently_truncated_to_an_initialized_byte(self):
        f=fixture()
        f['cells'][E+24]=('opaque-byte','unknown mode',0);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',76));self.assertIn('narrow read',r['boundary']['reason'])

    def test_descriptor_source_pointer_is_an_exact_entry_obligation(self):
        f=fixture();f['registers'][3]=P(E+8);r=self.derive(f)
        self.assertIn('entry differs',r['boundary']['reason']);self.assertEqual(r['memory_events'],[])

    def test_allocator_success_does_not_revive_declared_freed_node_bytes(self):
        f=fixture();f['released_payload_spans']=((NODE,NODE+68),);r=self.derive(f)
        self.assertIn('retired',r['boundary']['reason']);self.assertFalse(r['conditional_callback_return'])

    def test_exact_first_nested_fit_does_not_invent_a_second_split_header(self):
        f=fixture(size=3092);r=self.derive(f);self.returned(f,r)
        self.assertEqual(tuple(memory(r)[NODE+56+i] for i in range(4)),P(220))
        self.assertEqual([c['count'] for c in r['zero_calls']],[12,68])
