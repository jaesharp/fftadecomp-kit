"""New085 count12 and enclosing-return states with independent raw oracle."""
from dataclasses import replace
import unittest,hashlib,json,os
from pathlib import Path
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_source_return_state as model
upstream=model.source083
BASE,E,NODE,SCHED,OUTER,ROOT_PAYLOAD,ROOT_DESC,TAG=0x02000000,10000,140,5000,6000,7000,7100,7200
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

def layout(shift=0):
    p=source_layout(shift);h=0x081C0000+shift;g=h+0x400;coord=h+0x800;bios=0x0814186C+shift
    identity=upstream._validate(p)['identity'][0]
    b=bytearray(model.suffix084.helper075.HELPER)
    for off in model.suffix084.helper075.CALL_OFFSETS:
        target=g if off==114 else coord if off==130 else p.scheduler.address if off==266 else h+0x1000+off
        b[off:off+4]=model.removal._bl(h+off,target)
    b[80:84]=(h+84).to_bytes(4,'little')
    for i,off in enumerate(model.suffix084.helper075.TABLE_OFFSETS):b[84+4*i:88+4*i]=(h+off).to_bytes(4,'little')
    b[288:292]=(upstream._validate(p)['callback'][0]|1).to_bytes(4,'little')
    getter=model.suffix084.helper075.GETTER[:2]+model.removal._bl(g+2,identity)+model.suffix084.helper075.GETTER[6:]
    cd=model.suffix084.helper075.COORDINATES[:28]+model.removal._bl(coord+28,h+0x2000)+model.suffix084.helper075.COORDINATES[32:]
    helper=model.suffix084.helper075.Layout(h,bytes(b),g,getter,identity,b'\x70\x47',coord,cd)
    cb=bytearray(p.callback_data);cb[120:124]=model.removal._bl(p.callback+120,bios);cb[138:142]=model.removal._bl(p.callback+138,h)
    p=replace(p,callback_data=bytes(cb))
    return model.Layout(model.suffix084.Layout(p,helper,bios,b'\x0b\xdf\x70\x47'))

def half(m,a,v):put(m,a,tuple((v&65535).to_bytes(2,'little')))

def fixture(size=10,parent=OUTER,head=OUTER,shift=0):
    l=layout(shift);m={E-300+i:('opaque-byte','085 explicit reaching frame',i) for i in range(616)}
    for a,v in ((0,32),(2,32),(4,1),(130,0),(134,size),(136,0),(138,0)):half(m,a,v)
    put(m,SCHED,P(0));put(m,SCHED+4,I(0) if head is None else P(head));half(m,SCHED+12,1)
    put(m,0x8FF0,P(SCHED))
    if parent is not None:put(m,parent+16,I(0))
    if head is not None:put(m,head+8,I(0))
    put(m,E,I(0) if parent is None else P(parent));put(m,E+8,P(E+44))
    put(m,E+44,(0,0,2,('opaque-byte','085 untouched record byte',0)))
    put(m,E+48,I(0x0839D7E4))
    # Explicit reaching saved words. No producer or ABI assumption supplies them.
    saved={52:I(9),56:O('post BIOS R5'),60:P(OUTER+24),64:O('post BIOS R7'),68:I(at(l,'large_callback',142)|1),
           112:I(at(l,'large_callback')|1),116:I(112),120:P(SCHED),124:O('outer R6'),128:P(OUTER),132:I(at(l,'scheduler',184)|1),
           164:P(E+216),168:O('outer R9'),172:I(84),176:P(0x8FF0),180:I(at(l,'large_callback')|1),184:O('wrapper R7'),188:I(at(l,'wrapper',34)|1),
           196:O('source R8'),200:O('source R4'),204:O('source R5'),208:O('source R6'),212:I(at(l,'next',48)|1),
           244:P(ROOT_PAYLOAD),248:P(ROOT_DESC),252:O('root R6'),256:O('root R7'),260:I(at(l,'root',124)|1),
           300:O('entry R4'),304:O('entry R5'),308:O('entry R6'),312:I(RETURN)}
    for off,w in saved.items():put(m,E+off,w)
    put(m,OUTER+36,P(TAG));m[TAG]=77;half(m,ROOT_DESC,256)
    r={i:O('085 actual input R'+str(i)) for i in range(15)}
    r.update({0:P(SCHED),1:I(at(l,'callback')|1),2:I(12),3:P(E+4),4:P(9000),5:I(7),6:I(2),7:P(E+44),8:P(OUTER),13:P(E),14:I(at(l,'descriptor_helper',270)|1)})
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR,
                root_entry_sp=E+316,root_return_word=I(RETURN),literal_points=(0x02008FF0,))

def raw(f,stop_before=None):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for a,b in model._validate(f['layout']).values()};bodies[model.image079.IMAGE_BASE]=f['layout'].prior.prior.image[:50];regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
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
                    if a==f['layout'].prior.prior.scheduler.allocator.allocator.pointer_literal:regs[reg(ops[0])]=int.from_bytes(f['layout'].prior.prior.zero_pointer_data,'little')
                    else:regs[reg(ops[0])]=read(a,width)
                else:write(a,width,regs[reg(ops[0])])
        else:raise AssertionError((hex(pc),n,i.op_str))
        pc=nxt
    else:raise AssertionError('raw oracle bound exhausted')
    return regs,mem,trace,events,pc


@unittest.skipIf(IMAGE is None,'set FFTA_SOURCE84_IMAGE to the private authenticated176B source')
class SharedReturnTests(unittest.TestCase):
    def assert_raw(self,f,r,stop_before=None):
        regs,mem,trace,events,pc=raw(f,stop_before)
        self.assertEqual(r['trace'],trace);self.assertEqual(r['final_PC'],pc)
        self.assertEqual({k:number(v,f['arena_base']) for k,v in r['registers'].items()},regs)
        got=memory(r)
        for a,v in mem.items():self.assertEqual(byte(got[a-f['arena_base']],f['arena_base']),v,(hex(a),v))
        actual=[(e['site'],e['operation'],e['coordinate'],tuple(byte(v,f['arena_base']) for v in e['bytes'])) for e in r['memory_events'] if 'coordinate' in e]
        self.assertEqual(actual,events)
    def derive(self,f):return model.derive(**f)
    def closed(self,f,r):
        self.assertTrue(r['conditional_root_return'],r['boundary']);self.assertIsNone(r['boundary']);self.assertEqual(r['pending_calls'],[])
        self.assertEqual(r['final_PC'],RETURN&~1);self.assertEqual(r['registers'][13],P(E+316));self.assert_raw(f,r)

    def test_count12_private_record_phase0_and_complete_enclosing_return(self):
        f=fixture();r=self.derive(f);self.closed(f,r);m=memory(r)
        self.assertEqual([x['count'] for x in r['zero_calls']],[40]);self.assertEqual(r['callback_observed_phase'],0)
        self.assertEqual(tuple(m[NODE+24+i] for i in range(3)),(0,0,2));self.assertEqual(tuple(m[NODE+28+i] for i in range(4)),I(0x0839D7E4))
        self.assertEqual(tuple(m[OUTER+92+i] for i in range(4)),P(NODE));self.assertEqual(m[TAG],9)
        self.assertEqual(tuple(m[ROOT_PAYLOAD+8+i] for i in range(4)),P(OUTER));self.assertEqual((m[ROOT_DESC],m[ROOT_DESC+1]),(1,1))
        self.assertFalse(r['BIOS_prepost_gap_closed']);self.assertFalse(r['native_admission']);artifact('new-count12-whole-return.json',r)

    def test_split_zero12_then40_preserves_live_private_record(self):
        f=fixture(size=24);r=self.derive(f);self.closed(f,r)
        self.assertEqual([x['count'] for x in r['zero_calls']],[12,40]);self.assertIn(at(f['layout'],'insert'),r['trace'])
        artifact('new-split-whole-return.json',r)

    def test_record_high_byte_remains_opaque_and_unobserved(self):
        f=fixture();f['cells'][E+47]=('opaque-byte','uninitialized record high byte',3)
        r=self.derive(f);self.closed(f,r);self.assertEqual(memory(r)[E+47],f['cells'][E+47])
        self.assertFalse(any(e.get('coordinate')==E+44 and e['operation']=='read32' for e in r['memory_events']))

    def test_record_word_transports_opaque_fragments_without_pointer_permission(self):
        f=fixture();put(f['cells'],E+48,O('opaque record payload word'));r=self.derive(f);self.closed(f,r)
        self.assertEqual(tuple(memory(r)[NODE+28+i] for i in range(4)),O('opaque record payload word'))

    def test_post_bios_r4_is_used_as_supplied_not_assumed_zero(self):
        f=fixture();put(f['cells'],E+52,I(0x123456A5));r=self.derive(f);self.closed(f,r)
        self.assertEqual(memory(r)[TAG],0xA5)

    def test_unknown_post_bios_r4_stops_at_real_enclosing_tag_store(self):
        f=fixture();put(f['cells'],E+52,O('BIOS return R4 unknown'));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'large_callback',146));self.assertIn('opaque',r['boundary']['reason'])
        self.assertEqual(tuple(memory(r)[OUTER+92+i] for i in range(4)),P(NODE));self.assertFalse(r['conditional_root_return'])
        artifact('new-unknown-postbios-r4-refusal.json',r)

    def test_private_record_is_retired_before_later_alias_tag_write(self):
        f=fixture();put(f['cells'],OUTER+36,P(E+44));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'large_callback',146));self.assertIn('retired',r['boundary']['reason'])
        reads=[e['coordinate'] for e in r['memory_events'] if e['operation'].startswith('read') and 'coordinate' in e]
        self.assertIn(E+46,reads);self.assertIn(E+48,reads);self.assertIn(E+44,reads)

    def test_parent_slot_alias_changes_record_before_callback_observation(self):
        f=fixture(parent=E+28);put(f['cells'],E+44,I(0));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback',42));self.assertIn('narrow read',r['boundary']['reason'])
        self.assertEqual(tuple(memory(r)[E+44+i] for i in range(4)),P(NODE))
        self.assert_raw(f,r,stop_before=at(f['layout'],'callback',42))

    def test_common_tag_alias_changes_root_phase_before_actual_reload(self):
        f=fixture();put(f['cells'],OUTER+36,P(ROOT_DESC));r=self.derive(f);self.closed(f,r)
        self.assertEqual((memory(r)[ROOT_DESC],memory(r)[ROOT_DESC+1]),(10,1))

    def test_root_phase_increment_wraps_actual_halfword(self):
        f=fixture();half(f['cells'],ROOT_DESC,65535);r=self.derive(f);self.closed(f,r)
        self.assertEqual((memory(r)[ROOT_DESC],memory(r)[ROOT_DESC+1]),(0,0))

    def test_existing_parent_child_chain_is_followed_in_order(self):
        f=fixture();put(f['cells'],OUTER+16,P(8000));put(f['cells'],8008,P(8100));put(f['cells'],8108,I(0))
        r=self.derive(f);self.closed(f,r);m=memory(r)
        self.assertEqual(tuple(m[8108+i] for i in range(4)),P(NODE));self.assertEqual(tuple(m[NODE+4+i] for i in range(4)),P(8100))

    def test_empty_global_list_and_null_parent_take_actual_other_branches(self):
        f=fixture(parent=None,head=None);r=self.derive(f);self.closed(f,r)
        self.assertEqual(tuple(memory(r)[SCHED+4+i] for i in range(4)),P(NODE))

    def test_saved_helper_lr_corruption_is_observed_at_bx(self):
        f=fixture();put(f['cells'],E+68,I(0x08111111));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'descriptor_helper',276));self.assertIn('saved return',r['boundary']['reason'])
        self.assert_raw(f,r,stop_before=at(f['layout'],'descriptor_helper',276))

    def test_saved_root_lr_corruption_is_not_replaced_by_expected_word(self):
        f=fixture();put(f['cells'],E+312,I(0x08111111));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'root',228));self.assertIn('saved return',r['boundary']['reason'])
        self.assertFalse(r['conditional_root_return'])

    def test_missing_outer_saved_word_has_precise_reaching_refusal(self):
        f=fixture();del f['cells'][E+124];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'large_callback',696));self.assertIn('reaching',r['boundary']['reason'])

    def test_expired_record_cannot_be_read_by_synchronous_callback(self):
        f=fixture();f['retired_stack_spans']=((E+44,E+52),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback',42));self.assertIn('retired',r['boundary']['reason'])

    def test_zero40_writes_observe_protected_bytes(self):
        f=fixture();f['protected_spans']=((NODE+24,NODE+28),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],model.image079.IMAGE_BASE+22);self.assertIn('protected',r['boundary']['reason'])
        self.assertFalse(r['callback_entered'])

    def test_released_payload_is_not_revived_by_count40_zero(self):
        f=fixture();f['released_payload_spans']=((NODE,NODE+40),);r=self.derive(f)
        self.assertIn('retired',r['boundary']['reason']);self.assertFalse(r['callback_entered'])

    def test_stack_push_cannot_revive_released_payload_interval(self):
        f=fixture();f['released_payload_spans']=((E-20,E),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'scheduler'));self.assertIn('retired',r['boundary']['reason'])

    def test_prior_dead_stack_can_be_reused_by_actual_allocation(self):
        f=fixture();f['retired_stack_spans']=((E-300,E),);r=self.derive(f);self.closed(f,r)
        self.assertTrue(any(lo<=E+44<hi for lo,hi in r['retired_spans']))

    def test_literal_global_address_requires_explicit_numeric_identity(self):
        f=fixture();put(f['cells'],E+176,I(0x02008FF0));f['literal_points']=();r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'wrapper',34));self.assertIn('provenance',r['boundary']['reason'])

    def test_unknown_record_low_halfword_is_not_initialized_by_model(self):
        f=fixture();f['cells'][E+44]=('opaque-byte','unknown low half',0);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback',50));self.assertIn('narrow read',r['boundary']['reason'])
        self.assertEqual(tuple(memory(r)[NODE+28+i] for i in range(4)),I(0x0839D7E4))

    def test_wrong_count_cannot_select_zero40_contract(self):
        f=fixture();f['registers'][2]=I(64);r=self.derive(f)
        self.assertIn('count12',r['boundary']['reason']);self.assertEqual(r['trace'],[])

    def test_wrong_descriptor_address_is_not_adjusted(self):
        f=fixture();f['registers'][3]=P(E+8);r=self.derive(f)
        self.assertIn('count12',r['boundary']['reason']);self.assertEqual(r['trace'],[])

    def test_outer_frame_coordinate_must_match_actual_selected_prologues(self):
        f=fixture();f['root_entry_sp']+=4;r=self.derive(f)
        self.assertIn('frame',r['boundary']['reason']);self.assertEqual(r['trace'],[])

    def test_opaque_root_return_target_does_not_authorize_control(self):
        f=fixture();f['root_return_word']=O('unknown root return');r=self.derive(f)
        self.assertIn('opaque',r['boundary']['reason']);self.assertEqual(r['trace'],[])

    def test_instruction_budget_stops_without_claiming_termination(self):
        f=fixture();f['max_steps']=4;r=self.derive(f)
        self.assertEqual(len(r['trace']),4);self.assertIn('budget',r['boundary']['reason']);self.assertFalse(r['actual_termination_proved'])

    def test_relocated_complete_owners_use_shapes_not_address_allowlist(self):
        f=fixture(shift=0x10000);f['layout']=model.bind(f['layout'].prior,selector=model.SELECTOR)
        r=self.derive(f);self.closed(f,r)

    def test_changed_complete_callback_identity_is_rejected(self):
        f=fixture();p=f['layout'].prior;p83=p.prior;b=bytearray(p83.callback_data);b[142]^=1
        f['layout']=replace(f['layout'],prior=replace(p,prior=replace(p83,callback_data=bytes(b))))
        with self.assertRaisesRegex(ValueError,'identity'):self.derive(f)

    def test_wrong_helper_callback_literal_is_rejected(self):
        f=fixture();p=f['layout'].prior;b=bytearray(p.helper.helper_data);b[288:292]=(0x08111111).to_bytes(4,'little')
        f['layout']=replace(f['layout'],prior=replace(p,helper=replace(p.helper,helper_data=bytes(b))))
        with self.assertRaisesRegex(ValueError,'literal'):self.derive(f)

    def test_selector_is_closed_and_never_default(self):
        f=fixture();f['selector']='default'
        with self.assertRaisesRegex(ValueError,'explicit085'):self.derive(f)

    def test_actual_saved_literal_r5_uses_explicit_point_without_access_claim(self):
        f=fixture();put(f['cells'],E+176,I(0x02008FF0));r=self.derive(f);self.closed(f,r)
        self.assertFalse(r['physical_access_proved']);self.assertFalse(r['actual_reaching_proved'])

    def report084(self,f):
        l=f['layout'];r=f['registers'];owners=model._validate(l)
        return dict(schema=model.suffix084.SELECTOR,
            complete_owner_pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(owners.items())],
            final_PC=at(l,'scheduler'),observed_wrapper_BX_return=True,postsvc_entry_SP=E+72,
            nested_call_cutpoint=dict(call_site=at(l,'descriptor_helper',266),target=at(l,'scheduler'),SP=E,
                return_word=r[14],register_arguments={i:r[i] for i in range(4)},callee_executed=False),
            pending_calls=[dict(role='descriptor_helper',return_pc=at(l,'large_callback',142),entry_sp=E+72)],
            registers=r,post_cells={str(k):v for k,v in f['cells'].items()},retired_spans=[],conditional_released_payloads=[],
            obligations=['Synthetic conditional report only; actual BIOS and outer reaching state not authenticated.'])

    def via_report(self,f,report):
        return model.continue_from_084(f['layout'],f['arena_base'],report,selector=model.SELECTOR,
            root_entry_sp=f['root_entry_sp'],root_return_word=f['root_return_word'],literal_points=f['literal_points'])

    def test_exact_report_transport_keeps_bios_and_authentication_gaps(self):
        f=fixture();half(f['cells'],E+44,321);report=self.report084(f);r=self.via_report(f,report);self.closed(f,r)
        self.assertFalse(r['actual_084_report_authentication_proved']);self.assertFalse(r['actual_BIOS_poststate_proved'])
        self.assertEqual(r['inherited_084_obligations'],report['obligations']);artifact('new-report-transport.json',r)

    def test_report_wrong_callsite_cannot_stand_for_helper_entry(self):
        f=fixture();report=self.report084(f);report['nested_call_cutpoint']['call_site']+=2
        with self.assertRaisesRegex(ValueError,'interface'):self.via_report(f,report)

    def test_report_pending_helper_frame_cannot_be_dropped(self):
        f=fixture();report=self.report084(f);report['pending_calls']=[]
        with self.assertRaisesRegex(ValueError,'interface'):self.via_report(f,report)

    def test_report_wrong_owner_pin_is_not_current_authority(self):
        f=fixture();report=self.report084(f);report['complete_owner_pins'][0]['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'report'):self.via_report(f,report)

    def test_unknown_root_phase_stops_at_actual_halfword_read(self):
        f=fixture();f['cells'][ROOT_DESC]=('opaque-byte','unknown root phase',0);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'root',130));self.assertIn('narrow read',r['boundary']['reason'])
        self.assertEqual(tuple(memory(r)[ROOT_PAYLOAD+8+i] for i in range(4)),P(OUTER))

    def test_protected_root_output_is_checked_after_all_actual_returns(self):
        f=fixture();f['protected_spans']=((ROOT_PAYLOAD+8,ROOT_PAYLOAD+12),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'root',124));self.assertIn('protected',r['boundary']['reason'])
        self.assertTrue(any(x['role']=='next' for x in r['observed_returns']));self.assertFalse(r['conditional_root_return'])
