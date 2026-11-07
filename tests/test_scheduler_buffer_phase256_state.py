"""New088 record preparation cases and independent raw oracle."""
from dataclasses import replace
import unittest,hashlib,json,os
from pathlib import Path
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_buffer_phase256_state as model
prior_model=model.count087
upstream=prior_model.source083
BASE,E,NODE,PAYLOAD,DESC,RECORD,BUFFER,SUB,HANDLE=0x02000000,10000,2000,3000,5000,6000,7000,8000,9000
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
    b=bytearray(prior_model.phase086.returns085.suffix084.helper075.HELPER)
    for off in prior_model.phase086.returns085.suffix084.helper075.CALL_OFFSETS:
        target=g if off==114 else coord if off==130 else p.scheduler.address if off==266 else h+0x1000+off
        b[off:off+4]=prior_model.removal._bl(h+off,target)
    b[80:84]=(h+84).to_bytes(4,'little')
    for i,off in enumerate(prior_model.phase086.returns085.suffix084.helper075.TABLE_OFFSETS):b[84+4*i:88+4*i]=(h+off).to_bytes(4,'little')
    b[288:292]=(upstream._validate(p)['callback'][0]|1).to_bytes(4,'little')
    getter=prior_model.phase086.returns085.suffix084.helper075.GETTER[:2]+prior_model.removal._bl(g+2,identity)+prior_model.phase086.returns085.suffix084.helper075.GETTER[6:]
    cd=prior_model.phase086.returns085.suffix084.helper075.COORDINATES[:28]+prior_model.removal._bl(coord+28,h+0x2000)+prior_model.phase086.returns085.suffix084.helper075.COORDINATES[32:]
    helper=prior_model.phase086.returns085.suffix084.helper075.Layout(h,bytes(b),g,getter,identity,b'\x70\x47',coord,cd)
    cb=bytearray(p.callback_data);cb[120:124]=prior_model.removal._bl(p.callback+120,bios);cb[138:142]=prior_model.removal._bl(p.callback+138,h)
    p=replace(p,callback_data=bytes(cb))
    return prior_model.phase086.returns085.Layout(prior_model.phase086.returns085.suffix084.Layout(p,helper,bios,b'\x0b\xdf\x70\x47'))

def prior_phase_layout(shift=0):
    prior=prior_layout(shift);p84=prior.prior;p83=p84.prior;p82=p83.prior;p81=p82.prior
    predicate,getter,requester=0x081D0000+shift,0x081D0400+shift,0x081D0800+shift
    owners=[]
    for n,a,b in p81.owners:
        if n=='callback':
            b=bytearray(b)
            for off,t in ((56,predicate),(84,requester)):b[off:off+4]=prior_model.removal._bl(a+off,t)
            b=bytes(b)
        owners.append((n,a,b))
    prior=replace(prior,prior=replace(p84,prior=replace(p83,prior=replace(p82,prior=replace(p81,owners=tuple(owners))))))
    predicate_data=prior_model.phase086.PREDICATE[:2]+prior_model.removal._bl(predicate+2,getter)+prior_model.phase086.PREDICATE[6:]
    requester_data=prior_model.phase086.REQUESTER[:24]+prior_model.removal._bl(requester+24,p83.scheduler.address)+prior_model.phase086.REQUESTER[28:]
    return prior_model.phase086.Layout(prior,predicate,predicate_data,getter,prior_model.phase086.GETTER,requester,requester_data)

def prior_count_layout(shift=0):
    prior=prior_phase_layout(shift);cb=0x080D791C;pw=0x081E0400+shift;gw=0x081E0800+shift
    owners=prior_model.phase086._validate(prior);target=owners['allocator_wrapper'][0]
    data=bytearray(prior_model.CALLBACK)
    for off,t in ((88,pw),(98,gw)):data[off:off+4]=prior_model.removal._bl(cb+off,t)
    p=prior_model.POOL_WRAPPER[:4]+prior_model.removal._bl(pw+4,target)+prior_model.POOL_WRAPPER[8:]
    g=prior_model.GLOBAL_WRAPPER[:8]+prior_model.removal._bl(gw+8,target)+prior_model.GLOBAL_WRAPPER[12:]
    return prior_model.Layout(prior,cb,bytes(data),pw,p,gw,g)

def layout(shift=0):
    p=prior_count_layout(shift);addresses={'prepare':0x080D758C,'transfer':0x080D7798,'writer':0x080D7864,'fast_bios':0x08141868,'lz_bios':0x08141890}
    deps=[]
    for role,a in addresses.items():
        b=bytearray(model.SHAPES[role])
        for off,target in model.EDGES.get(role,{}).items():b[off:off+4]=model.removal._bl(a+off,addresses[target] if type(target) is str else target)
        if role=='transfer':
            b[36:40]=(a+40).to_bytes(4,'little')
            for i,off in enumerate(model.TABLE_OFFSETS):b[40+4*i:44+4*i]=(a+off).to_bytes(4,'little')
        deps.append((role,a,bytes(b)))
    return model.Layout(p,tuple(deps))
def half(m,a,v):put(m,a,tuple((v&65535).to_bytes(2,'little')))
def fixture(kind=6,flags=0,cursor=0,limit=1,subkind=1,subflags=0,count=100,shift=0):
    l=layout(shift);m={E-128+i:('opaque-byte','088 explicit stack origin',i) for i in range(128)}
    half(m,DESC,256);put(m,PAYLOAD,P(RECORD));m[PAYLOAD+6]=limit;m[PAYLOAD+7]=cursor
    put(m,PAYLOAD+24,O('prior source word'));put(m,PAYLOAD+32,P(BUFFER+200));put(m,PAYLOAD+36,P(BUFFER))
    a=RECORD+12*cursor;m[a]=kind;m[a+1]=flags;half(m,a+2,count);put(m,a+4,P(HANDLE));put(m,a+8,P(BUFFER))
    if kind==3:
        put(m,HANDLE,P(SUB));m[SUB]=subkind;m[SUB+1]=subflags
    elif kind==2:m[HANDLE]=0
    r={i:O('088 inputR'+str(i)) for i in range(15)};r.update({0:P(NODE),1:P(DESC),2:P(PAYLOAD),13:P(E),14:I(RETURN)})
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR)

def raw(f,stop_before=None):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for a,b in model._validate(f['layout']).values()};regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
    mem={f['arena_base']+k:byte(v,f['arena_base']) for k,v in f['cells'].items()};pc=at(f['layout'],'callback40');events=[];trace=[]
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
            d=reg(ops[0]);v=val(ops[1])
            if d==15:nxt=v
            else:regs[d]=v
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
                    rom_owner=next((p for p,b in bodies.items() if p<=a and a+width<=p+len(b)),None)
                    if rom_owner is not None:regs[reg(ops[0])]=int.from_bytes(bodies[rom_owner][a-rom_owner:a-rom_owner+width],'little')
                    else:regs[reg(ops[0])]=read(a,width)
                else:write(a,width,regs[reg(ops[0])])
        elif n=='svc':break
        else:raise AssertionError((hex(pc),n,i.op_str))
        pc=nxt
    else:raise AssertionError('raw oracle bound exhausted')
    return regs,mem,trace,events,pc


@unittest.skipIf(IMAGE is None,'set FFTA_SOURCE84_IMAGE to the private authenticated176B source')
class BufferPhaseTests(unittest.TestCase):
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
        self.assertEqual(r['final_PC'],RETURN&~1);self.assertEqual(r['registers'][13],P(E));self.assert_raw(f,r)
    def test_high_record_kind_returns_after_actual_phase257_write(self):
        f=fixture();r=self.derive(f);artifact('new-high-kind-return.json',r);self.returned(f,r)
        self.assertEqual((memory(r)[DESC],memory(r)[DESC+1]),(1,1));self.assertEqual(r['guarded_switch_events'],[])
    def test_empty_type2_operation_list_returns_through_guarded_switch(self):
        f=fixture(kind=2);r=self.derive(f);artifact('new-type2-empty-return.json',r);self.returned(f,r)
        self.assertEqual((memory(r)[DESC],memory(r)[DESC+1]),(3,1));self.assertEqual(memory(r)[PAYLOAD+7],1)
        self.assertEqual([s['index'] for s in r['guarded_switch_events']],[2])
    def test_fastfill_type4_prepares_exact_local_source_and_stops_at_svc(self):
        f=fixture(kind=4,flags=1);r=self.derive(f);artifact('new-fastfill-cutpoint.json',r)
        self.assertEqual(r['final_PC'],at(f['layout'],'fast_bios'));self.assertEqual(r['boundary']['service'],12)
        self.assertEqual(r['registers'][0],P(E-28));self.assertEqual(r['registers'][1],P(BUFFER));self.assertEqual(r['registers'][2],I(0x01001000))
        self.assertEqual(tuple(memory(r)[E-28+i] for i in range(4)),I(0x03FF03FF));self.assert_raw(f,r)
        self.assertFalse(r['actual_BIOS_poststate_proved'])
    def test_type1_decompression_reaches_actual_svc11_without_effect(self):
        f=fixture(kind=1);r=self.derive(f);self.assertEqual(r['boundary']['service'],17)
        self.assertEqual(r['final_PC'],at(f['layout'],'lz_bios'));self.assertEqual(r['registers'][0],P(HANDLE));self.assertEqual(r['registers'][1],P(BUFFER));self.assert_raw(f,r)
    def test_type3_real_subrecord_preparation_stops_at_next_actual_helper(self):
        f=fixture(kind=3,subkind=3,subflags=0,count=100);r=self.derive(f);artifact('new-type3-preparation-cutpoint.json',r)
        self.assertEqual(r['final_PC'],0x080D7674);self.assertFalse(r['nested_call_cutpoint']['callee_executed'])
        self.assertEqual(tuple(memory(r)[PAYLOAD+20+i] for i in range(4)),I(75))
        self.assertEqual(tuple(memory(r)[PAYLOAD+24+i] for i in range(4)),P(SUB+4));self.assert_raw(f,r)

    def test_fastfill_type5_uses_actual_negative_one_local_word(self):
        f=fixture(kind=5,flags=1);r=self.derive(f);self.assertEqual(r['boundary']['service'],12)
        self.assertEqual(r['registers'][0],P(E-24));self.assertEqual(tuple(memory(r)[E-24+i] for i in range(4)),I(0xffffffff));self.assert_raw(f,r)

    def test_fastfill_other_type_uses_zero_local_word_without_buffer_effects(self):
        f=fixture(kind=0,flags=1);put(f['cells'],BUFFER,O('untouched destination'))
        r=self.derive(f);self.assertEqual(r['boundary']['service'],12);self.assertEqual(r['registers'][0],P(E-20))
        self.assertEqual(tuple(memory(r)[E-20+i] for i in range(4)),I(0));self.assertEqual(tuple(memory(r)[BUFFER+i] for i in range(4)),O('untouched destination'));self.assert_raw(f,r)

    def test_fastfill_source_destination_alias_is_retained_as_condition(self):
        f=fixture(kind=4,flags=1);put(f['cells'],PAYLOAD+36,P(E-28));r=self.derive(f)
        self.assertEqual(r['registers'][0],r['registers'][1]);self.assertEqual(r['boundary']['service'],12);self.assert_raw(f,r)

    def test_fastfill_unknown_destination_is_transported_without_permission(self):
        f=fixture(kind=4,flags=1);put(f['cells'],PAYLOAD+36,O('unknown buffer pointer'));r=self.derive(f)
        self.assertEqual(r['registers'][1],O('unknown buffer pointer'));self.assertEqual(r['boundary']['service'],12);self.assert_raw(f,r)

    def test_type2_nonempty_list_prepares_real_fifth_stack_argument(self):
        f=fixture(kind=2);f['cells'][HANDLE]=1;put(f['cells'],HANDLE+4,P(SUB));put(f['cells'],SUB,O('opaque operation argument'))
        for off,v in ((4,17),(5,33),(6,65),(7,129)):f['cells'][SUB+off]=v
        r=self.derive(f);self.assertEqual(r['final_PC'],0x080D45D0);self.assertFalse(r['nested_call_cutpoint']['callee_executed'])
        self.assertEqual(r['registers'][0],O('opaque operation argument'));self.assertEqual([r['registers'][i] for i in (1,2,3)],[I(17),I(33),I(65)])
        self.assertEqual(r['registers'][13],P(E-52));self.assertEqual(tuple(memory(r)[E-52+i] for i in range(4)),I(129));self.assert_raw(f,r)
        artifact('new-type2-operation-cutpoint.json',r)

    def test_type2_empty_list_next_record_returns_phase256(self):
        f=fixture(kind=2,limit=2);r=self.derive(f);self.returned(f,r)
        self.assertEqual((memory(r)[DESC],memory(r)[DESC+1]),(0,1));self.assertEqual(memory(r)[PAYLOAD+7],1)

    def test_cursor255_arithmetic_and_byte_increment_wrap_match_actual_thumb(self):
        f=fixture(kind=2,cursor=255,limit=0);r=self.derive(f);self.returned(f,r)
        self.assertEqual(memory(r)[PAYLOAD+7],0);self.assertEqual((memory(r)[DESC],memory(r)[DESC+1]),(3,1))

    def test_type0_opaque_record_word_survives_until_actual_numeric_query(self):
        f=fixture(kind=0);w=O('opaque selected source');put(f['cells'],RECORD+4,w)
        r=self.derive(f);self.assertEqual(r['final_PC'],0x080C95A8);self.assertEqual(r['registers'][0],I(13))
        self.assertEqual(tuple(memory(r)[PAYLOAD+24+i] for i in range(4)),w);self.assert_raw(f,r)

    def test_type4_transfer_reaches_exact_format_helper_interface(self):
        f=fixture(kind=4);put(f['cells'],HANDLE,P(SUB));half(f['cells'],HANDLE+4,91);f['cells'][HANDLE+6]=7
        r=self.derive(f);self.assertEqual(r['final_PC'],0x080D6A34)
        self.assertEqual([r['registers'][i] for i in range(4)],[P(BUFFER),P(SUB),I(91),I(7)]);self.assert_raw(f,r)

    def test_type5_transfer_reaches_exact_other_format_helper_interface(self):
        f=fixture(kind=5);put(f['cells'],HANDLE,P(SUB));half(f['cells'],HANDLE+4,91)
        r=self.derive(f);self.assertEqual(r['final_PC'],0x080D6D0C)
        self.assertEqual([r['registers'][i] for i in range(3)],[P(BUFFER),P(SUB),I(91)]);self.assert_raw(f,r)

    def test_type3_flagged_eighth_width_and_stride_are_actual_integer_shifts(self):
        f=fixture(kind=3,subkind=1,subflags=1,count=103);r=self.derive(f)
        self.assertEqual(r['final_PC'],0x080D7674);m=memory(r)
        self.assertEqual(tuple(m[PAYLOAD+20+i] for i in range(4)),I(12));self.assertEqual((m[PAYLOAD+16],m[PAYLOAD+17]),(128,0));self.assert_raw(f,r)

    def test_type3_compressed_nonzero_conversion_selects_first_allocation(self):
        f=fixture(kind=3,subkind=1,subflags=3);r=self.derive(f)
        self.assertEqual(r['boundary']['service'],17);self.assertEqual(r['registers'][0],P(SUB+4));self.assertEqual(r['registers'][1],P(BUFFER+200));self.assert_raw(f,r)

    def test_type3_compressed_direct_mode_selects_second_allocation(self):
        f=fixture(kind=3,subkind=4,subflags=2);r=self.derive(f)
        self.assertEqual(r['boundary']['service'],17);self.assertEqual(r['registers'][0],P(SUB+4));self.assertEqual(r['registers'][1],P(BUFFER));self.assert_raw(f,r)

    def test_phase_store_aliases_saved_r4_and_changes_actual_returned_register(self):
        f=fixture();f['registers'][1]=P(E-16);f['registers'][4]=I(256)
        r=self.derive(f);self.returned(f,r);self.assertEqual(r['registers'][4],I(257));self.assertFalse(r['ABI_preservation_assumed'])

    def test_phase_store_aliases_selected_record_count_before_helper_reload(self):
        f=fixture(kind=3,subkind=9,count=256);f['registers'][1]=P(RECORD+2)
        r=self.derive(f);self.assertEqual(r['final_PC'],0x080D7674)
        self.assertEqual(tuple(memory(r)[PAYLOAD+20+i] for i in range(4)),I(257));self.assert_raw(f,r)

    def test_prefix_clear_aliases_selected_record_pointer_and_refuses(self):
        f=fixture();put(f['cells'],PAYLOAD,P(PAYLOAD+24));put(f['cells'],PAYLOAD+24,I(6));put(f['cells'],PAYLOAD+28,P(HANDLE))
        # The prefix clears the selected record's kind/flags. The actual
        # type0 transfer then replaces those same bytes with a pointer word.
        r=self.derive(f);self.assertEqual([s['index'] for s in r['guarded_switch_events']],[0])
        self.assertEqual(tuple(memory(r)[PAYLOAD+24+i] for i in range(4)),P(HANDLE))
        self.assertEqual(r['boundary']['site'],at(f['layout'],'transfer',190));self.assertIn('narrow read',r['boundary']['reason'])
        self.assert_raw(f,r,stop_before=at(f['layout'],'transfer',190))

    def test_literal_record_address_without_provenance_is_not_a_readable_table(self):
        f=fixture();put(f['cells'],PAYLOAD,I(0x0839D7E4));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',128));self.assertIn('provenance',r['boundary']['reason'])

    def test_missing_selected_record_flag_is_not_initialized_by_allocation(self):
        f=fixture();del f['cells'][RECORD+1];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',128));self.assertIn('reaching',r['boundary']['reason'])

    def test_retired_selected_record_bytes_stop_before_flag_read(self):
        f=fixture();f['retired_stack_spans']=((RECORD,RECORD+12),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',128));self.assertIn('retired',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'callback40',128))

    def test_protected_phase_word_refuses_real_phase257_store(self):
        f=fixture();f['protected_spans']=((DESC,DESC+2),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',194));self.assertIn('protected',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'callback40',194))

    def test_opaque_cursor_is_not_used_as_a_table_index(self):
        f=fixture();f['cells'][PAYLOAD+7]=('opaque-byte','unknown cursor',0);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',116));self.assertIn('narrow read',r['boundary']['reason'])

    def test_other_entry_phase_is_refused_after_real_save_and_phase_load(self):
        f=fixture();half(f['cells'],DESC,257);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',8));self.assertIn('exact256',r['boundary']['reason']);self.assertTrue(r['memory_events'])

    def test_complete_table_entry_mutation_is_refused_before_execution(self):
        f=fixture();deps=[]
        for n,a,b in f['layout'].dependencies:
            if n=='transfer':v=bytearray(b);v[40]^=2;b=bytes(v)
            deps.append((n,a,b))
        f['layout']=replace(f['layout'],dependencies=tuple(deps))
        with self.assertRaisesRegex(ValueError,'transfer identity'):self.derive(f)

    def test_actual_switch_guard_mutation_cannot_select_the_relation(self):
        f=fixture();deps=[]
        for n,a,b in f['layout'].dependencies:
            if n=='transfer':v=bytearray(b);v[20]=6;b=bytes(v)
            deps.append((n,a,b))
        f['layout']=replace(f['layout'],dependencies=tuple(deps))
        with self.assertRaisesRegex(ValueError,'transfer identity'):self.derive(f)

    def test_explicit_new_selector_has_no_default_admission(self):
        f=fixture();f['selector']='default'
        with self.assertRaisesRegex(ValueError,'explicit088'):self.derive(f)

    def test_bound_dependency_set_uses_complete_current_shapes(self):
        f=fixture(shift=0x10000);l=f['layout'];f['layout']=model.bind(l.prior,l.dependencies,selector=model.SELECTOR)
        r=self.derive(f);self.returned(f,r)

    def test_explicit_execution_bound_is_not_a_termination_claim(self):
        f=fixture(kind=2);f['max_steps']=30;r=self.derive(f)
        self.assertEqual(len(r['trace']),30);self.assertIn('budget',r['boundary']['reason']);self.assertFalse(r['actual_termination_proved'])
