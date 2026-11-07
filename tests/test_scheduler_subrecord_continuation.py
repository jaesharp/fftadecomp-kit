"""New089 subrecord continuation cases and independent raw oracle."""
from dataclasses import replace
import unittest,hashlib,json,os
from pathlib import Path
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_subrecord_continuation as model
buffer_model=model.buffer088
prior_model=buffer_model.count087
upstream=prior_model.source083
BASE,E,NODE,PAYLOAD,DESC,RECORD,BUFFER,SUB,HANDLE,SRC,DST=0x02000000,10000,2000,3000,5000,6000,7000,8000,9000,12000,13000
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

def prior_buffer_layout(shift=0):
    p=prior_count_layout(shift);addresses={'prepare':0x080D758C,'transfer':0x080D7798,'writer':0x080D7864,'fast_bios':0x08141868,'lz_bios':0x08141890}
    deps=[]
    for role,a in addresses.items():
        b=bytearray(buffer_model.SHAPES[role])
        for off,target in buffer_model.EDGES.get(role,{}).items():b[off:off+4]=buffer_model.removal._bl(a+off,addresses[target] if type(target) is str else target)
        if role=='transfer':
            b[36:40]=(a+40).to_bytes(4,'little')
            for i,off in enumerate(buffer_model.TABLE_OFFSETS):b[40+4*i:44+4*i]=(a+off).to_bytes(4,'little')
        deps.append((role,a,bytes(b)))
    return buffer_model.Layout(p,tuple(deps))
def layout(shift=0):
    p=prior_buffer_layout(shift);addresses={'subrecord':0x080D7674,'byte1':0x080D702C,'byte2':0x080D7080,'byte3':0x080D70D8,'byte4':0x080D7150,'nibble1':0x080D6EEC,'nibble2':0x080D6F64,'nibble3':0x080D6FBC}
    bios=buffer_model._validate(p)['bios'][0];deps=[]
    for role,a in addresses.items():
        b=bytearray(model.SHAPES[role])
        if role=='subrecord':
            for off,target in model.EDGES.items():b[off:off+4]=model.removal._bl(a+off,bios if target=='bios' else addresses[target])
        deps.append((role,a,bytes(b)))
    return model.Layout(p,tuple(deps))
def half(m,a,v):put(m,a,tuple((v&65535).to_bytes(2,'little')))
def fixture(kind=1,flags=0,remaining=4,stride=1,shift=0):
    l=layout(shift);m={E-128+i:('opaque-byte','089 explicit stack origin',i) for i in range(168)}
    for off,w in ((0,P(PAYLOAD)),(4,I(0)),(8,I(at(l,'callback40',214)|1)),(24,O('entryR4')),(28,O('entryR5')),(32,O('entryR6')),(36,I(RETURN))):put(m,E+off,w)
    half(m,DESC,257);put(m,PAYLOAD,P(RECORD));m[PAYLOAD+6]=1;m[PAYLOAD+7]=0;half(m,PAYLOAD+16,stride)
    put(m,PAYLOAD+20,I(remaining));put(m,PAYLOAD+24,P(SRC));put(m,PAYLOAD+28,P(DST))
    put(m,PAYLOAD+32,P(BUFFER+200));put(m,PAYLOAD+36,P(BUFFER))
    m[RECORD]=3;m[RECORD+1]=0;half(m,RECORD+2,31);put(m,RECORD+4,P(HANDLE));put(m,RECORD+8,P(BUFFER))
    put(m,HANDLE,P(SUB));m[HANDLE+4]=5;m[HANDLE+5]=2;m[HANDLE+6]=0;m[SUB]=kind;m[SUB+1]=flags
    for i,v in enumerate((0xA5,0x3C,0x81,0x69,0x96,0xC3)):m[SRC+i]=v
    for i in range(-4,40):m[DST+i]=0xCC
    r={i:O('089 inputR'+str(i)) for i in range(15)};r.update({0:P(PAYLOAD),4:P(PAYLOAD),5:I(0),6:P(DESC),13:P(E),14:I(at(l,'transfer',90)|1)})
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR,callback_entry_sp=E+40,callback_return_word=I(RETURN))

def raw(f,stop_before=None,stop_visit=1):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for a,b in model._validate(f['layout']).values()};regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
    mem={f['arena_base']+k:byte(v,f['arena_base']) for k,v in f['cells'].items()};pc=at(f['layout'],'subrecord');events=[];trace=[]
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
        if pc==stop_before and trace.count(pc)+1==stop_visit:trace.append(pc);break
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
class SubrecordTests(unittest.TestCase):
    def assert_raw(self,f,r,stop_before=None,stop_visit=1):
        regs,mem,trace,events,pc=raw(f,stop_before,stop_visit)
        self.assertEqual(r['trace'],trace);self.assertEqual(r['final_PC'],pc)
        self.assertEqual({k:number(v,f['arena_base']) for k,v in r['registers'].items()},regs)
        got=memory(r)
        for a,v in mem.items():self.assertEqual(byte(got[a-f['arena_base']],f['arena_base']),v,(hex(a),v))
        actual=[(e['site'],e['operation'],e['coordinate'],tuple(byte(v,f['arena_base']) for v in e['bytes'])) for e in r['memory_events'] if 'coordinate' in e]
        self.assertEqual(actual,events)
    def derive(self,f):return model.derive(**f)
    def returned(self,f,r):
        self.assertTrue(r['conditional_callback_return'],r['boundary']);self.assertIsNone(r['boundary']);self.assertEqual(r['pending_calls'],[])
        self.assertEqual(r['final_PC'],RETURN&~1);self.assertEqual(r['registers'][13],P(E+40));self.assert_raw(f,r)
    def test_real_one_bit_to_nibbles_and_partial_chunk_return(self):
        f=fixture();r=self.derive(f);artifact('new-nibble1-partial-return.json',r);self.returned(f,r);m=memory(r)
        self.assertEqual([m[DST+i] for i in range(4)],[5,5,0x50,0x50])
        self.assertEqual(tuple(m[PAYLOAD+20+i] for i in range(4)),I(3));self.assertEqual(tuple(m[PAYLOAD+24+i] for i in range(4)),P(SRC+1));self.assertEqual(tuple(m[PAYLOAD+28+i] for i in range(4)),P(DST+1024))
    def test_real_two_bit_packing_includes_actual_trailing_zero(self):
        f=fixture(kind=2);r=self.derive(f);self.returned(f,r)
        self.assertEqual([memory(r)[DST+i] for i in range(4)],[0x11,0x22,0,0xCC])
    def test_real_three_bit_packing_uses_three_source_bytes(self):
        f=fixture(kind=3,stride=3,remaining=6);r=self.derive(f);self.returned(f,r);v=0x813CA5
        chunks=[(v>>(3*i))&7 for i in range(8)];expected=[chunks[2*i]|(chunks[2*i+1]<<4) for i in range(4)]
        self.assertEqual([memory(r)[DST+i] for i in range(5)],expected+[0])
    def test_flagged_one_bit_expansion_consumes_real_fifth_argument(self):
        f=fixture(kind=1,flags=1);r=self.derive(f);self.returned(f,r)
        self.assertEqual([memory(r)[DST+i] for i in range(8)],[0x25 if 0xA5&(1<<i) else 0 for i in range(8)])
    def test_flagged_two_bit_expansion_preserves_transparent_zero(self):
        f=fixture(kind=2,flags=1);f['cells'][SRC]=0x21;r=self.derive(f);self.returned(f,r)
        self.assertEqual([memory(r)[DST+i] for i in range(4)],[0x21,0,0x22,0])
    def test_flagged_three_bit_expansion_restores_actual_high_saves(self):
        f=fixture(kind=3,flags=1,stride=3,remaining=6);r=self.derive(f);self.returned(f,r);v=0x813CA5
        self.assertEqual([memory(r)[DST+i] for i in range(8)],[((v>>(3*i))&7)|0x20 if ((v>>(3*i))&7) else 0 for i in range(8)])
        for reg in (8,9,10):self.assertEqual(r['registers'][reg],f['registers'][reg])
    def test_flagged_four_bit_expansion_follows_actual_two_byte_loop(self):
        f=fixture(kind=4,flags=1);r=self.derive(f);self.returned(f,r)
        self.assertEqual([memory(r)[DST+i] for i in range(3)],[0x25,0x2A,0xCC])

    def test_completed_chunk_clamps_stride_then_reaches_actual_writer_query(self):
        f=fixture(remaining=1,stride=4);r=self.derive(f);artifact('new-completed-chunk-query.json',r)
        self.assertEqual(r['final_PC'],0x080C95A8);self.assertFalse(r['nested_call_cutpoint']['callee_executed']);self.assertEqual(r['registers'][0],I(13))
        self.assertEqual((memory(r)[PAYLOAD+16],memory(r)[PAYLOAD+17]),(1,0));self.assertEqual((memory(r)[DESC],memory(r)[DESC+1]),(2,1));self.assert_raw(f,r)

    def test_zero_count_never_reads_missing_source_but_still_transports_actual_frames(self):
        f=fixture(remaining=0,stride=4)
        for i in range(6):del f['cells'][SRC+i]
        r=self.derive(f);self.assertEqual(r['final_PC'],0x080C95A8);self.assert_raw(f,r)
        self.assertFalse(any(SRC<=e.get('coordinate',-1)<SRC+6 for e in r['memory_events']))

    def test_three_bit_positive_count_reads_triplet_but_advances_by_actual_stride(self):
        f=fixture(kind=3,stride=1,remaining=4);r=self.derive(f);self.returned(f,r)
        read={e['coordinate'] for e in r['memory_events'] if e['operation']=='read8'}
        self.assertTrue({SRC,SRC+1,SRC+2}<=read);self.assertEqual(tuple(memory(r)[PAYLOAD+24+i] for i in range(4)),P(SRC+1))

    def test_three_bit_four_byte_count_reads_two_complete_triplets(self):
        f=fixture(kind=3,flags=1,stride=4,remaining=8);r=self.derive(f);self.returned(f,r)
        read={e['coordinate'] for e in r['memory_events'] if e['operation']=='read8'}
        self.assertTrue(set(range(SRC,SRC+6))<=read);self.assertEqual(tuple(memory(r)[PAYLOAD+24+i] for i in range(4)),P(SRC+4))

    def test_three_bit_count_does_not_grant_missing_extra_source_byte(self):
        f=fixture(kind=3,stride=1);del f['cells'][SRC+1];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'nibble3',30));self.assertIn('reaching',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'nibble3',30))

    def test_actual_trailing_packed_zero_respects_output_protection(self):
        f=fixture(kind=2);f['protected_spans']=((DST+2,DST+3),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'nibble2',50));self.assertIn('protected',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'nibble2',50),stop_visit=2)

    def test_overlapping_expansion_observes_prior_writes_to_next_source_byte(self):
        f=fixture(kind=1,flags=1,stride=2,remaining=4);put(f['cells'],PAYLOAD+28,P(SRC));f['cells'][SRC]=1;f['cells'][SRC+1]=2
        r=self.derive(f);self.returned(f,r)
        self.assertEqual([memory(r)[SRC+i] for i in range(16)],[0x25]+[0]*15)
        reads=[e['bytes'][0] for e in r['memory_events'] if e['operation']=='read8' and e['coordinate']==SRC+1];self.assertEqual(reads,[0])

    def test_conversion_alias_changes_reloaded_stride_and_remaining_subtraction(self):
        f=fixture(kind=1,flags=1);put(f['cells'],PAYLOAD+28,P(PAYLOAD+16));f['cells'][SRC]=1
        r=self.derive(f);self.returned(f,r);m=memory(r)
        self.assertEqual(tuple(m[PAYLOAD+24+i] for i in range(4)),P(SRC+37))
        self.assertEqual(tuple(m[PAYLOAD+20+i] for i in range(4)),I(0xffffffdb));self.assertEqual(tuple(m[PAYLOAD+28+i] for i in range(4)),P(PAYLOAD+1040))

    def test_output_alias_to_converter_saved_lr_is_not_an_abi_assumption(self):
        f=fixture(kind=1,flags=1);put(f['cells'],PAYLOAD+28,P(E-24));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'byte1',82));self.assertIn('saved return',r['boundary']['reason']);self.assertFalse(r['ABI_preservation_assumed']);self.assert_raw(f,r,stop_before=at(f['layout'],'byte1',82))

    def test_unflagged_direct_copy_prepares_exact_cpuset_cutpoint(self):
        f=fixture(kind=4,flags=0);r=self.derive(f);artifact('new-cpuset-cutpoint.json',r)
        self.assertEqual(r['boundary']['service'],11);self.assertEqual(r['final_PC'],at(f['layout'],'bios'))
        self.assertEqual([r['registers'][i] for i in range(3)],[P(SRC),P(DST),I(15)]);self.assert_raw(f,r)

    def test_flagged_eight_bit_direct_copy_has_same_real_cpuset_contract(self):
        f=fixture(kind=8,flags=1);r=self.derive(f)
        self.assertEqual(r['boundary']['service'],11);self.assertEqual(r['registers'][2],I(15));self.assert_raw(f,r)

    def test_direct_copy_compression_flag_skips_bios_without_fabricated_effect(self):
        f=fixture(kind=4,flags=2);r=self.derive(f);self.returned(f,r)
        self.assertNotIn(at(f['layout'],'bios'),r['trace']);self.assertEqual([memory(r)[DST+i] for i in range(4)],[0xCC]*4)

    def test_unknown_subtype_follows_real_default_and_partial_state_updates(self):
        f=fixture(kind=255,flags=0);r=self.derive(f);self.returned(f,r)
        self.assertEqual(tuple(memory(r)[PAYLOAD+20+i] for i in range(4)),I(3));self.assertEqual(memory(r)[DST],0xCC)

    def test_missing_palette_byte_is_not_inferred_from_conversion_name(self):
        f=fixture(kind=2,flags=1);del f['cells'][HANDLE+5];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'subrecord',80));self.assertIn('reaching',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'subrecord',80))

    def test_retired_source_is_not_revived_by_converter_stack_allocation(self):
        f=fixture();f['retired_stack_spans']=((SRC,SRC+1),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'nibble1',38));self.assertIn('retired',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'nibble1',38))

    def test_released_frame_refuses_subrecord_push_before_any_load(self):
        f=fixture();f['released_payload_spans']=((E-16,E),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'subrecord'));self.assertIn('externally retired',r['boundary']['reason'])

    def test_opaque_remaining_count_is_not_a_numeric_bound(self):
        f=fixture();put(f['cells'],PAYLOAD+20,O('unknown remaining'));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'subrecord',28));self.assertIn('opaque',r['boundary']['reason'])

    def test_actual_call_register_equality_is_an_explicit_input_guard(self):
        f=fixture();f['registers'][4]=P(PAYLOAD+4);r=self.derive(f)
        self.assertIn('entry differs',r['boundary']['reason']);self.assertEqual(r['memory_events'],[])

    def test_actual_zero_transfer_local_is_not_fabricated_for_arbitrary_entry(self):
        f=fixture();f['registers'][5]=I(1);r=self.derive(f)
        self.assertIn('entry differs',r['boundary']['reason']);self.assertEqual(r['memory_events'],[])

    def test_changed_complete_converter_instruction_is_rejected(self):
        f=fixture();deps=[]
        for n,a,b in f['layout'].dependencies:
            if n=='byte3':v=bytearray(b);v[74]^=1;b=bytes(v)
            deps.append((n,a,b))
        f['layout']=replace(f['layout'],dependencies=tuple(deps))
        with self.assertRaisesRegex(ValueError,'byte3 conversion identity'):self.derive(f)

    def test_bind_uses_exact_complete_edge_and_body_relations(self):
        f=fixture(shift=0x10000);l=f['layout'];f['layout']=model.bind(l.prior,l.dependencies,selector=model.SELECTOR)
        r=self.derive(f);self.returned(f,r)

    def test_explicit_selector_preserves_default_refusal(self):
        f=fixture();f['selector']='default'
        with self.assertRaisesRegex(ValueError,'explicit089'):self.derive(f)

    def test_loop_budget_keeps_partial_effects_without_termination_claim(self):
        f=fixture(kind=1,flags=1,stride=2);f['max_steps']=80;r=self.derive(f)
        self.assertEqual(len(r['trace']),80);self.assertIn('budget',r['boundary']['reason']);self.assertFalse(r['actual_termination_proved'])

    def preceding_report(self,f):
        old=model.buffer088._validate(f['layout'].prior);r=f['registers'];l=f['layout']
        return dict(schema=model.buffer088.SELECTOR,complete_owner_pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(old.items())],final_PC=at(l,'subrecord'),conditional_callback_return=False,
            registers=r,callback_entry_SP=E+40,callback_return_word=I(RETURN),post_cells={str(k):v for k,v in f['cells'].items()},
            nested_call_cutpoint=dict(call_site=at(l,'transfer',86),target=at(l,'subrecord'),SP=E,return_word=r[14],register_arguments={i:r[i] for i in range(4)},callee_executed=False),
            pending_calls=[dict(role='callback40',return_pc=RETURN&~1,entry_sp=E+40),dict(role='transfer',return_pc=at(l,'callback40',214),entry_sp=E+12)],retired_spans=[],conditional_released_payloads=[],obligations=['synthetic conditional entry'])

    def test_continuation_transport_consumes_all_current_bytes_without_old_producer(self):
        f=fixture();p=self.preceding_report(f);r=model.continue_from_088(f['layout'],BASE,p,selector=model.SELECTOR)
        self.returned(f,r);self.assertFalse(r['actual_088_report_authentication_proved']);self.assertEqual(r['inherited_088_obligations'],p['obligations']);artifact('new-transported-subrecord.json',r)

    def test_transport_rejects_already_executed_callee_claim(self):
        f=fixture();p=self.preceding_report(f);p['nested_call_cutpoint']['callee_executed']=True
        with self.assertRaisesRegex(ValueError,'interface'):model.continue_from_088(f['layout'],BASE,p,selector=model.SELECTOR)

    def test_transport_rejects_wrong_saved_owner_pin(self):
        f=fixture();p=self.preceding_report(f);p['complete_owner_pins'][0]['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'exact088'):model.continue_from_088(f['layout'],BASE,p,selector=model.SELECTOR)
