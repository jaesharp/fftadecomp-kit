"""New090 RAM queue continuation cases and independent raw oracle."""
from dataclasses import replace
import unittest,hashlib,json,os
from pathlib import Path
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_buffer_queue_state as model
previous=model.subrecord089
buffer_model=previous.buffer088
prior_model=buffer_model.count087
upstream=prior_model.source083
BASE,E,NODE,PAYLOAD,DESC,RECORD,BUFFER,SUB,HANDLE,SRC,DST=0x02000000,10000,2000,3000,5000,6000,7000,8000,9000,12000,13000
RETURN=0x081FFFF1
I=previous.words._constant;P=previous.words._pointer
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
def prior_subrecord_layout(shift=0):
    p=prior_buffer_layout(shift);addresses={'subrecord':0x080D7674,'byte1':0x080D702C,'byte2':0x080D7080,'byte3':0x080D70D8,'byte4':0x080D7150,'nibble1':0x080D6EEC,'nibble2':0x080D6F64,'nibble3':0x080D6FBC}
    bios=buffer_model._validate(p)['bios'][0];deps=[]
    for role,a in addresses.items():
        b=bytearray(previous.SHAPES[role])
        if role=='subrecord':
            for off,target in previous.EDGES.items():b[off:off+4]=previous.removal._bl(a+off,bios if target=='bios' else addresses[target])
        deps.append((role,a,bytes(b)))
    return previous.Layout(p,tuple(deps))
def half(m,a,v):put(m,a,tuple((v&65535).to_bytes(2,'little')))

QUERY=0x203D;CONTEXT_POINT=0x159C0;QUEUE_POINT=0x01002BCC;CONTEXT=20000
POINTS=(BASE+QUERY,BASE+CONTEXT_POINT,BASE+QUEUE_POINT)

def layout(shift=0):
    p=prior_subrecord_layout(shift);addresses={'query':0x080C95A8,'ring':0x080D3AF8,'payload':0x08005BFC,'enqueue':0x08000A98}
    return model.Layout(p,tuple((n,a,model.SHAPES[n]) for n,a in addresses.items()))
def slot(index=0,context=CONTEXT):
    j=(index+1)&255
    if j>15:j=0
    return context+24+0x918+28*j

def fixture(query=0,remaining=100,ring_index=0,kind=3,mode=0):
    l=layout();m={E-64+i:('opaque-byte','090 explicit stack origin',i) for i in range(116)}
    for off,w in ((4,P(PAYLOAD)),(8,O('writerR5')),(12,P(DESC)),(16,O('writerR7')),(20,I(at(l,'callback40',232)|1)),(36,O('callbackR4')),(40,O('callbackR5')),(44,O('callbackR6')),(48,I(RETURN))):put(m,E+off,w)
    half(m,DESC,258);put(m,PAYLOAD,P(RECORD));m[PAYLOAD+6]=1;m[PAYLOAD+7]=0
    put(m,PAYLOAD+8,I(0x200));put(m,PAYLOAD+12,I(0x400))
    put(m,PAYLOAD+20,I(remaining));put(m,PAYLOAD+24,P(SRC));put(m,PAYLOAD+28,P(DST))
    m[RECORD]=kind;put(m,RECORD+4,P(HANDLE));m[HANDLE+6]=mode
    m[QUERY]=query;put(m,CONTEXT_POINT,P(CONTEXT));m[CONTEXT+24+0x914]=ring_index
    put(m,QUEUE_POINT,I(0))
    for i in range(28):m[slot(ring_index)+i]=('opaque-byte','090 old descriptor',i)
    r={i:O('090 inputR'+str(i)) for i in range(15)}
    r.update({0:I(13),4:P(PAYLOAD),5:I(2048),7:I(0),13:P(E),14:I(at(l,'writer',84)|1)})
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR,callback_entry_sp=E+52,callback_return_word=I(RETURN),literal_points=POINTS)

def report089(f):
    owners=previous._validate(f['layout'].prior);r=f['registers'];e=f['callback_entry_sp']
    return dict(schema=previous.SELECTOR,complete_owner_pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(owners.items())],final_PC=at(f['layout'],'query'),conditional_callback_return=False,registers=r,post_cells={str(k):v for k,v in f['cells'].items()},callback_entry_SP=e,callback_return_word=f['callback_return_word'],nested_call_cutpoint=dict(call_site=at(f['layout'],'writer',80),target=at(f['layout'],'query'),SP=E,return_word=r[14],register_arguments={i:r[i] for i in range(4)},callee_executed=False),pending_calls=[dict(role='callback40',return_pc=RETURN&~1,entry_sp=e),dict(role='writer',return_pc=at(f['layout'],'callback40',232),entry_sp=e-28)],retired_spans=[],conditional_released_payloads=[],obligations=['synthetic conditional reaching witness only'])

def raw(f,stop_before=None,stop_visit=1,step_limit=None):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for a,b in model._validate(f['layout']).values()};regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
    mem={f['arena_base']+k:byte(v,f['arena_base']) for k,v in f['cells'].items()};pc=at(f['layout'],'query');events=[];trace=[]
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
    for step in range(4096):
        if step_limit is not None and step>=step_limit:break
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
class QueueTests(unittest.TestCase):
    def assert_raw(self,f,r,stop_before=None,stop_visit=1,step_limit=None):
        regs,mem,trace,events,pc=raw(f,stop_before,stop_visit,step_limit)
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
    def word(self,r,a):return tuple(memory(r)[a+i] for i in range(4))
    def test_empty_queue_descriptor_and_complete_callback_return(self):
        f=fixture();r=self.derive(f);artifact('new-empty-queue-return.json',r);self.returned(f,r);m=memory(r);d=slot()
        self.assertEqual(self.word(r,QUEUE_POINT),P(d));self.assertEqual([m[d],m[d+1]],[0,1]);self.assertEqual(self.word(r,d+4),P(SRC));self.assertEqual(self.word(r,d+8),P(DST+0x200));self.assertEqual(self.word(r,d+12),I(0x80000032));self.assertEqual(self.word(r,d+24),I(0))
        self.assertEqual(self.word(r,PAYLOAD+24),P(SRC+100));self.assertEqual(self.word(r,PAYLOAD+28),P(DST+100));self.assertEqual(self.word(r,PAYLOAD+20),I(0));self.assertEqual([m[DESC],m[DESC+1]],[3,1])
        for off in (2,3,16,17,18,19,20,21,22,23):self.assertEqual(m[d+off],f['cells'][d+off])
        for key in ('actual_device_transfer_proved','actual_DMA_completion_proved','queued_buffer_lifetime_proved','physical_access_proved','actual_reaching_proved','native_admission'):self.assertIs(r[key],False)
    def test_query_one_limits_chunk_to512_and_preserves_partial_phase(self):
        f=fixture(query=1,remaining=3000);r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.word(r,slot()+12),I(0x80000100));self.assertEqual(self.word(r,PAYLOAD+20),I(2488));self.assertEqual(memory(r)[PAYLOAD+7],0);self.assertEqual([memory(r)[DESC],memory(r)[DESC+1]],[2,1])
    def test_other_query_byte_uses2048_cap_and_actual_nonzero_mode(self):
        f=fixture(query=255,remaining=3000,mode=7);r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.word(r,slot()+12),I(0x80000400));self.assertEqual(self.word(r,slot()+8),P(DST+0x400));self.assertEqual(self.word(r,PAYLOAD+20),I(952))
    def test_non_type3_record_needs_no_handle_or_buffer_offset(self):
        f=fixture(kind=2);del f['cells'][HANDLE+6]
        for a in range(PAYLOAD+8,PAYLOAD+16):del f['cells'][a]
        r=self.derive(f);self.returned(f,r);self.assertEqual(self.word(r,slot()+8),P(DST))
    def test_ring_index14_selects_slot15(self):
        f=fixture(ring_index=14);r=self.derive(f);self.returned(f,r);self.assertEqual(memory(r)[CONTEXT+24+0x914],15);self.assertEqual(self.word(r,QUEUE_POINT),P(slot(14)))
    def test_ring_index15_wraps_to_slot0(self):
        f=fixture(ring_index=15);r=self.derive(f);self.returned(f,r);self.assertEqual(memory(r)[CONTEXT+24+0x914],0);self.assertEqual(self.word(r,QUEUE_POINT),P(slot(15)))
    def test_ring_index255_byte_overflow_selects_slot0(self):
        f=fixture(ring_index=255);r=self.derive(f);self.returned(f,r);self.assertEqual(memory(r)[CONTEXT+24+0x914],0);self.assertEqual(self.word(r,QUEUE_POINT),P(slot(255)))
    def test_nonempty_queue_walks_real_links_and_changes_only_tail(self):
        f=fixture();a,b=26000,26100;put(f['cells'],QUEUE_POINT,P(a));put(f['cells'],a+24,P(b));put(f['cells'],b+24,I(0))
        r=self.derive(f);artifact('new-nonempty-queue-return.json',r);self.returned(f,r)
        self.assertEqual(self.word(r,QUEUE_POINT),P(a));self.assertEqual(self.word(r,a+24),P(b));self.assertEqual(self.word(r,b+24),P(slot()))

    def test_odd_chunk_truncates_half_count_without_claiming_transfer(self):
        f=fixture(remaining=3);r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.word(r,slot()+12),I(0x80000001));self.assertEqual(self.word(r,PAYLOAD+24),P(SRC+3))
        self.assertFalse(any(SRC<=e.get('coordinate',-1)<SRC+3 for e in r['memory_events']));self.assertFalse(r['actual_device_transfer_proved'])

    def test_zero_chunk_still_enqueues_zero_count_and_advances_record(self):
        f=fixture(remaining=0);r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.word(r,slot()+12),I(0x80000000));self.assertEqual(self.word(r,PAYLOAD+24),P(SRC));self.assertEqual(memory(r)[PAYLOAD+7],1)

    def test_completed_chunk_with_next_record_sets_actual_phase256(self):
        f=fixture();f['cells'][PAYLOAD+6]=2;r=self.derive(f);self.returned(f,r)
        self.assertEqual(memory(r)[PAYLOAD+7],1);self.assertEqual([memory(r)[DESC],memory(r)[DESC+1]],[0,1])

    def test_descriptor_aliases_cursors_and_remaining_with_ordered_reloads(self):
        f=fixture();d=PAYLOAD+12;context=d-24-0x918-28
        put(f['cells'],CONTEXT_POINT,P(context));f['cells'][context+24+0x914]=0
        r=self.derive(f);artifact('new-descriptor-alias-return.json',r);self.returned(f,r)
        self.assertEqual(self.word(r,QUEUE_POINT),P(d));self.assertEqual(self.word(r,PAYLOAD+20),P(DST+0x200-100));self.assertEqual(self.word(r,PAYLOAD+24),I(0x80000032+100));self.assertEqual(self.word(r,PAYLOAD+28),P(DST+100))
        sequence=[e['bytes'] for e in r['memory_events'] if e.get('coordinate')==PAYLOAD+20 and e['operation']=='read32']
        self.assertEqual(sequence,[I(100),P(DST+0x200)])

    def test_existing_queue_node_equal_selected_slot_observes_zero_then_self_link(self):
        f=fixture();put(f['cells'],QUEUE_POINT,P(slot()));put(f['cells'],slot()+24,P(27000))
        r=self.derive(f);self.returned(f,r);self.assertEqual(self.word(r,slot()+24),P(slot()))
        self.assertFalse(r['actual_termination_proved']);self.assertFalse(r['actual_DMA_completion_proved'])

    def test_queue_cycle_stops_at_explicit_bound_without_assumed_acyclicity(self):
        f=fixture();head=26000;put(f['cells'],QUEUE_POINT,P(head));put(f['cells'],head+24,P(head));f['max_steps']=150
        r=self.derive(f);artifact('new-cyclic-queue-boundary.json',r)
        self.assertIn('budget',r['boundary']['reason']);self.assertEqual(len(r['trace']),150);self.assertFalse(r['conditional_callback_return']);self.assert_raw(f,r,step_limit=150)
        self.assertEqual(self.word(r,head+24),P(head));self.assertEqual(r['pending_calls'][-1]['role'],'enqueue')

    def test_exact_unaligned_byte_literal_does_not_grant_adjacent_points(self):
        f=fixture();f['literal_points']=(BASE+QUERY-13,BASE+CONTEXT_POINT,BASE+QUEUE_POINT);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'query',12));self.assertIn('provenance',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'query',12))

    def test_missing_query_byte_retains_precise_readability_refusal(self):
        f=fixture();del f['cells'][QUERY];r=self.derive(f)
        self.assertEqual(r['boundary']['coordinate'],QUERY);self.assertIn('reaching',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'query',12))

    def test_opaque_query_byte_is_not_an_initialized_scalar(self):
        f=fixture();f['cells'][QUERY]=('opaque-byte','query unknown',0);r=self.derive(f)
        self.assertIn('narrow read',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'query',12))

    def test_opaque_source_word_is_queued_intact_then_cursor_add_refuses(self):
        f=fixture();put(f['cells'],PAYLOAD+24,O('opaque source bits'));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'writer',158));self.assertEqual(self.word(r,slot()+4),O('opaque source bits'));self.assertIn('scalar observation',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'writer',158))

    def test_unaligned_queue_link_still_refuses_word_access(self):
        f=fixture();put(f['cells'],QUEUE_POINT,P(26001));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'enqueue',54));self.assertIn('unaligned',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'enqueue',54))

    def test_literal_head_identity_does_not_retype_ordinary_scalar_next(self):
        f=fixture();put(f['cells'],QUEUE_POINT,I(BASE+26000));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'enqueue',54));self.assertIn('provenance',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'enqueue',54))

    def test_protected_descriptor_stops_first_write_after_real_ring_increment(self):
        f=fixture();f['protected_spans']=((slot(),slot()+1),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'enqueue',10));self.assertIn('protected',r['boundary']['reason']);self.assertEqual(memory(r)[CONTEXT+24+0x914],1);self.assert_raw(f,r,stop_before=at(f['layout'],'enqueue',10))

    def test_retired_descriptor_payload_remains_dead(self):
        f=fixture();f['released_payload_spans']=((slot(),slot()+28),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'enqueue',10));self.assertIn('retired',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'enqueue',10))

    def test_protected_actual_ring_byte_refuses_before_queue_effects(self):
        f=fixture();idx=CONTEXT+24+0x914;f['protected_spans']=((idx,idx+1),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'ring',20));self.assertIn('protected',r['boundary']['reason']);self.assertEqual(self.word(r,QUEUE_POINT),I(0));self.assert_raw(f,r,stop_before=at(f['layout'],'ring',20))

    def test_descriptor_overwrites_real_writer_return_word_no_ABI_shortcut(self):
        f=fixture();d=E+8;context=d-24-0x918-28;put(f['cells'],CONTEXT_POINT,P(context));f['cells'][context+24+0x914]=0
        r=self.derive(f);self.assertEqual(r['boundary']['site'],at(f['layout'],'writer',182));self.assertIn('not Thumb',r['boundary']['reason']);self.assertFalse(r['conditional_callback_return']);self.assert_raw(f,r,stop_before=at(f['layout'],'writer',182))

    def test_corrupt_enclosing_callback_saved_target_is_observed(self):
        f=fixture();put(f['cells'],E+48,I(RETURN+4));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',334));self.assertIn('saved return',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'callback40',334))

    def test_callback_saved_pointer_remains_opaque_until_phase_store(self):
        f=fixture();put(f['cells'],E+12,O('unknown phase pointer'));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',324));self.assertIn('provenance',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'callback40',324))

    def test_conditional089_transport_preserves_bytes_and_unproved_authentication(self):
        f=fixture();report=report089(f)
        r=model.continue_from_089(f['layout'],BASE,report,selector=model.SELECTOR,literal_points=POINTS);artifact('new-transported-query.json',r);self.returned(f,r)
        self.assertFalse(r['actual_089_report_authentication_proved']);self.assertEqual(r['inherited_089_obligations'],report['obligations'])

    def test_transport_rejects_stale_owner_pin(self):
        f=fixture();report=report089(f);report['complete_owner_pins'][0]['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'exact089'):model.continue_from_089(f['layout'],BASE,report,selector=model.SELECTOR,literal_points=POINTS)

    def test_transport_rejects_invented_pending_frame(self):
        f=fixture();report=report089(f);report['pending_calls'][1]['entry_sp']+=4
        with self.assertRaisesRegex(ValueError,'interface'):model.continue_from_089(f['layout'],BASE,report,selector=model.SELECTOR,literal_points=POINTS)

    def test_transport_preserves_retired_query_byte(self):
        f=fixture();report=report089(f);report['retired_spans']=[(QUERY,QUERY+1)]
        r=model.continue_from_089(f['layout'],BASE,report,selector=model.SELECTOR,literal_points=POINTS)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'query',12));self.assertIn('retired',r['boundary']['reason']);self.assertFalse(r['physical_access_proved'])

    def test_query_reaching_interface_rejects_changed_incoming_chunk(self):
        f=fixture();f['registers'][5]=I(512);r=self.derive(f)
        self.assertIn('interface',r['boundary']['reason']);self.assertEqual(r['trace'],[]);self.assertEqual(r['memory_events'],[])

    def test_selector_and_full_body_guards_remain_explicit(self):
        f=fixture();l=f['layout']
        with self.assertRaisesRegex(ValueError,'selector'):model.bind(l.prior,l.dependencies,selector='default')
        deps=list(l.dependencies);role,a,b=deps[0];deps[0]=(role,a,b[:-1])
        with self.assertRaisesRegex(ValueError,'complete'):model.bind(l.prior,tuple(deps),selector=model.SELECTOR)
        deps=list(l.dependencies);role,a,b=deps[3];changed=bytearray(b);changed[24]^=1;deps[3]=(role,a,bytes(changed))
        with self.assertRaisesRegex(ValueError,'identity'):model.bind(l.prior,tuple(deps),selector=model.SELECTOR)

    def test_ring_payload_edge_must_match_complete_real_helper(self):
        l=layout();deps=list(l.dependencies);role,a,b=deps[2];deps[2]=(role,a+4,b)
        with self.assertRaisesRegex(ValueError,'identity'):model.bind(l.prior,tuple(deps),selector=model.SELECTOR)

    def test_new_binding_accepts_complete_body_and_pins_every_dependency(self):
        l=layout();b=model.bind(l.prior,l.dependencies,selector=model.SELECTOR);owners=model._validate(b)
        self.assertEqual({n:len(owners[n][1]) for n in model.SHAPES},{'query':24,'ring':64,'payload':4,'enqueue':68});self.assertEqual(b,l)
