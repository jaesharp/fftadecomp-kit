"""New093 complete byte-record continuation cases and independent raw oracle."""
from dataclasses import replace
import unittest,hashlib,json,os
from pathlib import Path
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_byte_record_state as model
previous=model.release091.queue090.subrecord089
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
    addresses['free_wrapper']=0x08007170
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



OUT,INPUT,CTX,QUEUE_POINT,CONTEXT_POINT,QUERY=20000,12000,30000,0x01002BCC,0x159C0,0x203D
POINTS=(BASE+QUERY,BASE+CONTEXT_POINT,BASE+QUEUE_POINT)

def prior_queue_layout():
    p=prior_subrecord_layout();q=model.release091.queue090;addresses={'query':0x080C95A8,'ring':0x080D3AF8,'payload':0x08005BFC,'enqueue':0x08000A98}
    return q.Layout(p,tuple((n,a,q.SHAPES[n]) for n,a in addresses.items()))
def prior_release_layout():
    p=prior_queue_layout();q=model.release091;addresses={'pool_release':0x08005B0C,'global_release':0x0800A668}
    return q.Layout(p,tuple((n,a,q.SHAPES[n]) for n,a in addresses.items()))
def prior_conversion_layout():
    p=prior_release_layout();addresses={'conversion':0x080D6A34,'tile_writer':0x080D6798,'value_reader':0x080D663C}
    return model.conversion092.Layout(p,tuple((n,a,model.conversion092.SHAPES[n]) for n,a in addresses.items()))
def layout():
    p=prior_conversion_layout();addresses={'byte_conversion':0x080D6D0C,'byte_writer':0x080D6950,'byte_reader':0x080D66F0}
    return model.Layout(p,tuple((n,a,model.SHAPES[n]) for n,a in addresses.items()))
def fixture(mode=1,width=2,height=2,flags=0,values=(1,2,3,4),addend=0):
    l=layout();m={E-256+i:('opaque-byte','093 explicit stack origin',i) for i in range(296)}
    for off,w in ((0,P(PAYLOAD)),(4,O('callbackR5')),(8,I(at(l,'callback40',214)|1)),(24,O('entryR4')),(28,O('entryR5')),(32,O('entryR6')),(36,I(RETURN))):put(m,E+off,w)
    half(m,DESC,257);put(m,PAYLOAD,P(RECORD));m[PAYLOAD+6]=1;m[PAYLOAD+7]=0;put(m,PAYLOAD+36,P(OUT))
    m[RECORD]=5;m[RECORD+1]=0;half(m,RECORD+2,width*height);put(m,RECORD+4,P(HANDLE));put(m,RECORD+8,P(50000))
    put(m,HANDLE,P(INPUT));half(m,HANDLE+4,addend)
    for i,v in enumerate((width,height,0,0,mode,flags)):m[INPUT+i]=v
    for i,v in enumerate(values):m[INPUT+6+i]=v
    m[QUERY]=0;put(m,CONTEXT_POINT,P(CTX));m[CTX+24+0x914]=0;put(m,QUEUE_POINT,I(0))
    r={i:O('093 incomingR'+str(i)) for i in range(15)}
    r.update({0:P(OUT),1:P(INPUT),2:I(addend),4:P(PAYLOAD),5:I(0),6:P(DESC),13:P(E),14:I(at(l,'transfer',156)|1)})
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR,callback_entry_sp=E+40,callback_return_word=I(RETURN),literal_points=POINTS)

def report088(f):
    q=model.release091.queue090.subrecord089.buffer088;old=q._validate(f['layout'].prior.prior.prior.prior.prior);r=f['registers'];e=f['callback_entry_sp']
    return dict(schema=q.SELECTOR,complete_owner_pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(old.items())],final_PC=at(f['layout'],'byte_conversion'),conditional_callback_return=False,registers=r,post_cells={str(k):v for k,v in f['cells'].items()},callback_entry_SP=e,callback_return_word=f['callback_return_word'],nested_call_cutpoint=dict(call_site=at(f['layout'],'transfer',152),target=at(f['layout'],'byte_conversion'),SP=E,return_word=r[14],register_arguments={i:r[i] for i in range(4)},callee_executed=False),pending_calls=[dict(role='callback40',return_pc=RETURN&~1,entry_sp=e),dict(role='transfer',return_pc=at(f['layout'],'callback40',214),entry_sp=e-28)],retired_spans=[],conditional_released_payloads=[],obligations=['synthetic conditional reaching witness only'])

def raw(f,stop_before=None,stop_visit=1,step_limit=None):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for a,b in model._validate(f['layout']).values()};regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
    mem={f['arena_base']+k:byte(v,f['arena_base']) for k,v in f['cells'].items()};pc=at(f['layout'],'byte_conversion');events=[];trace=[]
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
    for step in range(model.MAX_STEPS+1):
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
class ByteRecordTests(unittest.TestCase):
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
        self.assertEqual(r['final_PC'],RETURN&~1);self.assertEqual(r['registers'][13],P(E+40));self.assert_raw(f,r)
    def grid(self,r,width=2,height=2,out=OUT):return [memory(r)[out+32*y+x] for y in range(height) for x in range(width)]
    def test_plain_byte_rectangle_through_enclosing_ram_queue(self):
        f=fixture();r=self.derive(f);artifact('new-plain-byte-return.json',r);self.returned(f,r)
        self.assertEqual(self.grid(r),[1,2,3,4])
        for reg in (8,9,10):self.assertEqual(r['registers'][reg],f['registers'][reg])
        self.assertFalse(r['actual_device_transfer_proved']);self.assertFalse(r['actual_DMA_completion_proved'])
    def test_packed_constant_run_skips_unread_fourth_byte(self):
        f=fixture(flags=2,values=(4,0x40,19));r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.grid(r),[19]*4);self.assertNotIn(INPUT+9,memory(r))
        updates=[e['bytes'] for e in r['memory_events'] if e.get('coordinate')==E-104 and e['operation']=='write32'];self.assertEqual(updates[-1],P(INPUT+10))
    def test_packed_incrementing_run_wraps_to_byte(self):
        f=fixture(flags=2,values=(4,0x80,254));r=self.derive(f);self.returned(f,r);self.assertEqual(self.grid(r),[254,255,0,1])
    def test_packed_even_literal_run_preserves_all_four_values(self):
        f=fixture(flags=2,values=(4,0,11,22,33,44));r=self.derive(f);self.returned(f,r);self.assertEqual(self.grid(r),[11,22,33,44])
    def test_odd_literal_run_skips_absent_padding_before_next_header(self):
        f=fixture(flags=2,values=(3,0,1,2,3,0,1,0x40,7));del f['cells'][INPUT+11]
        r=self.derive(f);artifact('new-odd-run-padding.json',r);self.returned(f,r);self.assertEqual(self.grid(r),[1,2,3,7])
        self.assertFalse(any(e.get('coordinate')==INPUT+11 and e['operation'].startswith('read') for e in r['memory_events']))
        self.assertEqual(tuple(memory(r)[E-104+i] for i in range(4)),P(INPUT+16))
    def test_two_fixed_runs_skip_padding_and_reset_halfword_counter(self):
        f=fixture(flags=2,values=(2,0x40,8,0,2,0x80,254));del f['cells'][INPUT+9]
        r=self.derive(f);self.returned(f,r);self.assertEqual(self.grid(r),[8,8,254,255])
        self.assertEqual([memory(r)[E-108+i] for i in range(2)],[0,0])
    def test_signed_offset_and255_sentinel_follow_u8_truncation(self):
        f=fixture(values=(0,1,255,2),addend=0xFFFF);r=self.derive(f);self.returned(f,r);self.assertEqual(self.grid(r),[255,0,255,1])
    def test_positive_offset_wraps_non_sentinel_values(self):
        f=fixture(values=(254,255,0,128),addend=3);r=self.derive(f);self.returned(f,r);self.assertEqual(self.grid(r),[1,255,3,131])
    def test_horizontal_repeat_reloads_width(self):
        f=fixture(mode=2,width=16,height=1,values=tuple(range(16)));f['max_steps']=10000;r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.grid(r,32,1),list(range(16))*2);self.assertEqual(r['trace'].count(at(f['layout'],'byte_writer')),2)
    def test_vertical_repeat_reloads_height(self):
        f=fixture(mode=3,width=1,height=16,values=tuple(range(16)));f['max_steps']=10000;r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.grid(r,1,32),list(range(16))*2);self.assertEqual(r['trace'].count(at(f['layout'],'byte_writer')),2)
    def test_full32_grid_compares1024_actual_byte_writes(self):
        f=fixture(mode=4,width=32,height=32,flags=2,values=(0,0x44,0x81));f['max_steps']=200000;r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.grid(r,32,32),[0x81]*1024)
        writes=[e for e in r['memory_events'] if e['site']==at(f['layout'],'byte_writer',178) and e['operation']=='write8']
        self.assertEqual(len(writes),1024);self.assertEqual(r['trace'].count(at(f['layout'],'byte_reader')),1024)
        artifact('new-full-grid-counts.json',dict(instructions=len(r['trace']),byte_writes=len(writes),reader_calls=1024,explicit_bound=200000,default_bound=4096,existing_native_budget_changed=False))
    def test_mode_chain_rejects_zero_and_above4_without_source_read(self):
        for mode in (0,5,255):
            with self.subTest(mode=mode):
                f=fixture(mode=mode,values=());r=self.derive(f);self.returned(f,r);self.assertNotIn(at(f['layout'],'byte_writer'),r['trace'])
    def test_clipped33rd_column_does_not_read_missing_byte(self):
        f=fixture(width=33,height=1,values=tuple(range(32)));f['max_steps']=10000;r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.grid(r,32,1),list(range(32)));self.assertEqual(r['trace'].count(at(f['layout'],'byte_reader')),32)
        self.assertFalse(any(e.get('coordinate')==INPUT+38 for e in r['memory_events']))
    def test_clipped33rd_row_does_not_read_missing_byte(self):
        f=fixture(width=1,height=33,values=tuple(range(32)));f['max_steps']=10000;r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.grid(r,1,32),list(range(32)));self.assertEqual(r['trace'].count(at(f['layout'],'byte_reader')),32)
    def test_zero_width_repeat_stops_at_explicit_bound(self):
        f=fixture(mode=2,width=0,height=1,values=());f['max_steps']=600;r=self.derive(f);artifact('new-zero-stride-boundary.json',r)
        self.assertIn('budget',r['boundary']['reason']);self.assertNotIn(at(f['layout'],'byte_reader'),r['trace']);self.assert_raw(f,r,step_limit=600)
    def test_zero_height_repeat_stops_with_real_frame_state(self):
        f=fixture(mode=3,width=1,height=0,values=());f['max_steps']=600;r=self.derive(f)
        self.assertIn('budget',r['boundary']['reason']);self.assertNotIn(at(f['layout'],'byte_reader'),r['trace']);self.assert_raw(f,r,step_limit=600)
    def test_zero_run_length_is_not_invented_end_of_stream(self):
        f=fixture(flags=2,values=(0,0x40,9));r=self.derive(f);self.returned(f,r);self.assertEqual(self.grid(r),[9]*4)
        self.assertEqual(tuple(memory(r)[E-104+i] for i in range(4)),P(INPUT+6))
    def test_source_output_alias_changes_subsequent_reads(self):
        f=fixture();out=INPUT+7;f['registers'][0]=P(out);put(f['cells'],PAYLOAD+36,P(out));r=self.derive(f)
        artifact('new-source-output-alias.json',r);self.returned(f,r);self.assertEqual(self.grid(r,out=out),[1,1,1,4])
    def test_header_output_alias_changes_real_repeat_stride(self):
        f=fixture(mode=2,width=2,height=1,values=(32,1));f['registers'][0]=P(INPUT);put(f['cells'],PAYLOAD+36,P(INPUT));r=self.derive(f)
        artifact('new-header-output-alias.json',r);self.returned(f,r);self.assertEqual(r['trace'].count(at(f['layout'],'byte_writer')),1)
        reads=[e['bytes'][0] for e in r['memory_events'] if e.get('coordinate')==INPUT and e['operation']=='read8'];self.assertEqual(reads,[2,32])
    def test_output_byte_can_destroy_saved_thumb_return(self):
        f=fixture(width=1,height=1,values=(0,));f['registers'][0]=P(E-4);put(f['cells'],PAYLOAD+36,P(E-4));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'byte_conversion',288));self.assertIn('Thumb',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'byte_conversion',288))
    def test_protected_output_stops_after_reader_counter_advance(self):
        f=fixture();f['protected_spans']=((OUT,OUT+1),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'byte_writer',178));self.assertIn('protected',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'byte_writer',178))
        self.assertEqual([memory(r)[E-108+i] for i in range(2)],[1,0])
    def test_opaque_plain_byte_cannot_be_observed_as_scalar(self):
        f=fixture();f['cells'][INPUT+6]=('opaque-byte','byte unknown',0);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'byte_reader',154));self.assertIn('narrow read',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'byte_reader',154))
    def test_missing_packed_value_has_no_fabricated_extent(self):
        f=fixture(flags=2,values=(1,0x40));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'byte_reader',88));self.assertIn('reaching',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'byte_reader',88))
    def test_retired_source_byte_stops_at_actual_load(self):
        f=fixture();f['released_payload_spans']=((INPUT+6,INPUT+7),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'byte_reader',154));self.assertIn('retired',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'byte_reader',154))
    def test_unaligned_byte_output_is_valid_without_word_access(self):
        f=fixture();f['registers'][0]=P(OUT+1);put(f['cells'],PAYLOAD+36,P(OUT+1));r=self.derive(f);self.returned(f,r);self.assertEqual(self.grid(r,out=OUT+1),[1,2,3,4])
    def test_immutable_code_cannot_be_byte_output(self):
        f=fixture();f['registers'][0]=P(at(f['layout'],'byte_reader',68)-BASE);put(f['cells'],PAYLOAD+36,f['registers'][0]);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'byte_writer',178));self.assertIn('immutable',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'byte_writer',178))
    def test_conditional088_transport_runs_only_new_entry_continuation(self):
        f=fixture();report=report088(f);r=model.continue_from_088(f['layout'],BASE,report,selector=model.SELECTOR,literal_points=POINTS)
        artifact('new-transported-byte-entry.json',r);self.returned(f,r);self.assertFalse(r['actual_088_report_authentication_proved']);self.assertEqual(r['inherited_088_obligations'],report['obligations'])
    def test_transport_rejects_stale_owner_and_pending_frame(self):
        f=fixture();report=report088(f);report['complete_owner_pins'][0]['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'exact088'):model.continue_from_088(f['layout'],BASE,report,selector=model.SELECTOR)
        report=report088(f);report['pending_calls'][1]['entry_sp']+=4
        with self.assertRaisesRegex(ValueError,'interface'):model.continue_from_088(f['layout'],BASE,report,selector=model.SELECTOR)
    def test_complete_controller_branches_and_all_calls_are_required(self):
        l=layout();self.assertEqual(model.bind(l.prior,l.dependencies,selector=model.SELECTOR),l)
        for off in (24,30,44,80,126,184,246):
            with self.subTest(offset=off):
                deps=list(l.dependencies);n,a,b=deps[0];v=bytearray(b);v[off]^=2;deps[0]=(n,a,bytes(v))
                with self.assertRaisesRegex(ValueError,'identity'):model.bind(l.prior,tuple(deps),selector=model.SELECTOR)
    def test_complete_reader_and_writer_call_must_match(self):
        l=layout();deps=list(l.dependencies);n,a,b=deps[2];deps[2]=(n,a,b[:-2])
        with self.assertRaisesRegex(ValueError,'complete'):model.bind(l.prior,tuple(deps),selector=model.SELECTOR)
        deps=list(l.dependencies);n,a,b=deps[1];v=bytearray(b);v[144:148]=model.removal._bl(a+144,at(l,'byte_reader')+2);deps[1]=(n,a,bytes(v))
        with self.assertRaisesRegex(ValueError,'identity'):model.bind(l.prior,tuple(deps),selector=model.SELECTOR)
    def test_selector_bound_and_real_transfer_return_are_required(self):
        f=fixture();f['selector']='default'
        with self.assertRaisesRegex(ValueError,'selector'):self.derive(f)
        f['selector']=model.SELECTOR;f['max_steps']=model.MAX_STEPS+1
        with self.assertRaisesRegex(ValueError,'bounded'):self.derive(f)
        f['max_steps']=4096;f['registers'][14]=I(at(f['layout'],'transfer',124)|1);r=self.derive(f)
        self.assertIn('interface',r['boundary']['reason']);self.assertEqual(r['trace'],[])
    def test_grid_repetition_takes_both_real_loop_backedges(self):
        f=fixture(mode=4,width=16,height=16,flags=2,values=(0,0x41,0x47));f['max_steps']=200000;r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.grid(r,32,32),[0x47]*1024);self.assertEqual(r['trace'].count(at(f['layout'],'byte_writer')),4)
        self.assertEqual(r['trace'].count(at(f['layout'],'byte_reader')),1024)
        artifact('new-repeated-grid-counts.json',dict(instructions=len(r['trace']),writer_calls=4,reader_calls=1024,explicit_bound=200000))
    def test_output_alias_to_source_pointer_slot_preserves_corruption(self):
        f=fixture(width=2,height=1,values=(1,2));f['registers'][0]=P(E-104);put(f['cells'],PAYLOAD+36,P(E-104));r=self.derive(f)
        artifact('new-pointer-slot-alias-boundary.json',r)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'byte_reader',152));self.assertIn('opaque',r['boundary']['reason'])
        self.assert_raw(f,r,stop_before=at(f['layout'],'byte_reader',152),stop_visit=2)
    def test_output_alias_to_local_counter_changes_next_source_index(self):
        f=fixture(width=2,height=1,values=(9,1,2,3,4,5,6,7,8,21));f['registers'][0]=P(E-108);put(f['cells'],PAYLOAD+36,P(E-108));r=self.derive(f)
        artifact('new-counter-alias-return.json',r);self.returned(f,r)
        self.assertEqual([memory(r)[E-108+i] for i in range(2)],[10,21])
        reads=[e['coordinate'] for e in r['memory_events'] if e['site']==at(f['layout'],'byte_reader',154)];self.assertEqual(reads,[INPUT+6,INPUT+15])
    def test_both_packed_mode_bits_follow_increment_branch_priority(self):
        f=fixture(flags=2,values=(4,0xC0,253));r=self.derive(f);self.returned(f,r);self.assertEqual(self.grid(r),[253,254,255,0])
