"""New094 operation-list continuation cases and independent raw oracle."""
from dataclasses import replace
import unittest,hashlib,json,os
from pathlib import Path
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_operation_list_state as model
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
    al=state.split.Layout(core,sha(state.split._encoded(core,il,zth,0x0836D4B8)),il,zth,0x0836D4B8)
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
    return model.byte093.conversion092.Layout(p,tuple((n,a,model.byte093.conversion092.SHAPES[n]) for n,a in addresses.items()))
def prior_byte_layout():
    p=prior_conversion_layout();addresses={'byte_conversion':0x080D6D0C,'byte_writer':0x080D6950,'byte_reader':0x080D66F0}
    return model.byte093.Layout(p,tuple((n,a,model.byte093.SHAPES[n]) for n,a in addresses.items()))

OPLIST,OPS,INPUT=16000,18000,12000
BANK0,BANK1=0x03003860-BASE,0x03003A60-BASE

def layout():
    p=prior_byte_layout();owners=model.byte093._validate(p);a=0x080D45D0;b=bytearray(model.HELPER);b[98:102]=model.removal._bl(a+98,owners['thunk'][0])
    return model.Layout(p,a,bytes(b),0x0836D4BC,(owners['image'][0]+112|1).to_bytes(4,'little'))
def fixture(width=2,rows=2,skip=0,slot=0,bank=0,values=tuple(range(32)),count=1):
    l=layout();m={E-256+i:('opaque-byte','094 explicit stack origin',i) for i in range(308)}
    for off,w in ((0,I(rows)),(4,P(PAYLOAD)),(8,O('callbackR5')),(12,P(DESC)),(16,O('callbackR7')),(20,I(at(l,'callback40',232)|1)),(36,O('entryR4')),(40,O('entryR5')),(44,O('entryR6')),(48,I(RETURN))):put(m,E+off,w)
    half(m,DESC,258);put(m,PAYLOAD,P(RECORD));m[PAYLOAD+6]=1;m[PAYLOAD+7]=0
    m[RECORD]=2;put(m,RECORD+4,P(OPLIST));m[OPLIST]=count;put(m,OPLIST+4,P(OPS))
    put(m,OPS,P(INPUT));put(m,OPS+4,(slot,bank,skip,rows));m[INPUT]=0;m[INPUT+1]=width
    for i,v in enumerate(values):m[INPUT+2+i]=v
    r={i:O('094 incomingR'+str(i)) for i in range(15)}
    r.update({0:P(INPUT),1:I(slot),2:I(bank),3:I(skip),4:I(rows),5:I(0),6:P(OPLIST),7:I(0),13:P(E),14:I(at(l,'writer',58)|1)})
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR,callback_entry_sp=E+52,callback_return_word=I(RETURN),literal_pointer_points=(BASE+BANK0,BASE+BANK1),copy_image_identity=True)
def report088(f):
    q=model.release091.queue090.subrecord089.buffer088;old=q._validate(f['layout'].prior.prior.prior.prior.prior.prior);r=f['registers'];e=f['callback_entry_sp']
    return dict(schema=q.SELECTOR,complete_owner_pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(old.items())],final_PC=at(f['layout'],'operations'),conditional_callback_return=False,registers=r,post_cells={str(k):v for k,v in f['cells'].items()},callback_entry_SP=e,callback_return_word=f['callback_return_word'],nested_call_cutpoint=dict(call_site=at(f['layout'],'writer',54),target=at(f['layout'],'operations'),SP=E,return_word=r[14],register_arguments={i:r[i] for i in range(4)},callee_executed=False),pending_calls=[dict(role='callback40',return_pc=RETURN&~1,entry_sp=e),dict(role='writer',return_pc=at(f['layout'],'callback40',232),entry_sp=e-28)],retired_spans=[],conditional_released_payloads=[],obligations=['synthetic conditional reaching witness only'])

def raw(f,stop_before=None,stop_visit=1,step_limit=None):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for a,b in model._validate(f['layout']).values()};regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
    mem={f['arena_base']+k:byte(v,f['arena_base']) for k,v in f['cells'].items()};pc=at(f['layout'],'operations');events=[];trace=[]
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
class OperationTests(unittest.TestCase):
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
    def output(self,r,bank=0,slot=0,rows=2,width=2):
        b=(BANK1 if bank else BANK0)+32*slot+2;m=memory(r);return [[m[b+32*y+x] for x in range(2*width)] for y in range(rows)]
    def test_two_rows_real_image_byte_copy_and_callback_return(self):
        f=fixture();r=self.derive(f);artifact('new-operation-return.json',r);self.returned(f,r)
        self.assertEqual(self.output(r),[[0,1,2,3],[4,5,6,7]]);self.assertEqual(len(r['conditional_image_entries']),2)
        self.assertFalse(r['actual_installed_identity_proved']);self.assertFalse(r['physical_access_proved'])
        self.assertNotIn(at(f['layout'],'image',140),r['trace']) # destination +2 forces actual byte path
        for reg in (8,9):self.assertEqual(r['registers'][reg],f['registers'][reg])
    def test_nonzero_bank_selects_second_actual_literal(self):
        f=fixture(bank=3,slot=2);r=self.derive(f);self.returned(f,r);self.assertEqual(self.output(r,1,2),[[0,1,2,3],[4,5,6,7]])
    def test_source_skip_advances_without_reading_skipped_rows(self):
        f=fixture(skip=2);r=self.derive(f);self.returned(f,r);self.assertEqual(self.output(r),[[8,9,10,11],[12,13,14,15]])
        self.assertFalse(any(INPUT+2<=e.get('coordinate',-1)<INPUT+10 and e['operation'].startswith('read') for e in r['memory_events']))
    def test_zero_rows_returns_without_width_or_image_access(self):
        f=fixture(rows=0,values=());del f['cells'][INPUT+1];r=self.derive(f);self.returned(f,r);self.assertEqual(r['conditional_image_entries'],[])
    def test_zero_width_still_enters_real_zero_count_copy(self):
        f=fixture(width=0,rows=2,values=());r=self.derive(f);self.returned(f,r);self.assertEqual(len(r['conditional_image_entries']),2)
        self.assertNotIn(at(f['layout'],'image',154),r['trace']);self.assertNotIn(at(f['layout'],'image',140),r['trace'])
    def test_missing_installed_identity_stops_at_actual_tail_thunk(self):
        f=fixture();f['copy_image_identity']=False;r=self.derive(f);artifact('new-installation-boundary.json',r)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'thunk'));self.assertIn('installation',r['boundary']['reason']);self.assertFalse(r['conditional_callback_return'])
        self.assert_raw(f,r,stop_before=at(f['layout'],'thunk'));self.assertEqual(r['nested_call_cutpoint']['target'],at(f['layout'],'image',112))
    def test_literal_coordinate_condition_does_not_default_to_access(self):
        f=fixture();f['literal_pointer_points']=();r=self.derive(f);artifact('new-point-coordinate-boundary.json',r)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'image',156));self.assertIn('provenance',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'image',156))
    def test_two_outer_entries_reload_real_argument_records(self):
        f=fixture(count=2);m=f['cells'];put(m,OPS+8,P(INPUT+100));put(m,OPS+12,(1,1,0,1));m[INPUT+100]=0;m[INPUT+101]=1;put(m,INPUT+102,(88,99))
        r=self.derive(f);artifact('new-two-entry-list.json',r);self.returned(f,r);self.assertEqual(len(r['conditional_image_entries']),3);self.assertEqual(self.output(r,1,1,1,1),[[88,99]])
    def test_missing_actual_fifth_stack_word_is_not_replaced_by_r4(self):
        f=fixture()
        for i in range(4):del f['cells'][E+i]
        r=self.derive(f);self.assertEqual(r['boundary']['site'],at(f['layout'],'operations',10));self.assertIn('reaching',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'operations',10))
    def test_protected_destination_stops_after_real_source_read(self):
        f=fixture();f['protected_spans']=((BANK0+2,BANK0+3),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'image',156));self.assertIn('protected',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'image',156))
    def test_missing_second_source_byte_stops_after_first_store(self):
        f=fixture(width=1,rows=1,values=(7,));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'image',154));self.assertIn('reaching',r['boundary']['reason']);self.assertEqual(memory(r)[BANK0+2],7)
        self.assert_raw(f,r,stop_before=at(f['layout'],'image',154),stop_visit=2)
    def test_opaque_source_byte_cannot_become_copy_scalar(self):
        f=fixture();f['cells'][INPUT+2]=('opaque-byte','unknown copy byte',0);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'image',154));self.assertIn('narrow read',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'image',154))
    def test_retired_destination_preserves_real_source_read_and_refuses_write(self):
        f=fixture();f['released_payload_spans']=((BANK0+2,BANK0+3),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'image',156));self.assertIn('retired',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'image',156))
    def test_forward_overlapping_copy_reads_its_own_prior_writes(self):
        f=fixture(rows=1);src=BANK0-1;m=f['cells'];m[src]=0;m[src+1]=2;put(m,src+2,(1,2,3,4));f['registers'][0]=P(src)
        r=self.derive(f);artifact('new-overlap-copy.json',r);self.returned(f,r);self.assertEqual(self.output(r,rows=1),[[1,1,1,1]])
    def test_copy_into_source_width_changes_second_row_count_and_stride(self):
        f=fixture();src=BANK0+1;m=f['cells'];m[src]=0;m[src+1]=2;put(m,src+2,(1,2,3,4));f['registers'][0]=P(src)
        r=self.derive(f);artifact('new-width-alias.json',r);self.returned(f,r)
        self.assertEqual([number(e['register_arguments'][2]) for e in r['conditional_image_entries']],[4,2]);self.assertEqual(memory(r)[src+1],1)
        self.assertEqual([memory(r)[BANK0+34+i] for i in range(2)],[4,4])
    def test_copy_into_outer_count_shortens_list_without_nonescape_assumption(self):
        f=fixture(width=1,rows=1,values=(0,0),count=2);p=BANK0+2;m=f['cells'];m[p]=2;put(m,p+4,P(OPS));f['registers'][6]=P(p)
        r=self.derive(f);artifact('new-list-count-alias.json',r);self.returned(f,r);self.assertEqual(memory(r)[p],0);self.assertEqual(r['trace'].count(at(f['layout'],'operations')),1)
    def test_copy_into_outer_pointer_retains_mixed_origin_refusal(self):
        f=fixture(width=1,rows=1,values=(0,0),count=2);p=BANK0-4;m=f['cells'];m[p]=2;put(m,p+4,P(OPS));f['registers'][6]=P(p)
        r=self.derive(f);artifact('new-list-pointer-boundary.json',r)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'writer',40));self.assertIn('opaque',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'writer',40))
    def test_output_alias_to_actual_saved_return_is_observed(self):
        f=fixture(width=1,rows=1,values=(0,0));entry=BANK0+4;m=f['cells'];old={k:v for k,v in m.items() if E-256<=k<E+52}
        for k in old:del m[k]
        m.update({k+entry-E:v for k,v in old.items()});f['registers'][13]=P(entry);f['callback_entry_sp']=entry+52
        r=self.derive(f);artifact('new-saved-return-boundary.json',r)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'operations',130));self.assertIn('saved return',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'operations',130))
    def test_actual_slot255_does_not_invent_bank_extent_guard(self):
        f=fixture(width=1,rows=1,slot=255,bank=1,values=(17,18));r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.output(r,1,255,1,1),[[17,18]]);self.assertFalse(r['physical_access_proved'])
    def test_maximum_byte_width_uses_real510_byte_count(self):
        f=fixture(width=255,rows=1,values=tuple(i&255 for i in range(510)));f['max_steps']=12000;r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.output(r,rows=1,width=255),[list(i&255 for i in range(510))]);self.assertEqual(r['trace'].count(at(f['layout'],'image',156)),510)
        artifact('new-maximum-width-counts.json',dict(instructions=len(r['trace']),source_bytes=510,destination_writes=510,word_path_entered=at(f['layout'],'image',140) in r['trace']))
    def test_explicit_instruction_bound_retains_in_progress_copy(self):
        f=fixture(width=255,rows=1,values=tuple(i&255 for i in range(510)));f['max_steps']=100;r=self.derive(f);artifact('new-step-boundary.json',r)
        self.assertIn('budget',r['boundary']['reason']);self.assertFalse(r['conditional_callback_return']);self.assert_raw(f,r,step_limit=100)
    def test_conditional088_transport_preserves_fifth_word_and_pending_frames(self):
        f=fixture();old=report088(f);r=model.continue_from_088(f['layout'],BASE,old,selector=model.SELECTOR,literal_pointer_points=f['literal_pointer_points'],copy_image_identity=True)
        artifact('new-transported-operation.json',r);self.returned(f,r);self.assertFalse(r['actual_088_report_authentication_proved']);self.assertEqual(r['inherited_088_obligations'],old['obligations'])
    def test_transport_rejects_changed_pin_or_writer_frame(self):
        f=fixture();old=report088(f);old['complete_owner_pins'][0]['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'exact088'):model.continue_from_088(f['layout'],BASE,old,selector=model.SELECTOR)
        old=report088(f);old['pending_calls'][1]['entry_sp']+=4
        with self.assertRaisesRegex(ValueError,'interface'):model.continue_from_088(f['layout'],BASE,old,selector=model.SELECTOR)
    def test_complete_helper_literals_branches_and_call_must_match(self):
        l=layout();self.assertEqual(model.bind(l.prior,l.address,l.data,l.pointer_address,l.pointer_data,selector=model.SELECTOR),l)
        for off in (10,30,40,80,98,130,132,136):
            with self.subTest(offset=off):
                b=bytearray(l.data);b[off]^=2
                with self.assertRaisesRegex(ValueError,'identity'):model.bind(l.prior,l.address,bytes(b),l.pointer_address,l.pointer_data,selector=model.SELECTOR)
    def test_pointer_word_requires_exact_copy_entry_in_complete_image(self):
        l=layout()
        for b in (l.pointer_data[:3],(at(l,'image')|1).to_bytes(4,'little')):
            with self.subTest(pointer=b):
                with self.assertRaisesRegex(ValueError,'pointer'):model.bind(l.prior,l.address,l.data,l.pointer_address,b,selector=model.SELECTOR)
    def test_selector_and_conditional_inputs_are_explicit(self):
        f=fixture();f['selector']='default'
        with self.assertRaisesRegex(ValueError,'selector'):self.derive(f)
        f['selector']=model.SELECTOR;f['copy_image_identity']=1
        with self.assertRaisesRegex(ValueError,'conditional'):self.derive(f)
        f['copy_image_identity']=True;f['max_steps']=model.MAX_STEPS+1
        with self.assertRaisesRegex(ValueError,'bounded'):self.derive(f)
    def test_real_operation_entry_requires_writer_link_and_zero_r7(self):
        f=fixture();f['registers'][7]=I(1);r=self.derive(f);self.assertIn('interface',r['boundary']['reason']);self.assertEqual(r['trace'],[])
        f=fixture();f['registers'][14]=I(at(f['layout'],'writer',60)|1);r=self.derive(f);self.assertIn('interface',r['boundary']['reason']);self.assertEqual(r['trace'],[])
