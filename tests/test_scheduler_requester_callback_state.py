"""New100 requester/scheduler/callback composition continuation cases and independent raw oracle."""
from dataclasses import replace
import unittest,hashlib,json,os
from pathlib import Path
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_requester_callback_state as model
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
    return model.operations094.byte093.conversion092.Layout(p,tuple((n,a,model.operations094.byte093.conversion092.SHAPES[n]) for n,a in addresses.items()))
def prior_byte_layout():
    p=prior_conversion_layout();addresses={'byte_conversion':0x080D6D0C,'byte_writer':0x080D6950,'byte_reader':0x080D66F0}
    return model.operations094.byte093.Layout(p,tuple((n,a,model.operations094.byte093.SHAPES[n]) for n,a in addresses.items()))

OPLIST,OPS,INPUT=16000,18000,12000
BANK0,BANK1=0x03003860-BASE,0x03003A60-BASE

def prior_operations_layout():
    p=prior_byte_layout();owners=model.operations094.byte093._validate(p);a=0x080D45D0;b=bytearray(model.operations094.HELPER);b[98:102]=model.removal._bl(a+98,owners['thunk'][0])
    return model.operations094.Layout(p,a,bytes(b),0x0836D4BC,(owners['image'][0]+112|1).to_bytes(4,'little'))

def layout():return model.Layout(model.allocation099.Layout(model.dispatch098.Layout(model.phase097.Layout(model.phase096.Layout(model.phase095.Layout(prior_operations_layout()))))))
def fixture(kind=2,width=2,rows=2,skip=0,slot=0,bank=0,values=tuple(range(32)),count=1):
    l=layout();m={}
    half(m,DESC,256);put(m,PAYLOAD,P(RECORD));m[PAYLOAD+6]=1;m[PAYLOAD+7]=0
    m[RECORD]=kind;m[RECORD+1]=0;put(m,RECORD+4,P(OPLIST));m[OPLIST]=count;put(m,OPLIST+4,P(OPS))
    put(m,OPS,P(INPUT));put(m,OPS+4,(slot,bank,skip,rows));m[INPUT]=0;m[INPUT+1]=width
    for i,v in enumerate(values):m[INPUT+2+i]=v
    r={i:O('100 actual entry R'+str(i)) for i in range(15)}
    r.update({1:P(DESC),2:P(PAYLOAD),13:P(E),14:I(RETURN)})
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR,literal_pointer_points=(BASE+BANK0,BASE+BANK1),copy_image_identity=True)
def queue_fixture(kind=0,remaining=64,query=0):
    f=fixture(kind=kind);m=f['cells'];put(m,PAYLOAD+20,I(remaining));put(m,PAYLOAD+24,P(SRC));put(m,PAYLOAD+28,P(DST));m[QUERY]=query
    put(m,CONTEXT_POINT,P(CTX));m[CTX+24+0x914]=0;put(m,QUEUE_POINT,I(0));f['literal_points']=POINTS;f['copy_image_identity']=False;f['literal_pointer_points']=()
    return f

def raw(f,stop_before=None,stop_visit=1,step_limit=None,link_written=False):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for a,b in model._validate(f['layout']).values()};regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
    mem={f['arena_base']+k:byte(v,f['arena_base']) for k,v in f['cells'].items()};pc=at(f['layout'],'requester256');events=[];trace=[]
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
        if pc==stop_before and trace.count(pc)+1==stop_visit:
            if link_written:
                owner=next(a for a,b in bodies.items() if a<=pc<a+len(b))
                ins=next(decoder.disasm(bodies[owner][pc-owner:],pc,1))
                assert ins.mnemonic=='bl' and ins.size==4
                regs[14]=(pc+ins.size)|1
            trace.append(pc);break
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


def transfer_fixture(kind=0,count=64):
    f=queue_fixture(kind=kind);m=f['cells'];half(m,RECORD+2,count);put(m,RECORD+4,P(SRC));put(m,RECORD+8,P(DST));put(m,PAYLOAD+36,P(OUT));return f

def conversion_fixture(kind=4,mode=1,width=2,height=2,flags=0,values=(1,2,3,4),addend=0,palette=0):
    f=transfer_fixture(kind,count=width*height*(2 if kind==4 else 1));m=f['cells']
    for a in range(INPUT,INPUT+64):m.pop(a,None)
    put(m,RECORD+4,P(HANDLE));put(m,HANDLE,P(INPUT));half(m,HANDLE+4,addend);m[HANDLE+6]=palette
    for i,v in enumerate((width,height,0,0,mode,flags)):m[INPUT+i]=v
    for i,v in enumerate(values):
        if kind==4:half(m,INPUT+6+2*i,v)
        else:m[INPUT+6+i]=v
    return f

def subrecord_fixture(kind=1,flags=0,remaining=4,stride=1):
    f=transfer_fixture(3,count=31);m=f['cells'];m[RECORD+1]=0;half(m,PAYLOAD+16,stride)
    put(m,PAYLOAD+8,I(0));put(m,PAYLOAD+12,I(0));put(m,PAYLOAD+20,I(remaining));put(m,PAYLOAD+24,P(SRC));put(m,PAYLOAD+28,P(DST));put(m,PAYLOAD+32,P(BUFFER+200));put(m,PAYLOAD+36,P(BUFFER))
    put(m,RECORD+4,P(HANDLE));put(m,RECORD+8,P(BUFFER));put(m,HANDLE,P(SUB));m[HANDLE+4]=5;m[HANDLE+5]=2;m[HANDLE+6]=0;m[SUB]=kind;m[SUB+1]=flags
    for i,v in enumerate((0xA5,0x3C,0x81,0x69,0x96,0xC3)):m[SRC+i]=v
    for i in range(-4,40):m[DST+i]=0xCC
    return f

def prepared_subrecord(kind=1,flags=0,count=8):
    f=subrecord_fixture(kind,flags);m=f['cells'];half(m,RECORD+2,count)
    for i in range(256):m[SUB+4+i]=(0xA5+i)&255
    return f

GPOOL,GHEAP,POOL_HANDLE,HEAP1,HEAP2,NODE1,NODE2=0xF430,0x8FF4,38000,40000,42000,40256,42256
RELEASE_POINTS=(BASE+GPOOL,BASE+GHEAP)
def add_release_state(f,shared_pool=False):
    m=f['cells'];put(m,PAYLOAD+32,P(NODE1));put(m,PAYLOAD+36,P(NODE2))
    put(m,GPOOL,P(POOL_HANDLE));put(m,POOL_HANDLE,P(HEAP1));put(m,GHEAP,P(HEAP1 if shared_pool else HEAP2))
    for h in (HEAP1,HEAP2):
        for a in range(h,h+12):m[a]=0
    for n in (NODE1,NODE2):
        for a in range(n-12,n):m[a]=0
        half(m,n-8,0x7373);half(m,n-6,35)
    f['release_spans']=((NODE1,NODE1+128),(NODE2,NODE2+128));f['literal_points']=tuple(dict.fromkeys((*f.get('literal_points',()),*RELEASE_POINTS)))
    return f

def release_fixture(phase=260,count=1,shared_pool=False):
    f=fixture(count=0);half(f['cells'],DESC,phase);half(f['cells'],PAYLOAD+4,count);return add_release_state(f,shared_pool)

def next_entry(f,r):
    """Synthetic next call witness: caller explicitly restores arguments/LR.

    This supplies neither a scheduler path nor hardware completion. The new
    invocation explicitly permits stack reuse; retired payloads stay retired.
    """
    g=dict(f);g['cells']=memory(r);g['registers']=dict(r['registers']);g['registers'].update({1:P(DESC),2:P(PAYLOAD),14:I(RETURN)})
    g['released_payload_spans']=tuple(tuple(s) for s in r['conditional_released_payloads']);return g

ALLOC1,ALLOC2=40000,100000
def pool(m,base,size):
    for a in (*range(base,base+12),*range(base+128,base+140)):m[a]=0
    for off,value in ((0,32 if size else 0),(2,32 if size else 0),(4,1 if size else 0),(134,size)):
        half(m,base+off,value)
def allocation_fixture(first=3072,second=4096,shared=False,installed=False,count=0x103):
    f=fixture(count=0);m=f['cells'];half(m,DESC,0);put(m,DESC+4,P(RECORD));half(m,DESC+20,count)
    put(m,GPOOL,P(POOL_HANDLE));put(m,POOL_HANDLE,P(ALLOC1));put(m,GHEAP,P(ALLOC1 if shared else ALLOC2))
    pool(m,ALLOC1,first);pool(m,ALLOC2,second)
    f.update(literal_points=RELEASE_POINTS,literal_pointer_points=(),copy_image_identity=False,zero_image_identity=installed)
    return f

JOB=ALLOC1+140
def requester_fixture(first=8192,second=8192,installed=True,count=0x103,parent=0):
    f=allocation_fixture(first,second,installed=installed,count=count);m=f['cells']
    # Unknown physical bytes, not initialized scalars; both models receive
    # the same symbolic origins before the actual requester overwrites fields.
    for a in range(E-36,E-4):m[a]=('opaque-byte','100 incoming private frame',a-(E-36))
    put(m,POOL_HANDLE+4,I(0));half(m,POOL_HANDLE+12,0x2345)
    f['registers']={i:O('100 requester R'+str(i)) for i in range(15)}
    f['registers'].update({0:P(RECORD),1:I(count),2:I(0) if parent==0 else P(parent),13:P(E),14:I(RETURN)})
    return f

@unittest.skipIf(IMAGE is None,'set FFTA_SOURCE84_IMAGE to the private authenticated176B source')
class RequesterTests(unittest.TestCase):
    def assert_raw(self,f,r,stop_before=None,stop_visit=1,step_limit=None,link_written=False):
        regs,mem,trace,events,pc=raw(f,stop_before,stop_visit,step_limit,link_written)
        self.assertEqual(r['trace'],trace);self.assertEqual(r['final_PC'],pc)
        self.assertEqual({k:number(v,f['arena_base']) for k,v in r['registers'].items()},regs)
        got=memory(r)
        for a,v in mem.items():self.assertEqual(byte(got[a-f['arena_base']],f['arena_base']),v,(hex(a),v))
        actual=[(e['site'],e['operation'],e['coordinate'],tuple(byte(v,f['arena_base']) for v in e['bytes'])) for e in r['memory_events'] if 'coordinate' in e]
        self.assertEqual(actual,events)
    def derive(self,f):return model.derive(**f)
    def returned(self,f,r):
        self.assertTrue(r['conditional_requester_return'],r['boundary']);self.assertIsNone(r['boundary']);self.assertEqual(r['pending_calls'],[])
        self.assertTrue(r['conditional_callback_return']);self.assertEqual(r['final_PC'],RETURN&~1);self.assertEqual(r['registers'][13],P(E));self.assert_raw(f,r)
    def word(self,r,a):return tuple(memory(r)[a+i] for i in range(4))
    def halfword(self,r,a):return memory(r)[a]|memory(r)[a+1]<<8
    def test_requester_builds_every_frame_and_returns_actual_allocated_job(self):
        f=requester_fixture();r=self.derive(f);self.returned(f,r)
        self.assertEqual(r['registers'][0],P(JOB));self.assertEqual(self.word(r,POOL_HANDLE+4),P(JOB));self.assertEqual(self.halfword(r,JOB+20),256);self.assertEqual(self.halfword(r,JOB+22),0x2345)
        self.assertEqual(self.word(r,JOB+24),P(RECORD));self.assertEqual(memory(r)[JOB+30],3)
        self.assertEqual(self.word(r,JOB+56),P(ALLOC1+220));self.assertEqual(self.word(r,JOB+60),P(ALLOC2+140))
        self.assertEqual([e['size_word'] for e in r['actual_allocation_requests']],[I(68),I(0x3000),I(0x4000)])
        self.assertEqual([e['kind'] for e in r['conditional_image_entries']],['zero12','zero68','zero12','zero12'])
        self.assertEqual(r['actual_scheduler_entries'][0]['SP'],E-36);self.assertEqual(r['actual_callback_entries'][0]['SP'],E-92)
        self.assertEqual(r['observed_phase'],dict(kind='constant',value=0));artifact('new-requester-full-chain.json',r)
    def test_untouched_private_descriptor_words_remain_opaque_through_copy(self):
        f=requester_fixture(first=17,second=0);r=self.derive(f);self.returned(f,r)
        m=memory(r);src=E-32;dst=E-92
        for off in (8,12,16,24):
            self.assertEqual(tuple(m[src+off+i] for i in range(4)),tuple(m[dst+off+i] for i in range(4)))
            self.assertTrue(all(type(m[dst+off+i]) is tuple and m[dst+off+i][0]=='opaque-byte' for i in range(4)))
        self.assertEqual(self.word(r,JOB+56),I(0));self.assertEqual(self.word(r,JOB+60),I(0))
        artifact('new-requester-opaque-descriptor-copy.json',r)
    def test_count_byte_truncation_follows_actual_requester_instructions(self):
        for count in (0,255,256,0x12345678,0xffffffff):
            f=requester_fixture(first=17,second=0,count=count);r=self.derive(f);self.returned(f,r)
            self.assertEqual(memory(r)[JOB+30],count&255);self.assertEqual(self.halfword(r,E-72),count&255)
    def test_zero68_requires_installation_even_without_an_allocator_split(self):
        f=requester_fixture(first=17,second=0,installed=False);r=self.derive(f)
        self.assertIn('zero image installation',r['boundary']['reason']);self.assertEqual(r['registers'][0],P(JOB));self.assertEqual(r['registers'][1],I(68));self.assertEqual(r['nested_call_cutpoint']['call_site'],at(f['layout'],'scheduler',48))
        self.assert_raw(f,r,stop_before=at(f['layout'],'zero_thunk'));artifact('new-requester-zero68-identity-boundary.json',r)
    def test_empty_scheduler_pool_stops_before_null_zero_destination(self):
        f=requester_fixture(first=0);r=self.derive(f)
        self.assertIn('address lacks',r['boundary']['reason']);self.assertEqual(r['registers'][0],I(0));self.assertEqual(r['actual_callback_entries'],[])
        self.assert_raw(f,r,stop_before=at(f['layout'],'zero_thunk'));artifact('new-requester-null-job-boundary.json',r)
    def test_existing_global_list_tail_is_reloaded_and_linked(self):
        f=requester_fixture(first=17,second=0);m=f['cells'];head,tail=23000,24000;put(m,POOL_HANDLE+4,P(head));put(m,head+8,P(tail));put(m,tail+8,I(0))
        r=self.derive(f);self.returned(f,r);self.assertEqual(self.word(r,POOL_HANDLE+4),P(head));self.assertEqual(self.word(r,tail+8),P(JOB));self.assertEqual(self.word(r,JOB+4),P(tail))
    def test_parent_empty_child_list_uses_incoming_fifth_argument(self):
        parent=25000;f=requester_fixture(first=17,second=0,parent=parent);put(f['cells'],parent+16,I(0));r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.word(r,parent+16),P(JOB));self.assertEqual(self.word(r,JOB+12),P(parent));self.assertEqual(self.word(r,POOL_HANDLE+4),I(0))
    def test_parent_existing_child_chain_uses_actual_tail(self):
        parent,head,tail=25000,26000,27000;f=requester_fixture(first=17,second=0,parent=parent);m=f['cells'];put(m,parent+16,P(head));put(m,head+8,P(tail));put(m,tail+8,I(0));r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.word(r,parent+16),P(head));self.assertEqual(self.word(r,tail+8),P(JOB));self.assertEqual(self.word(r,JOB+4),P(tail));self.assertEqual(self.word(r,JOB+12),P(parent))
    def test_cycle_in_actual_global_list_ends_at_explicit_instruction_budget(self):
        f=requester_fixture(first=17,second=0);head=23000;put(f['cells'],POOL_HANDLE+4,P(head));put(f['cells'],head+8,P(head));f['max_steps']=700;r=self.derive(f)
        self.assertIn('budget',r['boundary']['reason']);self.assertEqual(r['actual_callback_entries'],[]);self.assert_raw(f,r,step_limit=700)
    def test_parent_pointer_numeric_bits_do_not_grant_common_base_origin(self):
        f=requester_fixture(first=17,second=0);f['registers'][2]=I(BASE+25000);r=self.derive(f)
        self.assertIn('address lacks',r['boundary']['reason']);self.assertEqual(r['boundary']['site'],at(f['layout'],'scheduler',64));self.assert_raw(f,r,stop_before=r['boundary']['site'])
    def test_protected_zeroed_job_stops_at_real_image_store(self):
        f=requester_fixture(first=17,second=0);f['protected_spans']=((JOB+16,JOB+20),);r=self.derive(f)
        self.assertIn('protected',r['boundary']['reason']);self.assertEqual(r['boundary']['coordinate'],JOB+16)
        artifact('new-requester-protected-zero-boundary.json',r)
    def test_declared_retired_requester_frame_cannot_be_revived(self):
        f=requester_fixture();f['retired_stack_spans']=((E-36,E-32),);r=self.derive(f)
        self.assertIn('externally retired',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'requester256',2))
    def test_uninterpreted_descriptor_pointer_word_survives_actual_copy(self):
        f=requester_fixture(first=17,second=0);put(f['cells'],E-24,P(ALLOC2+140));r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.word(r,E-84),P(ALLOC2+140));self.assertFalse(r['physical_access_proved'])
    def test_source_record_may_alias_new_job_without_freshness_assumption(self):
        f=requester_fixture(first=17,second=0);f['registers'][0]=P(JOB)
        for a in range(JOB,JOB+68):f['cells'][a]=0xAB
        r=self.derive(f);self.returned(f,r);self.assertEqual(self.word(r,JOB+24),P(JOB));self.assertEqual(memory(r)[JOB+16],0)
        self.assertFalse(r['actual_heap_lifetime_proved']);artifact('new-requester-record-job-alias.json',r)
    def test_parent_may_alias_job_and_real_zero_changes_its_child_head(self):
        f=requester_fixture(first=17,second=0,parent=JOB);put(f['cells'],JOB+16,P(25000));r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.word(r,JOB+16),P(JOB));self.assertEqual(self.word(r,JOB+12),P(JOB));self.assertEqual(self.word(r,POOL_HANDLE+4),I(0))
        artifact('new-requester-parent-job-alias.json',r)
    def test_global_head_alias_to_job_produces_actual_self_links(self):
        f=requester_fixture(first=17,second=0);put(f['cells'],POOL_HANDLE+4,P(JOB));r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.word(r,JOB+8),P(JOB));self.assertEqual(self.word(r,JOB+4),P(JOB));self.assertFalse(r['actual_termination_proved'])
        artifact('new-requester-self-link.json',r)
    def test_missing_counter_bytes_stop_after_zero_without_inventing_value(self):
        f=requester_fixture(first=17,second=0);del f['cells'][POOL_HANDLE+13];r=self.derive(f)
        self.assertIn('reaching byte',r['boundary']['reason']);self.assertEqual(r['boundary']['site'],at(f['layout'],'scheduler',56));self.assert_raw(f,r,stop_before=r['boundary']['site'])
    def test_unknown_source_word_is_copied_without_pointer_or_scalar_observation(self):
        f=requester_fixture(first=17,second=0);f['registers'][0]=O('unobserved record identity');r=self.derive(f);self.returned(f,r)
        self.assertEqual(self.word(r,JOB+24),O('unobserved record identity'));self.assertFalse(r['source_or_ELF_admission'])
    def test_opaque_count_stops_at_real_shift_before_scheduler_call(self):
        f=requester_fixture();f['registers'][1]=O('unknown count');r=self.derive(f)
        self.assertIn('scalar observation',r['boundary']['reason']);self.assertEqual(r['actual_scheduler_entries'],[]);self.assert_raw(f,r,stop_before=at(f['layout'],'requester256',4))
    def test_real_nested_saves_restore_all_incoming_callee_saved_origins(self):
        f=requester_fixture(first=10000,second=12000);f['registers'][4]=P(JOB);f['registers'][8]=O('new high origin');f['registers'][9]=P(RECORD)
        r=self.derive(f);self.returned(f,r)
        for reg in range(4,13):self.assertEqual(r['registers'][reg],f['registers'][reg])
        self.assertFalse(r['ABI_preservation_assumed'])
    def test_saved_scheduler_words_can_overwrite_allocators_existing_header(self):
        f=requester_fixture(first=17,second=0);h=E-176;pool(f['cells'],h,17);put(f['cells'],POOL_HANDLE,P(h));r=self.derive(f)
        self.assertIn('narrow read',r['boundary']['reason']);self.assertEqual(r['actual_callback_entries'],[]);self.assert_raw(f,r,stop_before=r['boundary']['site'])
        artifact('new-requester-frame-heap-alias.json',r)
    def test_live_allocation_does_not_revive_retired_job_payload(self):
        f=requester_fixture(first=17,second=0);f['released_payload_spans']=((JOB,JOB+68),);r=self.derive(f)
        self.assertIn('retired',r['boundary']['reason']);self.assertEqual(r['actual_callback_entries'],[]);self.assert_raw(f,r,stop_before=r['boundary']['site'])
    def test_parent_loop_uses_same_explicit_budget_without_list_shortcut(self):
        parent,head=25000,26000;f=requester_fixture(first=17,second=0,parent=parent);put(f['cells'],parent+16,P(head));put(f['cells'],head+8,P(head));f['max_steps']=613;r=self.derive(f)
        self.assertIn('budget',r['boundary']['reason']);self.assertEqual(len(r['trace']),613);self.assert_raw(f,r,step_limit=613)
    def test_complete_requester_identity_and_new_selector_are_required(self):
        def mutate(l):
            if hasattr(l,'requester_data'):
                data=l.requester_data;return replace(l,requester_data=data[:22]+bytes((data[22]^1,))+data[23:])
            return replace(l,prior=mutate(l.prior))
        l=layout();self.assertEqual(model.bind(l.prior,selector=model.SELECTOR),l)
        with self.assertRaises(ValueError):model._validate(mutate(l))
        with self.assertRaises(ValueError):model.bind(l.prior,selector=model.allocation099.SELECTOR)
