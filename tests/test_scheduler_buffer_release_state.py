"""New091 dual release continuation cases and independent raw oracle."""
from dataclasses import replace
import unittest,hashlib,json,os
from pathlib import Path
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_buffer_release_state as model
previous=model.queue090.subrecord089
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


GPOOL,GHEAP,POOL_HANDLE,HEAP1,HEAP2,NODE1,NODE2=0xF430,0x8FF4,600,1000,1600,1200,1800
POINTS=(BASE+GPOOL,BASE+GHEAP)

def prior_queue_layout():
    p=prior_subrecord_layout();addresses={'query':0x080C95A8,'ring':0x080D3AF8,'payload':0x08005BFC,'enqueue':0x08000A98}
    return model.queue090.Layout(p,tuple((n,a,model.queue090.SHAPES[n]) for n,a in addresses.items()))
def layout():
    p=prior_queue_layout();addresses={'pool_release':0x08005B0C,'global_release':0x0800A668}
    return model.Layout(p,tuple((n,a,model.SHAPES[n]) for n,a in addresses.items()))
def fixture(phase=260,count=1,shared_pool=False):
    l=layout();m={};r={i:O('091 incomingR'+str(i)) for i in range(15)}
    r.update({1:P(DESC),2:P(PAYLOAD),13:P(E),14:I(RETURN)})
    half(m,DESC,phase);half(m,PAYLOAD+4,count);put(m,PAYLOAD+32,P(NODE1));put(m,PAYLOAD+36,P(NODE2))
    put(m,GPOOL,P(POOL_HANDLE));put(m,POOL_HANDLE,P(HEAP1));put(m,GHEAP,P(HEAP1 if shared_pool else HEAP2))
    for h in (HEAP1,HEAP2):
        for a in range(h,h+12):m[a]=0
    for n in (NODE1,NODE2):
        for a in range(n-12,n):m[a]=0
        half(m,n-8,0x7373);half(m,n-6,35)
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR,release_spans=((NODE1,NODE1+128),(NODE2,NODE2+128)),literal_points=POINTS)

def raw(f,stop_before=None,stop_visit=1,step_limit=None):
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
class ReleaseTests(unittest.TestCase):
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
        self.assertEqual(r['final_PC'],RETURN&~1);self.assertEqual(r['registers'][13],P(E));self.assert_raw(f,r)
    def word(self,r,a):return tuple(memory(r)[a+i] for i in range(4))
    def test_phase259_sets_count_then_reloads_and_advances_phase(self):
        f=fixture(phase=259,count=83);r=self.derive(f);artifact('new-phase259-return.json',r);self.returned(f,r);m=memory(r)
        self.assertEqual([m[PAYLOAD+4],m[PAYLOAD+5]],[1,0]);self.assertEqual([m[DESC],m[DESC+1]],[4,1]);self.assertEqual(r['conditional_released_payloads'],[])
        self.assertNotIn(at(f['layout'],'pool_release'),r['trace'])
    def test_nonzero_decrement_returns_without_touching_missing_pool_data(self):
        f=fixture(count=2)
        for a in (GPOOL,GHEAP,POOL_HANDLE):
            for i in range(4):del f['cells'][a+i]
        r=self.derive(f);self.returned(f,r);self.assertEqual([memory(r)[PAYLOAD+4],memory(r)[PAYLOAD+5]],[1,0]);self.assertEqual(r['conditional_released_payloads'],[])
    def test_zero_count_underflows_to65535_without_release(self):
        f=fixture(count=0);r=self.derive(f);self.returned(f,r);self.assertEqual([memory(r)[PAYLOAD+4],memory(r)[PAYLOAD+5]],[255,255]);self.assertEqual(r['conditional_released_payloads'],[])
    def test_two_actual_pool_releases_execute_free_insert_and_callback_return(self):
        f=fixture();r=self.derive(f);artifact('new-dual-release-return.json',r);self.returned(f,r);m=memory(r)
        self.assertEqual(r['conditional_released_payloads'],[(NODE1,NODE1+128),(NODE2,NODE2+128)])
        self.assertEqual(self.word(r,PAYLOAD+32),I(0));self.assertEqual(self.word(r,PAYLOAD+36),I(0));self.assertEqual([m[DESC],m[DESC+1]],[2,0])
        self.assertEqual([m[NODE1-8],m[NODE1-7]],[0x70,0x73]);self.assertEqual([m[NODE2-8],m[NODE2-7]],[0x70,0x73])
        self.assertEqual([x['role'] for x in r['observed_returns']].count('free'),2)
        for i in (4,5,6,7,8,9,10,11,12):self.assertEqual(r['registers'][i],f['registers'][i])
        for k in ('actual_DMA_completion_proved','actual_device_transfer_proved','queued_buffer_lifetime_proved','actual_heap_lifetime_proved','physical_access_proved'):self.assertIs(r[k],False)
    def test_both_release_wrappers_share_one_actual_pool_state(self):
        f=fixture(shared_pool=True);r=self.derive(f);artifact('new-shared-pool-release.json',r);self.returned(f,r)
        self.assertEqual(r['conditional_released_payloads'],[(NODE1,NODE1+128),(NODE2,NODE2+128)]);self.assertEqual([memory(r)[HEAP1+4],memory(r)[HEAP1+5]],[2,0])
        self.assertEqual([memory(r)[HEAP2+4],memory(r)[HEAP2+5]],[0,0])
    def test_phase_descriptor_aliases_counter_reload_after_real_store(self):
        f=fixture(phase=259);f['registers'][1]=P(PAYLOAD+4);half(f['cells'],PAYLOAD+4,259);r=self.derive(f);self.returned(f,r)
        self.assertEqual([memory(r)[PAYLOAD+4],memory(r)[PAYLOAD+5]],[2,0]);self.assertEqual(r['conditional_released_payloads'],[])

    def add_neighbor(self,f,block,*,prev=0,nxt=0,size=16):
        for a in range(block,block+12):f['cells'][a]=0
        half(f['cells'],block,prev);half(f['cells'],block+2,nxt);half(f['cells'],block+4,0x7370);half(f['cells'],block+6,size)
        half(f['cells'],HEAP1,(block-HEAP1)//4);half(f['cells'],HEAP1+2,(block-HEAP1)//4);half(f['cells'],HEAP1+4,1)

    def test_first_release_coalesces_backward_before_second_pool_operation(self):
        f=fixture();self.add_neighbor(f,1100,nxt=47,size=16);half(f['cells'],NODE1-12,25)
        r=self.derive(f);self.returned(f,r);m=memory(r)
        self.assertEqual(m[1106]|m[1107]<<8,51);self.assertEqual(m[HEAP1]|m[HEAP1+1]<<8,25);self.assertEqual(r['trace'].count(at(f['layout'],'remove')),1)

    def test_first_release_coalesces_forward_then_second_releases_independently(self):
        f=fixture();self.add_neighbor(f,1400,prev=47,size=11);half(f['cells'],NODE1-10,100)
        r=self.derive(f);self.returned(f,r);m=memory(r)
        self.assertEqual(m[NODE1-6]|m[NODE1-5]<<8,46);self.assertEqual(r['trace'].count(at(f['layout'],'remove')),1)

    def test_both_neighbors_coalesce_with_actual_median_and_dual_release(self):
        f=fixture();self.add_neighbor(f,1100,nxt=47,size=16);self.add_neighbor(f,1400,prev=47,size=11)
        for a,v in ((HEAP1,25),(HEAP1+2,25),(HEAP1+4,2),(1110,100),(1408,25),(NODE1-12,25),(NODE1-10,100)):half(f['cells'],a,v)
        r=self.derive(f);artifact('new-coalescing-release.json',r);self.returned(f,r);m=memory(r)
        self.assertEqual(m[1106]|m[1107]<<8,65);self.assertEqual(m[HEAP1+4],1);self.assertEqual(r['trace'].count(at(f['layout'],'remove')),2)

    def test_nonfree_following_header_gets_actual_backlink_write(self):
        f=fixture()
        for a in range(1400,1412):f['cells'][a]=0
        half(f['cells'],1404,0x7373);half(f['cells'],NODE1-10,100)
        r=self.derive(f);self.returned(f,r);self.assertEqual([memory(r)[1400],memory(r)[1401]],[47,0])

    def test_missing_release_interval_stops_after_real_first_allocator_effects(self):
        f=fixture();f['release_spans']=();r=self.derive(f);artifact('new-missing-release-boundary.json',r)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'free',250));self.assertIn('lifetime premise',r['boundary']['reason']);self.assertEqual(r['conditional_released_payloads'],[]);self.assertEqual(memory(r)[NODE1-8],0x70)
        self.assertEqual(self.word(r,PAYLOAD+32),P(NODE1));self.assert_raw(f,r,stop_before=at(f['layout'],'free',250))

    def test_missing_second_release_interval_preserves_first_retirement(self):
        f=fixture();f['release_spans']=((NODE1,NODE1+128),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'free',250));self.assertIn('lifetime premise',r['boundary']['reason']);self.assertEqual(r['conditional_released_payloads'],[(NODE1,NODE1+128)])
        self.assertEqual(self.word(r,PAYLOAD+32),I(0));self.assertEqual(self.word(r,PAYLOAD+36),P(NODE2));self.assert_raw(f,r,stop_before=at(f['layout'],'free',250),stop_visit=2)

    def test_release_extent_intersecting_protected_bytes_stops_before_retirement(self):
        f=fixture();f['protected_spans']=((NODE1+32,NODE1+36),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'free',250));self.assertIn('protected',r['boundary']['reason']);self.assertEqual(r['conditional_released_payloads'],[]);self.assert_raw(f,r,stop_before=at(f['layout'],'free',250))

    def test_first_release_blocks_actual_caller_write_through_retired_alias(self):
        f=fixture();p=NODE1-20;f['registers'][2]=P(p);half(f['cells'],p+4,1);put(f['cells'],p+32,P(NODE1));put(f['cells'],p+36,P(NODE2))
        r=self.derive(f);artifact('new-retired-caller-alias.json',r)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',312));self.assertIn('retired',r['boundary']['reason']);self.assertEqual(r['conditional_released_payloads'],[(NODE1,NODE1+128)]);self.assert_raw(f,r,stop_before=at(f['layout'],'callback40',312))

    def test_first_release_retires_second_global_pointer_read_without_role_separation(self):
        f=fixture();n=GHEAP-16;put(f['cells'],PAYLOAD+32,P(n))
        for a in range(n-12,n):f['cells'][a]=0
        half(f['cells'],n-8,0x7373);half(f['cells'],n-6,35);f['release_spans']=((n,n+32),(NODE2,NODE2+128))
        r=self.derive(f);self.assertEqual(r['boundary']['site'],at(f['layout'],'global_release',6));self.assertIn('retired',r['boundary']['reason']);self.assertEqual(r['conditional_released_payloads'],[(n,n+32)]);self.assert_raw(f,r,stop_before=at(f['layout'],'global_release',6))

    def test_phase_pointer_inside_released_buffer_refuses_final_halfword_store(self):
        f=fixture();f['registers'][1]=P(NODE1+4);half(f['cells'],NODE1+4,260);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',324));self.assertIn('retired',r['boundary']['reason']);self.assertEqual(len(r['conditional_released_payloads']),2);self.assert_raw(f,r,stop_before=at(f['layout'],'callback40',324))

    def test_null_first_buffer_has_no_invented_null_free_guard(self):
        f=fixture();put(f['cells'],PAYLOAD+32,I(0));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'free_wrapper',4));self.assertIn('provenance',r['boundary']['reason']);self.assertEqual(r['conditional_released_payloads'],[])
        # The BL installs its real LR before the proven-provenance boundary.
        regs,mem,trace,events,pc=raw(f,stop_before=at(f['layout'],'free'))
        self.assertEqual(r['trace'],trace[:-1]);self.assertEqual(r['registers'][14],I(at(f['layout'],'free_wrapper',8)|1))

    def test_uninitialized_first_global_pointer_remains_opaque(self):
        f=fixture();put(f['cells'],GPOOL,O('unknown pool handle'));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'pool_release',2));self.assertIn('provenance',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'pool_release',2))

    def test_missing_pool_word_is_not_inferred_from_handle_identity(self):
        f=fixture();del f['cells'][POOL_HANDLE+2];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'pool_release',2));self.assertIn('reaching',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'pool_release',2))

    def test_actual_first_global_literal_requires_explicit_point_identity(self):
        f=fixture();f['literal_points']=(BASE+GHEAP,);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',304));self.assertIn('provenance',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'callback40',304))

    def test_preexisting_retired_allocator_header_refuses_real_byte_read(self):
        f=fixture();f['released_payload_spans']=((NODE1-12,NODE1+128),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'free',14));self.assertIn('retired',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'free',14))

    def test_external_retired_stack_interval_is_not_revived_by_callback_push(self):
        f=fixture();f['retired_stack_spans']=((E-4,E),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40'));self.assertIn('externally retired',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'callback40'))

    def test_opaque_counter_is_refused_before_scalar_decrement(self):
        f=fixture();f['cells'][PAYLOAD+4]=('opaque-byte','counter',0);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',288));self.assertIn('narrow read',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'callback40',288))

    def test_wrong_later_phase_is_cut_after_actual_read_and_saved_frame(self):
        f=fixture(phase=258);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',10));self.assertIn('phase259/260',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'callback40',10))

    def test_protected_countdown_halfword_stops_actual_store(self):
        f=fixture(count=2);f['protected_spans']=((PAYLOAD+4,PAYLOAD+6),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',292));self.assertIn('protected',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'callback40',292))

    def test_phase259_store_alias_overwrites_real_saved_return_and_is_observed(self):
        f=fixture(phase=259);f['registers'][2]=P(E-8);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'callback40',334));self.assertIn('saved return',r['boundary']['reason']);self.assert_raw(f,r,stop_before=at(f['layout'],'callback40',334))

    def test_explicit_step_bound_retains_partial_allocator_state(self):
        f=fixture();f['max_steps']=80;r=self.derive(f)
        self.assertIn('budget',r['boundary']['reason']);self.assertEqual(len(r['trace']),80);self.assertFalse(r['conditional_callback_return']);self.assert_raw(f,r,step_limit=80)

    def test_complete_release_shapes_and_explicit_selector_are_required(self):
        l=layout();self.assertEqual(model.bind(l.prior,l.dependencies,selector=model.SELECTOR),l)
        with self.assertRaisesRegex(ValueError,'selector'):model.bind(l.prior,l.dependencies,selector='default')
        deps=list(l.dependencies);n,a,b=deps[0];deps[0]=(n,a,b[:-2])
        with self.assertRaisesRegex(ValueError,'complete'):model.bind(l.prior,tuple(deps),selector=model.SELECTOR)
        deps=list(l.dependencies);n,a,b=deps[1];bad=bytearray(b);bad[16]^=4;deps[1]=(n,a,bytes(bad))
        with self.assertRaisesRegex(ValueError,'identity'):model.bind(l.prior,tuple(deps),selector=model.SELECTOR)

    def test_real_wrapper_call_edge_is_not_an_arbitrary_accepted_address(self):
        l=layout();deps=list(l.dependencies);n,a,b=deps[0];bad=bytearray(b);bad[4:8]=model.removal._bl(a+4,at(l,'free_wrapper')+2);deps[0]=(n,a,bytes(bad))
        with self.assertRaisesRegex(ValueError,'identity'):model.bind(l.prior,tuple(deps),selector=model.SELECTOR)

    def test_ambiguous_or_malformed_release_intervals_are_rejected(self):
        f=fixture();f['release_spans']=((NODE1,NODE1+128),(NODE1,NODE1+64))
        with self.assertRaisesRegex(ValueError,'unique'):self.derive(f)
        f['release_spans']=((NODE1,NODE1),)
        with self.assertRaisesRegex(ValueError,'intervals'):self.derive(f)
