"""Conditional exact84 wrapper, actual allocator and phase0 callback prefix.

All effects are executed on one alias-aware byte state. The retained176B source
image supplies conditional instruction identity only, never installed-code or
physical-memory authority. The real callback CpuSet entry remains a cutpoint.
"""
from dataclasses import dataclass
import hashlib
import scheduler_source_query_state as source082
import scheduler_allocator_state as scheduler069
import scheduler_zero40_state as image079

words,atoms,removal=source082.words,source082.atoms,source082.removal
_call=source082._call
SELECTOR='conditional-source84-scheduler-common-byte-state-v1'
CALLBACK=bytes.fromhex('f0b5474680b48ab080460f1c161c3c880648844268d084420fdc012c00d147e1012c05dc002c1bd042e100000101000080204000844233d03ae10848844200d1f0e0844200dab5e00130844200d107e10130844200d123e12ae10000030100007868b064b868f060b88ab071f88af0710948311c1031102243f02cfeb06c074900944246019202220723e2f7e9fb7064f06804700ce1000020390003e4d73908706ce2f7cffc031c7364002b00d0ffe03424b079062800d15424b06c311c3031321c08320092074a019205220292039343460493221c0123e0f77af9f06438880130e4e0fcd7390805a91f481cc81cc100680860307a002800d1d9e0306b09ac6d462635211c2a1cdef792f8306bddf7efff16490006801568441430038824881b191b041b1440882d88401900040014009000200190081c01210322d9f7a4fa0b484146d6f7def8b0630821ff22d6f74df9b079062811d006484146d6f706fdf063054810e00000949d1408e0588f089cd6940828a0940850a094080a484146d6f7f4fcf06309484146d6f7effc3064074844460094012104220023e2f72af830653888013082e084be9408acbe940804d83908301c3c300221d6f7c3fd0006002875d0b06bd6f7d3f8041cb463002c6ed1032005f71cfc0f4a118881431180301c10300d49102243f074fd306b0021e0f718fbf06cddf75ffe306b321c0832074b00940194414602910121e0f7a6fbf064388801304ae0400900032039000300d83908307a002842d0194842460092012104220023e1f7ddff3065b06c0021dff764fbb21c311c0023dff7b1fc7063f179def767f91e20b080388801303880b088002804d00138b080000400281fd1daf7a0fe000600281ad1b06c0021daf71ffd0006002805d1f168022004e000000cd83908f168012008703888013006e0306be0f7d9f90006002801d00220388000200ab008bc9846f0bc02bc0847')
CALLBACK_SITES=frozenset(range(0,42,2))|frozenset(range(96,122,2))

@dataclass(frozen=True)
class Layout:
    prior: source082.Layout
    scheduler: scheduler069.Layout
    callback: int
    callback_data: bytes
    image: bytes
    zero_pointer_data: bytes


def _validate(layout):
    if type(layout) is not Layout or type(layout.scheduler) is not scheduler069.Layout:
        raise ValueError('complete source and scheduler layouts required')
    owners=source082._validate(layout.prior)
    s=layout.scheduler;w=s.allocator;a=w.allocator;i=a.insertion;m=i.median
    data=scheduler069._identity(s.address,w,s.callback_thunk)
    if hashlib.sha256(data).hexdigest()!=s.sha256:
        raise ValueError('complete scheduler identity differs')
    if _call(owners['wrapper'][1],owners['wrapper'][0],30)!=s.address:
        raise ValueError('source wrapper does not call actual scheduler')
    if type(layout.callback) is not int or layout.callback%4 or not 0<=layout.callback<=2**32-702 or             type(layout.callback_data) is not bytes or len(layout.callback_data)!=702:
        raise ValueError('complete aligned702B callback required')
    if int.from_bytes(owners['next'][1][52:56],'little')!=layout.callback|1:
        raise ValueError('source literal does not identify actual callback')
    expected=bytearray(CALLBACK)
    for off in (120,138):
        target=_call(layout.callback_data,layout.callback,off)
        if not 0<=target<2**32 or target%2:raise ValueError('callback BL target invalid')
        expected[off:off+4]=removal._bl(layout.callback+off,target)
    if bytes(expected)!=layout.callback_data:raise ValueError('complete callback instruction identity differs')
    if type(layout.image) is not bytes or len(layout.image)!=176 or hashlib.sha256(layout.image).hexdigest()!=image079.IMAGE_SHA256:
        raise ValueError('complete retained176B source image required')
    if type(layout.zero_pointer_data) is not bytes or layout.zero_pointer_data!=(image079.IMAGE_BASE|1).to_bytes(4,'little'):
        raise ValueError('actual four-byte zero pointer differs from image entry')
    extra={
        'scheduler':(s.address,data),
        'allocator_wrapper':(w.address,scheduler069.wrapper._identity(w.address,a)),
        'allocator':(a.address,scheduler069.split._identity(a.address,i,a.thunk,a.pointer_literal)),
        'insert':(i.address,scheduler069.split.insert.HEAD+removal._bl(i.address+22,i.search.address)+scheduler069.split.insert.MIDDLE+removal._bl(i.address+138,m.median)+scheduler069.split.insert.TAIL),
        'search':(i.search.address,scheduler069.split.insert.search.SHAPE),
        'remove':(m.removal,removal.REMOVE_HEAD+removal._bl(m.removal+124,m.median)+removal.REMOVE_TAIL),
        'median':(m.median,removal.MEDIAN),
        'zero_thunk':(a.thunk,b'\x10\x47'),
        'large_callback':(layout.callback,layout.callback_data),
        'image':(image079.IMAGE_BASE,layout.image),
    }
    for name,item in extra.items():
        if name in owners and owners[name]!=item:raise ValueError('shared allocator owner differs')
        owners[name]=item
    # The already-bound081 R3 thunk is the same canonical callback entry.
    if owners['thunk']!=(s.callback_thunk,b'\x18\x47'):
        raise ValueError('actual R3 callback thunk differs')
    spans=sorted((p,p+len(b)) for p,b in owners.values())
    if any(x[1]>y[0] for x,y in zip(spans,spans[1:])):
        raise ValueError('complete code/image owners overlap')
    if any(lo<a.pointer_literal+4 and hi>a.pointer_literal for lo,hi in spans):
        raise ValueError('zero literal overlaps immutable code')
    return owners


def bind(prior_layout,scheduler_layout,callback_address,callback_data,image,zero_pointer_data,*,selector):
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit083 selector required')
    result=Layout(prior_layout,scheduler_layout,callback_address,callback_data,image,zero_pointer_data)
    _validate(result);return result


def continue_from_082(layout,arena_base,report,*,selector,protected_spans=(),literal_points=(),max_steps=4096):
    owners=_validate(layout);old=source082._validate(layout.prior)
    pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(old.items())]
    if type(report) is not dict or report.get('schema')!=source082.SELECTOR or report.get('complete_owner_pins')!=pins or             report.get('final_PC')!=owners['wrapper'][0] or report.get('conditional_root_return') is not False or             report.get('boundary',{}).get('reason')!='actual84-byte scheduler request requires independent composition':
        raise ValueError('082 precise wrapper-entry report required')
    root_sp=report.get('root_entry_SP')
    expected=[dict(role='next',return_pc=owners['root'][0]+124,entry_sp=root_sp-52),
              dict(role='wrapper',return_pc=owners['next'][0]+48,entry_sp=root_sp-100)] if type(root_sp) is int else None
    if report.get('pending_calls')!=expected:raise ValueError('082 pending source/wrapper calls differ')
    retired=tuple(tuple(x) for x in report.get('retired_spans',()))
    released=tuple(tuple(x) for x in report.get('conditional_released_payloads',()))
    stack_events=tuple(tuple(e['coordinates']) for e in report.get('memory_events',()) if e.get('operation')=='retire-frame')
    if any(not any(lo<=a and b<=hi for lo,hi in (*stack_events,*released)) for a,b in retired):
        raise ValueError('082 unclassified retirement interval')
    result=derive(layout,arena_base,{int(k):v for k,v in report['post_cells'].items()},report['registers'],
        selector=selector,protected_spans=protected_spans,retired_stack_spans=retired,
        released_payload_spans=released,literal_points=literal_points,max_steps=max_steps)
    result['inherited_082_obligations']=report.get('obligations',[])
    result['inherited_082_owner_pins']=pins
    result['actual_082_report_authentication_proved']=False
    return result


def derive(layout,arena_base,cells,registers,*,selector,
           protected_spans=(),retired_stack_spans=(),released_payload_spans=(),literal_points=(),max_steps=4096):
    """Execute a conditional exact84 wrapper entry through the real allocator.

    Input origins and permitted fixed literal points are explicit premises.
    Literal point conversion proves only numeric identity, never accessibility.
    """
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit083 selector required')
    owners=_validate(layout)
    if type(arena_base) is not int or arena_base%4 or not 0<=arena_base<2**32 or type(cells) is not dict or len(cells)>4096 or         any(type(k) is not int or not -(2**31)<=k<2**31 or not atoms._cell(v) for k,v in cells.items()) or         type(registers) is not dict or set(registers)!=set(range(15)) or any(type(k) is not int or not words._word(v) for k,v in registers.items()) or         type(max_steps) is not int or not 1<=max_steps<=4096:
        raise ValueError('bounded common byte/register/numeric witness required')
    for spans in (protected_spans,retired_stack_spans,released_payload_spans):
        if type(spans) is not tuple or len(spans)>128 or any(type(s) is not tuple or len(s)!=2 or
            any(type(v) is not int for v in s) or not -(2**31)<=s[0]<s[1]<=2**31 for s in spans):
            raise ValueError('bounded explicit intervals required')
    if type(literal_points) is not tuple or len(literal_points)>16 or any(type(v) is not int or v%4 or not 0<=v<2**32 for v in literal_points):
        raise ValueError('explicit aligned literal point identities required')
    r,m=dict(registers),dict(cells);retired=list(retired_stack_spans)+list(released_payload_spans)
    trace=[];events=[];stack=[];returns=[];zero_calls=[]
    pc=owners['wrapper'][0];flags=None;boundary=None;cut=None;freed=list(released_payload_spans);frames=[]
    entry_sp=None;entry_lr=r[14];callback_phase=None;callback_entered=False
    scheduler_address=layout.scheduler.address;a=layout.scheduler.allocator.allocator
    executable=frozenset(('wrapper','scheduler','allocator_wrapper','allocator','insert','remove','median','search','zero_thunk','thunk','image','large_callback'))
    literals={'wrapper':(56,),'scheduler':(100,),'allocator':(196,),'large_callback':(44,92,152,156)}
    starts={}
    for role in executable:
        data=owners[role][1];off=0;sites=set()
        while off<len(data):
            if any(p<=off<p+4 for p in literals.get(role,())):off+=2;continue
            sites.add(off);h=int.from_bytes(data[off:off+2],'little');off+=4 if h&0xf800==0xf000 else 2
        starts[role]=sites
    def stop(reason,at=None,**extra):
        e=removal._Boundary(pc,reason,at);e.report.update(extra);raise e
    def observed(w):return words.observe(w)
    def numeric(w,allow_pointer=False):
        v=observed(w)
        if v['kind']=='constant':return v['value']
        if allow_pointer and v['kind']=='base-plus':
            n=arena_base+v['coordinate']
            if not 0<=n<2**32:stop('pointer numeric interpretation wraps')
            return n
        stop('scalar observation has opaque or pointer bits')
    def address(w):
        v=observed(w)
        if v['kind']=='constant' and v['value'] in literal_points:
            at=v['value']-arena_base
            if not -(2**31)<=at<2**31:stop('literal point outside coordinate range')
            return at
        if v['kind']!='base-plus':stop('address lacks intact common-base provenance')
        return v['coordinate']
    def physical(at,width,write=False,allocating=False):
        if not -(2**31)<=at<=2**31-width or not 0<=arena_base+at<=2**32-width:stop('common-base access wraps',at)
        if width in (2,4) and at%width:stop('unaligned common-byte access',at)
        if not allocating and any(at<hi and at+width>lo for lo,hi in retired):stop('access intersects retired bytes',at)
        if write and any(at<hi and at+width>lo for lo,hi in protected_spans):stop('write intersects protected bytes',at)
        if write and any(arena_base+at<a+len(b) and arena_base+at+width>a for a,b in owners.values()):
            stop('write intersects immutable owner',at)
    def load(at,width):
        physical(at,width);v=tuple(m.get(at+i) for i in range(width))
        if any(x is None for x in v):stop('read lacks reaching byte origins',at)
        if width<4 and any(type(x) is not int for x in v):stop('narrow read observes opaque or pointer bytes',at)
        events.append(dict(site=pc,operation='read'+str(width*8),coordinate=at,bytes=v))
        return v+(0,)*(4-width)
    def store(at,v):
        physical(at,len(v),True)
        if len(v)<4 and any(type(x) is not int for x in v):stop('narrow store requires scalar bits',at)
        if len(set(m)|set(range(at,at+len(v))))>4096:stop('byte state exceeds4096 cells',at)
        m.update({at+i:x for i,x in enumerate(v)});events.append(dict(site=pc,operation='write'+str(len(v)*8),coordinate=at,bytes=v))
    def allocate(lo,hi,forget=False):
        nonlocal retired
        physical(lo,hi-lo,allocating=True)
        if lo%4 or hi%4:stop('unaligned stack allocation',lo)
        # Stack reuse does not revive a caller-declared freed payload interval.
        if any(lo<b and hi>a for a,b in freed):stop('stack allocation intersects externally retired payload/frame',lo)
        retired=[piece for a,b in retired for piece in ((a,min(b,lo)),(max(a,hi),b)) if piece[0]<piece[1]]
        if forget:
            if len(set(m)|set(range(lo,hi)))>4096:stop('local byte state exceeds4096 cells',lo)
            used={v[1] for v in [*m.values(),*(v for w in r.values() for v in w)] if type(v) is tuple and v[0]=='opaque-byte'}
            name='083 local '+str(len(trace))
            while name in used:name+='x'
            for at in range(lo,hi):m.setdefault(at,('opaque-byte',name,at-lo))
        frames.append((lo,hi));events.append(dict(site=pc,operation='allocate-frame',coordinates=[lo,hi],initialization_granted=False))
    def retire(lo,hi,kind='frame'):
        retired.append((lo,hi));events.append(dict(site=pc,operation='retire-'+kind,coordinates=[lo,hi]))
    def bits_add(a,b,sub=False):
        av,bv=observed(a),observed(b)
        if av['kind']=='base-plus' and bv['kind']=='constant':
            delta=bv['value'] if bv['value']<2**31 else bv['value']-2**32;n=av['coordinate']+(-delta if sub else delta)
            if not -(2**31)<=n<2**31 or not 0<=arena_base+n<2**32:stop('pointer arithmetic wraps')
            return words._pointer(n)
        if not sub and av['kind']=='constant' and bv['kind']=='base-plus':return bits_add(b,a)
        if sub and av['kind']==bv['kind']=='base-plus':return words._constant((av['coordinate']-bv['coordinate'])&0xffffffff)
        # ADDS Rx,Ry,#0 is an exact bit copy even for opaque words.
        if bv==dict(kind='constant',value=0):return a
        return words._constant((numeric(a)+(-numeric(b) if sub else numeric(b)))&0xffffffff)
    def arithmetic_flags(a,b,result,sub=False):
        nonlocal flags
        try:av,bv,rv=numeric(a,True),numeric(b,True),numeric(result,True)
        except removal._Boundary:flags=None;return
        flags=(bool(rv&0x80000000),rv==0,av>=bv if sub else av+bv>0xffffffff,
               bool(((av^bv) if sub else ~(av^bv))&(av^rv)&0x80000000))
    def nz_flags(result,carry=None):
        nonlocal flags
        v=numeric(result);old=flags
        flags=(bool(v&0x80000000),v==0,carry if carry is not None else (old[2] if old else None),old[3] if old else None)
    def compare(a,b):
        av,bv=numeric(a,True),numeric(b,True)
        arithmetic_flags(a,b,words._constant((av-bv)&0xffffffff),True)
    def branch(cond):
        if flags is None:stop('branch requires justified flags')
        n,z,c,v=flags
        required={0:(z,),1:(z,),2:(c,),3:(c,),8:(c,z),9:(c,z),10:(n,v),11:(n,v),12:(z,n,v),13:(z,n,v)}
        if cond not in required or any(x is None for x in required[cond]):stop('branch flag unsupported or unknown')
        return {0:z,1:not z,2:c,3:not c,8:c and not z,9:not c or z,10:n==v,11:n!=v,12:not z and n==v,13:z or n!=v}[cond]
    def call(target,ret):
        if len(stack)>=64:stop('nested call bound exhausted')
        role=next((name for name,(p,b) in owners.items() if p==target),None)
        if role not in executable:return False
        stack.append(dict(role=role,return_pc=ret,entry_sp=address(r[13])))
        return True
    try:
        entry_sp=address(r[13]);physical(entry_sp,0)
        if entry_sp%4 or r[0]!=words._constant(layout.callback|1) or r[1]!=words._constant(84) or \
                r[2]!=words._pointer(entry_sp) or r[14]!=words._constant((owners['next'][0]+48)|1):
            stop('wrapper entry differs from exact84 source interface')
        for step in range(max_steps):
            found=next(((name,a,b) for name,(a,b) in owners.items() if a<=pc<a+len(b)),None)
            if found is None:stop('control outside complete owners')
            role,p,data=found;off=pc-p
            if role not in executable or off not in starts[role]:stop('control outside selected instruction boundaries')
            if role=='large_callback' and off not in CALLBACK_SITES:stop('callback phase outside selected phase0 prefix')
            if role=='image' and off>=50:stop('image control outside exact zero entry')
            trace.append(pc)
            h=int.from_bytes(data[off:off+2],'little');nxt=pc+2
            if h&0xf800==0xf000:
                target=_call(data,p,off);nxt=pc+4;r[14]=words._constant(nxt|1)
                events.append(dict(site=pc,operation='ordinary-call',target=target,SP=address(r[13]),return_word=r[14]))
                if not call(target,nxt):
                    cut=dict(call_site=pc,target=target,SP=address(r[13]),return_word=r[14],register_arguments={i:r[i] for i in range(4)},callee_executed=False)
                    pc=target;stop('actual nested helper effect requires independent closure',cutpoint='callee-entry')
                nxt=target
            elif h&0xfe00==0xb400:
                regs=[i for i in range(8) if h&(1<<i)]+([14] if h&256 else [])
                hi=address(r[13]);lo=hi-4*len(regs);allocate(lo,hi)
                vals=[r[i] for i in regs]
                for j,v in enumerate(vals):store(lo+4*j,v)
                r[13]=words._pointer(lo)
            elif h&0xfe00==0xbc00:
                if h&256:stop('POP PC outside selected shape')
                regs=[i for i in range(8) if h&(1<<i)];lo=address(r[13]);values=[load(lo+4*j,4) for j in range(len(regs))]
                for reg,value in zip(regs,values):r[reg]=value
                hi=lo+4*len(regs);retire(lo,hi);r[13]=words._pointer(hi)
            elif h&0xff00==0xb000:
                amount=(h&127)*4;old=address(r[13]);new=old-amount if h&128 else old+amount
                if h&128:allocate(new,old,True)
                else:physical(new,0);retire(old,new)
                r[13]=words._pointer(new)
            elif h&0xfc00==0x4400:
                op=(h>>8)&3;rd=(h&7)|((h>>4)&8);rs=(h>>3)&15
                if rd==15 and op!=3 or rs==15:stop('unsupported PC register operation')
                if op==2:r[rd]=r[rs]
                elif op==1:
                    compare(r[rd],r[rs])
                elif op==0:r[rd]=bits_add(r[rd],r[rs])
                else:
                    target=numeric(r[rs])
                    if not target&1:stop('observed control word is not Thumb tagged')
                    if role in ('zero_thunk','thunk'):
                        if not stack or stack[-1]['role']!=role:stop('tail thunk lacks actual call record')
                        rec=stack[-1]
                        if role=='zero_thunk':
                            count=12 if rec['return_pc']==a.address+102 else 112 if rec['return_pc']==scheduler_address+52 else None
                            if count is None or r[1]!=words._constant(count) or target!=image079.IMAGE_BASE|1:
                                stop('actual zero target/count/callsite differs')
                            dest=address(r[0]);zero_calls.append(dict(call_site=rec['return_pc']-4,count=count,destination=dest,SP=address(r[13]),installation_proved=False))
                            rec['role']='image';rec['zero_count']=count;nxt=image079.IMAGE_BASE
                        else:
                            if rec['return_pc']!=scheduler_address+184 or target!=layout.callback|1:stop('actual reloaded callback identity differs')
                            rec['role']='large_callback';nxt=layout.callback;callback_entered=True
                    elif stack:
                        rec=stack[-1]
                        if role!=rec['role'] or target!=(rec['return_pc']|1) or address(r[13])!=rec['entry_sp']:
                            stop('actual saved return word or restored SP differs',observed_target=target)
                        stack.pop();returns.append(dict(role=rec['role'],site=pc,observed_target=target,entry_sp=rec['entry_sp'],zero_count=rec.get('zero_count')));nxt=target&~1
                    else:
                        stop('wrapper continuation requires independent return closure',observed_target=target)
            elif h&0xe000==0x0000:
                if h&0xf800==0x1800:
                    sub=bool(h&512);d=h&7;s=(h>>3)&7;b=words._constant((h>>6)&7) if h&1024 else r[(h>>6)&7]
                    old=r[s];v=bits_add(old,b,sub);r[d]=v;arithmetic_flags(old,b,v,sub)
                else:
                    op=(h>>11)&3;count=(h>>6)&31;s=(h>>3)&7;d=h&7;v=numeric(r[s])
                    if op>2:stop('unsupported shift')
                    count=(count or 32) if op else count
                    value=(v<<count)&0xffffffff if op==0 else v>>count if op==1 else ((v-2**32 if v&0x80000000 else v)>>count)&0xffffffff
                    carry=(bool(v&(1<<(32-count))) if op==0 else bool(v&(1<<(count-1)))) if count else None
                    r[d]=words._constant(value);nz_flags(r[d],carry)
            elif h&0xe000==0x2000:
                op=(h>>11)&3;d=(h>>8)&7;b=words._constant(h&255)
                if op==0:r[d]=b;nz_flags(b)
                elif op==1:compare(r[d],b)
                else:
                    old=r[d];v=bits_add(old,b,op in (1,3));arithmetic_flags(old,b,v,op in (1,3))
                    if op!=1:r[d]=v
            elif h&0xfc00==0x4000:
                op=(h>>6)&15;d=h&7;s=(h>>3)&7
                if op==10:
                    compare(r[d],r[s])
                elif op in (0,1,12):
                    av,bv=numeric(r[d],op==0),numeric(r[s],op==0);r[d]=words._constant(av&bv if op==0 else av^bv if op==1 else av|bv);nz_flags(r[d])
                elif op==9:
                    old=r[s];v=words._constant((-numeric(old))&0xffffffff);r[d]=v;arithmetic_flags(words._constant(0),old,v,True)
                else:stop('unsupported scalar ALU')
            elif h&0xf800==0x4800:
                at=((pc+4)&~3)+(h&255)*4
                if at-p not in literals.get(role,()):stop('literal outside bound owner pool')
                value=int.from_bytes(data[at-p:at-p+4],'little');r[(h>>8)&7]=words._constant(value)
                events.append(dict(site=pc,operation='read-code-literal',address=at,value=value,grants_access=False))
            elif h&0xe000==0x6000 or h&0xf000==0x8000:
                half=h&0xf000==0x8000;width=2 if half else 1 if h&4096 else 4
                offset=((h>>6)&31)*width;d=h&7
                base=r[(h>>3)&7]
                if pc in (scheduler_address+42,a.address+92):
                    if h!=0x6802 or base!=words._constant(a.pointer_literal):stop('actual zero pointer load differs')
                    r[d]=tuple(layout.zero_pointer_data)
                    events.append(dict(site=pc,operation='read-code-literal',address=a.pointer_literal,value=int.from_bytes(layout.zero_pointer_data,'little'),grants_access=False))
                else:
                    at=address(base)+offset
                    if h&2048:
                        r[d]=load(at,width)
                        if role=='large_callback' and off==14:callback_phase=numeric(r[d])
                    else:store(at,r[d] if width==4 else words._constant(numeric(r[d]))[:width])
            elif h&0xf000==0xc000:
                rn=(h>>8)&7;selected=[i for i in range(8) if h&(1<<i)]
                if not selected or rn in selected:stop('ambiguous multiple-transfer register list')
                at=address(r[rn])
                if h&0x800:
                    values=[load(at+4*j,4) for j in range(len(selected))]
                    for reg,value in zip(selected,values):r[reg]=value
                else:
                    values=[r[reg] for reg in selected]
                    for j,value in enumerate(values):store(at+4*j,value)
                r[rn]=bits_add(r[rn],words._constant(4*len(selected)))
            elif h&0xf000==0x9000:
                at=address(r[13])+(h&255)*4;d=(h>>8)&7
                if h&2048:r[d]=load(at,4)
                else:store(at,r[d])
            elif h&0xf000==0xa000:
                if not h&2048:stop('unexpected ADR')
                r[(h>>8)&7]=bits_add(r[13],words._constant((h&255)*4))
            elif h&0xf000==0xd000:
                cond=(h>>8)&15;imm=h&255;imm=imm-256 if imm&128 else imm
                if branch(cond):nxt=pc+4+2*imm
            elif h&0xf800==0xe000:
                imm=h&2047;imm=imm-2048 if imm&1024 else imm;nxt=pc+4+2*imm
            else:stop('unsupported actual instruction',halfword=h)
            pc=nxt
        else:stop('explicit instruction budget exhausted')
    except removal._Boundary as e:boundary=e.report
    pins=[dict(role=role,address=p,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for role,(p,b) in sorted(owners.items())]
    return dict(schema=SELECTOR,complete_owner_pins=pins,trace=trace,final_PC=pc,registers=r,
        post_cells={str(k):v for k,v in sorted(m.items())},changed_cells={str(k):v for k,v in sorted(m.items()) if cells.get(k)!=v},
        memory_events=events,retired_spans=retired,conditional_released_payloads=freed,
        observed_returns=returns,pending_calls=stack,boundary=boundary,nested_call_cutpoint=cut,
        wrapper_entry_SP=entry_sp,wrapper_return_word=entry_lr,source_size=84,allocation_count=112,
        zero_calls=zero_calls,callback_entered=callback_entered,callback_observed_phase=callback_phase,
        image_pin=dict(address=image079.IMAGE_BASE,bytes=176,sha256=image079.IMAGE_SHA256),
        actual_reaching_proved=False,physical_access_proved=False,actual_heap_lifetime_proved=False,
        actual_installed_identity_proved=False,ABI_preservation_assumed=False,fabricated_callee_effects=False,
        actual_termination_proved=False,whole_CFG_closed=False,source_or_ELF_admission=False,native_admission=False,
        obligations=[
            'All supplied082 wrapper-entry registers, bytes, intervals and literal identities must equal actual reaching state. Shape/report validation is not state authentication.',
            'Every common-base read/write/save/frame needs live ordinary little-endian physical permission and synchronous noninterference, with complete protections and alias coverage. Literal identity supplies no access.',
            'The exact176B source must be installed and executable at03005E78 for each instruction fetch. Pointer and source hashes do not prove installation. Actual zero12 and zero112 traces retain this condition.',
            'All allocator output slots, saves, node fields, descriptor transfers and callback saves use the same bytes. Allocation success grants neither fresh disjoint memory nor caller-register survival.',
            'Stack lifetime reuse and released payload classification are supplied conditions; dead payloads cannot revive through stack allocation. Actual ownership and external stale aliases remain unproved.',
            'The real phase0 callback reaches its CpuSet helper with source literal03003920, destination node+40 and count16. Its32-byte access, BIOS effects, later E03F8 call and all returns remain separate prerequisites.',
            'No actual heap/SP witness, wholeCFG, global termination, old Sqrt closure, source/native admission or publication credit follows.'])
