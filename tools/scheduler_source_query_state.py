"""Conditional source query, exact scheduler-entry cutpoint and root return.

One common byte state carries the new predicate's real saves, repeated field
reads and nested returns. Earlier081 remains frozen; no actual reaching,
physical, allocation, callback or native authority is supplied here.
"""
from dataclasses import dataclass
import hashlib
import scheduler_phase256_state as phase081

words,atoms,removal=phase081.words,phase081.atoms,phase081.removal
_call=phase081._call
SELECTOR='conditional-source-query-root-continuation-v1'
SHAPES={}
SHAPES['predicate']=bytes.fromhex('10b5041cd4f758fe818808200840002801d0012000e0002000280ed1201c202109f090fd0006002807d1201c09f088fc0006002801d1012000e0002010bc02bc0847')
SHAPES['identity']=bytes.fromhex('7047')
SHAPES['mask']=bytes.fromhex('10b50c04240ccbf7b5f880880440002c01d1002000e0012010bc02bc0847')
SHAPES['byte_wrapper']=bytes.fromhex('00b5cbf7cbf90006000e02bc0847')
SHAPES['byte_getter']=bytes.fromhex('b0218900401800787047')
SHAPES['wrapper']=bytes.fromhex('70b5464640b481b0061c0c1c90462404240c094d28680093311c221c4346fff7e3fe2968898901225140c18201b008bc984670bc02bc0847f08f0002')

EDGES={'predicate':{4:'identity',32:'mask',44:'byte_wrapper'},'mask':{6:'identity'},'byte_wrapper':{2:'byte_getter'},'wrapper':{30:None}}
LITERALS={**phase081.LITERALS,'wrapper':(56,)}
ROOT_SITES=frozenset((124,126,128,130,132,216,218,220,222,224,226,228))
EXECUTABLE=frozenset(('root','next','predicate','identity','mask','byte_wrapper','byte_getter','wrapper'))

@dataclass(frozen=True)
class Layout:
    prior: phase081.Layout
    dependencies: tuple


def _validate(layout):
    if type(layout) is not Layout or type(layout.dependencies) is not tuple or len(layout.dependencies)!=len(SHAPES):
        raise ValueError('complete source-query layout and six dependencies required')
    owners=phase081._validate(layout.prior);extra={}
    for item in layout.dependencies:
        if type(item) is not tuple or len(item)!=3:raise ValueError('dependency record required')
        name,a,b=item
        if type(name) is not str or name not in SHAPES or name in extra or type(a) is not int or a%4 or             not 0<=a<=2**32-len(SHAPES[name]) or type(b) is not bytes or len(b)!=len(SHAPES[name]):
            raise ValueError('complete aligned dependency required')
        extra[name]=(a,b)
    owners.update(extra)
    spans=sorted((a,a+len(b)) for a,b in owners.values())
    if any(a[1]>b[0] for a,b in zip(spans,spans[1:])):raise ValueError('complete owners overlap')
    for name,(a,b) in extra.items():
        want=bytearray(SHAPES[name])
        for off,target_name in EDGES.get(name,{}).items():
            target=_call(b,a,off)
            if not 0<=target<2**32 or target_name is not None and target!=owners[target_name][0]:
                raise ValueError('actual nested dependency target differs')
            want[off:off+4]=removal._bl(a+off,target)
        for off in LITERALS.get(name,()):want[off:off+4]=b[off:off+4]
        if bytes(want)!=b:raise ValueError('complete source-query instruction shape differs')
    a,b=owners['next']
    if _call(b,a,16)!=owners['predicate'][0] or _call(b,a,44)!=owners['wrapper'][0]:
        raise ValueError('source helper calls do not identify query/wrapper owners')
    return owners


def bind(prior_layout,dependencies,*,selector):
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit082 selector required')
    result=Layout(prior_layout,dependencies);_validate(result);return result


def continue_from_081(layout,arena_base,report,root_entry_sp,root_return_word,*,selector,protected_spans=(),max_steps=1024):
    owners=_validate(layout);old=phase081._validate(layout.prior)
    pins=[dict(role=name,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for name,(a,b) in sorted(old.items())]
    if type(report) is not dict or report.get('schema')!=phase081.SELECTOR or report.get('complete_owner_pins')!=pins or         report.get('final_PC')!=owners['next'][0] or not isinstance(report.get('boundary'),dict) or         report['boundary'].get('reason')!='next source helper entry requires independent closure' or         report.get('conditional_root_return') is not False:
        raise ValueError('exact081 source-entry report required')
    expected=dict(role='next',return_pc=owners['root'][0]+124,entry_sp=root_entry_sp-52)
    if report.get('pending_calls')!=[expected]:raise ValueError('081 source call frame differs')
    # Classifying inherited retirement uses retained events, never coordinate guesses.
    stack_spans=tuple(tuple(e['coordinates']) for e in report.get('memory_events',()) if e.get('operation')=='retire-frame')
    released=tuple(tuple(s) for s in report.get('conditional_released_payloads',()))
    recorded=tuple(tuple(s) for s in report.get('retired_spans',()))
    payload_events=tuple(tuple(e['coordinates']) for e in report.get('memory_events',()) if e.get('operation')=='retire-payload-conditional')
    if payload_events!=released:
        raise ValueError('081 payload retirement events and intervals differ')
    # A later PUSH may clip an earlier retired stack interval. Such fragments
    # retain the earlier event's classification; exact tuple equality is too strong.
    if any(not any(lo<=a and b<=hi for lo,hi in (*stack_spans,*released)) for a,b in recorded):
        raise ValueError('unclassified incoming retired intervals require an explicit lifetime adapter')
    result=derive(layout,arena_base,{int(k):v for k,v in report['post_cells'].items()},report['registers'],
        root_entry_sp,root_return_word,selector=selector,protected_spans=protected_spans,
        retired_stack_spans=recorded,released_payload_spans=released,max_steps=max_steps)
    result['inherited_081_obligations']=report.get('obligations',[])
    result['inherited_081_owner_pins']=pins
    result['actual_081_reaching_authentication_proved']=False
    return result


def derive(layout,arena_base,cells,registers,root_entry_sp,root_return_word,*,selector,
           protected_spans=(),retired_stack_spans=(),released_payload_spans=(),max_steps=1024):
    """Start at actual FDE58 entry under explicit enclosing root frame premises.

    Retired stack intervals permit real subsequent stack reuse. Released payload
    intervals never revive merely because SP moves. Neither supplies permission.
    """
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit082 selector required')
    owners=_validate(layout)
    if type(arena_base) is not int or arena_base%4 or not 0<=arena_base<2**32 or type(cells) is not dict or len(cells)>4096 or         any(type(k) is not int or not -(2**31)<=k<2**31 or not atoms._cell(v) for k,v in cells.items()) or         type(registers) is not dict or set(registers)!=set(range(15)) or any(type(k) is not int or not words._word(v) for k,v in registers.items()) or         type(max_steps) is not int or not 1<=max_steps<=1024:
        raise ValueError('bounded common byte/register/numeric witness required')
    for spans in (protected_spans,retired_stack_spans,released_payload_spans):
        if type(spans) is not tuple or len(spans)>128 or any(type(s) is not tuple or len(s)!=2 or
            any(type(v) is not int for v in s) or not -(2**31)<=s[0]<s[1]<=2**31 for s in spans):
            raise ValueError('bounded explicit intervals required')
    if type(root_entry_sp) is not int or not -(2**31)<=root_entry_sp<2**31 or not words._word(root_return_word):
        raise ValueError('explicit root entrySP and return word required')
    r,m=dict(registers),dict(cells);retired=list(retired_stack_spans)+list(released_payload_spans)
    trace=[];events=[];stack=[];returns=[]
    pc=owners['next'][0];flags=None;boundary=None;root_return=False;freed=list(released_payload_spans);frames=[]
    entry_lr=root_return_word;entry_sp=root_entry_sp;active_role=None
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
            name='082 local '+str(len(trace))
            while name in used:name+='x'
            for at in range(lo,hi):m.setdefault(at,('opaque-byte',name,at-lo))
        frames.append((lo,hi));events.append(dict(site=pc,operation='allocate-frame',coordinates=[lo,hi],initialization_granted=False))
    def retire(lo,hi,kind='frame'):
        retired.append((lo,hi));events.append(dict(site=pc,operation='retire-'+kind,coordinates=[lo,hi]))
    def bits_add(a,b,sub=False):
        av,bv=observed(a),observed(b)
        if av['kind']=='base-plus' and bv['kind']=='constant':
            delta=bv['value'];n=av['coordinate']+(-delta if sub else delta)
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
        role=next((name for name,(a,b) in owners.items() if a==target),None)
        if role is None:stop('unsupported direct callee',target=target)
        record=dict(role=role,return_pc=ret,entry_sp=address(r[13]))
        stack.append(record)
    try:
        physical(root_entry_sp,0)
        if address(r[13])!=root_entry_sp-52 or r[14]!=words._constant((owners['root'][0]+124)|1):
            stop('source entry SP/LR differs from actual root call interface')
        if r[1]!=words._constant(5) or r[2]!=words._constant(0):
            stop('source entry scalar arguments differ from actual root call')
        stack.append(dict(role='next',return_pc=owners['root'][0]+124,entry_sp=root_entry_sp-52))
        for step in range(max_steps):
            found=next(((name,a,b) for name,(a,b) in owners.items() if a<=pc<a+len(b)),None)
            if found is None:stop('control outside complete owners')
            role,a,data=found;active_role=role;off=pc-a;trace.append(pc)
            if off%2 or any(o<=off<o+4 for o in LITERALS.get(role,())):stop('control reaches literal or noninstruction')
            if role=='root' and off not in ROOT_SITES:stop('unsupported root phase or continuation')
            if role not in EXECUTABLE:stop('control reaches an owner outside the selected source continuation')
            if role=='wrapper':stop('actual84-byte scheduler request requires independent composition',target=pc)
            h=int.from_bytes(data[off:off+2],'little');nxt=pc+2
            if h&0xf800==0xf000:
                target=_call(data,a,off);nxt=pc+4;r[14]=words._constant(nxt|1);call(target,nxt);nxt=target
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
                    if stack:
                        rec=stack[-1]
                        if target!=(rec['return_pc']|1) or address(r[13])!=rec['entry_sp']:
                            stop('actual saved return word or restored SP differs',observed_target=target)
                        stack.pop();returns.append(dict(role=rec['role'],site=pc,observed_target=target));nxt=target&~1
                    else:
                        if role!='root' or r[rs]!=entry_lr or address(r[13])!=entry_sp:stop('root return word or SP differs from entry')
                        root_return=True;pc=target&~1;break
            elif h&0xe000==0x0000:
                if h&0xf800==0x1800:
                    sub=bool(h&512);d=h&7;s=(h>>3)&7;b=words._constant((h>>6)&7) if h&1024 else r[(h>>6)&7]
                    old=r[s];v=bits_add(old,b,sub);r[d]=v;arithmetic_flags(old,b,v,sub)
                else:
                    op=(h>>11)&3;count=(h>>6)&31;s=(h>>3)&7;d=h&7;v=numeric(r[s])
                    if op>1:stop('unsupported shift')
                    count=(count or 32) if op else count
                    value=(v<<count)&0xffffffff if op==0 else v>>count
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
                elif op in (0,12):
                    av,bv=numeric(r[d]),numeric(r[s]);r[d]=words._constant(av&bv if op==0 else av|bv);nz_flags(r[d])
                else:stop('unsupported scalar ALU')
            elif h&0xf800==0x4800:
                at=((pc+4)&~3)+(h&255)*4
                if not a<=at<=a+len(data)-4:stop('literal outside bound owner')
                value=int.from_bytes(data[at-a:at-a+4],'little');r[(h>>8)&7]=words._constant(value)
                events.append(dict(site=pc,operation='read-code-literal',address=at,value=value,grants_access=False))
            elif h&0xe000==0x6000 or h&0xf000==0x8000:
                half=h&0xf000==0x8000;width=2 if half else 1 if h&4096 else 4
                offset=((h>>6)&31)*width;at=address(r[(h>>3)&7])+offset;d=h&7
                if h&2048:r[d]=load(at,width)
                else:store(at,r[d] if width==4 else words._constant(numeric(r[d]))[:width])
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
    pins=[dict(role=role,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for role,(a,b) in sorted(owners.items())]
    return dict(schema=SELECTOR,complete_owner_pins=pins,trace=trace,final_PC=pc,registers=r,
        post_cells={str(k):v for k,v in sorted(m.items())},changed_cells={str(k):v for k,v in sorted(m.items()) if cells.get(k)!=v},
        memory_events=events,retired_spans=retired,conditional_released_payloads=freed,conditional_root_return=root_return,
        observed_returns=returns,pending_calls=stack,boundary=boundary,
        root_entry_SP=root_entry_sp,root_return_word=root_return_word,
        actual_reaching_proved=False,physical_access_proved=False,actual_heap_lifetime_proved=False,
        actual_termination_proved=False,whole_CFG_closed=False,native_admission=False,
        obligations=[
            'Actual source-entry registers and all byte origins must equal the root+120 reaching interface; root entrySP/LR are explicit enclosing premises.',
            'Every read/write/frame needs live physical permission and synchronous noninterference. Code and literal words grant no memory access or callback effect.',
            'Retired stack reuse and released payload lifetimes require their stated classification. Freed payload aliases remain dead even when SP allocation overlaps them.',
            'Repeated predicate field reads observe intervening real stack stores. No invariant flags, purity, saved-register ABI or uninitialized scalar values are assumed.',
            'The selected nonzero-predicate path returns through actual helper/root epilogues. The zero-predicate path stops before the actual84-byte wrapper entry with its descriptor bytes and all aliases retained.',
            'No actual reaching, allocation, installed image, source admission, global termination, wholeCFG or native credit follows from this conditional relation.'])
