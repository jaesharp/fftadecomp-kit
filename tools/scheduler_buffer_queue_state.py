"""Conditional query, ring descriptor, RAM enqueue and callback continuation.

Actual common-byte instructions execute in order. Queuing descriptor words
establishes neither a device transfer nor hardware completion or lifetime.
"""
from dataclasses import dataclass
import hashlib
import scheduler_subrecord_continuation as subrecord089
words,atoms,removal=subrecord089.words,subrecord089.atoms,subrecord089.removal
_call=subrecord089._call
SELECTOR='conditional-buffer-query-queue-continuation-v1'
SHAPES={'query': b'\x00\x04\x00\x0c\x02I\x03J\x89\x18@\x18\x00xpG\x00\x00\x00\x020 \x00\x00', 'ring': b'\x00\xb5\x0cH\x00h2\xf7}\xf8\x02\x1c\nH\x11\x18\x08x\x010\x08p\x00\x06\x00\x0e\x0f(\x01\xd9\x00 \x08p\tx\xc8\x00@\x1a\x80\x00\x04I@\x18\x10\x18\x02\xbc\x08G\xc0Y\x01\x02\x14\t\x00\x00\x18\t\x00\x00', 'payload': b'\x180pG', 'enqueue': b'0\xb5\x05\x1c\x1b\x04\x1b\x0c\x00$,p\x01 hpi`\xaa`\x80 \x00\x06\x03C\xeb`\xaca\x03I\x08h\x00(\x04\xd1\r`\t\xe0\x00\x00\xcc+\x00\x03\x01\x1c\x00\xe0\x89i\x88i\x00(\xfb\xd1\x8da0\xbc\x01\xbc\x00G'}
@dataclass(frozen=True)
class Layout:
    prior: subrecord089.Layout
    dependencies: tuple

def _validate(layout):
    if type(layout) is not Layout or type(layout.dependencies) is not tuple or len(layout.dependencies)!=4:
        raise ValueError('complete090 layout required')
    owners=subrecord089._validate(layout.prior);new={}
    for row in layout.dependencies:
        if type(row) is not tuple or len(row)!=3:raise ValueError('complete actual helper tuple required')
        role,a,data=row
        if role not in SHAPES or role in new or type(a) is not int or a%4 or not 0<=a<=2**32-len(SHAPES[role]) or type(data) is not bytes or len(data)!=len(SHAPES[role]):
            raise ValueError('complete aligned actual queue helper required')
        new[role]=(a,data)
    owners.update(new);a,b=owners['writer']
    for off,target in ((80,'query'),(138,'ring'),(152,'enqueue')):
        if _call(b,a,off)!=new[target][0]:raise ValueError('actual writer/'+target+' edge differs')
    for role,(a,data) in new.items():
        expected=bytearray(SHAPES[role])
        if role=='ring':expected[6:10]=removal._bl(a+6,new['payload'][0])
        if data!=bytes(expected):raise ValueError('complete '+role+' identity differs')
    spans=sorted((a,a+len(b)) for a,b in owners.values())
    if any(x[1]>y[0] for x,y in zip(spans,spans[1:])):raise ValueError('complete owner spans overlap')
    return owners

def bind(prior_layout,dependencies,*,selector):
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit090 selector required')
    result=Layout(prior_layout,dependencies);_validate(result);return result

def continue_from_089(layout,arena_base,report,*,selector,protected_spans=(),literal_points=(),max_steps=4096):
    """Transport conditional bytes/frames, without replay or authentication."""
    owners=_validate(layout);old=subrecord089._validate(layout.prior)
    pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(old.items())]
    if type(report) is not dict or report.get('schema')!=subrecord089.SELECTOR or report.get('complete_owner_pins')!=pins or report.get('final_PC')!=owners['query'][0] or report.get('conditional_callback_return') is not False:
        raise ValueError('exact089 query entry report required')
    r,cut,e,ret=report.get('registers'),report.get('nested_call_cutpoint'),report.get('callback_entry_SP'),report.get('callback_return_word')
    if type(r) is not dict or set(r)!=set(range(15)) or any(not words._word(w) for w in r.values()) or type(e) is not int or not words._word(ret) or words.observe(ret).get('kind')!='constant' or type(cut) is not dict or cut.get('call_site')!=owners['writer'][0]+80 or cut.get('target')!=owners['query'][0] or cut.get('SP')!=e-52 or cut.get('return_word')!=r[14] or cut.get('register_arguments')!={i:r[i] for i in range(4)} or cut.get('callee_executed') is not False or report.get('pending_calls')!=[dict(role='callback40',return_pc=words.observe(ret)['value']&~1,entry_sp=e),dict(role='writer',return_pc=owners['callback40'][0]+232,entry_sp=e-28)]:
        raise ValueError('089 actual writer call/interface differs')
    result=derive(layout,arena_base,{int(k):v for k,v in report['post_cells'].items()},r,selector=selector,callback_entry_sp=e,callback_return_word=ret,protected_spans=protected_spans,retired_stack_spans=tuple(tuple(x) for x in report.get('retired_spans',())),released_payload_spans=tuple(tuple(x) for x in report.get('conditional_released_payloads',())),literal_points=literal_points,max_steps=max_steps)
    result['inherited_089_obligations']=report.get('obligations',[]);result['actual_089_report_authentication_proved']=False
    return result

def derive(layout,arena_base,cells,registers,*,selector,callback_entry_sp,callback_return_word,
           protected_spans=(),retired_stack_spans=(),released_payload_spans=(),literal_points=(),max_steps=4096):
    """Execute actual query and RAM queue from explicit writer cutpoint."""
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit090 selector required')
    owners=_validate(layout)
    if type(arena_base) is not int or arena_base%4 or not 0<=arena_base<2**32 or type(cells) is not dict or len(cells)>4096 or         any(type(k) is not int or not -(2**31)<=k<2**31 or not atoms._cell(v) for k,v in cells.items()) or         type(registers) is not dict or set(registers)!=set(range(15)) or any(type(k) is not int or not words._word(v) for k,v in registers.items()) or         type(max_steps) is not int or not 1<=max_steps<=4096:
        raise ValueError('bounded common byte/register/numeric witness required')
    for spans in (protected_spans,retired_stack_spans,released_payload_spans):
        if type(spans) is not tuple or len(spans)>128 or any(type(s) is not tuple or len(s)!=2 or
            any(type(v) is not int for v in s) or not -(2**31)<=s[0]<s[1]<=2**31 for s in spans):
            raise ValueError('bounded explicit intervals required')
    if type(literal_points) is not tuple or len(literal_points)>16 or any(type(v) is not int or not 0<=v<2**32 for v in literal_points):
        raise ValueError('explicit exact literal point identities required')
    if type(callback_entry_sp) is not int or callback_entry_sp%4 or not words._word(callback_return_word):raise ValueError('explicit enclosing callback frame/return required')
    r,m=dict(registers),dict(cells);retired=list(retired_stack_spans)+list(released_payload_spans)
    trace=[];events=[];stack=[];returns=[];frames=[];freed=list(released_payload_spans)
    pc=owners['query'][0];flags=None;boundary=None;cut=None
    entry_sp=None;entry_lr=r[14];returned=False
    executable=frozenset(('callback40','writer','query','ring','payload','enqueue'))
    literals={'callback40':(36,64,108,168,172,260,264,268,336),'query':(16,20),'ring':(52,56,60),'enqueue':(44,)}
    allowed={'callback40':frozenset(range(232,258,2))|frozenset((272,274,276,324,326,328,330,332,334)),
             'writer':frozenset(range(84,184,2)), 'enqueue':frozenset(range(0,42,2))|frozenset(range(48,68,2))}
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
            name='090 local '+str(len(trace))
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
        entry_sp=address(r[13]);physical(entry_sp,0);physical(callback_entry_sp,0)
        if entry_sp%4 or callback_entry_sp!=entry_sp+52 or r[14]!=words._constant((owners['writer'][0]+84)|1) or r[0]!=words._constant(13) or r[5]!=words._constant(2048) or r[7]!=words._constant(0):
            stop('query entry differs from actual writer call/frame interface')
        target=numeric(callback_return_word)
        if not target&1:stop('enclosing callback return word is not Thumb tagged')
        stack=[dict(role='callback40',return_pc=target&~1,entry_sp=callback_entry_sp),dict(role='writer',return_pc=owners['callback40'][0]+232,entry_sp=entry_sp+24),dict(role='query',return_pc=owners['writer'][0]+84,entry_sp=entry_sp)]
        for step in range(max_steps):
            found=next(((name,a,b) for name,(a,b) in owners.items() if a<=pc<a+len(b)),None)
            if found is None:stop('control outside complete owners')
            role,p,data=found;off=pc-p
            if role not in executable or off not in starts[role] or role in allowed and off not in allowed[role]:stop('control outside selected phase256 instructions')
            trace.append(pc)
            h=int.from_bytes(data[off:off+2],'little');nxt=pc+2
            if h&0xff00==0xdf00:
                stop('actual BIOS SVC requires independent effect contract',service=h&255,register_arguments={i:r[i] for i in range(4)},SP=address(r[13]))
            elif h&0xf800==0xf000:
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
                    if not stack:stop('return lacks actual call record')
                    rec=stack[-1]
                    if role!=rec['role'] or target!=(rec['return_pc']|1) or address(r[13])!=rec['entry_sp']:
                        stop('actual saved return word or restored SP differs',observed_target=target)
                    stack.pop();returns.append(dict(role=rec['role'],site=pc,observed_target=target,entry_sp=rec['entry_sp']));nxt=target&~1
                    if role=='callback40':
                        if stack:stop('callback returned with pending nested call')
                        returned=True;pc=nxt;break
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
                elif op==1:
                    compare(r[d],b)
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
                at=address(r[(h>>3)&7])+offset
                if h&2048:
                    r[d]=load(at,width)
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
        query_entry_SP=entry_sp,query_return_word=entry_lr,callback_entry_SP=callback_entry_sp,callback_return_word=callback_return_word,
        conditional_callback_return=returned,
        actual_reaching_proved=False,physical_access_proved=False,actual_heap_lifetime_proved=False,
        ABI_preservation_assumed=False,fabricated_callee_effects=False,actual_BIOS_poststate_proved=False,
        actual_termination_proved=False,whole_CFG_closed=False,source_or_ELF_admission=False,native_admission=False,
        actual_device_transfer_proved=False,actual_DMA_completion_proved=False,queued_buffer_lifetime_proved=False,
        obligations=[
            'All supplied query-entry registers, bytes, intervals and pending callback/writer frames must equal actual reaching state. Transport validation is not authentication; no old producer is rerun.',
            'Actual query reads one byte at 02002030 plus truncated R0. An exact numeric literal point grants neither extent, physical permission nor initialization. Byte points may be unaligned; actual halfword/word accesses still require alignment.',
            'Actual query byte 1 limits the chunk to 512, otherwise 2048. Remaining length can clamp it further. The ring index increments as a byte then values greater than 15 reset to zero; all reloads see prior aliases.',
            'Actual 28-byte RAM descriptor stores flag bytes, source/destination words, truncated half-count OR 80000000, and a zero next pointer. Unwritten descriptor bytes retain their origins. The real linked-list walk appends it without invented acyclicity or disjointness.',
            'Every physical read/write/frame requires live ordinary little-endian access, complete protection/lifetime inputs and synchronous noninterference. Unknown bytes remain unknown and stack reuse cannot revive freed payloads.',
            'Actual post-enqueue cursor/remaining reloads and saved return words govern continuation. Aliases can change those values or prevent return; no ABI preservation is assumed.',
            'No hardware DMA execution, copied source bytes, completion, asynchronous buffer lifetime, physical access, actual heap/SP, whole CFG, termination, source/ELF/native admission or publication credit follows from RAM queue construction.'])
