"""Actual post-SVC callback/helper suffix with an explicit unclosed BIOS gap.

No function in this module computes BIOS memory/register effects or manufactures
its return state. The suffix relation begins at the actual wrapper BX LR from
separately supplied post-SVC state, preserving every observed byte and alias.
"""
from dataclasses import dataclass
import hashlib
import scheduler_source_scheduler_state as source083
import scheduler_helper_common_state as helper075

words,atoms,removal=source083.words,source083.atoms,source083.removal
_call=source083._call
SELECTOR='conditional-source-callback-postsvc-suffix-v1'

@dataclass(frozen=True)
class Layout:
    prior: source083.Layout
    helper: helper075.Layout
    bios: int
    bios_data: bytes


def _validate(layout):
    if type(layout) is not Layout:raise ValueError('complete084 layout required')
    owners=source083._validate(layout.prior);facts=helper075._validate(layout.helper)
    h=layout.helper;c=layout.prior.callback;s=layout.prior.scheduler.address
    if type(layout.bios) is not int or layout.bios%4 or not 0<=layout.bios<=2**32-4 or type(layout.bios_data) is not bytes or layout.bios_data!=b'\x0b\xdf\x70\x47':
        raise ValueError('complete SVC0B/BXLR wrapper required')
    if _call(layout.prior.callback_data,c,120)!=layout.bios or _call(layout.prior.callback_data,c,138)!=h.helper or facts['calls'][h.helper+266]!=s:
        raise ValueError('actual callback/helper/scheduler call edges differ')
    if owners['identity']!=(h.identity,h.identity_data):raise ValueError('shared actual identity owner differs')
    extra={'bios':(layout.bios,layout.bios_data),'descriptor_helper':(h.helper,h.helper_data),
           'helper_getter':(h.getter,h.getter_data),'helper_coordinates':(h.coordinates,h.coordinates_data)}
    owners.update(extra)
    spans=sorted((p,p+len(b)) for p,b in owners.values())
    if any(x[1]>y[0] for x,y in zip(spans,spans[1:])):raise ValueError('complete bound owners overlap')
    return owners


def bind(prior_layout,helper_layout,bios_address,bios_data,*,selector):
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit084 selector required')
    result=Layout(prior_layout,helper_layout,bios_address,bios_data);_validate(result);return result


def requirements_from_083(layout,arena_base,report,*,selector):
    """Identify the open SVC interface; never supply or infer a poststate."""
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit084 selector required')
    _validate(layout);owners=source083._validate(layout.prior);c=layout.prior.callback
    pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(owners.items())]
    if type(arena_base) is not int or arena_base%4 or not 0<=arena_base<2**32 or type(report) is not dict or \
            report.get('schema')!=source083.SELECTOR or report.get('complete_owner_pins')!=pins or report.get('final_PC')!=layout.bios:
        raise ValueError('exact083 CpuSet-entry report required')
    r,cut=report.get('registers'),report.get('nested_call_cutpoint')
    if type(r) is not dict or set(r)!=set(range(15)) or any(type(k) is not int or not words._word(w) for k,w in r.items()) or \
            type(cut) is not dict or cut.get('call_site')!=c+120 or cut.get('target')!=layout.bios or cut.get('callee_executed') is not False or \
            cut.get('return_word')!=words._constant((c+124)|1) or cut.get('register_arguments')!={i:r[i] for i in range(4)}:
        raise ValueError('actual083 callsite/interface differs')
    src=int.from_bytes(layout.prior.callback_data[152:156],'little');dest=words.observe(r[1]);payload=words.observe(r[6]);sp=words.observe(r[13])
    if r[0]!=words._constant(src) or r[2]!=words._constant(16) or r[14]!=words._constant((c+124)|1) or \
            dest.get('kind')!='base-plus' or payload.get('kind')!='base-plus' or dest['coordinate']!=payload['coordinate']+16 or \
            sp.get('kind')!='base-plus' or cut.get('SP')!=sp['coordinate']:
        raise ValueError('actual32-byte control/source/destination/register origins differ')
    d=arena_base+dest['coordinate']
    if src%2 or d%2 or not 0<=src<=2**32-32 or not 0<=d<=2**32-32:raise ValueError('numeric halfword spans wrap or misalign')
    return dict(schema=SELECTOR+'-open-bios-interface',call_site=c+120,wrapper=layout.bios,
        exact_control=16,width=2,units=16,source_numeric_span=[src,src+32],destination_numeric_span=[d,d+32],
        numeric_overlap=max(src,d)<min(src+32,d+32),required_return_word=words._constant((c+124)|1),
        suffix_entry=layout.bios+2,precall_SP=sp['coordinate'],
        suffix_demand=dict(control=['LR must actually identify callback+124 in Thumb state'],
            address_registers=['actual post-SVC R6 payload base','actual post-SVC SP'],
            transported_origins=['post-SVC R4 into first stack argument','post-SVC R8 into parent stack argument','all actual helper PUSH origins, including R5 and R7'],
            memory=['actual post-SVC payload+72 word','all alias-visible post-SVC saves/locals and fixed scheduler point','actual future allocator/callback memory']),
        poststate=None,BIOS_effects=None,register_preservation=None,
        actual083_reaching_authenticated=False,source_readability_proved=False,destination_writability_proved=False,
        BIOS_copy_proved=False,BIOS_return_proved=False,ABI_preservation_assumed=False,native_admission=False,
        obligations=report.get('obligations',[])+[
            'A separate actual BIOS effect/return relation must connect this prestate to the independently supplied post-SVC state. No copy, register preservation, memory equality or poststate is generated here.',
            'These numeric32-byte spans do not grant physical access, noninterference, nonalias or BIOS instruction semantics.'])


def derive_postsvc(layout,arena_base,cells,registers,*,selector,
           protected_spans=(),retired_stack_spans=(),released_payload_spans=(),literal_points=(),max_steps=4096):
    """Start at the real BX LR using an independently supplied post-SVC state.

    In particular, no083 state is accepted as a BIOS return state merely by
    copying it. Actual post-SVC reaching/effect authority remains external.
    """
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit084 selector required')
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
    trace=[];events=[];stack=[];returns=[];frames=[];freed=list(released_payload_spans)
    pc=layout.bios+2;flags=None;boundary=None;cut=None;entry_sp=None;bios_bx_returned=False
    c,helper_address=layout.prior.callback,layout.helper.helper
    executable=frozenset(('bios','large_callback','descriptor_helper'))
    allowed={'bios':frozenset((2,)),
        'large_callback':frozenset((124,126,128,130,132,134,136,138)),
        'descriptor_helper':frozenset(range(0,22,2))|frozenset(range(30,60,2))|frozenset(range(250,268,2))}
    literals={'large_callback':(156,),'descriptor_helper':(72,76,284,288)}
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
            name='084 local '+str(len(trace))
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
        try:v=numeric(result)
        except removal._Boundary:flags=None;return
        old=flags;flags=(bool(v&0x80000000),v==0,carry if carry is not None else (old[2] if old else None),old[3] if old else None)
    def bitwise(left,right,operation):
        out=[]
        for x,y in zip(left,right):
            if type(x) is int and type(y) is int:out.append(x&y if operation==0 else x|y)
            elif operation==0 and (x==0 or y==0):out.append(0)
            elif operation==0 and x==255:out.append(y)
            elif operation==0 and y==255:out.append(x)
            elif operation==12 and x==0:out.append(y)
            elif operation==12 and y==0:out.append(x)
            elif operation==12 and (x==255 or y==255):out.append(255)
            elif x==y:out.append(x)
            else:stop('partial unknown bit mask is unsupported')
        return tuple(out)
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
        if entry_sp%4:stop('actual post-SVC SP is not aligned')
        for step in range(max_steps):
            found=next(((name,a,b) for name,(a,b) in owners.items() if a<=pc<a+len(b)),None)
            if found is None:stop('control outside complete owners')
            role,p,data=found;off=pc-p
            if role not in executable or off not in allowed[role]:stop('control outside exact post-SVC suffix')
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
                    if role=='bios':
                        if target!=(c+124)|1:stop('actual post-SVC LR does not return to callback suffix',observed_target=target)
                        bios_bx_returned=True;nxt=target&~1
                    else:stop('unsupported actual suffix return',observed_target=target)
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
                elif op in (0,12):
                    r[d]=bitwise(r[d],r[s],op);nz_flags(r[d])
                else:stop('unsupported scalar ALU')
            elif h&0xf800==0x4800:
                at=((pc+4)&~3)+(h&255)*4
                if at-p not in literals.get(role,()):stop('literal outside bound owner pool')
                value=int.from_bytes(data[at-p:at-p+4],'little');r[(h>>8)&7]=words._constant(value)
                events.append(dict(site=pc,operation='read-code-literal',address=at,value=value,grants_access=False))
            elif h&0xe000==0x6000 or h&0xf000==0x8000:
                half=h&0xf000==0x8000;width=2 if half else 1 if h&4096 else 4
                offset=((h>>6)&31)*width;d=h&7;at=address(r[(h>>3)&7])+offset
                if h&2048:r[d]=load(at,width)
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
    return dict(schema=SELECTOR,complete_owner_pins=pins,starts_at=layout.bios+2,trace=trace,final_PC=pc,registers=r,
        post_cells={str(k):v for k,v in sorted(m.items())},changed_cells={str(k):v for k,v in sorted(m.items()) if cells.get(k)!=v},
        memory_events=events,retired_spans=retired,conditional_released_payloads=freed,pending_calls=stack,
        boundary=boundary,nested_call_cutpoint=cut,postsvc_entry_SP=entry_sp,observed_wrapper_BX_return=bios_bx_returned,
        actual_BIOS_effects_executed=False,actual_BIOS_poststate_proved=False,ABI_preservation_assumed=False,
        fabricated_BIOS_copy=False,fabricated_callee_effects=False,actual_reaching_proved=False,
        physical_access_proved=False,actual_heap_lifetime_proved=False,actual_installed_identity_proved=False,
        actual_termination_proved=False,whole_CFG_closed=False,source_or_ELF_admission=False,native_admission=False,
        obligations=[
            'Every input register and byte must be the actual independently established post-SVC state at the wrapper BX LR. This module neither computes nor authenticates that state and does not connect083 across the BIOS.',
            'Actual post-SVC LR, SP, R6, R4 and R8 are observed as supplied. No pre-SVC ABI survival, saved snapshot, unchanged memory or copy32 effect is assumed.',
            'All common-base accesses and frames require live ordinary physical permission, complete protection/alias coverage and synchronous noninterference. Numeric literals do not grant access.',
            'All helper saves/locals and descriptor records share the same bytes. Local allocation retains existing byte origins; only absent bytes become fresh unknown tokens. Executed masks establish only the bits they actually overwrite.',
            'The selected real suffix prepares mode2/tag7, a live pointer to the helper private record and count12/DFF04 descriptor before5954. Synchronous callback, allocation, installation, return and pointer lifetime still require exact composition.',
            'WholeCFG, actual BIOS/heap/SP execution, global termination, Sqrt, native/source admission and publication credit remain unproved.'])
