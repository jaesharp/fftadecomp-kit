"""Conditional phase256 scheduler removal and allocator byte-state execution.

Complete relocated shapes provide instruction identities, not actual reaching,
physical permission, allocation ownership, callback purity or native admission.
"""
from dataclasses import dataclass
import hashlib
import scheduler_copy_state as words
import scheduler_allocator_state as atoms
import scheduler_helper_root_state as root080
import scheduler_small_entry_state as small078
import allocator_remove_relation as removal
import allocator_insert_relation as insertion
import allocator_search_relation as search

SELECTOR = 'conditional-phase256-list-free-common-bytes-v1'
SHAPES = {'root': root080.ROOT, 'callback': small078.CALLBACK,
          'remove': removal.REMOVE_HEAD + removal._bl(0x08006E1C,0x08006D38) + removal.REMOVE_TAIL,
          'insert': insertion.HEAD + removal._bl(0x08006E3E,0x08006C88) + insertion.MIDDLE + removal._bl(0x08006EB2,0x08006D38) + insertion.TAIL,
          'search': search.SHAPE, 'median': removal.MEDIAN}
SHAPES['query'] = bytes.fromhex('10b5041c002c0dd025f7e4fa002801d0012000e00020002804d0201c25f7aefa002000e0201c10bc02bc0847')
SHAPES['status'] = bytes.fromhex('00b50021808a022800d10121081c02bc0847')
SHAPES['scheduler_remove'] = bytes.fromhex('00b5011c02480068fff7a0fe01bc0047f08f0002')
SHAPES['list_remove'] = bytes.fromhex('f0b587b0061c0f1c6946012008803d1c002d47d02969002907d08868002802d10869002801d0011cf7e70c1c002c00d12c1c221c18322368201c69463cf1b6fcbc4202d10025616804e06568291c002d00d1e568002901d0a0688860a168002901d060684860e168002904d00869a04201d1a06808617068a04201d1a06870600020e060a060606008483168844203d1032001380028fcda081c211c01f016fc002db7d107b0f0bc01bc004750ba0202')
SHAPES['free_wrapper'] = bytes.fromhex('00b50c39fff72aff01bc0047')
SHAPES['free'] = bytes.fromhex('f0b54f464646c0b4061c0d1ca846a979e879000208430338a871000ae8717020287173206871014a03e0000070730000251c2978687800020843002802d08000311800e000210c1c002c05d021796079000208439042ebd0454503d0301c291cfff7b8fe01488146ff2720e070730000444503d0301c211cfff7acfea879e979090201430331a279e0790002104309180904080c3840a871090ee971a078e17809020143081c3840a870090ae970a978e87800020843002802d08000311800e000210c1c002c0fd021796079000208434845cdd0002d03d0a81b8003000c00e000202070000a6070301c291cfff7b6fe18bc9846a146f0bc01bc0047')
SHAPES['thunk'] = bytes.fromhex('1847')
SHAPES['next'] = bytes.fromhex('f0b587b0061c1f1c09060c0e1206150ed5f774fe000600280ed168468482c58201960297034854216a460c9b07f772fe03e0000099db0f08002007b0f0bc02bc0847')

# A None edge is an authenticated but unsupported target, never an effect.
EDGES = {'root': {80:None,92:None,100:'query',120:'next',174:None,194:None,206:None},
 'query':{8:'status',28:'scheduler_remove'},'scheduler_remove':{8:'list_remove'},
 'list_remove':{60:'thunk',156:'free_wrapper'},'free_wrapper':{4:'free'},
 'free':{96:'remove',120:'remove',236:'insert'},'remove':{124:'median'},
 'insert':{22:'search',138:'median'},'callback':{56:None,84:None,108:None},'next':{16:None,44:None}}
LITERALS = {'root':(48,88,188),'scheduler_remove':(16,),'list_remove':(172,),
            'free':(44,108),'next':(52,)}
ROOT_SITES = frozenset(range(0,20,2)) | frozenset((98,100,104,106,108,110,112,114,116,118,120,220,222,224,226,228))
CALLBACK_SITES = frozenset((0,2,4,6,8,10,12,128,130,132,134))

@dataclass(frozen=True)
class Layout:
    # Ordered tuples prevent silently duplicated role/address keys.
    owners: tuple


def _call(data,address,offset):
    a=int.from_bytes(data[offset:offset+2],'little');b=int.from_bytes(data[offset+2:offset+4],'little')
    if a&0xf800!=0xf000 or b&0xf800!=0xf800:raise ValueError('expected complete Thumb BL')
    hi=(a&2047)<<12
    if hi&0x400000:hi-=0x800000
    return address+offset+4+hi+((b&2047)<<1)


def _validate(layout):
    if type(layout) is not Layout or type(layout.owners) is not tuple or len(layout.owners)!=len(SHAPES):
        raise ValueError('complete distinct owner roles required')
    roles={}
    for item in layout.owners:
        if type(item) is not tuple or len(item)!=3:raise ValueError('owner record required')
        role,address,data=item
        if type(role) is not str or role not in SHAPES or role in roles or type(address) is not int or address%4 or             not 0<=address<=2**32-len(SHAPES[role]) or type(data) is not bytes or len(data)!=len(SHAPES[role]):
            raise ValueError('complete aligned owner shape required')
        roles[role]=(address,data)
    spans=sorted((a,a+len(b)) for a,b in roles.values())
    if any(a[1]>b[0] for a,b in zip(spans,spans[1:])):raise ValueError('complete owners overlap')
    for role,(a,b) in roles.items():
        want=bytearray(SHAPES[role])
        for off,target_role in EDGES.get(role,{}).items():
            target=_call(b,a,off)
            if not 0<=target<2**32 or target%2 or target_role is not None and target!=roles[target_role][0]:
                raise ValueError('exact nested target differs')
            want[off:off+4]=removal._bl(a+off,target)
        for off in LITERALS.get(role,()):want[off:off+4]=b[off:off+4]
        # Numeric magic0x7370 is algorithmic, not a relocatable identity.
        if role=='free' and any(b[o:o+4]!=(0x7370).to_bytes(4,'little') for o in (44,108)):
            raise ValueError('allocator free marker changed')
        if bytes(want)!=b:raise ValueError('complete owner instruction shape differs: '+role)
    return roles


def bind(owners,*,selector):
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit081 selector required')
    result=Layout(owners);_validate(result);return result


def derive(layout,arena_base,cells,registers,*,selector,protected_spans=(),retired_spans=(),
           release_spans=(),literal_points=(),max_steps=4096):
    """Execute one conditional root entry. release_spans are explicit premises.

    (node, end) gives the externally justified payload lifetime interval for a
    successful free. The machine's byte effects do not establish that interval.
    literal_points grant numeric provenance only, never memory accessibility.
    """
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit081 selector required')
    owners=_validate(layout)
    if type(arena_base) is not int or arena_base%4 or not 0<=arena_base<2**32 or type(cells) is not dict or len(cells)>4096 or         any(type(k) is not int or not -(2**31)<=k<2**31 or not atoms._cell(v) for k,v in cells.items()) or         type(registers) is not dict or set(registers)!=set(range(15)) or any(type(k) is not int or not words._word(v) for k,v in registers.items()) or         type(max_steps) is not int or not 1<=max_steps<=4096:
        raise ValueError('bounded common byte/register/numeric witness required')
    for spans in (protected_spans,retired_spans,release_spans):
        if type(spans) is not tuple or len(spans)>128 or any(type(s) is not tuple or len(s)!=2 or
            any(type(v) is not int for v in s) or not -(2**31)<=s[0]<s[1]<=2**31 for s in spans):
            raise ValueError('bounded explicit intervals required')
    if len({s[0] for s in release_spans})!=len(release_spans):raise ValueError('unique payload release intervals required')
    if type(literal_points) is not tuple or len(literal_points)>16 or any(type(v) is not int or v%4 or not 0<=v<2**32 for v in literal_points):
        raise ValueError('explicit fixed literal point identities required')
    r,m=dict(registers),dict(cells);retired=list(retired_spans);trace=[];events=[];stack=[];returns=[]
    pc=owners['root'][0];flags=None;boundary=None;root_return=False;freed=[];frames=[]
    entry_lr=r[14];entry_sp=None;active_role=None
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
        if any(lo<b and hi>a for a,b in (*freed,*retired_spans)):stop('stack allocation intersects externally retired payload/frame',lo)
        retired=[piece for a,b in retired for piece in ((a,min(b,lo)),(max(a,hi),b)) if piece[0]<piece[1]]
        if forget:
            if len(set(m)|set(range(lo,hi)))>4096:stop('local byte state exceeds4096 cells',lo)
            used={v[1] for v in [*m.values(),*(v for w in r.values() for v in w)] if type(v) is tuple and v[0]=='opaque-byte'}
            name='081 local '+str(len(trace))
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
        if role=='free':record['node']=address(r[1])+12
        stack.append(record)
    try:
        entry_sp=address(r[13]);physical(entry_sp,0)
        for step in range(max_steps):
            found=next(((name,a,b) for name,(a,b) in owners.items() if a<=pc<a+len(b)),None)
            if found is None:stop('control outside complete owners')
            role,a,data=found;active_role=role;off=pc-a;trace.append(pc)
            if off%2 or any(o<=off<o+4 for o in LITERALS.get(role,())):stop('control reaches literal or noninstruction')
            if role=='root' and off not in ROOT_SITES:stop('unsupported root phase or continuation')
            if role=='callback' and off not in CALLBACK_SITES:stop('unsupported observed callback phase')
            if role=='next':stop('next source helper entry requires independent closure',target=pc)
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
                    if role=='thunk':
                        if target!=owners['callback'][0]|1:stop('unsupported actual callback identity',target=target)
                        nxt=target&~1
                    elif stack:
                        rec=stack[-1]
                        if target!=(rec['return_pc']|1) or address(r[13])!=rec['entry_sp']:
                            stop('actual saved return word or restored SP differs',observed_target=target)
                        if rec['role']=='free':
                            node=rec['node'];span=next((s for s in release_spans if s[0]==node),None)
                            if span is None:stop('payload release extent/lifetime premise missing',node)
                            physical(span[0],span[1]-span[0])
                            if any(span[0]<hi and span[1]>lo for lo,hi in protected_spans):
                                stop('payload release intersects protected bytes',node)
                            if any(arena_base+span[0]<a+len(b) and arena_base+span[1]>a for a,b in owners.values()):
                                stop('payload release intersects immutable owner',node)
                            freed.append(span);retire(*span,kind='payload-conditional')
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
                if value in literal_points:r[(h>>8)&7]=words._pointer(value-arena_base)
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
        actual_reaching_proved=False,physical_access_proved=False,actual_heap_lifetime_proved=False,
        actual_termination_proved=False,whole_CFG_closed=False,native_admission=False,
        obligations=[
            'Every register, byte, owner identity and common-base relation must match the actual reaching state.',
            'All reads/writes and stack ranges require ordinary live physical permission, alignment and synchronous noninterference; literal_points grant no extent or access.',
            'release_spans are explicit external allocation/lifetime premises; free marker/list effects never establish ownership, extent, deallocation authority or freshness.',
            'All aliases must inhabit this one byte state. Actual POP reads and stale pointer origins remain observable after stores and lifetime transitions.',
            'Only observed phase256 root and phase1 callback paths are admitted. Other phases, source helpers, bad flags/control words, missing bytes and finite budget exhaustion retain exact boundaries.',
            'Conditional returns are instruction relations under these premises, not actual execution, termination, installed code, fullCFG or native credit.'])
