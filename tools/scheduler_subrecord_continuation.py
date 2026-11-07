"""Conditional actual subrecord conversion and enclosing callback continuation.

Complete conversion loops execute against ordered common bytes. Neither
nominal buffer roles nor returned pointers grant nonaliasing or extents.
"""
from dataclasses import dataclass
import hashlib
import scheduler_buffer_phase256_state as buffer088
words,atoms,removal=buffer088.words,buffer088.atoms,buffer088.removal
_call=buffer088._call
SELECTOR='conditional-subrecord-conversion-continuation-v1'
SHAPES={'subrecord': b'p\xb5\x81\xb0\x05\x1c\x00&\xe8y*hA\x00\t\x18\x89\x00\x89\x18Lh!hhi*\x8a\x90B\x01\xd8(\x82\x01&Jx\x01 \x10@\x00(9\xd0\x08x\x01(\x08\xd1\xa8i)\x8a\xeai#ydy\x00\x94\xff\xf7\xba\xfcY\xe0\x02(\x06\xd1\xa8i)\x8a\xeaicy\xff\xf7\xdb\xfcP\xe0\x03(\x06\xd1\xa8i)\x8a\xeaicy\xff\xf7\xfe\xfcG\xe0\x04(\x06\xd1\xa8i)\x8a\xeaicy\xff\xf71\xfd>\xe0\x08(<\xd1\x02 \x10@\x00(8\xd1\xa8i\xe9i\xeby,hZ\x00\xd2\x18\x92\x00\x12\x19R\x88R\x08j\xf0\xac\xf8+\xe0\x08x\x01(\x06\xd1\xa8i)\x8a\xeai#y\xff\xf7\xe2\xfb!\xe0\x02(\x05\xd1\xa8i)\x8a\xeai\xff\xf7\x16\xfc\x19\xe0\x03(\x05\xd1\xa8i)\x8a\xeai\xff\xf7:\xfc\x11\xe0\x04(\x0f\xd1\x02 \x10@\x00(\x0b\xd1\xa8i\xe9i\xeby,hZ\x00\xd2\x18\x92\x00\x12\x19R\x88R\x08j\xf0\x7f\xf8\x00.\x0c\xd1)\x8a\xa8i@\x18\xa8a\xe8i\x80!\xc9\x00@\x18\xe8a)\x8ahi@\x1aha0\x1c\x01\xb0p\xbc\x02\xbc\x08G', 'byte1': b'\xf0\xb5\x84F\x14\x1c\x05\x98\t\x04\x0e\x0c\x1b\x06\x1b\x0e\x00\x07\x00\x0e\x00"\xb2B\x19\xd2\x01\'\x05\x1c\x1dCaF\x88\x18\x01x\x00 \x012\x0b\x1c;@\x00+\x01\xd0%p\x00\xe0#p\x014I\x08\x010\x00\x04\x00\x0c\x07(\xf1\xd9\x10\x04\x02\x0c\xb2B\xe8\xd3\xf0\xbc\x01\xbc\x00G', 'byte2': b'\xf0\xb5GF\x80\xb4\x80F\x14\x1c\t\x04\x0f\x0c\x1b\x07\x1e\x0e\x00!\xb9B\x1a\xd2\x03 \x84FBFP\x18\x02x\x00#M\x1c\x11\x1c`F\x01@!p\x00)\x02\xd00\x1c\x08C p\x014\x92\x08X\x1c\x00\x04\x03\x0c\x03+\xef\xd9(\x04\x01\x0c\xb9B\xe6\xd3\x08\xbc\x98F\xf0\xbc\x01\xbc\x00G', 'byte3': b'\xf0\xb5WFNFEF\xe0\xb4\x81F\x14\x1c\t\x04\t\x0c\x8aF\x1b\x07\x1e\x0e\x00%UE%\xd2\x07 \x80F\x07!\x8cFOFx\x19\x02xAx\t\x02\nC\x80x\x00\x04\x02C\x00#\x035\x11\x1c@F\x01@!p\x10\x1cgF8@\x00(\x02\xd00\x1c\x08C p\x014\xd2\x08X\x1c\x00\x04\x03\x0c\x07+\xec\xd9(\x04\x05\x0cUE\xdd\xd38\xbc\x98F\xa1F\xaaF\xf0\xbc\x01\xbc\x00G', 'byte4': b'\xf0\xb5GF\x80\xb4\x80F\x14\x1c\t\x04\x0f\x0c\x1b\x07\x1e\x0e\x00!\xb9B\x1a\xd2\x0f \x84FBFP\x18\x02x\x00#M\x1c\x11\x1c`F\x01@!p\x00)\x02\xd00\x1c\x08C p\x014\x12\tX\x1c\x00\x04\x03\x0c\x01+\xef\xd9(\x04\x01\x0c\xb9B\xe6\xd3\x08\xbc\x98F\xf0\xbc\x01\xbc\x00G', 'nibble1': b'\xf0\xb5OFFF\xc0\xb4\x81F\t\x04\t\x0c\x88F\x1b\x06\x1f\x0e8\x07\x00\x0e\x84F\x00!AE%\xd2\x01%KFX\x18\x04x\x00 \x10`\x00#N\x1c \x1c(@\x00(\n\xd0\x18\x1c(@\x00(\x02\xd0\x11x`F\x01\xe0\x11x8\x1c\x08C\x10p\x18\x1c(@\x00(\x00\xd0\x012d\x08X\x1c\x00\x04\x03\x0c\x07+\xe5\xd90\x04\x01\x0cAE\xda\xd3\x18\xbc\x98F\xa1F\xf0\xbc\x01\xbc\x00G', 'nibble2': b"\xf0\xb5\x84F\t\x04\x0e\x0c\x00#\xb3B \xd2\x00'aF\xc8\x18\x01x\x17p\x00$]\x1c\x03#\x0b@\x01  @\x00(\x06\xd0\x1b\x01\x10x\x03C\x13p\x012\x17p\x02\xe0\x10x\x03C\x13p\x89\x08`\x1c\x00\x04\x04\x0c\x03,\xe9\xd9(\x04\x03\x0c\xb3B\xdf\xd3\xf0\xbc\x01\xbc\x00G", 'nibble3': b"\xf0\xb5GF\x80\xb4\x80F\t\x04\x0e\x0c\x00%\xb5B)\xd2\x00'\x07 \x84FAFH\x19\x03xAx\t\x02\x0bC\x80x\x00\x04\x03C\x17p\x00$\x035\x19\x1c`F\x01@\x01  @\x00(\x06\xd0\x08\x01\x11x\x08C\x10p\x012\x17p\x02\xe0\x10x\x01C\x11p\xdb\x08`\x1c\x00\x04\x04\x0c\x07,\xe8\xd9(\x04\x05\x0c\xb5B\xd8\xd3\x08\xbc\x98F\xf0\xbc\x01\xbc\x00G"}
EDGES={64:'byte1',82:'byte2',100:'byte3',118:'byte4',156:'bios',176:'nibble1',192:'nibble2',208:'nibble3',246:'bios'}
@dataclass(frozen=True)
class Layout:
    prior: buffer088.Layout
    dependencies: tuple

def _validate(layout):
    if type(layout) is not Layout or type(layout.dependencies) is not tuple or len(layout.dependencies)!=8:
        raise ValueError('complete089 layout required')
    owners=buffer088._validate(layout.prior);new={}
    for row in layout.dependencies:
        if type(row) is not tuple or len(row)!=3:raise ValueError('complete actual helper tuple required')
        role,a,data=row
        if role not in SHAPES or role in new or type(a) is not int or a%4 or not 0<=a<=2**32-len(SHAPES[role]) or type(data) is not bytes or len(data)!=len(SHAPES[role]):
            raise ValueError('complete aligned actual conversion helper required')
        new[role]=(a,data)
    owners.update(new);a,b=owners['transfer']
    if _call(b,a,86)!=new['subrecord'][0]:raise ValueError('actual transfer/subrecord edge differs')
    for role,(a,data) in new.items():
        expected=bytearray(SHAPES[role])
        if role=='subrecord':
            for off,target in EDGES.items():expected[off:off+4]=removal._bl(a+off,owners[target][0])
        if data!=bytes(expected):raise ValueError('complete '+role+' conversion identity differs')
    spans=sorted((a,a+len(b)) for a,b in owners.values())
    if any(x[1]>y[0] for x,y in zip(spans,spans[1:])):raise ValueError('complete owner spans overlap')
    return owners

def bind(prior_layout,dependencies,*,selector):
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit089 selector required')
    result=Layout(prior_layout,dependencies);_validate(result);return result

def continue_from_088(layout,arena_base,report,*,selector,protected_spans=(),literal_points=(),max_steps=4096):
    """Validate a conditional actual-entry shape without replay/authentication."""
    owners=_validate(layout);old=buffer088._validate(layout.prior)
    pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(old.items())]
    if type(report) is not dict or report.get('schema')!=buffer088.SELECTOR or report.get('complete_owner_pins')!=pins or report.get('final_PC')!=owners['subrecord'][0] or report.get('conditional_callback_return') is not False:
        raise ValueError('exact088 subrecord entry report required')
    r,cut,e,ret=report.get('registers'),report.get('nested_call_cutpoint'),report.get('callback_entry_SP'),report.get('callback_return_word')
    if type(r) is not dict or set(r)!=set(range(15)) or any(not words._word(w) for w in r.values()) or type(e) is not int or not words._word(ret) or words.observe(ret).get('kind')!='constant' or type(cut) is not dict or cut.get('call_site')!=owners['transfer'][0]+86 or cut.get('target')!=owners['subrecord'][0] or cut.get('SP')!=e-40 or cut.get('return_word')!=r[14] or cut.get('register_arguments')!={i:r[i] for i in range(4)} or cut.get('callee_executed') is not False or report.get('pending_calls')!=[dict(role='callback40',return_pc=words.observe(ret)['value']&~1,entry_sp=e),dict(role='transfer',return_pc=owners['callback40'][0]+214,entry_sp=e-28)]:
        raise ValueError('088 actual transfer call/interface differs')
    result=derive(layout,arena_base,{int(k):v for k,v in report['post_cells'].items()},r,selector=selector,callback_entry_sp=e,callback_return_word=ret,protected_spans=protected_spans,retired_stack_spans=tuple(tuple(x) for x in report.get('retired_spans',())),released_payload_spans=tuple(tuple(x) for x in report.get('conditional_released_payloads',())),literal_points=literal_points,max_steps=max_steps)
    result['inherited_088_obligations']=report.get('obligations',[]);result['actual_088_report_authentication_proved']=False
    return result

def derive(layout,arena_base,cells,registers,*,selector,callback_entry_sp,callback_return_word,
           protected_spans=(),retired_stack_spans=(),released_payload_spans=(),literal_points=(),max_steps=4096):
    """Execute actualD7674 from explicit088 cutpoint, with all aliases live."""
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit089 selector required')
    owners=_validate(layout)
    if type(arena_base) is not int or arena_base%4 or not 0<=arena_base<2**32 or type(cells) is not dict or len(cells)>4096 or         any(type(k) is not int or not -(2**31)<=k<2**31 or not atoms._cell(v) for k,v in cells.items()) or         type(registers) is not dict or set(registers)!=set(range(15)) or any(type(k) is not int or not words._word(v) for k,v in registers.items()) or         type(max_steps) is not int or not 1<=max_steps<=4096:
        raise ValueError('bounded common byte/register/numeric witness required')
    for spans in (protected_spans,retired_stack_spans,released_payload_spans):
        if type(spans) is not tuple or len(spans)>128 or any(type(s) is not tuple or len(s)!=2 or
            any(type(v) is not int for v in s) or not -(2**31)<=s[0]<s[1]<=2**31 for s in spans):
            raise ValueError('bounded explicit intervals required')
    if type(literal_points) is not tuple or len(literal_points)>16 or any(type(v) is not int or v%4 or not 0<=v<2**32 for v in literal_points):
        raise ValueError('explicit aligned literal point identities required')
    if type(callback_entry_sp) is not int or callback_entry_sp%4 or not words._word(callback_return_word):raise ValueError('explicit enclosing callback frame/return required')
    r,m=dict(registers),dict(cells);retired=list(retired_stack_spans)+list(released_payload_spans)
    trace=[];events=[];stack=[];returns=[];frames=[];freed=list(released_payload_spans)
    pc=owners['subrecord'][0];flags=None;boundary=None;cut=None
    entry_sp=None;entry_lr=r[14];returned=False
    executable=frozenset(('callback40','transfer','writer','subrecord','byte1','byte2','byte3','byte4','nibble1','nibble2','nibble3','bios'))
    literals={'callback40':(36,64,108,168,172,260,264,268,336),'transfer':(36,40,44,48,52,56,60)}
    allowed={'callback40':frozenset(range(214,258,2))|frozenset((272,274,276,324,326,328,330,332,334)),
             'transfer':frozenset(range(90,98,2))|frozenset(range(124,132,2))|frozenset(range(162,202,2))}
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
            name='089 local '+str(len(trace))
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
        if entry_sp%4 or callback_entry_sp!=entry_sp+40 or r[14]!=words._constant((owners['transfer'][0]+90)|1) or r[0]!=r[4] or r[5]!=words._constant(0):
            stop('subrecord entry differs from actual transfer call/frame interface')
        target=numeric(callback_return_word)
        if not target&1:stop('enclosing callback return word is not Thumb tagged')
        stack=[dict(role='callback40',return_pc=target&~1,entry_sp=callback_entry_sp),dict(role='transfer',return_pc=owners['callback40'][0]+214,entry_sp=entry_sp+12),dict(role='subrecord',return_pc=owners['transfer'][0]+90,entry_sp=entry_sp)]
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
        subrecord_entry_SP=entry_sp,subrecord_return_word=entry_lr,callback_entry_SP=callback_entry_sp,callback_return_word=callback_return_word,
        conditional_callback_return=returned,
        actual_reaching_proved=False,physical_access_proved=False,actual_heap_lifetime_proved=False,
        ABI_preservation_assumed=False,fabricated_callee_effects=False,actual_BIOS_poststate_proved=False,
        actual_termination_proved=False,whole_CFG_closed=False,source_or_ELF_admission=False,native_admission=False,
        obligations=[
            'All supplied088callee-entry registers,bytes,intervals and pending callback/transfer frames must equalactualreachingstate. Reportshape validation is not authentication and no oldproducer is rerun.',
            'Complete290B D7674 selects an actual12Brecord andsubrecord,compares remainingword tostridehalfword,clampsonly when actualconditionholds, andperforms real converter calls orpreciseCpuSetSVC0B cutpoint.',
            'All seven completeconversion bodies execute bytepacking/unpacking,highregistersaves andloopconditions ononeorderedstate. Source/destination/frame aliasing is permittedonly throughactualoperations,not a puretransformation ornonoverlap assumption.',
            'Actual3bitconverters read3sourcebytes periteration evenfor a shorter positivecount. Packed2/3bitconverters also writea trailingzero byte. Nominalcount/outputratio confersno narroweraccessauthority.',
            'Every physical read/write/frame needslive ordinarylittle-endianaccess,completeprotection/lifetimeinputs andsynchronousnoninterference. Unknownbytes do notbecomenumbers andstackreuse doesnot revivefreedpayloads.',
            'Actual returnedwords andSP controlenclosingreturns. A partialchunk advancescurrent sourcebyreloadedstride,destinationby1024 andsubtractsstridefromremaining; aliases areobservedbetweenwrites. A completedchunk continuesthe actualtransfer/writer untilthenext unsupportedcallee.',
            'BIOS,C95A8andotherexternal effects remainunproved. Noactualheap/SP,imageinstallation,wholeCFG,termination,source/ELF/nativeadmission orpublicationcredit isasserted.'])
