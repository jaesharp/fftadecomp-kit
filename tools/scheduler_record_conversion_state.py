"""Conditional complete record conversion, tile writer and packed reader.

All nested instructions and caller continuation share ordered byte origins.
Seven-way dispatch requires the actual guard, table index and loaded target.
"""
from dataclasses import dataclass
import hashlib
import scheduler_buffer_release_state as release091
words,atoms,removal=release091.words,release091.atoms,release091.removal
_call=release091._call
SELECTOR='conditional-record-conversion-common-bytes-v1'
SHAPES={'conversion': b'\xf0\xb5WFNFEF\xe0\xb4\x88\xb0\x07\x90\x0f\x1c\x12\x04\x12\x0c\x91F\x1b\x06\x1b\x0e\x9aF8y\x018\x06(\x00\xd9P\xe1\x80\x00\x01I@\x18\x00h\x87Fhj\r\x08\x84j\r\x08\xb4j\r\x08\xf8j\r\x08<k\r\x08\x90k\r\x08\xe8k\r\x08Hl\r\x08\xbb\x1d8x\x00\x90xx\x01\x90HF\x02\x90PF\x03\x90\x00 \x04\x90\x05\x90yy\x02 \x08@\x00\x06\x00\x0e\x06\x90\x07\x98\x00!\x00"\xff\xf7s\xfe#\xe1\x00$\xb8\x1d\x80F!\x04\t\x148x\x00\x90xx\x01\x90HF\x02\x90PF\x03\x90\x00 \x04\x90\x05\x90zy\x02 \x10@\x00\x06\x00\x0e\x06\x90\x07\x98\x00"CF\xff\xf7W\xfe8x \x18\x00\x04\x04\x0c\x1f,\xe1\xd9\x01\xe1\x00$\xb8\x1d\x80F"\x04\x12\x148x\x00\x90xx\x01\x90HF\x02\x90PF\x03\x90\x00 \x04\x90\x05\x90yy\x02 \x08@\x00\x06\x00\x0e\x06\x90\x07\x98\x00!CF\xff\xf75\xfexx \x18\x00\x04\x04\x0c\x1f,\xe1\xd9\xdf\xe0\x00%\xb8\x1d\x80F\x00$.\x04!\x04\t\x148x\x00\x90xx\x01\x90HF\x02\x90PF\x03\x90\x00 \x04\x90\x05\x90zy\x02 \x10@\x00\x06\x00\x0e\x06\x90\x07\x982\x14CF\xff\xf7\x11\xfe8x \x18\x00\x04\x04\x0c\x1f,\xe1\xd9xx(\x18\x00\x04\x05\x0c\x1f-\xd9\xd9\xb5\xe0\xbe\x1d8x\x00\x90xx\x01\x90HF\x02\x90PF\x03\x90\x00%\x04\x95\x05\x95yy\x02$ \x1c\x08@\x00\x06\x00\x0e\x06\x90\x07\x98\x00!\x00"3\x1c\xff\xf7\xeb\xfd9x\x00\x91xx\x01\x90HF\x02\x90PF\x03\x90\x01 \x04\x90\x05\x95xy\x04@$\x06$\x0e\x06\x94\x07\x98\x00"+\xe0\xbe\x1d8x\x00\x90xx\x01\x90HF\x02\x90PF\x03\x90\x00%\x04\x95\x05\x95yy\x02$ \x1c\x08@\x00\x06\x00\x0e\x06\x90\x07\x98\x00!\x00"3\x1c\xff\xf7\xbf\xfdzx8x\x00\x90xx\x01\x90HF\x02\x90PF\x03\x90\x04\x95\x01 \x05\x90xy\x04@$\x06$\x0e\x06\x94\x07\x98\x00!3\x1c\xff\xf7\xa9\xfdY\xe0\xb8\x1d\x80F8x\x00\x90xx\x01\x90HF\x02\x90PF\x03\x90\x00%\x04\x95\x05\x95yy\x02$ \x1c\x08@\x00\x06\x00\x0e\x06\x90\x07\x98\x00!\x00"CF\xff\xf7\x8e\xfd9x\x00\x91xx\x01\x90HF\x02\x90PF\x03\x90\x01&\x04\x96\x05\x95zy \x1c\x10@\x00\x06\x00\x0e\x06\x90\x07\x98\x00"CF\xff\xf7x\xfdzx8x\x00\x90xx\x01\x90HF\x02\x90PF\x03\x90\x04\x95\x05\x96yy \x1c\x08@\x00\x06\x00\x0e\x06\x90\x07\x98\x00!CF\xff\xf7b\xfd9xzx\x00\x91xx\x01\x90HF\x02\x90PF\x03\x90\x04\x96\x05\x96xy\x04@$\x06$\x0e\x06\x94\x07\x98CF\xff\xf7N\xfd\x08\xb08\xbc\x98F\xa1F\xaaF\xf0\xbc\x01\xbc\x00G', 'tile_writer': b'\xf0\xb5WFNFEF\xe0\xb4\x92\xb0\x02\x90\x01\x93\x1a\x98\x1b\x9b\x1c\x9c\x1d\x9d\x1e\x9e\xb1F\x1f\x9e \x9f\xb8F\t\x04\t\x0c\x03\x91\x12\x04\x12\x0c\x04\x92\x00\x06\x00\x0e\x05\x90\x1b\x06\x1b\x0e\x06\x93$\x04$\x0c\x07\x94-\x06-\x0e\x08\x95HF\x00\x06\x81F6\x066\x0eAF\t\x06\t\x0e\t\x91\x00!hF\x01\x80\x00"\n\x92\x01\'\x0b\x97\x01 \x0c\x90IF\x00)\x0b\xd0\x80"\xd2\x00\n\x923O\x0b\x97\x05\x99\xc8\x19\x03\x9a\x10\x18\x00\x04\x00\x0c\x03\x90\x00.\x0e\xd0\x80&6\x010\x1c\n\x9f\x07C\n\x97*H\x0c\x90\x06\x99\x08\x18\x04\x9a\x10\x18\x00\x04\x00\x0c\x04\x90\x00#\x00!\x06\x9e\xb3Bx\xd2\x04\x9f8\x04\x00\x14\n\x04\x11\x14@\x18\x00\x04\x00\x14\x0f\x92\x013\x0e\x93\x0c\x99\t\x04\x10\x91\x00([\xdb\x1f(Y\xdc\x80\x01\x02\x9a\x10\x18\r\x90\x00%\x00!\x05\x9e\xb5BP\xd2\x03\x9f8\x04\x00\x14\x82F\x15H\x81F\t\x04\x08\x14PD\x00\x04\x00\x14\x88F\x00(4\xdb\x1f(2\xdc@\x00\r\x99\x08\x18\x11\x90\x01\xa8iF\t\x9a\xff\xf7\xc4\xfe\x00\x04\x02\x0c\x07\x9e\x00.\x02\xd1\x08\x9f\x00/\x1d\xd0\x07\x99\x08\x04\x06\x14\x08\x9c\x13\x1cOF;@KE\x06\xd1\x10\x1c\x10\xe0\x00\x00\xff\xff\x00\x00\xff\x03\x00\x00\x10\x0b\xc0\'?\x019\x1c\n@\x99\x19\t\x04\x00\x19\x00\x07\x08C\x00\x0c\x10C\x00\x04\x02\x0c\n\x98B@\x11\x99\n\x80h\x1c\x00\x06\x05\x0eBF\x11\x14\x0b\x9e0\x04\x00\x14\t\x18\t\x04\t\x0c\x05\x9f\xbdB\xb4\xd3\x0e\x99\x08\x06\x03\x0e\x0f\x9a\x10\x14\x10\x9e1\x14@\x18\x00\x04\x01\x0c\x06\x9f\xbbB\x86\xd3\x12\xb08\xbc\x98F\xa1F\xaaF\xf0\xbc\x01\xbc\x00G', 'value_reader': b'\xf0\xb5\x07\x1c\r\x1c\x12\x06\x00*G\xd0:h\x11xPx\x03\x02\x0bC\x0cI\x08\x1c\x1e\x1c\x06@\x00 \x84F\x80 \x00\x02\x01\x1c\x18\x1c\x08@\x14\x1c\x00(\x0c\xd0\x01!\x8cF\xa0x\xe1x\t\x02\x01C(\x88A\x18\t\x04\x0b\x0c\x17\xe0\xff?\x00\x00\x80!\xc9\x01\x08\x1c\x03@\x00+\x07\xd0\x02 \x84F\xa1x\xe0x\x03\x02\x0bC(\x88\x07\xe0*\x88P\x00 \x18\x81x\xc0x\x03\x02\x0bC\x10\x1c\x010(\x80\x00\x04\x00\x0c\xb0B\x12\xd1aF\x00)\x01\xd0 \x1d\x02\xe0\xa0\x1cq\x00@\x188`\x00 (\x80\x06\xe0:h)\x88H\x00\x80\x18\x03\x88\x011)\x80\x18\x1c\xf0\xbc\x02\xbc\x08G'}
CALL_OFFSETS=(122, 178, 246, 318, 394, 482, 526, 580, 624, 668, 708)
TABLE_OFFSETS=(80, 128, 196, 264, 348, 436, 532)
# An explicit private relation bound; no native budget or default policy changes.
MAX_STEPS=262144
@dataclass(frozen=True)
class Layout:
    prior: release091.Layout
    dependencies: tuple

def _validate(layout):
    if type(layout) is not Layout or type(layout.dependencies) is not tuple or len(layout.dependencies)!=3:
        raise ValueError('complete092 layout required')
    owners=release091._validate(layout.prior);new={}
    for row in layout.dependencies:
        if type(row) is not tuple or len(row)!=3:raise ValueError('complete actual helper tuple required')
        role,a,data=row
        if role not in SHAPES or role in new or type(a) is not int or a%4 or not 0<=a<=2**32-len(SHAPES[role]) or type(data) is not bytes or len(data)!=len(SHAPES[role]):
            raise ValueError('complete aligned conversion helper required')
        new[role]=(a,data)
    owners.update(new);a,b=owners['transfer']
    if _call(b,a,120)!=new['conversion'][0]:raise ValueError('actual transfer/conversion edge differs')
    for role,(a,data) in new.items():
        expected=bytearray(SHAPES[role])
        if role=='conversion':
            expected[48:52]=(a+52).to_bytes(4,'little')
            for i,o in enumerate(TABLE_OFFSETS):expected[52+4*i:56+4*i]=(a+o).to_bytes(4,'little')
            for off in CALL_OFFSETS:expected[off:off+4]=removal._bl(a+off,new['tile_writer'][0])
        elif role=='tile_writer':expected[280:284]=removal._bl(a+280,new['value_reader'][0])
        if data!=bytes(expected):raise ValueError('complete '+role+' identity or guarded table differs')
    spans=sorted((a,a+len(b)) for a,b in owners.values())
    if any(x[1]>y[0] for x,y in zip(spans,spans[1:])):raise ValueError('complete owner spans overlap')
    return owners

def bind(prior_layout,dependencies,*,selector):
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit092 selector required')
    result=Layout(prior_layout,dependencies);_validate(result);return result

def continue_from_088(layout,arena_base,report,*,selector,protected_spans=(),literal_points=(),max_steps=4096):
    """Conditional exact callee entry transport; no old producer execution."""
    owners=_validate(layout)
    buffer088=release091.queue090.subrecord089.buffer088
    old=buffer088._validate(layout.prior.prior.prior.prior)
    pins=[dict(role=n,address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for n,(a,b) in sorted(old.items())]
    if type(report) is not dict or report.get('schema')!=buffer088.SELECTOR or report.get('complete_owner_pins')!=pins or report.get('final_PC')!=owners['conversion'][0] or report.get('conditional_callback_return') is not False:
        raise ValueError('exact088 conversion entry report required')
    r,cut,e,ret=report.get('registers'),report.get('nested_call_cutpoint'),report.get('callback_entry_SP'),report.get('callback_return_word')
    if type(r) is not dict or set(r)!=set(range(15)) or any(not words._word(w) for w in r.values()) or type(e) is not int or not words._word(ret) or words.observe(ret).get('kind')!='constant' or type(cut) is not dict or cut.get('call_site')!=owners['transfer'][0]+120 or cut.get('target')!=owners['conversion'][0] or cut.get('SP')!=e-40 or cut.get('return_word')!=r[14] or cut.get('register_arguments')!={i:r[i] for i in range(4)} or cut.get('callee_executed') is not False or report.get('pending_calls')!=[dict(role='callback40',return_pc=words.observe(ret)['value']&~1,entry_sp=e),dict(role='transfer',return_pc=owners['callback40'][0]+214,entry_sp=e-28)]:
        raise ValueError('088 actual transfer call/interface differs')
    result=derive(layout,arena_base,{int(k):v for k,v in report['post_cells'].items()},r,selector=selector,callback_entry_sp=e,callback_return_word=ret,protected_spans=protected_spans,retired_stack_spans=tuple(tuple(x) for x in report.get('retired_spans',())),released_payload_spans=tuple(tuple(x) for x in report.get('conditional_released_payloads',())),literal_points=literal_points,max_steps=max_steps)
    result['inherited_088_obligations']=report.get('obligations',[]);result['actual_088_report_authentication_proved']=False
    return result

def derive(layout,arena_base,cells,registers,*,selector,callback_entry_sp,callback_return_word,
           protected_spans=(),retired_stack_spans=(),released_payload_spans=(),literal_points=(),max_steps=4096):
    """Execute actual type4 conversion entry through supported caller returns."""
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit092 selector required')
    owners=_validate(layout)
    if type(arena_base) is not int or arena_base%4 or not 0<=arena_base<2**32 or type(cells) is not dict or len(cells)>4096 or         any(type(k) is not int or not -(2**31)<=k<2**31 or not atoms._cell(v) for k,v in cells.items()) or         type(registers) is not dict or set(registers)!=set(range(15)) or any(type(k) is not int or not words._word(v) for k,v in registers.items()) or         type(max_steps) is not int or not 1<=max_steps<=MAX_STEPS:
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
    pc=owners['conversion'][0];flags=None;boundary=None;cut=None
    entry_sp=None;entry_lr=r[14];returned=False
    switch_observation=None;switch_load=None;switch_events=[]
    executable=frozenset(('callback40','transfer','writer','query','ring','payload','enqueue','conversion','tile_writer','value_reader'))
    literals={'callback40':(36,68,108,168,172,260,264,268,336),'transfer':(36,40,44,48,52,56,60),'query':(16,20),'ring':(52,56,60),'enqueue':(44,),
              'conversion':(48,52,56,60,64,68,72,76),'tile_writer':(324,328),'value_reader':(72,)}
    allowed={'callback40':frozenset(range(214,258,2))|frozenset((272,274,276,324,326,328,330,332,334)),
             'transfer':frozenset(range(124,132,2))|frozenset(range(162,202,2)),
             'enqueue':frozenset(range(0,42,2))|frozenset(range(48,68,2))}
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
            name='092 local '+str(len(trace))
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
        if entry_sp%4 or callback_entry_sp!=entry_sp+40 or r[14]!=words._constant((owners['transfer'][0]+124)|1) or r[5]!=words._constant(0):
            stop('conversion entry differs from actual transfer call/frame interface')
        target=numeric(callback_return_word)
        if not target&1:stop('enclosing callback return word is not Thumb tagged')
        stack=[dict(role='callback40',return_pc=target&~1,entry_sp=callback_entry_sp),dict(role='transfer',return_pc=owners['callback40'][0]+214,entry_sp=entry_sp+12),dict(role='conversion',return_pc=owners['transfer'][0]+124,entry_sp=entry_sp)]
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
                if rd==15 or rs==15:
                    if role!='conversion' or off!=46 or h!=0x4687 or switch_load is None or r[0]!=words._constant(switch_load['target']):
                        stop('unsupported or unjustified PC register operation')
                    nxt=switch_load['target'];switch_events.append(dict(site=pc,**switch_load));switch_load=None;pc=nxt;continue
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
                    if role=='conversion' and off==32:
                        switch_observation=numeric(r[0]);switch_load=None
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
                if role=='conversion' and off==44 and h==0x6800:
                    table_address=numeric(r[0])
                    if switch_observation is None or not 0<=switch_observation<7 or table_address!=p+52+4*switch_observation or p+34 not in trace:
                        stop('table load lacks actual bounded guard/index correlation')
                    target=int.from_bytes(data[52+4*switch_observation:56+4*switch_observation],'little')
                    if target!=p+TABLE_OFFSETS[switch_observation] or target-p not in starts[role]:stop('table target is not a validated instruction boundary')
                    switch_load=dict(index=switch_observation,address=table_address,target=target);r[0]=words._constant(target)
                    events.append(dict(site=pc,operation='read-guarded-code-table',**switch_load,grants_access=False));pc=nxt;continue
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
        conversion_entry_SP=entry_sp,conversion_return_word=entry_lr,callback_entry_SP=callback_entry_sp,callback_return_word=callback_return_word,
        conditional_callback_return=returned,guarded_switch_events=switch_events,
        actual_reaching_proved=False,physical_access_proved=False,actual_heap_lifetime_proved=False,
        ABI_preservation_assumed=False,fabricated_callee_effects=False,actual_BIOS_poststate_proved=False,
        actual_termination_proved=False,whole_CFG_closed=False,source_or_ELF_admission=False,native_admission=False,
        actual_device_transfer_proved=False,actual_DMA_completion_proved=False,queued_buffer_lifetime_proved=False,
        obligations=[
            'All supplied088 type4 helper-entry registers, bytes, pending callback/transfer frames and intervals must equal actual reaching state. Transport validation is not authentication and no old producer is rerun.',
            'Complete728B conversion,438B tile writer and178B packed reader execute actual nested instructions. Seven-way dispatch is tied to actual subtract/compare/branch, exact table address and selected target; no accepted-address whitelist supplies control.',
            'Actual width/height/mode/flags reloads, signed clipping, mirror coordinates, tile/palette arithmetic, compressed run state and source pointer/counter updates share one ordered byte state. Clipped coordinates skip the actual reader call; no nominal-width source consumption is assumed.',
            'Record/output/frame overlap is permitted only through actual operations. All saved high registers, seven incoming stack words, packed pointer slots and local counters retain byte origins and lifetime checks. Unknown data never becomes initialized scalar data.',
            'Every physical read/write/frame requires live ordinary little-endian access, full protection/lifetime inputs and synchronous noninterference. Exact numeric points do not grant neighboring extents or permission.',
            'After actual conversion return, transfer/writer/query/ring/RAM enqueue execute where supported. This establishes neither hardware transfer nor source readiness, device completion or queued buffer lifetime.',
            'The private relation accepts an explicit bound up to262144 instructions so complete32x32 clipped grid cases can be tested; default4096 remains. No native budget or existing policy changes. Zero-stride and alias-driven loops may exhaust the bound; global termination is not asserted.',
            'Actual heap/SP, physical permissions, installed image, whole CFG, BIOS/device effects and source/ELF/native admission remain unproved.'])
