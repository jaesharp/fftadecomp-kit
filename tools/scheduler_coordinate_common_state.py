"""Conditional C918 output effects and actual shared-state continuations.

Fresh literal reads, output stores and real POPs share one byte arena. The
motion equality branch closes its actual return; other paths retain exact
callee-entry cutpoints. No callee outcome or output initialization is supplied.
"""
from dataclasses import dataclass
import hashlib

import scheduler_helper_common_state as prior
import scheduler_copy_state as words
import scheduler_allocator_state as atoms
import scheduler_callback_zero_phase as shapes

SELECTOR='conditional-scheduler-coordinate-common-byte-state-v1'
TRANSFORM=bytes.fromhex('f0b5474680b4069ca046079f0004001412041214841a64101c800a4e358c64191c808018821009044914521a41460a80718c521844462280388008bc9846f0bc01bc0047407f0002')
PREDICATE=bytes.fromhex('00b581b0000400140904091404220092102343f72bf80004000c4042c00f01b002bc0847')
MOTION=bytes.fromhex('f0b557464e464546e0b484b00c9c000409040e0c1206120e01921b061b0e02932406240e0394094f3a1c343a010c8a4600142423d15e88420ad1300400142623d15e884204d1002050e00000747f00022a488146808c51460c042414201a4a46d18c35042d14691a00040014031c4343181c090409140a1c4a43111c4018000225f140fe0004030d9846002251467980be80391c60316b461b790b7001316e46367a0e7001316b461b7b0b7001316e4636790e70400d7866381c6830027060384a462423d15e464600960022231cebf7b3fc381c34304a462623d15e009600222b1cebf7a9fc01203870787004b038bc9846a146aa46f0bc02bc0847407f0002')


@dataclass(frozen=True)
class Layout:
    helper: prior.Layout
    transform: int
    transform_data: bytes
    predicate: int
    predicate_data: bytes
    motion: int
    motion_data: bytes


def _validate(layout):
    if type(layout) is not Layout:raise ValueError('retained helper and complete continuation owners required')
    facts=prior._validate(layout.helper)
    old=layout.helper
    spans=[(old.helper,292),(old.getter,12),(old.identity,2),(old.coordinates,40)]
    for a,b,n in [(layout.transform,layout.transform_data,72),(layout.predicate,layout.predicate_data,36),
                  (layout.motion,layout.motion_data,256)]:
        if type(a) is not int or a%4 or not 0<=a<=2**32-n or type(b) is not bytes or len(b)!=n:
            raise ValueError('complete aligned72/36/256B continuation owners required')
        if any(a<s+length and a+n>s for s,length in spans):raise ValueError('complete continuation owners overlap')
        spans.append((a,n))
    t,p,m=layout.transform,layout.predicate,layout.motion
    point=int.from_bytes(layout.transform_data[68:72],'little')
    motion_point=int.from_bytes(layout.motion_data[252:256],'little')
    if point%4 or point>2**32-40 or motion_point%4 or motion_point>2**32-56:
        raise ValueError('nonwrapping aligned literal points required')
    if layout.transform_data!=TRANSFORM[:68]+point.to_bytes(4,'little') or \
            facts['calls'][old.coordinates+28]!=t or facts['calls'][old.helper+214]!=p:
        raise ValueError('C918 complete body or real continuation call identity differs')
    if layout.predicate_data!=PREDICATE[:18]+atoms.remove._bl(p+18,m)+PREDICATE[22:]:
        raise ValueError('complete predicate body/call identity differs')
    expected=bytearray(MOTION)
    expected[76:80]=(motion_point+52).to_bytes(4,'little')
    expected[252:256]=motion_point.to_bytes(4,'little')
    calls={}
    for offset in (128,206,226):
        target=shapes._call(layout.motion_data,m,offset)
        if target is None or target%2 or not 0<=target<2**32 or any(s<=target<s+n for s,n in spans):
            raise ValueError('unsupported motion call must retain a separate Thumb target')
        expected[offset:offset+4]=atoms.remove._bl(m+offset,target);calls[m+offset]=target
    if layout.motion_data!=bytes(expected):raise ValueError('complete motion body/literals/calls differ')
    return dict(prior=facts,point=point,motion_point=motion_point,calls=calls)


def bind(helper_layout,transform_data,transform_address,predicate_data,predicate_address,
         motion_data,motion_address,*,selector):
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit coordinate continuation selector required')
    result=Layout(helper_layout,transform_address,transform_data,predicate_address,predicate_data,motion_address,motion_data)
    _validate(result);return result


def continue_from_075(layout,arena_base,report,*,selector,protected_spans=()):
    """Consume one075 cutpoint report without invoking075 again.

Report shape/context checks do not authenticate an actual reaching state.
They prevent accidental mixing of conditional owners, sites and registers.
"""
    _validate(layout);old=layout.helper
    if type(report) is not dict or report.get('schema')!=prior.SELECTOR or \
            not report.get('reaches_explicit_nested_call') or report.get('observed_dispatch')!=0:
        raise ValueError('actual075 table-case0 cutpoint report required')
    cut=report.get('nested_call_cutpoint')
    expected=[dict(address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for a,b in
              [(old.helper,old.helper_data),(old.getter,old.getter_data),(old.identity,old.identity_data),(old.coordinates,old.coordinates_data)]]
    if report.get('complete_owner_pins')!=expected or type(cut) is not dict or \
            cut.get('call_site')!=old.coordinates+28 or cut.get('target')!=layout.transform or \
            report.get('boundary',{}).get('site')!=layout.transform or cut.get('callee_executed') is not False:
        raise ValueError('075 code context or exact unexecuted C918 entry differs')
    r=report['registers']
    if cut.get('return_word')!=r[14] or cut.get('register_arguments')!={i:r[i] for i in range(4)} or \
            r[13]!=words._pointer(cut['SP']):raise ValueError('075 actual cutpoint registers disagree')
    return derive(layout,arena_base,{int(k):v for k,v in report['post_cells'].items()},r,
                  helper_entry_sp=report['entry_SP'],selector=selector,protected_spans=protected_spans,
                  retired_spans=tuple(tuple(span) for span in report['retired_spans']))


def derive(layout,arena_base,cells,registers,*,helper_entry_sp,selector,protected_spans=(),retired_spans=()):
    """Execute a NEW conditional C918-entry state; no synthetic callee result."""
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit coordinate continuation selector required')
    facts=_validate(layout)
    if type(arena_base) is not int or arena_base%4 or not 0<=arena_base<2**32 or \
            type(helper_entry_sp) is not int or helper_entry_sp%4 or not -(2**31)<=helper_entry_sp<2**31 or \
            type(registers) is not dict or set(registers)!=set(range(15)) or any(type(k) is not int or not words._word(v) for k,v in registers.items()) or \
            type(cells) is not dict or len(cells)>4096 or any(type(k) is not int or not -(2**31)<=k<2**31 or not atoms._cell(v) for k,v in cells.items()):
        raise ValueError('bounded exact entry origins and numeric common-base state required')
    for spans in (protected_spans,retired_spans):
        if type(spans) is not tuple or len(spans)>40 or any(type(s) is not tuple or len(s)!=2 or
                any(type(v) is not int for v in s) or not -(2**31)<=s[0]<s[1]<=2**31 for s in spans):
            raise ValueError('bounded explicit protection/lifetime intervals required')
    h,c=layout.helper.helper,layout.helper.coordinates
    t,p,b=layout.transform,layout.predicate,layout.motion
    owners={t:layout.transform_data,c:layout.helper.coordinates_data,h:layout.helper.helper_data,
            p:layout.predicate_data,b:layout.motion_data}
    r,m,retired=dict(registers),dict(cells),list(retired_spans)
    trace,events=[],[];pc=t;boundary=cutpoint=None;flags=None
    finished=dict(transform=False,coordinate=False,predicate=False,motion_early=False)
    returns=[(t,c+32)]
    global_reads={t+28:(6,facts['point'],32),t+48:(6,facts['point'],34),
                  b+52:(2,facts['motion_point'],36),b+64:(2,facts['motion_point'],38),
                  b+84:(0,facts['motion_point'],36),b+96:(2,facts['motion_point'],38),
                  h+254:(0,facts['prior']['scheduler_point'],0)}

    def stop(reason,at=None,**extra):
        error=atoms.remove._Boundary(pc,reason,at);error.report.update(extra);raise error

    def physical(at,width,write=False,allocating=False):
        if not -(2**31)<=at<=2**31-width or not 0<=arena_base+at<=2**32-width:
            stop('access/frame wraps the numeric common base',at)
        if not allocating and any(at<hi and at+width>lo for lo,hi in retired):stop('access overlaps retired private bytes',at)
        if write and any(at<hi and at+width>lo for lo,hi in protected_spans):stop('actual write overlaps protected bytes',at)

    def address(reg):
        v=words.observe(r[reg])
        if v['kind']!='base-plus':stop('address R'+str(reg)+' lacks intact common-base provenance')
        return v['coordinate']

    def number(reg):
        v=words.observe(r[reg])
        if v['kind']!='constant':stop('scalar/control R'+str(reg)+' has opaque or pointer bits')
        return v['value']

    def location(reg,offset):
        if pc in global_reads:
            expected,point,disp=global_reads[pc]
            if reg!=expected or offset!=disp or r[reg]!=words._constant(point):
                stop('literal-derived memory operand differs from actual instruction state')
            return point-arena_base+offset
        return address(reg)+offset

    def load(at,width,signed=False):
        physical(at,width)
        if at%width:stop('unaligned memory read',at)
        values=tuple(m.get(at+i) for i in range(width))
        if any(v is None for v in values):stop('read has missing reaching byte origins',at)
        if width<4 and any(type(v) is not int for v in values):stop('scalar read observes opaque or pointer bytes',at)
        events.append(dict(site=pc,operation='read'+str(width*8),coordinate=at,bytes=values,signed=signed))
        if width==4:return values
        value=sum(v<<(8*i) for i,v in enumerate(values))
        if signed and value&(1<<(8*width-1)):value-=1<<(8*width)
        return words._constant(value&0xffffffff)

    def store(at,value):
        physical(at,len(value),True)
        if at%len(value):stop('unaligned memory write',at)
        if len(value)<4 and any(type(v) is not int for v in value):stop('narrow store has unknown scalar bits',at)
        if len(set(m)|set(range(at,at+len(value))))>4096:stop('byte state exceeds4096 cells',at)
        m.update({at+i:v for i,v in enumerate(value)})
        events.append(dict(site=pc,operation='write'+str(len(value)*8),coordinate=at,bytes=value))

    def activate(lo,hi,opaque=False):
        nonlocal retired
        physical(lo,hi-lo,allocating=True)
        if len(set(m)|set(range(lo,hi)))>4096:stop('frame byte state exceeds4096 cells',lo)
        live=[]
        for a,z in retired:
            if hi<=a or lo>=z:live.append((a,z))
            else:
                if a<lo:live.append((a,lo))
                if hi<z:live.append((hi,z))
        retired=live
        if opaque:
            names={v[1] for v in [*m.values(),*(v for w in r.values() for v in w)] if type(v) is tuple and v[0]=='opaque-byte'}
            name='unmodeled coordinate local';n=0
            while name in names:n+=1;name='unmodeled coordinate local:'+str(n)
            for at in range(lo,hi):m[at]=('opaque-byte',name,at-lo)
        events.append(dict(site=pc,operation='allocate-frame',coordinates=[lo,hi],initialization_granted=False))

    def retire(lo,hi):
        retired.append((lo,hi));events.append(dict(site=pc,operation='retire-frame',coordinates=[lo,hi]))

    try:
        physical(helper_entry_sp,1)
        if r[13]!=words._pointer(helper_entry_sp-100) or r[14]!=words._constant((c+32)|1):
            stop('C918 entry SP/LR does not match the actual075 call cutpoint')
        for _ in range(220):
            owner=next((a for a,data in owners.items() if a<=pc<a+len(data)),None)
            if owner is None:stop('control outside complete continuation owners')
            offset=pc-owner;body=owners[owner]
            allowed=(set(range(0,68,2)) if owner==t else set(range(32,40,2)) if owner==c else
                     set(range(134,148,2))|set(range(210,220,2))|set(range(250,270,2)) if owner==h else
                     set(range(0,36,2)) if owner==p else set(range(0,74,2))|set(range(80,130,2))|set(range(236,252,2)))
            if offset not in allowed:stop('path outside the selected continuation subset')
            trace.append(pc);op=int.from_bytes(body[offset:offset+2],'little');nxt=pc+2
            if op&0xfe00==0xb400:
                selected=[i for i in range(8) if op&(1<<i)]+([14] if op&256 else [])
                top=address(13);low=top-4*len(selected)
                if low%4:stop('unaligned PUSH SP',low)
                physical(low,top-low,True,True);values=[r[i] for i in selected];activate(low,top)
                for i,v in enumerate(values):store(low+4*i,v)
                r[13]=words._pointer(low)
            elif op&0xff00==0xbc00:
                selected=[i for i in range(8) if op&(1<<i)];low=address(13)
                values=[load(low+4*i,4) for i in range(len(selected))]
                for i,v in zip(selected,values):r[i]=v
                r[13]=words._pointer(low+4*len(selected));retire(low,low+4*len(selected))
            elif op&0xff00==0xb000:
                old=address(13);new=old-4*(op&127) if op&128 else old+4*(op&127)
                if op&128:activate(new,old,True)
                else:physical(new,1);retire(old,new)
                r[13]=words._pointer(new)
            elif op&0xff00==0x4600:r[(op&7)|((op>>4)&8)]=r[(op>>3)&15]
            elif op&0xf800==0x2000:r[(op>>8)&7]=words._constant(op&255);flags=None
            elif op&0xf800 in (0x0000,0x0800,0x1000):
                value=number((op>>3)&7);shift=(op>>6)&31;kind=op&0xf800
                if kind==0:value<<=shift
                elif kind==0x0800:value>>=shift or 32
                else:
                    if value&0x80000000:value-=2**32
                    value>>=shift or 32
                r[op&7]=words._constant(value&0xffffffff);flags=None
            elif op&0xf800==0x1800:
                src=(op>>3)&7;dst=op&7
                if op&0x400:
                    immediate=(op>>6)&7
                    if immediate==0 and not op&0x200:r[dst]=r[src]
                    else:r[dst]=words._constant((number(src)+(-immediate if op&0x200 else immediate))&0xffffffff)
                else:
                    rhs=number((op>>6)&7);r[dst]=words._constant((number(src)+(-rhs if op&0x200 else rhs))&0xffffffff)
                flags=None
            elif op&0xf800 in (0x3000,0x3800):
                reg=(op>>8)&7;delta=op&255
                if op&0xf800==0x3800:delta=-delta
                r[reg]=words._constant((number(reg)+delta)&0xffffffff);flags=None
            elif op&0xffc0==0x4340:
                r[op&7]=words._constant((number(op&7)*number((op>>3)&7))&0xffffffff);flags=None
            elif op&0xffc0==0x4240:r[op&7]=words._constant((-number((op>>3)&7))&0xffffffff);flags=None
            elif op&0xffc0==0x4280:flags=number(op&7)==number((op>>3)&7)
            elif op&0xf000==0xd000:
                condition=(op>>8)&15
                if flags is None or condition not in (0,1):stop('branch lacks selected equality comparison')
                if (flags if condition==0 else not flags):
                    delta=op&255
                    if delta&128:delta-=256
                    nxt=pc+4+2*delta
            elif op&0xf800==0xe000:nxt=shapes._branch(body,owner,offset)
            elif op&0xf800==0x4800:
                at=((pc+4)&~3)+4*(op&255)
                if (owner,at-owner) not in ((t,68),(b,76),(b,252),(h,284),(h,288)):
                    stop('literal outside the selected complete owner')
                value=int.from_bytes(body[at-owner:at-owner+4],'little');r[(op>>8)&7]=words._constant(value)
                events.append(dict(site=pc,operation='read-ROM32',address=at,value=value))
            elif op&0xf800==0xa800:r[(op>>8)&7]=words._pointer(address(13)+4*(op&255))
            elif op&0xf000==0x9000:
                at=address(13)+4*(op&255);reg=(op>>8)&7
                if op&0x800:r[reg]=load(at,4)
                else:store(at,r[reg])
            elif op&0xfe00==0x5e00:
                r[op&7]=load(location((op>>3)&7,number((op>>6)&7)),2,True)
            elif op&0xf800 in (0x6000,0x6800,0x8000,0x8800):
                kind=op&0xf800;width=4 if kind in (0x6000,0x6800) else 2
                at=location((op>>3)&7,width*((op>>6)&31));reg=op&7
                if kind in (0x6800,0x8800):r[reg]=load(at,width)
                else:store(at,r[reg][:width])
            elif op&0xf800==0xf000:
                destination=shapes._call(body,owner,offset);site=pc
                r[14]=words._constant((pc+4)|1)
                events.append(dict(site=pc,operation='ordinary-call',target=destination,SP=address(13),return_word=r[14]))
                if (owner,offset) in ((h,214),(p,18)):
                    returns.append((destination,pc+4));nxt=destination
                else:
                    cutpoint=dict(call_site=site,target=destination,SP=address(13),return_word=r[14],
                                  register_arguments={i:r[i] for i in range(4)},callee_executed=False)
                    pc=destination;stop('no composed common-byte effect for this actual callee',call_site=site,cutpoint='callee-entry')
            elif op&0xff87==0x4700:
                value=r[(op>>3)&15]
                if owner==c:expected=h+134
                elif returns and returns[-1][0]==owner:expected=returns[-1][1]
                else:stop('nested return has no actual call continuation')
                if value!=words._constant(expected|1):stop('actual popped return word differs from the BL continuation')
                if owner==c:finished['coordinate']=True
                else:
                    returns.pop()
                    finished[{t:'transform',p:'predicate',b:'motion_early'}[owner]]=True
                nxt=expected
                events.append(dict(site=pc,operation='bx-known-continuation',target=expected,executable_authority_proved=False))
            else:stop('instruction outside the bounded common-byte continuation decoder')
            pc=nxt
        else:stop('bounded acyclic continuation step limit exhausted')
    except atoms.remove._Boundary as error:boundary=error.report
    stale={}
    for reg,value in r.items():
        v=words.observe(value)
        if v['kind']=='base-plus' and any(lo<=v['coordinate']<hi for lo,hi in retired):stale[str(reg)]=v['coordinate']
    return dict(schema=SELECTOR,starts_at=t,boundary=boundary,nested_call_cutpoint=cutpoint,
        reaches_explicit_nested_call=cutpoint is not None,reaches_helper_scheduler_call=cutpoint is not None and cutpoint['call_site']==h+266,
        conditional_returns=finished,registers=r,post_cells={str(k):v for k,v in sorted(m.items())},
        changed_cells={str(k):v for k,v in sorted(m.items()) if cells.get(k)!=v},changed_cells_include_explicit_forgetting=True,
        trace=trace,memory_events=events,helper_entry_SP=helper_entry_sp,retired_spans=retired,known_retired_alias_registers=stale,
        fabricated_callee_effects=False,fabricated_saved_words=False,output_initialization_assumed=False,
        role_separation_assumed=False,ABI_preservation_assumed=False,flags_proved=False,
        actual_reaching_state_proved=False,physical_access_proved=False,actual_heap_or_SP_proved=False,
        actual_lifetime_proved=False,actual_code_execution_proved=False,actual_termination_proved=False,
        returns_to_root=False,full_CFG_closed=False,source_or_ELF_admission=False,native_admission=False,
        obligations=[dict(id=k,proved=False,text=v) for k,v in (
            ('entry','The supplied075 cutpoint is the actual live C918 entry state. Shape checks and scalar values do not establish actual reaching or root transport.'),
            ('memory','Every numeric common-base access has real live permitted memory, complete caller/code protections and exclusion of interference. Literal points alone grant no extent.'),
            ('aliases','All output/global/save aliases share this state. Actual pops, fresh global reads and later consumers must observe resulting words without ABI or output snapshots.'),
            ('remaining-callee','The actual next callee requires its own complete effect relation. No sqrt, allocator, callback or installed image outcome is assumed.'),
            ('lifetime','Dead ranges remain retired until real stack reallocation, which grants no old initialization. All ambient/escaped alias lifetimes remain obligations.'),
            ('scope','Conditional known return words do not prove executable authority, actual termination, all paths, root return or source/native admission.'),
        )])
