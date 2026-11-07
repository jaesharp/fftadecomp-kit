"""Ordered shared-byte callback continuation after the first twelve bytes.

The prefix, actual incoming origins and physical access are separate premises.
Payload, descriptor and saved words share one arena. Aliases alter later reads
and POPs; this module never substitutes role separation or ABI preservation.
Only the phase0/tag158 path and actual nested early-return path are interpreted.
Other reachable branches retain exact cutpoints and partial state.
"""
from dataclasses import dataclass
import hashlib

import scheduler_allocator_state as atoms
import scheduler_copy_state as words
import scheduler_callback_zero_phase as shapes

SELECTOR = 'conditional-scheduler-shared-callback-continuation-v1'


@dataclass(frozen=True)
class Layout:
    callback: int
    helper: int
    callback_data: bytes
    helper_data: bytes


def _validate(layout):
    if type(layout) is not Layout or type(layout.callback_data) is not bytes or len(layout.callback_data)!=658 or \
            type(layout.helper_data) is not bytes or len(layout.helper_data)!=292 or any(type(a) is not int or a%4 or not 0<=a<=2**32-n
            for a,n in [(layout.callback,658),(layout.helper,292)]):
        raise ValueError('complete aligned658B callback and292B helper required')
    c,h=layout.callback,layout.helper;b,d=layout.callback_data,layout.helper_data
    if max(c,h)<min(c+658,h+292):raise ValueError('complete callback/helper spans overlap')
    # Reuse frozen instruction facts, not the old bind/derive producer.
    if b[:52]!=shapes.DISPATCH or b[56:76]!=shapes.PHASE or b[92:108]!=shapes.COPY_FIELDS or \
            b[116:138]!=shapes.CALL_SETUP or b[142:144]!=b'\x68\x63' or b[648:]!=shapes.RETURN or \
            d[:30]!=shapes.HELPER_GATE or d[270:278]!=shapes.HELPER_RETURN or \
            int.from_bytes(b[52:56],'little')!=257 or shapes._call(b,c,138)!=h or \
            shapes._branch(b,c,144)!=c+648 or shapes._branch(d,h,28)!=h+270:
        raise ValueError('selected instructions, real call, literal or continuation differs')


def bind(callback_data,callback_address,helper_data,helper_address,*,selector):
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit shared-callback selector required')
    result=Layout(callback_address,helper_address,callback_data,helper_data)
    _validate(result)
    return result


def derive(layout,registers,cells,*,entry_sp,selector,protected_spans=()):
    """Execute a NEW post-save state from callback+12, without prefix replay.

entry_sp is the callback entry coordinate, so supplied post-prefix SP is
entry_sp-36. R1 is the already-observed zero-extended phase, not a fresh load.
The unmodeled initial16-byte local area cannot supply stale scalar/pointer
facts. New instruction writes establish byte origins there normally.
Protected spans are explicitly immutable bytes: writes refuse, reads do not
invent a value and still require supplied reaching origins and access premises.
"""
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit shared-callback selector required')
    _validate(layout)
    if type(registers) is not dict or set(registers)!=set(range(15)) or any(type(k) is not int or not words._word(v) for k,v in registers.items()) or \
            type(cells) is not dict or len(cells)>4096 or any(type(k) is not int or not -(2**31)<=k<2**31 or not atoms._cell(v) for k,v in cells.items()) or \
            type(entry_sp) is not int or entry_sp%4 or not -(2**31)+108<=entry_sp<=2**31-40 or \
            type(protected_spans) is not tuple or len(protected_spans)>32 or any(type(p) is not tuple or len(p)!=2 or
                any(type(v) is not int for v in p) or not -(2**31)<=p[0]<p[1]<=2**31 for p in protected_spans):
        raise ValueError('bounded complete post-save register/byte origins and coordinates required')
    c,h=layout.callback,layout.helper
    r=dict(registers);m=dict(cells);initial_lr=r[14];events=[];changed={};trace=[];retired=[]
    initial_saves={str(reg):tuple(m.get(entry_sp-20+4*i+n) for n in range(4))
                   for i,reg in enumerate((4,5,6,7,14))}
    pc=c+12;boundary=None;phase0=False;helper_entered=False;helper_returned=False
    reaches_thunk=False;return_matches=False;target=None;flags=None
    pending_locals=range(entry_sp-36,entry_sp-20)
    origins={v[1] for v in [*m.values(),*(a for w in r.values() for a in w)] if type(v) is tuple and v[0]=='opaque-byte'}
    namespace='unmodeled callback local'
    generation=0
    while namespace in origins:
        generation+=1
        namespace='unmodeled callback local:'+str(generation)
    for at in pending_locals:m[at]=('opaque-byte',namespace,at-(entry_sp-36))
    allowed_c=set(range(12,52,2))|set(range(56,76,2))|set(range(92,108,2))|set(range(116,140,2))|{142,144}|set(range(648,658,2))
    allowed_h=set(range(0,30,2))|set(range(270,278,2))
    def stop(reason,at=None):raise atoms.remove._Boundary(pc,reason,at)
    def guard(at,width,writing=False):
        if type(at) is not int or not -(2**31)<=at<=2**31-width or at%width:
            stop('memory access is unaligned or outside nonwrapping common-byte coordinates',at)
        if writing and any(at<end and at+width>start for start,end in protected_spans):
            stop('actual write overlaps explicitly protected caller/source bytes',at)
    def addr(reg,offset=0):
        observation=words.observe(r[reg])
        if observation['kind']!='base-plus':stop('address R'+str(reg)+' lacks intact common-base provenance')
        return observation['coordinate']+offset
    def number(reg):
        observation=words.observe(r[reg])
        if observation['kind']!='constant':stop('scalar/control R'+str(reg)+' has opaque or pointer bits')
        return observation['value']
    def load(at,width,*,signed=False):
        guard(at,width)
        values=tuple(m.get(at+i) for i in range(width))
        if any(v is None for v in values):stop('read has missing reaching byte origins',at)
        if width==4:
            events.append(dict(site=pc,operation='read32',coordinate=at,bytes=values));return values
        if any(type(v) is not int for v in values):stop('scalar load observes opaque or pointer byte origins',at)
        value=sum(v<<(8*i) for i,v in enumerate(values))
        if signed and value&(1<<(8*width-1)):value-=1<<(8*width)
        events.append(dict(site=pc,operation='read'+str(width*8),coordinate=at,value=value,signed=signed))
        return words._constant(value&0xffffffff)
    def store(at,width,value):
        guard(at,width,True)
        chosen=value[:width]
        if width<4 and any(type(v) is not int for v in chosen):stop('narrow store lacks exact scalar byte bits',at)
        for i,v in enumerate(chosen):m[at+i]=v;changed[at+i]=v
        events.append(dict(site=pc,operation='write'+str(width*8),coordinate=at,bytes=chosen))
    def retired_range(start,end,role):
        retired.append((start,end))
        events.append(dict(site=pc,operation='retire-frame',coordinates=[start,end],role=role,bytes_erased=False))
    def scalar_result(reg,value):
        nonlocal flags
        r[reg]=words._constant(value&0xffffffff);flags=None
    try:
        if r[13]!=words._pointer(entry_sp-36):stop('post-save SP differs from callback entry minus36')
        if r[1][2:]!=(0,0) or any(type(v) is tuple and v[0]=='base-plus-byte' for v in r[1][:2]):
            stop('post-LDRH R1 is not a zero-extended scalar phase halfword')
        for _ in range(128):
            if c<=pc<c+658:
                offset=pc-c;body=layout.callback_data;owner=c
                if offset not in allowed_c:stop('callback branch leaves the explicit phase0/tag158 continuation')
                if offset==56:phase0=True
                if offset==648 and not phase0:stop('non-phase0 default-return cutpoint is outside this continuation')
            elif h<=pc<h+292:
                offset=pc-h;body=layout.helper_data;owner=h
                if offset not in allowed_h:stop('nested helper branch leaves the explicit R2zero/R3seven early-return path')
            else:stop('control leaves the two complete bound owners')
            trace.append(pc);op=int.from_bytes(body[offset:offset+2],'little');next_pc=pc+2
            if op&0xf800==0x2000:
                scalar_result((op>>8)&7,op&255)
            elif op&0xf800 in (0x0000,0x0800):
                source=number((op>>3)&7);shift=(op>>6)&31
                value=source<<shift if op&0xf800==0 else source>>(shift or 32)
                scalar_result(op&7,value)
            elif op&0xfe00==0x1c00:
                if (op>>6)&7:stop('nonzero three-register arithmetic outside selected transfer')
                r[op&7]=r[(op>>3)&7];flags=None
            elif op&0xf800==0x3000:
                reg=(op>>8)&7;scalar_result(reg,number(reg)+(op&255))
            elif op&0xffc0==0x4280 or op&0xf800==0x2800:
                if op&0xf800==0x2800:a=number((op>>8)&7);b=op&255
                else:a=number(op&7);b=number((op>>3)&7)
                diff=(a-b)&0xffffffff
                flags=dict(Z=diff==0,N=bool(diff&0x80000000),C=a>=b,V=bool((a^b)&(a^diff)&0x80000000))
            elif op&0xf000==0xd000:
                condition=(op>>8)&15
                if flags is None:stop('conditional branch lacks established comparison flags')
                take={0:flags['Z'],1:not flags['Z'],12:not flags['Z'] and flags['N']==flags['V']}.get(condition)
                if take is None:stop('conditional code outside selected branch subset')
                displacement=op&255
                if displacement&128:displacement-=256
                if take:next_pc=pc+4+2*displacement
            elif op&0xf800==0xe000:
                displacement=op&2047
                if displacement&1024:displacement-=2048
                next_pc=pc+4+2*displacement
            elif op&0xf800==0xf000:
                destination=shapes._call(body,owner,offset)
                if owner!=c or offset!=138 or destination!=h:stop('unexpected nested call')
                r[14]=words._constant((pc+4)|1);next_pc=h;helper_entered=True
                events.append(dict(site=pc,operation='ordinary-call',target=h,SP=addr(13)))
            elif op&0xf800==0x4800:
                literal=((pc+4)&~3)+4*(op&255)
                if owner!=c or literal not in (c+52,c+148):stop('literal outside selected owned words')
                value=int.from_bytes(body[literal-owner:literal-owner+4],'little')
                r[(op>>8)&7]=words._constant(value)
                events.append(dict(site=pc,operation='read-ROM32',address=literal,value=value))
            elif op&0xfe00==0x5e00:
                r[op&7]=load(addr((op>>3)&7,number((op>>6)&7)),2,signed=True)
            elif op&0xf800 in (0x6000,0x6800,0x7000,0x7800,0x8000,0x8800):
                kind=op&0xf800;reg=op&7;base=(op>>3)&7
                width=4 if kind in (0x6000,0x6800) else 1 if kind in (0x7000,0x7800) else 2
                at=addr(base,width*((op>>6)&31))
                if kind in (0x6800,0x7800,0x8800):r[reg]=load(at,width)
                else:store(at,width,r[reg])
            elif op&0xf000==0x9000:
                at=addr(13,4*(op&255));reg=(op>>8)&7
                if op&0x0800:r[reg]=load(at,4)
                else:store(at,4,r[reg])
            elif op&0xfe00==0xb400:
                selected=[reg for reg in range(8) if op&(1<<reg)]+([14] if op&256 else [])
                if not selected:stop('empty PUSH outside selected subset')
                start=addr(13)-4*len(selected);values=[r[reg] for reg in selected]
                for i,value in enumerate(values):store(start+4*i,4,value)
                r[13]=words._pointer(start)
            elif op&0xff00==0xb000:
                old=addr(13);delta=4*(op&127);new=old-delta if op&128 else old+delta
                if not -(2**31)<=new<2**31 or new%4:stop('SP arithmetic leaves bounded common-byte coordinates',new)
                r[13]=words._pointer(new)
                if op&128:
                    events.append(dict(site=pc,operation='allocate-frame',coordinates=[new,old],initialization_granted=False))
                else:retired_range(old,new,'actual ADD SP deallocation')
            elif op&0xfe00==0xbc00:
                if op&256:stop('POP PC is outside selected suffix')
                selected=[reg for reg in range(8) if op&(1<<reg)];start=addr(13)
                values=[load(start+4*i,4) for i in range(len(selected))]
                for reg,value in zip(selected,values):r[reg]=value
                r[13]=words._pointer(start+4*len(selected));retired_range(start,start+4*len(selected),'actual POP deallocation')
            elif op&0xff87==0x4700:
                branch_word=r[(op>>3)&15]
                if owner==h:
                    if branch_word!=words._constant((c+142)|1):stop('actual nested saved return word differs from BL continuation')
                    next_pc=c+142;helper_returned=True
                    events.append(dict(site=pc,operation='bx-nested-continuation',target=(c+142)|1))
                else:
                    target=branch_word
                    reaches_thunk=True;return_matches=target==initial_lr
                    if not return_matches:stop('actual callback saved return word changed by shared-memory effects')
                    break
            else:stop('instruction outside closed shared-memory continuation decoder')
            pc=next_pc
        else:stop('explicit acyclic continuation step bound exhausted')
    except atoms.remove._Boundary as error:
        boundary=error.report
    stale={}
    for reg,value in r.items():
        observation=words.observe(value)
        if observation['kind']=='base-plus' and any(lo<=observation['coordinate']<hi for lo,hi in retired):stale[str(reg)]=observation['coordinate']
    return dict(schema=SELECTOR,callback=dict(address=c,bytes=658,sha256=hashlib.sha256(layout.callback_data).hexdigest()),
        helper=dict(address=h,bytes=292,sha256=hashlib.sha256(layout.helper_data).hexdigest()),
        starts_at=c+12,boundary=boundary,reaches_return_thunk=reaches_thunk,
        returns_to_input_continuation_under_conditions=boundary is None and reaches_thunk and return_matches,
        observed_return_word=target,expected_input_continuation=initial_lr,registers=r,
        trace=trace,memory_events=events,changed_cells={str(k):v for k,v in sorted(changed.items())},
        post_cells={str(k):v for k,v in sorted(m.items())},
        initial_saved_words=initial_saves,
        saved_origin_equalities={str(reg):r[reg]==initial_saves[str(reg)] for reg in (4,5,6,7)},
        unmodeled_initial_local_span=[entry_sp-36,entry_sp-20],
        phase0_entered=phase0,nested_helper_entered=helper_entered,nested_helper_early_returned=helper_returned,
        entry_SP=entry_sp,final_SP_origin=r[13],retired_spans=retired,known_retired_alias_registers=stale,
        register_origin_equalities={str(reg):r[reg]==registers[reg] for reg in range(15)},
        flags_proved=False,actual_prefix_or_reaching_state_proved=False,actual_heap_base_proved=False,
        physical_access_proved=False,source_initialization_proved=False,actual_termination_proved=False,
        actual_R7_survival_proved=False,role_separation_assumed=False,ABI_preservation_assumed=False,
        nonescape_proved=False,possible_unknown_escaped_aliases=True,dead_bytes_erased=False,
        whole_callback_CFG_closed=False,full_scheduler_proved=False,native_admission=False,
        obligations=[dict(id=k,proved=False,text=t) for k,t in [
            ('post-prefix','Actual first12B reaches callback+12 with precisely these R0..R14 origins, SP=entrySP-36, observed R1 phase and shared byte state. No source phase is re-read or initialized here.'),
            ('physical-arena','The common base is word aligned and all recorded coordinates translate to nonwrapping accessible live memory with the required permissions. Numeric origins alone grant no extent or allocation.'),
            ('code-and-literals','Both complete bound owners and selected ROM literal words retain their authenticated bytes during execution. Every immutable caller/source/code protection is supplied.'),
            ('stable-memory','Only listed ordinary instruction writes change this shared state. No interrupt/device/external writer changes an observed value or instruction.'),
            ('lifetime','Frame allocations grant no initialization; POP/ADD retire spans without erasure. All source, payload and escaped or ambient aliases need actual lifetime/access justification, including any access overlapping a retired span.'),
            ('return-control','Equality with the input LR is conditional byte-origin equality, not actual executable return permission. Any altered saved register or return word must feed the next consumer unchanged; no ABI or role-separation shortcut applies.')]])
