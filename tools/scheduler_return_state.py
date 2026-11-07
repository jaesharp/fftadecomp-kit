"""Exact conditional scheduler continuation on post-callback byte origins.

The callback is not executed or assumed pure. Supplied saved bytes, SP and R7
are checked against their required origins. Real ordered field observations
and both frame retirements follow; neither a literal point nor a numeric base
grants physical access, allocation, lifetime, callback return or nonescape.
"""
from dataclasses import dataclass
import hashlib

import scheduler_allocator_state as state
import scheduler_copy_state as copy
import scheduler_descriptor_lifetime as lifetime

SELECTOR = 'conditional-scheduler-postcallback-return-state-v1'


@dataclass(frozen=True)
class Layout:
    wrapper: int
    wrapper_sha256: str
    scheduler_point: int
    callee: state.Layout


def _wrapper(address, callee, point):
    return (lifetime.WRAPPER_HEAD + state.remove._bl(address+30,callee.address) +
            lifetime.WRAPPER_TAIL + point.to_bytes(4,'little'))


def _validate(layout):
    if type(layout) is not Layout or type(layout.callee) is not state.Layout or \
            type(layout.wrapper) is not int or layout.wrapper % 4 or not 0 <= layout.wrapper <= 2**32-60 or \
            type(layout.scheduler_point) is not int or layout.scheduler_point % 4 or not 0 <= layout.scheduler_point <= 2**32-4:
        raise ValueError('complete aligned wrapper and retained state layout required')
    c = layout.callee
    if c.sha256 != hashlib.sha256(state._identity(c.address,c.allocator,c.callback_thunk)).hexdigest() or \
            layout.wrapper_sha256 != hashlib.sha256(_wrapper(layout.wrapper,c,layout.scheduler_point)).hexdigest():
        raise ValueError('retained complete body identity changed')
    a=c.allocator.allocator;i=a.insertion;m=i.median
    spans=[(c.address,206),(c.allocator.address,54),(a.address,266),(i.address,150),
           (i.search.address,174),(m.removal,134),(m.median,102),(a.thunk,2),(c.callback_thunk,2)]
    if any(layout.wrapper < start+size and layout.wrapper+60 > start for start,size in spans):
        raise ValueError('wrapper overlaps a complete retained helper owner')


def bind(wrapper_data, wrapper_address, instruction_count, state_layout, *, selector):
    if type(selector) is not str or selector != SELECTOR or type(wrapper_data) is not bytes or len(wrapper_data) != 60 or \
            type(instruction_count) is not int or instruction_count != 27:
        raise ValueError('explicit continuation selector and complete60B/27-instruction wrapper required')
    layout=Layout(wrapper_address,hashlib.sha256(wrapper_data).hexdigest(),int.from_bytes(wrapper_data[56:60],'little'),state_layout)
    _validate(layout)
    if wrapper_data != _wrapper(wrapper_address,state_layout,layout.scheduler_point):
        raise ValueError('wrapper body, call or literal differs from closed shape')
    return layout


def _registers(value, keys):
    return type(value) is dict and set(value) == keys and all(type(k) is int and copy._word(v) for k,v in value.items())


def _saved(layout, entry, entry_sp):
    size=copy.observe(entry[1])
    if size['kind'] != 'constant':
        raise ValueError('wrapper incoming size requires concrete unsigned32 bits')
    e=entry_sp
    return {e-16:entry[4],e-12:entry[5],e-8:entry[6],e-4:entry[14],e-20:entry[8],
            e-44:copy._constant(size['value']&65535),e-40:copy._constant(layout.scheduler_point),
            e-36:entry[0],e-32:entry[7],e-28:copy._constant((layout.wrapper+34)|1),
            e-52:entry[2],e-48:entry[9]}


def derive(layout, arena_base, entry_sp, allocation_offset, entry_registers, post_registers,
           post_cells, *, selector, protected_spans=()):
    """Observe a new conditional callback-return state, never invent one.

The entry is at callee+184 after a normal synchronous callback return. The
actual occurrence of that return and equality of these bytes remain premises.
The concrete common base relates the fixed scheduler point to byte coordinates;
it is a supplied numeric condition, not an inferred heap or physical witness.
"""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit postcallback continuation selector required')
    _validate(layout)
    if type(arena_base) is not int or arena_base % 4 or not 0 <= arena_base < 2**32 or \
            any(type(v) is not int or v % 4 or not -(2**31) <= v < 2**31 for v in (entry_sp,allocation_offset)) or \
            not _registers(entry_registers,set(range(13))|{14}) or not _registers(post_registers,set(range(15))) or \
            type(post_cells) is not dict or len(post_cells)>4096 or any(type(k) is not int or not -(2**31)<=k<2**31 or not state._cell(v) for k,v in post_cells.items()) or \
            type(protected_spans) is not tuple or len(protected_spans)>27 or any(type(p) is not tuple or len(p)!=2 or
                any(type(v) is not int for v in p) or not -(2**31)<=p[0]<p[1]<=2**31 for p in protected_spans):
        raise ValueError('bounded aligned arena, exact entry/post register origins and byte state required')
    e=entry_sp;c=layout.callee.address;w=layout.wrapper
    expected=_saved(layout,entry_registers,e)
    memory=dict(post_cells);regs=dict(post_registers)
    events=[];changed={};retired=[];boundary=None
    scheduler=None;phase=None;final_target=None
    saved_verified=False;retired_copy=False;returned_callee=False
    def fail(site,reason,at=None):
        raise state.remove._Boundary(site,reason,at)
    def physical(at,width,site):
        if not -(2**31)<=at<=2**31-width or not 0<=arena_base+at<=2**32-width or at % (4 if width==4 else 2 if width==2 else 1):
            fail(site,'access is unaligned or wraps the supplied numeric arena base',at)
    def field(at,width,site,role):
        physical(at,width,site)
        if at<e and at+width>e-156:
            fail(site,role+' overlaps live or retired private-frame envelope',at)
        if any(at<end and at+width>start for start,end in protected_spans):
            fail(site,role+' overlaps protected caller bytes',at)
    def load(at,site,role,*,stack=False):
        (physical if stack else lambda a,b,s:field(a,b,s,role))(at,4,site)
        value=tuple(memory.get(at+i) for i in range(4))
        if not copy._word(value):fail(site,'word has missing reaching byte origins: '+role,at)
        events.append(dict(site=site,operation='read32',coordinate=at,bytes=value,role=role))
        return value
    def address(value,site,role):
        observation=copy.observe(value)
        if observation['kind'] != 'base-plus':
            fail(site,role+' lacks intact common-base pointer provenance')
        return observation['coordinate']
    def write_half(at,value,site,role):
        field(at,2,site,role)
        memory[at]=changed[at]=value&255
        memory[at+1]=changed[at+1]=value>>8&255
        events.append(dict(site=site,operation='write16',coordinate=at,value=value&65535,role=role))
    def retire(start,end,site,role):
        retired.append((start,end))
        events.append(dict(site=site,operation='retire-frame',coordinates=[start,end],role=role,bytes_erased=False))
    def pop(numbers,site):
        at=address(regs[13],site,'POP SP')
        values=[load(at+4*i,site,'saved register R'+str(reg),stack=True) for i,reg in enumerate(numbers)]
        for reg,value in zip(numbers,values):regs[reg]=value
        regs[13]=copy._pointer(at+4*len(numbers))
        retire(at,at+4*len(numbers),site,'popped saved words')
    try:
        # A frame may end at2**32 as an interval, but a restored architectural
        # SP equal to2**32 is not representable. Do not admit that one-past case.
        physical(e,1,c+184)
        physical(e-156,156,c+184)
        if any(e-52<end and e>start for start,end in protected_spans):
            fail(c+184,'caller protection overlaps the already-created saved/private frame')
        if regs[13] != copy._pointer(e-80):fail(c+184,'callback return SP lacks exact live descriptor-frame origin')
        if regs[7] != copy._pointer(allocation_offset):fail(c+184,'callback R7 allocation origin was not preserved')
        for at,value in sorted(expected.items()):
            # This is a checked cutpoint invariant, not another machine read.
            observed=tuple(memory.get(at+i) for i in range(4))
            if observed != value:fail(c+184,'callback/prefix saved word changed or missing',at)
        saved_verified=True
        regs[0]=copy._constant(256)
        write_half(allocation_offset+20,256,c+188,'allocation status after callback')
        regs[0]=regs[7]
        regs[13]=copy._pointer(e-52)
        retire(e-80,e-52,c+192,'descriptor local ends');retired_copy=True
        pop((3,4),c+194);regs[8]=regs[3];regs[9]=regs[4]
        pop((4,5,6,7),c+200);pop((1,),c+202)
        if regs[1] != copy._constant((w+34)|1):fail(c+204,'callee return word does not name exact wrapper continuation')
        events.append(dict(site=c+204,operation='bx-known-continuation',target=(w+34)|1))
        returned_callee=True
        # R5 is the actual restored numeric literal; the numeric common-base
        # input supplies the coordinate equation without granting any extent.
        if regs[5] != copy._constant(layout.scheduler_point):fail(w+34,'restored scheduler point changed')
        point_offset=layout.scheduler_point-arena_base
        regs[1]=load(point_offset,w+34,'fresh postcallback scheduler pointer')
        scheduler=address(regs[1],w+36,'fresh scheduler pointer')
        field(scheduler+12,2,w+36,'fresh scheduler phase')
        values=[memory.get(scheduler+12+i) for i in range(2)]
        if any(type(v) is not int or not 0<=v<=255 for v in values):fail(w+36,'fresh scheduler phase has missing or opaque bits',scheduler+12)
        phase=values[0]|values[1]<<8
        events.append(dict(site=w+36,operation='read16',coordinate=scheduler+12,value=phase,role='fresh scheduler phase'))
        regs[1]=copy._constant(phase^1);regs[2]=copy._constant(1)
        write_half(address(regs[0],w+42,'allocation return pointer')+22,phase^1,w+42,'allocation toggled phase')
        regs[13]=copy._pointer(e-20);retire(e-24,e-20,w+44,'wrapper incoming parent slot ends')
        pop((3,),w+46);regs[8]=regs[3];pop((4,5,6),w+50);pop((1,),w+52)
        final_target=regs[1]
        if any(regs[r]!=entry_registers[r] for r in [4,5,6,7,8,9]) or regs[13]!=copy._pointer(e) or regs[1]!=entry_registers[14]:
            raise ValueError('closed instruction replay disagrees with saved-origin restoration')
    except state.remove._Boundary as error:
        boundary=error.report
    stale={}
    for r,value in regs.items():
        observation=copy.observe(value)
        if observation['kind']=='base-plus' and any(lo<=observation['coordinate']<hi for lo,hi in retired):
            stale[str(r)]=observation['coordinate']
    return dict(schema=SELECTOR,reaches_outer_return_thunk=boundary is None,boundary=boundary,
        actual_outer_return_executed=False,registers=regs,memory_events=events,
        changed_cells={str(k):v for k,v in sorted(changed.items())},
        checked_saved_origins=saved_verified,conditional_R7_preserved=post_registers[7]==copy._pointer(allocation_offset),
        callee_reaches_wrapper_continuation=returned_callee,observed_scheduler_coordinate=scheduler,
        observed_scheduler_phase=phase,outer_return_word=final_target,
        descriptor_local_retired=retired_copy,retired_spans=retired,known_retired_alias_registers=stale,
        possible_unknown_escaped_aliases=True,nonescape_proved=False,dead_bytes_erased=False,
        restored_entry_registers=[4,5,6,7,8,9] if boundary is None else [],
        ambient_R10_R11_R12_unchanged_from_supplied_callback_poststate=True,
        actual_callback_return_proved=False,actual_poststate_proved=False,physical_access_proved=False,
        actual_heap_or_stack_base_proved=False,callback_effects_closed=False,full_scheduler_proved=False,native_admission=False,
        obligations=[dict(id=k,proved=False,text=t) for k,t in [
            ('entry-and-poststate','The supplied complete entry origins, postcallback registers and bytes equal actual reaching state after a normal synchronous callback return at callee+184.'),
            ('numeric-base','The supplied word-aligned arena base and wrapper-entry-SP coordinate equal actual addresses. Their checked nonwrapping equations alone grant no memory access or allocation extent.'),
            ('saves-and-protection','The checked saved-word equality, R7 origin and SP relation hold in actual memory; all caller/source/code protections are complete and no asynchronous/device interference changes reads.'),
            ('field-access','Every real allocation field write, fixed-point pointer read, scheduler phase read and stack pop is physically accessible with live provenance and correct permission.'),
            ('callback-and-lifetime','Actual callback effects and all escaping or ambient aliases must be accounted for. Retired frames remain dead even if snapshots or registers retain their byte/pointer origins.'),
            ('final-control','The observed saved outer LR is compatible executable return control. The relation stops at BX R1 and does not execute that target or admit native source.')]])
