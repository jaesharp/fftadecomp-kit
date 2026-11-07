"""Conditional callback702 entry, dispatch and phase-zero byte effects.

Complete code identities bind the scheduler, helpers, BX R3 and callback.
The byte relation stops before the first phase-zero copy call. Literal RAM
addresses remain values; no access, installation or callback return is granted.
"""
from dataclasses import dataclass
import hashlib

import installed_copy_effects as flags
import scheduler_allocator_state as state
import scheduler_copy_state as words

SELECTOR = 'conditional-scheduler-callback702-prefix-v1'
ADDRESS = 0x080FDB98
BODY_SHA256 = '8527501ea17bd5cf5f925548ec0f3c27aa82594b623e87da2fa4b20bb63e0784'
MEMCPY = 0x0814186C
OFFSETS = frozenset(range(0,42,2)) | frozenset(range(48,90,2)) | frozenset(range(96,120,2))


@dataclass(frozen=True)
class Layout:
    scheduler: state.Layout
    callback: int
    body: bytes


def _validate(layout):
    if type(layout) is not Layout or type(layout.scheduler) is not state.Layout or \
            type(layout.callback) is not int or layout.callback != ADDRESS or \
            type(layout.body) is not bytes or len(layout.body) != 702 or \
            hashlib.sha256(layout.body).hexdigest() != BODY_SHA256:
        raise ValueError('complete exact702B callback and retained scheduler layout required')
    c = layout.scheduler
    raw = state._identity(c.address,c.allocator,c.callback_thunk)
    if hashlib.sha256(raw).hexdigest() != c.sha256:
        raise ValueError('retained scheduler identity changed')
    w, a = c.allocator, c.allocator.allocator
    i, m = a.insertion, a.insertion.median
    rows = [(c.address,raw), (w.address,state.wrapper._identity(w.address,a)),
            (a.address,state.split._identity(a.address,i,a.thunk,a.pointer_literal)),
            (i.address,state.split.insert.HEAD+state.remove._bl(i.address+22,i.search.address)+
             state.split.insert.MIDDLE+state.remove._bl(i.address+138,m.median)+state.split.insert.TAIL),
            (i.search.address,state.split.insert.search.SHAPE),
            (m.removal,state.remove.REMOVE_HEAD+state.remove._bl(m.removal+124,m.median)+state.remove.REMOVE_TAIL),
            (m.median,state.remove.MEDIAN), (a.thunk,b'\x10\x47'),
            (c.callback_thunk,b'\x18\x47'), (layout.callback,layout.body)]
    spans = sorted((a,a+len(b)) for a,b in rows)
    if any(x[1] > y[0] for x,y in zip(spans,spans[1:])):
        raise ValueError('complete callback and scheduler/helper owners overlap')
    if layout.body[120:124] != state.remove._bl(layout.callback+120,MEMCPY):
        raise ValueError('callback phase-zero copy target changed')
    return dict(rows)


def bind(scheduler, body, address, *, selector):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit callback702 selector required')
    result = Layout(scheduler,address,body)
    _validate(result)
    return result


def _pins(owners):
    return [dict(address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
            for a,b in sorted(owners.items())]


def _spans(value):
    return type(value) is tuple and len(value) <= 128 and all(
        type(v) is tuple and len(v) == 2 and all(type(n) is int for n in v)
        and -(2**31) <= v[0] < v[1] <= 2**31 for v in value)


def derive(layout, arena_base, cells, registers, *, selector, protected_spans=(),
           retired_spans=(), reusable_frame_spans=(), unavailable_spans=(), max_steps=128):
    """Execute a new conditional BX R3/callback entry; never execute its copy."""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit callback702 selector required')
    owners = _validate(layout)
    if type(arena_base) is not int or arena_base % 4 or not 0 <= arena_base < 2**32 or \
            type(cells) is not dict or len(cells) > 4096 or any(type(k) is not int or
                not -(2**31) <= k < 2**31 or not state._cell(v) for k,v in cells.items()) or \
            type(registers) is not dict or set(registers) != set(range(15)) or any(
                type(k) is not int or not words._word(v) for k,v in registers.items()) or \
            type(max_steps) is not int or not 1 <= max_steps <= 128:
        raise ValueError('bounded numeric common base, exact cells and all register origins required')
    if not all(_spans(v) for v in (protected_spans,retired_spans,reusable_frame_spans,unavailable_spans)):
        raise ValueError('bounded explicit protection/lifetime intervals required')
    r, m = dict(registers), dict(cells)
    retired = list(retired_spans)
    cb, pc = layout.callback, layout.scheduler.callback_thunk
    trace, events, changed, activations = [], [], set(), []
    boundary = pending = phase = phase_bytes = entry_sp = None
    comparison = None
    entered = reached = False

    def stop(reason, at=None, **extra):
        error = state.remove._Boundary(pc,reason,at)
        error.report.update(extra)
        raise error

    def address(word):
        value = words.observe(word)
        if value['kind'] != 'base-plus':
            stop('address lacks intact common-base provenance')
        return value['coordinate']

    def numeric(word):
        value = words.observe(word)
        if value['kind'] != 'constant':
            stop('scalar/control observation has opaque or pointer byte origins')
        return value['value']

    def physical(at, width, write=False, allocating=False):
        if not -(2**31) <= at <= 2**31-width or not 0 <= arena_base+at <= 2**32-width:
            stop('common-base access or stack allocation wraps',at)
        if width in (2,4) and at % width:
            stop('unaligned common-byte access',at)
        if any(at < hi and at+width > lo for lo,hi in unavailable_spans):
            stop('access intersects unavailable payload/frame bytes',at)
        if not allocating and any(at < hi and at+width > lo for lo,hi in retired):
            stop('access intersects retired bytes',at)
        if write and any(at < hi and at+width > lo for lo,hi in protected_spans):
            stop('actual write intersects protected bytes',at)
        if write and any(arena_base+at < a+len(b) and arena_base+at+width > a for a,b in owners.items()):
            stop('actual write intersects immutable complete owner',at)

    def covered(lo,hi):
        cursor = lo
        for start,end in sorted(reusable_frame_spans):
            if start <= cursor < end:
                cursor = max(cursor,end)
        return cursor >= hi

    def allocate(lo,hi,local=False):
        nonlocal retired
        physical(lo,hi-lo,allocating=True)
        if lo % 4 or hi % 4:
            stop('unaligned stack allocation',lo)
        for a,b in retired:
            start,end = max(a,lo),min(b,hi)
            if start < end and not covered(start,end):
                stop('stack allocation intersects nonreusable retired bytes',start)
        retired = [p for a,b in retired for p in ((a,min(b,lo)),(max(a,hi),b)) if p[0] < p[1]]
        activations.append(dict(site=pc,coordinates=[lo,hi],initialization_granted=False))
        if local:
            if len(set(m) | set(range(lo,hi))) > 4096:
                stop('local byte state exceeds4096 cells',lo)
            names = {v[1] for v in [*m.values(),*(v for w in r.values() for v in w)]
                     if type(v) is tuple and v[0] == 'opaque-byte'}
            n = 0
            name = 'callback702 local'
            while name in names:
                n += 1
                name = 'callback702 local:'+str(n)
            for at in range(lo,hi):
                m.setdefault(at,('opaque-byte',name,at-lo))
            events.append(dict(site=pc,operation='allocate-frame',coordinates=[lo,hi],
                               initialization_granted=False))

    def load(at,width):
        physical(at,width)
        value = tuple(m.get(at+i) for i in range(width))
        if any(v is None for v in value):
            stop('read lacks reaching byte origins',at)
        events.append(dict(site=pc,operation='read'+str(width*8),coordinate=at,bytes=value))
        return value+(0,)*(4-width)

    def store(at,value):
        physical(at,len(value),True)
        if len(set(m) | set(range(at,at+len(value)))) > 4096:
            stop('byte state exceeds4096 cells',at)
        m.update({at+i:v for i,v in enumerate(value)})
        changed.update(range(at,at+len(value)))
        events.append(dict(site=pc,operation='write'+str(len(value)*8),coordinate=at,bytes=value))

    def add(word,n):
        value = words.observe(word)
        if value['kind'] == 'base-plus':
            at = value['coordinate']+n
            if not -(2**31) <= at < 2**31 or not 0 <= arena_base+at < 2**32:
                stop('common-base pointer arithmetic wraps',at)
            return words._pointer(at)
        if value['kind'] == 'constant':
            return words._constant((value['value']+n)&0xffffffff)
        if n == 0:
            return word
        stop('arithmetic interprets opaque or partial word bits')

    try:
        for _ in range(max_steps):
            if pc == cb+120:
                reached = True
                pending = dict(site=pc,target=MEMCPY,register_arguments={i:r[i] for i in range(4)},
                               SP=r[13],LR=r[14],callee_executed=False)
                stop('unproved ordinary memory-copy call',target=MEMCPY,callee_executed=False)
            if pc == layout.scheduler.callback_thunk:
                trace.append(pc)
                if r[3] != words._constant(cb|1):
                    stop('actual R3 does not identify the bound Thumb callback')
                entered = True
                pc = cb
                continue
            offset = pc-cb
            if offset not in OFFSETS:
                stop('phase target lies outside the modeled callback prefix',observed_phase=phase)
            trace.append(pc)
            op = int.from_bytes(layout.body[offset:offset+2],'little')
            nxt = pc+2
            if op & 0xfe00 == 0xb400:
                selected = [i for i in range(8) if op >> i & 1]+([14] if op & 0x100 else [])
                top = address(r[13])
                if entry_sp is None:
                    entry_sp = top
                lo = top-4*len(selected)
                physical(lo,top-lo,True,True)
                allocate(lo,top)
                for i,reg in enumerate(selected):
                    store(lo+4*i,r[reg])
                r[13] = words._pointer(lo)
            elif op & 0xff80 == 0xb080:
                top = address(r[13]);lo = top-4*(op & 127)
                allocate(lo,top,True)
                r[13] = words._pointer(lo)
            elif op & 0xff00 == 0x4600:
                r[(op & 7) | ((op >> 4) & 8)] = r[(op >> 3) & 15]
            elif op & 0xfe00 == 0x1c00:
                r[op & 7] = add(r[(op >> 3) & 7],(op >> 6) & 7)
                comparison = None
            elif op & 0xf800 == 0x2000:
                r[(op >> 8) & 7] = words._constant(op & 255)
                comparison = None
            elif op & 0xf800 == 0x2800:
                comparison = flags._sub_flags(numeric(r[(op >> 8) & 7]),op & 255)
            elif op & 0xffc0 == 0x4280:
                comparison = flags._sub_flags(numeric(r[op & 7]),numeric(r[(op >> 3) & 7]))
            elif op & 0xf800 == 0x0000:
                r[op & 7] = words._constant((numeric(r[(op >> 3) & 7]) << ((op >> 6) & 31)) & 0xffffffff)
                comparison = None
            elif op & 0xf800 == 0x3000:
                reg = (op >> 8) & 7
                r[reg] = add(r[reg],op & 255)
                comparison = None
            elif op & 0xf000 == 0xd000 and (op >> 8) & 15 < 14:
                if flags._condition((op >> 8) & 15,comparison):
                    delta = (op & 255)*2
                    nxt = pc+4+(delta-512 if delta & 256 else delta)
            elif op & 0xf800 == 0xe000:
                delta = (op & 2047)*2
                nxt = pc+4+(delta-4096 if delta & 2048 else delta)
            elif op & 0xf800 == 0x4800:
                pool = ((pc+4)&~3)+4*(op & 255)
                if not cb <= pool <= cb+len(layout.body)-4:
                    stop('literal read leaves complete callback owner')
                value = int.from_bytes(layout.body[pool-cb:pool-cb+4],'little')
                r[(op >> 8) & 7] = words._constant(value)
                events.append(dict(site=pc,operation='literal32',address=pool,value=value))
            elif op & 0xf000 == 0x6000:
                reg = op & 7
                at = address(r[(op >> 3) & 7])+4*((op >> 6) & 31)
                if op & 0x0800:
                    r[reg] = load(at,4)
                else:
                    store(at,r[reg])
            elif op & 0xf800 == 0x8800:
                at = address(r[(op >> 3) & 7])+2*((op >> 6) & 31)
                r[op & 7] = load(at,2)
                if offset == 14:
                    phase_bytes = r[4][:2]
                    phase = sum(v << (8*i) for i,v in enumerate(phase_bytes)) if all(type(v) is int for v in phase_bytes) else None
            elif op & 0xf800 == 0x7000:
                at = address(r[(op >> 3) & 7])+((op >> 6) & 31)
                store(at,r[op & 7][:1])
            else:
                stop('unsupported callback prefix encoding',encoding=op)
            pc = nxt
        else:
            stop('explicit callback step bound exhausted')
    except state.remove._Boundary as error:
        boundary = error.report
    return dict(schema=SELECTOR,complete_owner_pins=_pins(owners),starts_at=layout.scheduler.callback_thunk,
        callback_entry_reached=entered,reaches_memcpy_boundary=reached,boundary=boundary,pending_call=pending,
        final_PC=pc,trace=trace,memory_events=events,registers=r,post_cells={str(k):v for k,v in sorted(m.items())},
        changed_cells={str(k):m[k] for k in sorted(changed)},observed_phase=phase,observed_phase_bytes=phase_bytes,
        callback_entry_SP=entry_sp,frame_bytes=64,stack_activations=activations,retired_spans=retired,
        actual_reaching_state_proved=False,actual_installed_identity_proved=False,physical_access_proved=False,
        actual_lifetime_proved=False,actual_termination_proved=False,callback_effects_closed=False,
        full_CFG_closed=False,source_or_native_admission=False,
        obligations=[dict(id=k,proved=False,text=t) for k,t in (
            ('reaching','All supplied register and byte origins equal actual reaching callback state. Complete source hashes do not prove execution.'),
            ('memory','Every observed field/save/local access is live ordinary memory with access permission, complete caller protection and no asynchronous interference. Numeric checks do not establish those premises.'),
            ('frames','Only explicitly reusable retired frames can be reactivated by actual stack allocation. No heap extent, fresh initialization or unavailable-payload lifetime follows.'),
            ('copy','The pending copy needs its actual code, arguments, source and destination access/alias effects, return and saved-origin protection before execution can continue.'),
            ('continuation','Other phases, subsequent helper calls, saved-register restoration, frame retirement and parent continuation remain open.'))])


def continue_from_copy(layout, arena_base, initial_cells, report, *, selector, protected_spans=(),
                       retired_spans=(), reusable_frame_spans=(), unavailable_spans=(), max_steps=128):
    """Consume one conditional copy result without replaying its producer.

    Report/interface checks do not authenticate actual reaching state. Old
    allocator private bytes are forgotten before real callback frame reuse.
    """
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit callback702 selector required')
    _validate(layout)
    c = layout.scheduler
    if type(report) is not dict or report.get('schema') != words.SELECTOR or \
            report.get('bodies') != dict(scheduler=c.sha256,copy=hashlib.sha256(words.COPY).hexdigest()) or \
            report.get('reaches_callback_thunk') is not True or report.get('boundary') is not None or \
            report.get('callback_site') != c.address+180 or report.get('callback_thunk') != c.callback_thunk:
        raise ValueError('successful exact scheduler-copy interface required')
    p, r = report.get('prefix'), report.get('callback_registers')
    if type(p) is not dict or p.get('schema') != state.SELECTOR or p.get('count') != 112 or \
            p.get('reaches_copy_cutpoint') is not True or p.get('boundary') is not None or \
            type(r) is not dict or set(r) != set(range(15)) or any(type(k) is not int or
                not words._word(v) for k,v in r.items()):
        raise ValueError('complete count112 prefix and callback register origins required')
    e = p.get('frame',{}).get('entry_SP_coordinate')
    node = p.get('allocation')
    if type(e) is not int or e % 4 or type(node) is not int or node % 4 or \
            report.get('descriptor_local') != e-56 or \
            any(r[k] != value for k,value in {0:words._pointer(node),1:words._pointer(e-56),
                2:words._pointer(node+24),13:words._pointer(e-56),14:words._constant((c.address+184)|1)}.items()) or \
            report.get('observed_callback_word') != r[3] or not any(
                v.get('operation') == 'conditional-installed-zero112' and v.get('count') == 112
                and v.get('receipt_sha256') == state.ZERO112_SHA256 and v.get('destination') == node
                for v in p.get('memory_events',[])):
        raise ValueError('count112 frame, allocation, return or direct-zero interface changed')
    if type(initial_cells) is not dict or len(initial_cells) > 4096 or any(type(k) is not int or
            not -(2**31) <= k < 2**31 or not state._cell(v) for k,v in initial_cells.items()):
        raise ValueError('complete bounded pre-copy cell state required')
    if not all(_spans(v) for v in (protected_spans,retired_spans,reusable_frame_spans,unavailable_spans)):
        raise ValueError('bounded explicit protection/lifetime intervals required')
    m = dict(initial_cells)
    for changes in (p.get('changed_cells'),report.get('changed_cells')):
        if type(changes) is not dict:
            raise ValueError('exact prefix/copy changed-cell maps required')
        for key,value in changes.items():
            try:
                at = int(key)
            except (ValueError,TypeError) as error:
                raise ValueError('canonical changed-cell coordinates required') from error
            if type(key) is not str or key != str(at) or not -(2**31) <= at < 2**31 or not state._cell(value):
                raise ValueError('bounded exact changed-cell origins required')
            m[at] = value
    if tuple(m.get(node+i) for i in range(4)) != r[3] or \
            tuple(m.get(e-56+i) for i in range(28)) != report.get('descriptor_bytes'):
        raise ValueError('actual reloaded callback or local descriptor bytes differ')
    lo,hi = e-132,e-56
    names = {v[1] for v in [*m.values(),*(v for w in r.values() for v in w)]
             if type(v) is tuple and v[0] == 'opaque-byte'}
    name,n = 'unmodeled count112 allocator',0
    while name in names:
        n += 1
        name = 'unmodeled count112 allocator:'+str(n)
    for at in range(lo,hi):
        m[at] = ('opaque-byte',name,at-lo)
    result = derive(layout,arena_base,m,r,selector=selector,protected_spans=protected_spans,
        retired_spans=retired_spans+((lo,hi),),reusable_frame_spans=reusable_frame_spans+((lo,hi),),
        unavailable_spans=unavailable_spans,max_steps=max_steps)
    result['forgotten_allocator_private_span'] = [lo,hi]
    result['input_copy_schema'] = report['schema']
    result['inherited_copy_obligations'] = report.get('obligations',[])
    result['inherited_allocator_obligations'] = p.get('obligations',[])
    result['actual_prior_report_authentication_proved'] = False
    return result
