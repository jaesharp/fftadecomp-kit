"""Actual helper stack and masked byte effects for callback702's R2=2 call.

The relation executes the real caller BL, saves and nonzero/default path. It
stops before the nested scheduler call. Missing local bytes become distinct
unknown origins, never initialized values. Physical access remains a premise.
"""
from dataclasses import dataclass
import hashlib

import scheduler_callback702_cpuset_state as cpuset

SELECTOR = 'conditional-scheduler-helper2-default-state-v1'
ADDRESS = 0x080E03F8
BODY_SHA256 = '9d2304e0e45bcd0d4859bc63bcfbdb768d12e8c02ed94d0eb2f84f960898367a'
GLOBAL = 0x0200F430
SCHEDULER = 0x08005954
OFFSETS = frozenset(range(0,22,2)) | frozenset(range(30,60,2)) | frozenset(range(250,266,2))
words = cpuset.words
prefix = cpuset.prefix


@dataclass(frozen=True)
class Layout:
    prior: cpuset.Layout
    helper: int
    body: bytes


def _validate(layout):
    if type(layout) is not Layout or type(layout.helper) is not int or layout.helper != ADDRESS or \
            type(layout.body) is not bytes or len(layout.body) != 292 or \
            hashlib.sha256(layout.body).hexdigest() != BODY_SHA256:
        raise ValueError('complete exact292B helper identity required')
    owners = cpuset._validate(layout.prior)
    if layout.prior.prefix.scheduler.address != SCHEDULER or \
            layout.body[266:270] != prefix.state.remove._bl(ADDRESS+266,SCHEDULER):
        raise ValueError('nested call must identify the retained scheduler owner')
    if any(a < ADDRESS+292 and a+len(b) > ADDRESS for a,b in owners.items()):
        raise ValueError('complete helper overlaps another owner')
    return owners | {ADDRESS:layout.body}


def bind(prior, body, address, *, selector):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit helper2 state selector required')
    result = Layout(prior,address,body)
    _validate(result)
    return result


def derive(layout, arena_base, cells, registers, *, selector, global_coordinate,
           protected_spans=(), retired_spans=(), reusable_frame_spans=(), unavailable_spans=(), max_steps=64):
    """Execute a NEW state from the callback BL through helper+264.

Only R2=2/R3=7 is modeled. The global literal needs an explicit common-base
coordinate and reaching bytes. Stack reuse requires explicit authorization;
SUB SP neither clears memory nor proves its lifetime. No callee is summarized.
"""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit helper2 state selector required')
    owners = _validate(layout)
    if type(arena_base) is not int or arena_base % 4 or not 0 <= arena_base < 2**32 or \
            type(global_coordinate) is not int or not -(2**31) <= global_coordinate < 2**31 or \
            arena_base+global_coordinate != GLOBAL or \
            type(cells) is not dict or len(cells) > 4096 or any(type(k) is not int or
                not -(2**31) <= k < 2**31 or not prefix.state._cell(v) for k,v in cells.items()) or \
            type(registers) is not dict or set(registers) != set(range(15)) or any(
                type(k) is not int or not words._word(v) for k,v in registers.items()) or \
            type(max_steps) is not int or not 1 <= max_steps <= 64:
        raise ValueError('bounded common-base origins, exact global coordinate and all registers required')
    if not all(prefix._spans(v) for v in (protected_spans,retired_spans,reusable_frame_spans,unavailable_spans)):
        raise ValueError('bounded explicit protection/lifetime intervals required')
    cb, h = layout.prior.prefix.callback,layout.helper
    pc, r, m = cb+138,dict(registers),dict(cells)
    retired = list(retired_spans)
    trace, events, activations, changed = [],[],[],set()
    boundary = pending = entry_sp = descriptor = None
    entered = reached = False
    comparison = None

    def stop(reason, at=None):
        raise prefix.state.remove._Boundary(pc,reason,at)

    def address(word):
        value = words.observe(word)
        if value['kind'] != 'base-plus':
            stop('address lacks intact common-base provenance')
        return value['coordinate']

    def number(word):
        value = words.observe(word)
        if value['kind'] != 'constant':
            stop('scalar observation has opaque or pointer origins')
        return value['value']

    def guard(at,width,*,write=False,allocating=False):
        if not -(2**31) <= at <= 2**31-width or not 0 <= arena_base+at <= 2**32-width:
            stop('common-base access or frame allocation wraps',at)
        if at % 4 or width % 4:
            stop('unaligned word access or stack allocation',at)
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

    def allocate(lo,hi,*,local=False):
        nonlocal retired
        guard(lo,hi-lo,allocating=True)
        for a,b in retired:
            start,end = max(a,lo),min(b,hi)
            if start < end and not covered(start,end):
                stop('stack allocation intersects nonreusable retired bytes',start)
        if local and len(set(m) | set(range(lo,hi))) > 4096:
            stop('local byte state exceeds4096 cells',lo)
        retired = [v for a,b in retired for v in ((a,min(b,lo)),(max(a,hi),b)) if v[0] < v[1]]
        activations.append(dict(site=pc,coordinates=[lo,hi],initialization_granted=False))
        if local:
            names = {v[1] for v in [*m.values(),*(v for w in r.values() for v in w)]
                     if type(v) is tuple and v[0] == 'opaque-byte'}
            namespace, generation = 'helper2 local',0
            while namespace in names:
                generation += 1
                namespace = 'helper2 local:'+str(generation)
            for at in range(lo,hi):
                m.setdefault(at,('opaque-byte',namespace,at-lo))
            events.append(dict(site=pc,operation='allocate-frame',coordinates=[lo,hi],initialization_granted=False))

    def load(at):
        guard(at,4)
        value = tuple(m.get(at+i) for i in range(4))
        if any(v is None for v in value):
            stop('read lacks reaching byte origins',at)
        events.append(dict(site=pc,operation='read32',coordinate=at,bytes=value))
        return value

    def store(at,value):
        guard(at,4,write=True)
        if len(set(m) | set(range(at,at+4))) > 4096:
            stop('byte state exceeds4096 cells',at)
        m.update({at+i:v for i,v in enumerate(value)})
        changed.update(range(at,at+4))
        events.append(dict(site=pc,operation='write32',coordinate=at,bytes=value))

    def masked(a,b,disjunction):
        if type(a) is int and type(b) is int:
            return a | b if disjunction else a & b
        if disjunction:
            if a == 255 or b == 255:
                return 255
            if a == 0:
                return b
            if b == 0:
                return a
        else:
            if a == 0 or b == 0:
                return 0
            if a == 255:
                return b
            if b == 255:
                return a
        if a == b:
            return a
        stop('bitwise operation would inspect unknown bits')

    try:
        if r[2] != words._constant(2) or r[3] != words._constant(7) or r[1] != words._constant(0x0839D7E4):
            stop('actual callback R2equal2/R3equal7 or descriptor argument differs')
        for _ in range(max_steps):
            if pc == cb+138:
                trace.append(pc)
                r[14] = words._constant((pc+4)|1)
                events.append(dict(site=pc,operation='direct-call',target=h))
                entered = True
                pc = h
                continue
            if pc == h+266:
                reached = True
                sp = address(r[13])
                descriptor = tuple(m[sp+4+i] for i in range(28))
                pending = dict(site=pc,target=SCHEDULER,register_arguments={i:r[i] for i in range(4)},
                    stack_argument_bytes={i:tuple(m[sp+i+j] for j in range(4)) for i in (0,8)},
                    SP=r[13],LR=r[14],callee_executed=False)
                stop('unproved nested scheduler call')
            offset = pc-h
            if offset not in OFFSETS:
                stop('control leaves the explicit helper2 default path')
            trace.append(pc)
            op = int.from_bytes(layout.body[offset:offset+2],'little')
            nxt = pc+2
            if op & 0xfe00 == 0xb400:
                selected = [i for i in range(8) if op >> i & 1]+([14] if op & 0x100 else [])
                entry_sp = address(r[13])
                lo = entry_sp-4*len(selected)
                guard(lo,entry_sp-lo,write=True,allocating=True)
                allocate(lo,entry_sp)
                for i,reg in enumerate(selected):
                    store(lo+4*i,r[reg])
                r[13] = words._pointer(lo)
            elif op & 0xff80 == 0xb080:
                top = address(r[13]);lo = top-4*(op & 127)
                allocate(lo,top,local=True)
                r[13] = words._pointer(lo)
            elif op & 0xfe00 == 0x1c00 and (op >> 6) & 7 == 0:
                r[op & 7] = r[(op >> 3) & 7]
                comparison = None
            elif op & 0xf800 == 0x9800:
                r[(op >> 8) & 7] = load(address(r[13])+4*(op & 255))
            elif op & 0xf800 in (0x0000,0x0800):
                value,shift = number(r[(op >> 3) & 7]),(op >> 6) & 31
                value = value << shift if op & 0xf800 == 0 else value >> (shift or 32)
                r[op & 7] = words._constant(value & 0xffffffff)
                comparison = None
            elif op & 0xf800 == 0x2800:
                comparison = prefix.flags._sub_flags(number(r[(op >> 8) & 7]),op & 255)
            elif op & 0xf000 == 0xd000 and (op >> 8) & 15 < 14:
                if prefix.flags._condition((op >> 8) & 15,comparison):
                    delta = (op & 255)*2
                    nxt = pc+4+(delta-512 if delta & 256 else delta)
            elif op & 0xf800 == 0x4800:
                pool = ((pc+4)&~3)+4*(op & 255)
                value = int.from_bytes(layout.body[pool-h:pool-h+4],'little')
                r[(op >> 8) & 7] = words._constant(value)
                events.append(dict(site=pc,operation='literal32',address=pool,value=value))
            elif op & 0xffc0 in (0x4000,0x4300):
                dst,src = op & 7,(op >> 3) & 7
                r[dst] = tuple(masked(a,b,op & 0xffc0 == 0x4300) for a,b in zip(r[dst],r[src]))
                comparison = None
            elif op & 0xf800 == 0x9000:
                store(address(r[13])+4*(op & 255),r[(op >> 8) & 7])
            elif op & 0xf800 == 0xa800:
                at = address(r[13])+4*(op & 255)
                if not -(2**31) <= at < 2**31 or not 0 <= arena_base+at < 2**32:
                    stop('stack-relative pointer arithmetic wraps',at)
                r[(op >> 8) & 7] = words._pointer(at)
            elif op & 0xf000 == 0x6000:
                reg,base = op & 7,r[(op >> 3) & 7]
                if offset == 254 and base == words._constant(GLOBAL):
                    at = global_coordinate
                else:
                    at = address(base)+4*((op >> 6) & 31)
                if op & 0x0800:
                    r[reg] = load(at)
                else:
                    store(at,r[reg])
            elif op & 0xf800 == 0x2000:
                r[(op >> 8) & 7] = words._constant(op & 255)
                comparison = None
            else:
                stop('unsupported helper2 path encoding')
            pc = nxt
        stop('explicit helper2 step bound exhausted')
    except prefix.state.remove._Boundary as error:
        boundary = error.report
    return dict(schema=SELECTOR,complete_owner_pins=prefix._pins(owners),starts_at=cb+138,
        helper_entry_reached=entered,helper_entry_SP=entry_sp,private_frame_bytes=72,
        reaches_scheduler_boundary=reached,boundary=boundary,pending_call=pending,descriptor_bytes=descriptor,
        final_PC=pc,trace=trace,memory_events=events,registers=r,
        post_cells={str(k):v for k,v in sorted(m.items())},
        changed_cells={str(k):m[k] for k in sorted(changed)},
        stack_activations=activations,retired_spans=retired,
        actual_reaching_state_proved=False,physical_access_proved=False,actual_lifetime_proved=False,
        actual_termination_proved=False,helper_effects_closed=False,full_CFG_closed=False,
        source_or_native_admission=False,
        obligations=[dict(id=k,proved=False,text=t) for k,t in (
            ('reaching','Supplied registers and byte origins equal actual state at the callback BL.'),
            ('memory','All observed stack and global accesses are live ordinary memory with physical permission and no asynchronous interference. Numeric bindings do not establish this.'),
            ('frames','Only explicit retired-frame reuse can reactivate bytes; allocation does not initialize them or prove actual frame ownership.'),
            ('scheduler','The nested scheduler call needs actual global, descriptor, allocator and callback composition. Its return and later helper/callback restoration remain open.'))])


def continue_from_cpuset(layout, arena_base, report, *, selector, global_coordinate,
                         protected_spans=(), reusable_frame_spans=(), unavailable_spans=(), max_steps=64):
    """Consume a conditional CpuSet report without rerunning its producer."""
    _validate(layout)
    cb = layout.prior.prefix.callback
    if type(report) is not dict or report.get('schema') != cpuset.SELECTOR or \
            report.get('complete_owner_pins') != prefix._pins(cpuset._validate(layout.prior)) or \
            report.get('conditional_copy_applied') is not True or report.get('transfer_bytes') != 32 or \
            report.get('CpuSet_contract') != cpuset.CONTRACT or report.get('reaches_helper_boundary') is not True or \
            report.get('final_PC') != cb+138 or type(report.get('boundary')) is not dict or \
            report['boundary'].get('site') != cb+138:
        raise ValueError('exact successful CpuSet helper-boundary interface required')
    r,call,cells = report.get('registers'),report.get('pending_call'),report.get('post_cells')
    if type(r) is not dict or set(r) != set(range(15)) or any(type(k) is not int or
            not words._word(v) for k,v in r.items()) or type(cells) is not dict or len(cells) > 4096:
        raise ValueError('complete conditional helper register and byte origins required')
    sp = words.observe(r[13])
    if sp['kind'] != 'base-plus':
        raise ValueError('intact helper entry SP required')
    m = {}
    for key,value in cells.items():
        try:
            at = int(key)
        except (ValueError,TypeError) as error:
            raise ValueError('canonical post-CpuSet byte coordinates required') from error
        if type(key) is not str or key != str(at):
            raise ValueError('canonical post-CpuSet byte coordinates required')
        m[at] = value
    if call != dict(site=cb+138,target=ADDRESS,register_arguments={i:r[i] for i in range(4)},
            stack_argument_bytes={i:tuple(m.get(sp['coordinate']+i+j) for j in range(4)) for i in (0,4)},
            SP=r[13],LR=r[14],callee_executed=False):
        raise ValueError('actual helper call arguments or stack words differ')
    retired = report.get('retired_spans')
    if type(retired) not in (tuple,list) or not prefix._spans(tuple(retired)):
        raise ValueError('explicit bounded retired spans required')
    result = derive(layout,arena_base,m,r,selector=selector,global_coordinate=global_coordinate,
        protected_spans=protected_spans,retired_spans=tuple(retired),
        reusable_frame_spans=reusable_frame_spans,unavailable_spans=unavailable_spans,max_steps=max_steps)
    result['input_CpuSet_schema'] = cpuset.SELECTOR
    result['inherited_CpuSet_obligations'] = report.get('obligations',[])
    result['actual_prior_report_authentication_proved'] = False
    return result
