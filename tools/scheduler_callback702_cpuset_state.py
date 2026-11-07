"""Conditional CpuSet transfer and the callback702 instructions after return.

The four-byte SWI wrapper identifies a BIOS boundary, not its implementation.
Copy behavior, ordinary return, saved-register preservation and memory access
remain explicit premises. This relation stops before the next helper call.
"""
from dataclasses import dataclass

import bios_cpuset_fill_profile as bios
import scheduler_callback702_state as prefix

SELECTOR = 'conditional-scheduler-callback702-cpuset-continuation-v1'
CONTRACT = 'conditional-bios-cpuset-16-halfwords-copy-return-v1'
CPUSET = bios.ADDRESS
SOURCE = 0x03003920
HELPER = 0x080E03F8
COUNT = 32
words = prefix.words


@dataclass(frozen=True)
class Layout:
    prefix: prefix.Layout
    wrapper: bytes


def _validate(layout):
    if type(layout) is not Layout or type(layout.wrapper) is not bytes or layout.wrapper != bios.WRAPPER:
        raise ValueError('complete exact SWI0B/BX LR CpuSet wrapper required')
    owners = prefix._validate(layout.prefix)
    if any(a < CPUSET+4 and a+len(b) > CPUSET for a,b in owners.items()):
        raise ValueError('CpuSet wrapper overlaps another complete owner')
    cb = layout.prefix.callback
    if layout.prefix.body[138:142] != prefix.state.remove._bl(cb+138,HELPER):
        raise ValueError('actual callback helper target changed')
    return owners | {CPUSET:layout.wrapper}


def bind(callback_layout, wrapper, address, *, selector):
    if type(selector) is not str or selector != SELECTOR or type(address) is not int or address != CPUSET:
        raise ValueError('explicit CpuSet continuation selector and exact wrapper address required')
    result = Layout(callback_layout,wrapper)
    _validate(result)
    return result


def derive(layout, arena_base, cells, registers, *, selector, cpuset_contract,
           source_coordinate, protected_spans=(), retired_spans=(), unavailable_spans=(), max_steps=7):
    """Relate a NEW state at callback+120 to the next helper boundary.

The explicit contract assumes a 16-halfword BIOS copy, ordinary return with
R4..R11/SP preserved and no other memory effects. R0..R3/R12/LR become unknown.
Provided bytes and common-base coordinates do not prove physical access. Only
disjoint source/destination or exact self-copy is supported; transfer ordering
for other overlap is deliberately unproved. BIOS access order is not traced.
"""
    if type(selector) is not str or selector != SELECTOR or type(cpuset_contract) is not str or cpuset_contract != CONTRACT:
        raise ValueError('explicit continuation selector and conditional BIOS copy/return contract required')
    owners = _validate(layout)
    if type(arena_base) is not int or arena_base % 4 or not 0 <= arena_base < 2**32 or \
            type(source_coordinate) is not int or not -(2**31) <= source_coordinate < 2**31 or \
            type(cells) is not dict or len(cells) > 4096 or any(type(k) is not int or
                not -(2**31) <= k < 2**31 or not prefix.state._cell(v) for k,v in cells.items()) or \
            type(registers) is not dict or set(registers) != set(range(15)) or any(
                type(k) is not int or not words._word(v) for k,v in registers.items()) or \
            type(max_steps) is not int or not 1 <= max_steps <= 7:
        raise ValueError('bounded common-base cells, source coordinate and all register origins required')
    if not all(prefix._spans(v) for v in (protected_spans,retired_spans,unavailable_spans)):
        raise ValueError('bounded explicit protection/lifetime intervals required')
    cb = layout.prefix.callback
    pc, r, m = cb+120, dict(registers), dict(cells)
    trace, events, changed = [], [], set()
    boundary = pending = source_bytes = None
    copied = reached = False
    destination = None

    def stop(reason, at=None):
        raise prefix.state.remove._Boundary(pc,reason,at)

    def address(word):
        observed = words.observe(word)
        if observed['kind'] != 'base-plus':
            stop('address lacks intact common-base provenance')
        return observed['coordinate']

    def guard(at,width,*,write=False,alignment=4):
        if not -(2**31) <= at <= 2**31-width or not 0 <= arena_base+at <= 2**32-width:
            stop('common-base access wraps',at)
        if at % alignment:
            stop('unaligned common-byte access',at)
        if any(at < hi and at+width > lo for lo,hi in unavailable_spans):
            stop('access intersects unavailable bytes',at)
        if any(at < hi and at+width > lo for lo,hi in retired_spans):
            stop('access intersects retired bytes',at)
        if write and any(at < hi and at+width > lo for lo,hi in protected_spans):
            stop('actual write intersects protected bytes',at)
        if write and any(arena_base+at < a+len(b) and arena_base+at+width > a for a,b in owners.items()):
            stop('actual write intersects immutable complete owner',at)

    def load(at):
        guard(at,4)
        value = tuple(m.get(at+i) for i in range(4))
        if any(v is None for v in value):
            stop('read lacks reaching byte origins',at)
        events.append(dict(site=pc,operation='read32',coordinate=at,bytes=value))
        return value

    def store(at,value):
        guard(at,len(value),write=True)
        if len(set(m) | set(range(at,at+len(value)))) > 4096:
            stop('byte state exceeds4096 cells',at)
        m.update({at+i:v for i,v in enumerate(value)})
        changed.update(range(at,at+len(value)))
        events.append(dict(site=pc,operation='write32',coordinate=at,bytes=value))

    try:
        if registers[0] != words._constant(SOURCE) or arena_base+source_coordinate != SOURCE:
            stop('source literal and explicit common-base source coordinate differ')
        if registers[2] != words._constant(16) or registers[4] != words._constant(0):
            stop('actual phase-zero CpuSet control or R4 origin differs')
        destination = address(r[1])
        if destination != address(r[6])+16:
            stop('destination is not actual payload plus16',destination)
        guard(source_coordinate,COUNT,alignment=2)
        guard(destination,COUNT,write=True,alignment=2)
        if source_coordinate != destination and max(source_coordinate,destination) < min(source_coordinate+COUNT,destination+COUNT):
            stop('overlapping CpuSet transfer order is unproved',destination)
        source_bytes = tuple(m.get(source_coordinate+i) for i in range(COUNT))
        if any(v is None for v in source_bytes):
            stop('CpuSet source lacks all32 reaching byte origins',source_coordinate)
        if len(set(m) | set(range(destination,destination+COUNT))) > 4096:
            stop('byte state exceeds4096 cells',destination)
        # These are an assumed external relation, not decoded BIOS accesses.
        m.update({destination+i:v for i,v in enumerate(source_bytes)})
        changed.update(range(destination,destination+COUNT))
        events.append(dict(site=pc,operation='conditional-bios-cpuset-copy',source=source_coordinate,
            destination=destination,units=16,width=2,count=COUNT,bytes=source_bytes,
            exact_self_copy=source_coordinate==destination,contract=CONTRACT,
            actual_BIOS_effects_proved=False,BIOS_access_order_inferred=False))
        names = {v[1] for v in [*m.values(),*(v for w in r.values() for v in w)]
                 if type(v) is tuple and v[0] == 'opaque-byte'}
        namespace, generation = 'conditional CpuSet clobbers',0
        while namespace in names:
            generation += 1
            namespace = 'conditional CpuSet clobbers:'+str(generation)
        for reg in (0,1,2,3,12,14):
            r[reg] = tuple(('opaque-byte',namespace,4*reg+i) for i in range(4))
        copied = True
        trace.append(pc)
        pc = cb+124
        for _ in range(max_steps):
            offset = pc-cb
            trace.append(pc)
            op = int.from_bytes(layout.prefix.body[offset:offset+2],'little')
            if op & 0xf800 == 0x6800:
                r[op & 7] = load(address(r[(op >> 3) & 7])+4*((op >> 6) & 31))
            elif op & 0xf800 == 0x4800:
                pool = ((pc+4)&~3)+4*(op & 255)
                value = int.from_bytes(layout.prefix.body[pool-cb:pool-cb+4],'little')
                r[(op >> 8) & 7] = words._constant(value)
                events.append(dict(site=pc,operation='literal32',address=pool,value=value))
            elif op & 0xf800 == 0x9000:
                store(address(r[13])+4*(op & 255),r[(op >> 8) & 7])
            elif op & 0xff00 == 0x4600:
                r[(op & 7) | ((op >> 4) & 8)] = r[(op >> 3) & 15]
            elif op & 0xf800 == 0x2000:
                r[(op >> 8) & 7] = words._constant(op & 255)
            else:
                stop('unsupported post-CpuSet callback encoding')
            pc += 2
            if pc == cb+138:
                reached = True
                sp = address(r[13])
                pending = dict(site=pc,target=HELPER,register_arguments={i:r[i] for i in range(4)},
                    stack_argument_bytes={i:tuple(m[sp+i+j] for j in range(4)) for i in (0,4)},
                    SP=r[13],LR=r[14],callee_executed=False)
                stop('unproved helper call with actual R2equal2',pc)
        stop('explicit post-CpuSet step bound exhausted')
    except prefix.state.remove._Boundary as error:
        boundary = error.report
    return dict(schema=SELECTOR,complete_owner_pins=prefix._pins(owners),starts_at=cb+120,
        CpuSet_wrapper=CPUSET,CpuSet_contract=CONTRACT,source_coordinate=source_coordinate,
        destination_coordinate=destination,transfer_bytes=COUNT,conditional_copy_applied=copied,
        reaches_helper_boundary=reached,boundary=boundary,pending_call=pending,final_PC=pc,
        trace=trace,memory_events=events,registers=r,
        post_cells={str(k):v for k,v in sorted(m.items())},
        changed_cells={str(k):m[k] for k in sorted(changed)},
        retired_spans=retired_spans,actual_reaching_state_proved=False,
        actual_BIOS_effects_proved=False,actual_BIOS_return_proved=False,
        actual_ABI_preservation_proved=False,physical_access_proved=False,
        actual_lifetime_proved=False,actual_termination_proved=False,
        callback_effects_closed=False,full_CFG_closed=False,source_or_native_admission=False,
        obligations=[dict(id=k,proved=False,text=t) for k,t in (
            ('reaching','Supplied origins describe the actual state at callback+120.'),
            ('BIOS','The BIOS performs the assumed16-halfword copy and no other memory effects. Wrapper bytes do not prove its implementation or access order.'),
            ('return','CpuSet returns to callback+124 and preserves R4..R11/SP under the explicit ordinary ABI premise.'),
            ('memory','Every observed source, destination, field and stack access has live physical permission with no asynchronous interference; provided origins and numeric checks do not prove this.'),
            ('continuation','The next helper has actual R2equal2. Its effects, return, callback restoration and remaining scheduler continuation are unproved.'))])


def continue_from_prefix(layout, arena_base, report, *, selector, cpuset_contract,
                         source_coordinate, protected_spans=(), unavailable_spans=(), max_steps=7):
    """Consume the retained prefix interface without replaying its producer.

The historical prefix schema calls this boundary memcpy. Its exact target is
checked as CpuSet here; the old label grants no copy effects or authentication.
"""
    _validate(layout)
    cb = layout.prefix.callback
    if type(report) is not dict or report.get('schema') != prefix.SELECTOR or \
            report.get('complete_owner_pins') != prefix._pins(prefix._validate(layout.prefix)) or \
            report.get('starts_at') != layout.prefix.scheduler.callback_thunk or \
            report.get('callback_entry_reached') is not True or \
            report.get('reaches_memcpy_boundary') is not True or report.get('final_PC') != cb+120 or \
            type(report.get('observed_phase')) is not int or report.get('observed_phase') != 0 or \
            report.get('observed_phase_bytes') != (0,0) or \
            report.get('frame_bytes') != 64 or type(report.get('boundary')) is not dict or \
            report['boundary'].get('site') != cb+120:
        raise ValueError('exact successful callback prefix boundary required')
    r, call = report.get('registers'),report.get('pending_call')
    e, cells = report.get('callback_entry_SP'),report.get('post_cells')
    if type(r) is not dict or set(r) != set(range(15)) or any(type(k) is not int or
            not words._word(v) for k,v in r.items()) or type(e) is not int or e % 4 or \
            r[13] != words._pointer(e-64) or type(call) is not dict or \
            call != dict(site=cb+120,target=CPUSET,register_arguments={i:r[i] for i in range(4)},
                SP=r[13],LR=r[14],callee_executed=False) or type(cells) is not dict or len(cells) > 4096:
        raise ValueError('complete count32 CpuSet arguments, actual frame and post-prefix cells required')
    m = {}
    for key,value in cells.items():
        try:
            at = int(key)
        except (ValueError,TypeError) as error:
            raise ValueError('canonical post-prefix byte coordinates required') from error
        if type(key) is not str or key != str(at):
            raise ValueError('canonical post-prefix byte coordinates required')
        m[at] = value
    result = derive(layout,arena_base,m,r,selector=selector,cpuset_contract=cpuset_contract,
        source_coordinate=source_coordinate,protected_spans=protected_spans,
        retired_spans=tuple(report.get('retired_spans',())),unavailable_spans=unavailable_spans,max_steps=max_steps)
    result['input_prefix_schema'] = prefix.SELECTOR
    result['legacy_boundary_label_corrected'] = 'BIOS CpuSet SWI0B,16halfwords/32bytes'
    result['inherited_prefix_obligations'] = report.get('obligations',[])
    result['actual_prior_report_authentication_proved'] = False
    return result
