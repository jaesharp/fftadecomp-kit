"""Conditional selected request path through the scheduler and real epilogue.

One incoming byte state feeds every component. The final stores and POPs read
that same state in instruction order, including aliases of saved words. This
does not establish actual entry, physical access, code execution or admission.
"""
from dataclasses import dataclass

import scheduler_request_entry_state as entry
import scheduler_whole_state as whole
import scheduler_copy_state as words
import scheduler_allocator_state as atoms

SELECTOR = 'conditional-scheduler-request-whole-state-v1'
TAIL_HEAD = bytes.fromhex('e060288801300fe0')
TAIL_END = bytes.fromhex('2880002009b070bc02bc0847')


@dataclass(frozen=True)
class Layout:
    root: entry.Layout
    chain: whole.Layout


def _validate(layout):
    if type(layout) is not Layout:
        raise ValueError('complete request and whole scheduler layouts required')
    entry._validate(layout.root)
    whole._validate(layout.chain)
    root, chain = layout.root, layout.chain
    if root.wrapper != chain.outer or root.callback != chain.effect:
        raise ValueError('root call and callback must identify the same retained chain')
    if root.data[178:186] != TAIL_HEAD or root.data[218:230] != TAIL_END:
        raise ValueError('selected postcall stores, branch or actual epilogue differ')
    callee = chain.outer.callee
    allocator = callee.allocator.allocator
    insertion = allocator.insertion
    median = insertion.median
    spans = [(callee.allocator.address, 54), (allocator.address, 266),
             (insertion.address, 150), (insertion.search.address, 174),
             (median.removal, 134), (median.median, 102),
             (allocator.thunk, 2), (callee.callback_thunk, 2)]
    if any(root.address < address+size and root.address+230 > address for address, size in spans):
        raise ValueError('complete request controller overlaps a retained nested code owner')


def bind(root_layout, whole_layout, *, selector):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit request whole-state selector required')
    layout = Layout(root_layout, whole_layout)
    _validate(layout)
    return layout


def derive(layout, arena_base, cells, registers, *, selector, zero12_receipt=None,
           zero92_receipt=None, observed_zero_target=None, protected_spans=(),
           max_links=128, max_search_transitions=256, max_median_links=256):
    """Derive a selected conditional relation from one root entry state.

Retained kernels are invoked once, on the newly reaching state. Their input
and memory guards stay in force. The final BX is a cutpoint: equality with
the incoming LR is reported, while executable return authority stays open.
"""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit request whole-state selector required')
    _validate(layout)
    if type(protected_spans) is not tuple or len(protected_spans) > 24 or any(
            type(p) is not tuple or len(p) != 2 or any(type(n) is not int for n in p) or
            not -(2**31) <= p[0] < p[1] <= 2**31 for p in protected_spans):
        raise ValueError('bounded explicit protection intervals required')
    protected_spans = whole._spans(protected_spans)
    c = layout.root.address
    memory, r, stages, retired, trace, events = {}, None, {}, [], [], []
    boundary = None
    stage = 'root-entry'
    entry_sp = descriptor = phase = stored_phase = None
    continued = reached = returned = descriptor_retired = False
    pc = c

    def at(offset):
        nonlocal pc
        pc = c+offset
        trace.append(pc)

    def stop(reason, coordinate=None):
        raise atoms.remove._Boundary(pc, reason, coordinate)

    def consume(report, key, success):
        nonlocal r, memory
        stages[key] = report
        r = None if report['registers'] is None else dict(report['registers'])
        memory = {int(k):v for k, v in report['post_cells'].items()}
        if not report[success]:
            error = atoms.remove._Boundary(report['boundary']['site'], report['boundary']['reason'],
                                           report['boundary'].get('coordinate'))
            error.report.update(report['boundary'])
            raise error

    def address(word, role):
        observed = words.observe(word)
        if observed['kind'] != 'base-plus':
            stop(role+' lacks intact common-base provenance')
        return observed['coordinate']

    def guard(coordinate, width, writing=False):
        if not -(2**31) <= coordinate <= 2**31-width or coordinate % width or \
                not 0 <= arena_base+coordinate <= 2**32-width:
            stop('access is unaligned or wraps the numeric common base', coordinate)
        if any(coordinate < hi and coordinate+width > lo for lo, hi in retired):
            stop('actual access overlaps retired private bytes', coordinate)
        if writing and any(coordinate < hi and coordinate+width > lo for lo, hi in protected_spans):
            stop('actual write overlaps protected bytes', coordinate)

    def load(coordinate, width):
        guard(coordinate, width)
        value = tuple(memory.get(coordinate+i) for i in range(width))
        if any(v is None for v in value):
            stop('read has missing reaching byte origins', coordinate)
        if width < 4 and any(type(v) is not int for v in value):
            stop('scalar read has opaque or pointer byte origins', coordinate)
        events.append(dict(site=pc, operation='read'+str(width*8), coordinate=coordinate, bytes=value))
        return value

    def store(coordinate, value):
        guard(coordinate, len(value), True)
        memory.update({coordinate+i:v for i, v in enumerate(value)})
        events.append(dict(site=pc, operation='write'+str(len(value)*8), coordinate=coordinate, bytes=value))

    def retire(lo, hi):
        retired.append((lo, hi))
        events.append(dict(site=pc, operation='retire-frame', coordinates=[lo, hi]))

    try:
        first = entry.derive(layout.root, arena_base, cells, registers, selector=entry.SELECTOR,
                             protected_spans=protected_spans)
        entry_sp, descriptor = first['root_entry_SP'], first['descriptor_coordinate']
        consume(first, 'root-entry', 'reaches_wrapper_entry_under_conditions')
        stage = 'whole-wrapper'
        pc = layout.chain.outer.wrapper
        if len(memory) > 4096:
            stop('bounded next-stage byte state exceeds4096 cells')
        nested = whole.derive(layout.chain, arena_base, memory, r, selector=whole.SELECTOR,
            zero12_receipt=zero12_receipt, zero92_receipt=zero92_receipt,
            observed_zero_target=observed_zero_target, protected_spans=protected_spans,
            max_links=max_links, max_search_transitions=max_search_transitions,
            max_median_links=max_median_links)
        retired.extend(tuple(span) for span in nested['retired_spans'])
        consume(nested, 'whole-wrapper', 'reaches_outer_return_thunk')
        stage = 'wrapper-return-control'
        pc = layout.chain.outer.wrapper+54
        expected = words._constant((c+178) | 1)
        if nested['outer_return_word'] != expected or r[1] != expected:
            stop('actual wrapper BX R1 does not identify the selected root continuation')
        if r[13] != words._pointer(entry_sp-52):
            stop('actual wrapper SP does not identify the live root frame')
        events.append(dict(site=pc, operation='conditional-indirect-continuation', target=c+178,
                           target_word=r[1], executable_authority_proved=False))
        continued = True
        stage = 'root-tail'
        at(178); store(address(r[4], 'restored payload R4')+12, r[0])
        at(180); value = load(address(r[5], 'restored request R5'), 2)
        phase = value[0] | value[1] << 8
        r[0] = words._constant(phase)
        at(182); r[0] = words._constant(phase+1)
        at(184)
        events.append(dict(site=pc, operation='branch', target=c+218))
        at(218); store(address(r[5], 'restored request R5'), r[0][:2])
        stored_phase = (phase+1) & 0xffff
        at(220); r[0] = words._constant(0)
        at(222)
        if r[13] != words._pointer(entry_sp-52):
            stop('actual SP differs at root local retirement')
        r[13] = words._pointer(entry_sp-16)
        retire(entry_sp-52, entry_sp-16)
        descriptor_retired = True
        at(224)
        start = address(r[13], 'root POP SP')
        for i, reg in enumerate((4, 5, 6)):
            r[reg] = load(start+4*i, 4)
        r[13] = words._pointer(start+12)
        retire(start, start+12)
        at(226)
        start = address(r[13], 'root return POP SP')
        r[1] = load(start, 4)
        r[13] = words._pointer(start+4)
        retire(start, start+4)
        at(228)
        reached = True
        if r[1] != registers[14]:
            stop('actual popped root BX R1 word differs from incoming LR')
        returned = True
    except atoms.remove._Boundary as error:
        boundary = error.report
    stale = {}
    if r is not None:
        for reg, value in r.items():
            observed = words.observe(value)
            if observed['kind'] == 'base-plus' and any(lo <= observed['coordinate'] < hi for lo, hi in retired):
                stale[str(reg)] = observed['coordinate']
    return dict(schema=SELECTOR, stage=stage, boundary=boundary, stages=stages,
        reaches_selected_root_continuation=continued, reaches_root_return_thunk=reached,
        returns_to_input_continuation_under_conditions=returned, registers=r,
        post_cells={str(k):v for k, v in sorted(memory.items())},
        changed_cells={str(k):v for k, v in sorted(memory.items()) if cells.get(k) != v},
        changed_cells_include_explicit_forgetting=True, tail_trace=trace, tail_memory_events=events,
        root_entry_SP=entry_sp, descriptor_coordinate=descriptor, descriptor_retired=descriptor_retired,
        retired_spans=list(whole._spans(retired)), known_retired_alias_registers=stale,
        phase_observed_after_wrapper=phase, phase_stored=stored_phase,
        observed_return_word=None if not reached else r[1],
        flags_not_modeled=True, fabricated_saved_words=False, role_separation_assumed=False,
        ABI_preservation_assumed=False, descriptor_phase_initialized=False,
        actual_reaching_state_proved=False, actual_heap_or_SP_proved=False, physical_access_proved=False,
        actual_code_execution_proved=False, actual_termination_proved=False,
        actual_return_executed=False, full_scheduler_proved=False, whole_owner_CFG_closed=False,
        source_or_ELF_admission=False, native_admission=False,
        obligations=[dict(id=k, proved=False, text=t) for k, t in (
            ('entry', 'The one supplied root register vector and byte state equal actual live entry origins.'),
            ('components', 'All retained entry, scheduler, allocator, installed image, copy, callback and return conditions hold. No successful conditional kernel supplies an actual heap, SP or execution witness.'),
            ('access', 'All actual accesses have live permitted physical mappings, numeric common-base separation, complete caller/code protections and exclusion of interference.'),
            ('lifetime', 'Retired private bytes remain dead through all subsequent uses and escapes. Root locals are live through the postcall stores, then retire at the actual SP adjustment.'),
            ('control', 'Complete retained code identities are installed and executable. The final observed BX word has justified control authority; equality to incoming LR alone does not grant execution.'),
            ('scope', 'Only the selected phase257 call path is modeled. Other root branches, unhandled helper paths, processor flags and full source/native admission remain open.'),
        )])
