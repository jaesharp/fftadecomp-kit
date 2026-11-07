"""Compose helper2's actual nested scheduler and ordered helper return.

The producer report is consumed, never rerun. Existing count40 kernels execute
the allocator, installed-image assumption, descriptor copy and DFF04 callback
on the same byte map. Conditional execution supplies no whole-owner admission.
"""
from dataclasses import dataclass

import scheduler_helper2_state as helper
import scheduler_zero40_state as zero

SELECTOR = 'conditional-helper2-nested-scheduler-state-v1'
words = helper.words
small = zero.small


@dataclass(frozen=True)
class Layout:
    helper: helper.Layout
    nested: zero.Layout


def _validate(layout):
    if type(layout) is not Layout:
        raise ValueError('complete helper2 and nested count40 layouts required')
    owners = helper._validate(layout.helper)
    child = zero._validate(layout.nested)
    prior = layout.nested.prior
    if prior.scheduler != layout.helper.prior.prefix.scheduler or \
            prior.coordinate.helper.helper != layout.helper.helper or \
            prior.coordinate.helper.helper_data != layout.helper.body or \
            prior.callback != 0x080DFF04:
        raise ValueError('helper, scheduler and actual DFF04 identities must agree')
    for address, body in child.items():
        if address in owners and owners[address] != body:
            raise ValueError('shared complete owner bytes differ')
        owners[address] = body
    spans = sorted((p, p+len(b)) for p, b in owners.items())
    if any(a[1] > b[0] for a, b in zip(spans, spans[1:])):
        raise ValueError('distinct complete owners overlap')
    return owners


def bind(helper_layout, nested_layout, *, selector):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit helper2 nested scheduler selector required')
    result = Layout(helper_layout, nested_layout)
    _validate(result)
    return result


def continue_from_helper(layout, arena_base, report, *, selector, zero12_receipt=None,
                         protected_spans=(), reusable_frame_spans=(), max_steps=1024):
    """Execute a new conditional continuation without repeating its producer.

The real BL supplies LR. Helper saves remain ordinary shared bytes, so nested
effects can corrupt them; only the actual POP/BX observations decide return.
Explicit retired-frame reuse is required within the retained132-byte envelope.
"""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit helper2 nested scheduler selector required')
    owners = _validate(layout)
    h, cb = layout.helper.helper, layout.helper.prior.prefix.callback
    if type(arena_base) is not int or arena_base % 4 or not 0 <= arena_base < 2**32 or \
            type(max_steps) is not int or not 1 <= max_steps <= 1024:
        raise ValueError('aligned numeric base and bounded step limit required')
    for spans in (protected_spans, reusable_frame_spans):
        if not helper.prefix._spans(spans):
            raise ValueError('explicit bounded protection and reuse spans required')
    if type(report) is not dict or report.get('schema') != helper.SELECTOR or \
            report.get('complete_owner_pins') != helper.prefix._pins(helper._validate(layout.helper)) or \
            report.get('helper_entry_reached') is not True or \
            report.get('reaches_scheduler_boundary') is not True or \
            report.get('starts_at') != cb+138 or report.get('final_PC') != h+266 or \
            type(report.get('boundary')) is not dict or report['boundary'].get('site') != h+266:
        raise ValueError('exact helper2 nested-call boundary interface required')
    r, post, entry = report.get('registers'), report.get('post_cells'), report.get('helper_entry_SP')
    if type(r) is not dict or set(r) != set(range(15)) or any(type(k) is not int or
            not words._word(v) for k, v in r.items()) or type(post) is not dict or len(post) > 4096 or \
            type(entry) is not int or not -(2**31)+204 <= entry < 2**31:
        raise ValueError('complete bounded helper register, byte and frame origins required')
    memory = {}
    for key, value in post.items():
        try:
            at = int(key)
        except (ValueError, TypeError) as error:
            raise ValueError('canonical helper byte coordinates required') from error
        if type(key) is not str or key != str(at) or not -(2**31) <= at < 2**31 or \
                not small.state._cell(value):
            raise ValueError('canonical helper byte coordinates and origins required')
        memory[at] = value
    e = entry-72
    expected = dict(site=h+266, target=helper.SCHEDULER,
        register_arguments={i:r[i] for i in range(4)},
        stack_argument_bytes={i:tuple(memory.get(e+i+j) for j in range(4)) for i in (0, 8)},
        SP=r[13], LR=r[14], callee_executed=False)
    if r[13] != words._pointer(e) or r[14] != words._constant((cb+142)|1) or \
            r[1] != words._constant(0x080DFF05) or r[2] != words._constant(12) or \
            r[3] != words._pointer(e+4) or report.get('pending_call') != expected or \
            report.get('descriptor_bytes') != tuple(memory.get(e+4+i) for i in range(28)):
        raise ValueError('actual helper call, descriptor or original BL return differs')
    retired = report.get('retired_spans')
    if type(retired) not in (tuple, list) or not helper.prefix._spans(tuple(retired)):
        raise ValueError('explicit bounded inherited retired spans required')
    protections = list(protected_spans)
    protections.extend((p-arena_base, p+len(b)-arena_base) for p, b in owners.items())
    protections.extend(((layout.nested.image_base-arena_base,
                         layout.nested.image_base+176-arena_base),
                        (layout.nested.prior.scheduler.allocator.allocator.pointer_literal-arena_base,
                         layout.nested.prior.scheduler.allocator.allocator.pointer_literal+4-arena_base)))
    merged = []
    for lo, hi in sorted(protections):
        if merged and lo <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(hi, merged[-1][1]))
        else:
            merged.append((lo, hi))
    protections = tuple(merged)
    if not helper.prefix._spans(protections) or len(protections) > 40:
        raise ValueError('complete immutable-owner protection exceeds bounded spans')
    stages, trace, events = {}, [], []
    working, pc, boundary, returned = dict(r), h+266, None, False

    def stop(reason, at=None):
        raise small.state.remove._Boundary(pc, reason, at)

    def covered(lo, hi):
        cursor = lo
        for start, end in sorted(reusable_frame_spans):
            if start <= cursor < end:
                cursor = max(cursor, end)
        return cursor >= hi

    def consume(result, name):
        nonlocal working, memory, retired, pc
        stages[name] = result
        working = dict(result['registers'])
        memory = {int(k):v for k, v in result['post_cells'].items()}
        retired = list(result['retired_spans'])
        trace.extend(result['trace'])
        events.extend(result['memory_events'])
        supported_zero = name == 'allocator' and result['reaches_unproved_installed_call'] and \
            result['nested_call_cutpoint'].get('call_site') == helper.SCHEDULER+48 and \
            working[1] == words._constant(40)
        if result['boundary'] is not None and not supported_zero:
            error = small.state.remove._Boundary(result['boundary']['site'], result['boundary']['reason'],
                                                  result['boundary'].get('coordinate'))
            error.report.update(result['boundary'])
            raise error
        pc = result.get('final_PC', result['boundary']['site'] if result['boundary'] else pc)

    def load(at):
        if at % 4 or not 0 <= arena_base+at <= 2**32-4 or \
                any(at < hi and at+4 > lo for lo, hi in retired):
            stop('helper POP reads unaligned, wrapped or retired bytes', at)
        value = tuple(memory.get(at+i) for i in range(4))
        if not words._word(value):
            stop('helper POP lacks reaching byte origins', at)
        events.append(dict(site=pc, operation='read32', coordinate=at, bytes=value))
        return value

    try:
        if not 0 <= arena_base+e-132 <= arena_base+entry < 2**32:
            stop('nested frame envelope wraps the numeric arena', e-132)
        for lo, hi in retired:
            a, b = max(lo, e-132), min(hi, e)
            if a < b and not covered(a, b):
                stop('nested frame intersects nonreusable retired bytes', a)
        trace.append(pc)
        working[14] = words._constant((h+270)|1)
        events.append(dict(site=pc, operation='direct-call', target=helper.SCHEDULER,
                           return_word=working[14]))
        first = small.derive(layout.nested.prior, arena_base, memory, working,
            selector=small.SELECTOR, protected_spans=protections,
            retired_spans=tuple(retired), max_steps=max_steps, zero12_receipt=zero12_receipt)
        consume(first, 'allocator')
        last = zero.continue_from_078(layout.nested, arena_base, first, selector=zero.SELECTOR,
                                     protected_spans=protections, max_steps=max_steps)
        consume(last, 'zero-copy-callback-return')
        if last['conditional_returns'] != dict(zero40=True, callback=True, scheduler=True) or \
                pc != h+270 or working[13] != words._pointer(e):
            stop('nested scheduler has not returned to the actual helper frame')
        trace.append(pc)
        working[13] = words._pointer(e+52)
        retired.append((e, e+52))
        events.append(dict(site=pc, operation='retire-frame', coordinates=[e, e+52]))
        pc = h+272
        trace.append(pc)
        values = [load(e+52+4*i) for i in range(4)]
        working.update(dict(zip(range(4, 8), values)))
        working[13] = words._pointer(e+68)
        retired.append((e+52, e+68))
        pc = h+274
        trace.append(pc)
        working[1] = load(e+68)
        working[13] = words._pointer(entry)
        retired.append((e+68, entry))
        pc = h+276
        trace.append(pc)
        if working[1] != words._constant((cb+142)|1):
            stop('actual helper popped return does not identify callback continuation')
        events.append(dict(site=pc, operation='bx-known-continuation', target=cb+142,
                           executable_authority_proved=False))
        pc, returned = cb+142, True
    except small.state.remove._Boundary as error:
        boundary = error.report
        pc = boundary['site']
    return dict(schema=SELECTOR, complete_owner_pins=helper.prefix._pins(owners),
        starts_at=h+266, final_PC=pc, boundary=boundary, stages=stages,
        returns_to_callback_under_conditions=returned, helper_entry_SP=entry,
        scheduler_entry_SP=e, allocation_count=40, helper_frame_bytes=72,
        registers=working, post_cells={str(k):v for k, v in sorted(memory.items())},
        changed_cells={str(k):v for k, v in sorted(memory.items()) if post.get(str(k)) != v},
        trace=trace, memory_events=events, retired_spans=retired,
        inherited_helper_obligations=report.get('obligations', []),
        inherited_CpuSet_obligations=report.get('inherited_CpuSet_obligations', []),
        actual_prior_report_authentication_proved=False, producer_replayed=False,
        actual_reaching_state_proved=False, physical_access_proved=False,
        actual_installed_identity_proved=False, actual_lifetime_proved=False,
        actual_termination_proved=False, full_CFG_closed=False,
        source_or_native_admission=False,
        obligations=[dict(id=k, proved=False, text=t) for k, t in (
            ('reaching', 'The supplied helper boundary report must describe actual reaching registers and bytes. Interface checks are conditional only.'),
            ('memory', 'All actual accesses require live permitted ordinary memory, complete protections, immutable code and no interference.'),
            ('installed', 'The retained count40 source image and any zero12 certificate do not prove installation, execution or physical permissions.'),
            ('continuation', 'This selected helper path stops at the callback continuation. Remaining callback paths and whole-helper frame admission remain open.'))])
