"""Conditional wrapper and scheduler saves on the actual shared byte arena.

This consumes an already bound complete return layout. It materializes saves
and incoming parent transport, including aliases with the fixed-point read.
It stops at scheduler+20, before allocation, copy or callback effects.
"""
import scheduler_return_state as returns
import scheduler_copy_state as words
import scheduler_allocator_state as state

SELECTOR = 'conditional-scheduler-entry-save-state-v1'


def derive(layout, arena_base, cells, registers, *, selector, protected_spans=()):
    """Execute the two entry sequences; equality to actual state stays a premise."""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit entry-save selector required')
    returns._validate(layout)
    if type(arena_base) is not int or arena_base % 4 or not 0 <= arena_base < 2**32 or \
            not returns._registers(registers, set(range(15))) or \
            type(cells) is not dict or len(cells) > 4096 or any(type(k) is not int or
                not -(2**31) <= k < 2**31 or not state._cell(v) for k, v in cells.items()) or \
            type(protected_spans) is not tuple or any(type(p) is not tuple or len(p) != 2 or
                any(type(v) is not int for v in p) or not -(2**31) <= p[0] < p[1] <= 2**31
                for p in protected_spans):
        raise ValueError('numeric common base, complete byte origins and protected spans required')
    memory, regs, changed, events = dict(cells), dict(registers), {}, []
    w, c = layout.wrapper, layout.callee.address
    boundary, entry_sp, observed_scheduler = None, None, None

    def fail(site, reason, at=None):
        raise state.remove._Boundary(site, reason, at)

    def pointer(word, site):
        observation = words.observe(word)
        if observation['kind'] != 'base-plus':
            fail(site, 'SP lacks intact common-base byte origins')
        return observation['coordinate']

    def check(at, width, site, writing=False):
        if not -(2**31) <= at <= 2**31-width or at % 4 or \
                not 0 <= arena_base+at <= 2**32-width:
            fail(site, 'word access is unaligned or wraps the numeric common base', at)
        if writing and any(at < end and at+width > start for start, end in protected_spans):
            fail(site, 'actual save or parent store overlaps protected bytes', at)

    def store(at, value, site):
        check(at, 4, site, True)
        for i, byte in enumerate(value):
            memory[at+i] = changed[at+i] = byte
        events.append(dict(site=site, operation='write32', coordinate=at, bytes=value))

    def load(at, site):
        check(at, 4, site)
        value = tuple(memory.get(at+i) for i in range(4))
        if not words._word(value):
            fail(site, 'word read lacks complete reaching byte origins', at)
        events.append(dict(site=site, operation='read32', coordinate=at, bytes=value))
        return value

    def push(numbers, site):
        at = pointer(regs[13], site)-4*len(numbers)
        for i, reg in enumerate(numbers):
            store(at+4*i, regs[reg], site)
        regs[13] = words._pointer(at)

    try:
        entry_sp = pointer(regs[13], w)
        if entry_sp % 4 or not -(2**31)+80 <= entry_sp < 2**31 or \
                not 0 <= arena_base+entry_sp-80 <= arena_base+entry_sp < 2**32:
            fail(w, 'entry SP or complete entry frame is unaligned or wraps', entry_sp)
        push((4, 5, 6, 14), w)
        regs[6] = regs[8]
        push((6,), w+4)
        regs[13] = words._pointer(entry_sp-24)
        regs[6], regs[4], regs[8] = registers[0], registers[1], registers[2]
        # The two shifts discard the high bytes without inventing low bits.
        regs[4] = regs[4][:2]+(0, 0)
        regs[5] = words._constant(layout.scheduler_point)
        events.append(dict(site=w+18, operation='literal32', address=w+56,
                           value=layout.scheduler_point))
        regs[0] = observed_scheduler = load(layout.scheduler_point-arena_base, w+20)
        store(entry_sp-24, regs[3], w+22)
        regs[1], regs[2], regs[3] = regs[6], regs[4], regs[8]
        regs[14] = words._constant((w+34) | 1)
        events.append(dict(site=w+30, operation='conditional-direct-call', target=c,
                           return_word=regs[14]))
        push((4, 5, 6, 7, 14), c)
        regs[7], regs[6] = regs[9], regs[8]
        push((6, 7), c+6)
        regs[13] = words._pointer(entry_sp-80)
        regs[5], regs[8], regs[4], regs[9] = regs[0], regs[1], regs[2], regs[3]
        regs[6] = load(entry_sp-24, c+18)
    except state.remove._Boundary as error:
        boundary = error.report
    return dict(schema=SELECTOR, reaches_scheduler_count_prefix=boundary is None,
        stop_before=c+20 if boundary is None else None, boundary=boundary,
        wrapper_entry_SP=entry_sp, scheduler_entry_SP=None if entry_sp is None else entry_sp-24,
        registers=regs, changed_cells={str(k):v for k,v in sorted(changed.items())},
        memory_events=events, observed_scheduler_word=observed_scheduler,
        all_saves_materialized=boundary is None, flags_not_modeled=True,
        actual_reaching_state_proved=False, actual_code_execution_proved=False,
        physical_access_proved=False, allocation_or_initialization_proved=False,
        callback_effects_closed=False, source_or_ELF_admission=False, native_admission=False,
        obligations=[dict(id=name, proved=False, text=text) for name, text in (
            ('entry-state', 'The supplied complete register and byte origins equal the actual live wrapper entry state.'),
            ('code-and-control', 'Both bound complete owners and their direct call remain installed and executable; the modeled call alone grants no execution witness.'),
            ('memory', 'Every actual save, fixed-point read and parent word access is live ordinary permitted memory, without interference or hidden protected bytes.'),
            ('continuation', 'The scheduler count prefix, allocator, descriptor copy, callback and real return effects remain separate obligations.'),
        )])
