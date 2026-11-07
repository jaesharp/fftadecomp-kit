"""Conditional request-controller entry and its phase257 scheduler call.

Only the selected path is closed. The private record starts with opaque bytes;
its actual tag, option and subject writes execute on the same byte arena as
incoming objects and saves. Unmodeled phase/option branches remain cutpoints.
"""
from dataclasses import dataclass
import hashlib

import scheduler_allocator_state as atoms
import scheduler_copy_state as words
import scheduler_return_state as returns
import scheduler_callback_state as callback

SELECTOR = 'conditional-scheduler-request-entry-state-v1'
HEAD = bytes.fromhex('70b589b0061c0d1c141c2b8880204000834226d0834204dc002b0bd0012b1dd05ce0034883422fd00130834248d055e0')
SELECTED = bytes.fromhex('e078002826d0022802d18120400020e002a99e2088820120c882206903900548402102aa331c')


@dataclass(frozen=True)
class Layout:
    address: int
    data: bytes
    wrapper: returns.Layout
    callback: callback.Layout


def _validate(layout):
    if type(layout) is not Layout or type(layout.address) is not int or layout.address % 4 or \
            not 0 <= layout.address <= 2**32-230 or type(layout.data) is not bytes or len(layout.data) != 230:
        raise ValueError('complete aligned230B request controller required')
    returns._validate(layout.wrapper)
    callback._validate(layout.callback)
    c, b = layout.address, layout.data
    if b[:48] != HEAD or b[136:174] != SELECTED or int.from_bytes(b[48:52], 'little') != 257 or \
            callback.shapes._call(b, c, 174) != layout.wrapper.wrapper or \
            int.from_bytes(b[188:192], 'little') != layout.callback.callback | 1:
        raise ValueError('selected dispatch, descriptor writes, call or callback literal differs')
    for start, size in [(layout.wrapper.wrapper, 60), (layout.wrapper.callee.address, 206),
                        (layout.callback.callback, 658), (layout.callback.helper, 292)]:
        if c < start+size and c+230 > start:
            raise ValueError('complete request controller overlaps a composed owner')


def bind(data, address, wrapper_layout, callback_layout, *, selector):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit request-entry selector required')
    layout = Layout(address, data, wrapper_layout, callback_layout)
    _validate(layout)
    return layout


def derive(layout, arena_base, cells, registers, *, selector, protected_spans=()):
    """Transport actual conditional origins to the wrapper entry, not beyond it."""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit request-entry selector required')
    _validate(layout)
    if type(arena_base) is not int or arena_base % 4 or not 0 <= arena_base < 2**32 or \
            not returns._registers(registers, set(range(15))) or \
            type(cells) is not dict or len(cells) > 4096 or any(type(k) is not int or
                not -(2**31) <= k < 2**31 or not atoms._cell(v) for k, v in cells.items()) or \
            type(protected_spans) is not tuple or any(type(p) is not tuple or len(p) != 2 or
                any(type(v) is not int for v in p) or not -(2**31) <= p[0] < p[1] <= 2**31
                for p in protected_spans):
        raise ValueError('numeric common base, complete origins and protected intervals required')
    c = layout.address
    r, memory, changes, events, trace = dict(registers), dict(cells), {}, [], []
    boundary, entry_sp, phase, option, subject, descriptor, namespace = (None,)*7
    pc, reached = c, False

    def at(offset):
        nonlocal pc
        pc = c+offset
        trace.append(pc)

    def stop(reason, coordinate=None):
        raise atoms.remove._Boundary(pc, reason, coordinate)

    def cut(offset, reason):
        nonlocal pc
        pc = c+offset
        stop(reason)

    def address(word, role):
        observation = words.observe(word)
        if observation['kind'] != 'base-plus':
            stop(role+' lacks intact common-base provenance')
        return observation['coordinate']

    def guard(coordinate, width, writing=False):
        if not -(2**31) <= coordinate <= 2**31-width or coordinate % width or \
                not 0 <= arena_base+coordinate <= 2**32-width:
            stop('access is unaligned or wraps the numeric common base', coordinate)
        if writing and any(coordinate < end and coordinate+width > start for start, end in protected_spans):
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
        for i, byte in enumerate(value):
            memory[coordinate+i] = changes[coordinate+i] = byte
        events.append(dict(site=pc, operation='write'+str(len(value)*8), coordinate=coordinate, bytes=value))

    try:
        at(0)
        entry_sp = address(r[13], 'entry SP')
        if entry_sp % 4 or not -(2**31)+52 <= entry_sp < 2**31 or \
                not 0 <= arena_base+entry_sp-52 <= arena_base+entry_sp < 2**32:
            stop('entry SP or complete private frame is unaligned or wraps', entry_sp)
        for i, reg in enumerate((4, 5, 6, 14)):
            store(entry_sp-16+4*i, r[reg])
        at(2); r[13] = words._pointer(entry_sp-52)
        origins = {v[1] for v in [*memory.values(), *(byte for word in r.values() for byte in word)]
                   if type(v) is tuple and v[0] == 'opaque-byte'}
        namespace = 'unmodeled request local'
        generation = 0
        while namespace in origins:
            generation += 1
            namespace = 'unmodeled request local:'+str(generation)
        for coordinate in range(entry_sp-52, entry_sp-16):
            memory[coordinate] = ('opaque-byte', namespace, coordinate-(entry_sp-52))
        events.append(dict(site=pc, operation='allocate-frame', coordinates=[entry_sp-52, entry_sp-16],
                           initialization_granted=False))
        at(4); r[6] = r[0]
        at(6); r[5] = r[1]
        at(8); r[4] = r[2]
        at(10); observed = load(address(r[5], 'request'), 2)
        phase = observed[0] | observed[1] << 8; r[3] = words._constant(phase)
        at(12); r[0] = words._constant(128)
        at(14); r[0] = words._constant(256)
        at(16); at(18)
        if phase == 256:cut(98, 'dispatch reaches unmodeled phase256 branch')
        at(20); at(22)
        if phase <= 256:
            at(24); at(26)
            if phase == 0:cut(52, 'dispatch reaches unmodeled phase0 branch')
            at(28); at(30)
            if phase == 1:cut(92, 'dispatch reaches unmodeled phase1 branch')
            at(32); cut(220, 'dispatch reaches unmodeled default return')
        at(34); r[0] = words._constant(257)
        events.append(dict(site=pc, operation='read-ROM32', address=c+48, value=257))
        at(36); at(38)
        if phase != 257:
            at(40); r[0] = words._constant(258)
            at(42); at(44)
            if phase == 258:cut(192, 'dispatch reaches unmodeled phase258 branch')
            at(46); cut(220, 'dispatch reaches unmodeled default return')
        at(136); option = load(address(r[4], 'payload')+3, 1)[0]; r[0] = words._constant(option)
        at(138); at(140)
        if option == 0:cut(220, 'completion zero reaches unmodeled return')
        at(142); at(144)
        if option == 2:
            at(146); r[0] = words._constant(129)
            at(148); r[0] = words._constant(258)
            at(150); cut(218, 'completion two reaches unmodeled request-phase store')
        descriptor = entry_sp-44
        at(152); r[1] = words._pointer(descriptor)
        at(154); r[0] = words._constant(158)
        at(156); store(descriptor+20, r[0][:2])
        at(158); r[0] = words._constant(1)
        at(160); store(descriptor+22, r[0][:2])
        at(162); r[0] = subject = load(address(r[4], 'payload')+16, 4)
        at(164); store(descriptor+4, r[0])
        at(166); r[0] = words._constant(layout.callback.callback | 1)
        events.append(dict(site=pc, operation='read-ROM32', address=c+188, value=layout.callback.callback | 1))
        at(168); r[1] = words._constant(64)
        at(170); r[2] = words._pointer(descriptor)
        at(172); r[3] = r[6]
        at(174); r[14] = words._constant((c+178) | 1)
        events.append(dict(site=pc, operation='conditional-direct-call', target=layout.wrapper.wrapper, return_word=r[14]))
        reached = True
    except atoms.remove._Boundary as error:
        boundary = error.report
    return dict(schema=SELECTOR, complete_owner=dict(address=c, bytes=230, sha256=hashlib.sha256(layout.data).hexdigest()),
        reaches_wrapper_entry_under_conditions=reached, boundary=boundary,
        wrapper=layout.wrapper.wrapper, root_entry_SP=entry_sp,
        wrapper_entry_SP=None if not reached else entry_sp-52,
        observed_phase=phase, observed_completion=option, observed_subject_word=subject,
        descriptor_coordinate=descriptor, registers=r, trace=trace, memory_events=events,
        changed_cells={str(k):v for k,v in sorted(changes.items())},
        post_cells={str(k):v for k,v in sorted(memory.items())},
        unmodeled_private_namespace=namespace, flags_not_modeled=True,
        descriptor_phase_initialized=False, whole_descriptor_initialized=False,
        actual_reaching_state_proved=False, physical_access_proved=False,
        actual_code_execution_proved=False, actual_heap_or_SP_proved=False,
        whole_owner_CFG_closed=False, source_or_ELF_admission=False, native_admission=False,
        obligations=[dict(id=name, proved=False, text=text) for name, text in (
            ('entry-state', 'All supplied common-base register and memory origins equal actual request-controller entry state.'),
            ('access-and-code', 'Both owners and callback retain executable code identity; all actual live stack, descriptor and payload accesses are permitted and free of interference.'),
            ('partial-initialization', 'Only the observed subject word, tag158 and option1 stores initialize the child descriptor. Other copied bytes remain opaque; later observations require their own proof.'),
            ('continuation', 'The scheduler call, allocator, callback, return, subsequent root writes and all other request phases remain separate obligations.'),
        )])
