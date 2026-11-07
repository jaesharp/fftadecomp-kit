"""Conditional post-allocation descriptor bytes and actual callback exposure.

The retained allocator/list relation supplies the reaching byte state. The
retained partial-word copy executes the exact suffix in a disjoint shadow
frame; this is a byte-transport coordinate change, never actual local-memory
permission. Payload origins are injectively renamed and restored, not read as
addresses. Actual frame-source overlap and partial pointer phase overwrite
still refuse. The relation stops at the BX R3 thunk, before target validity or any callback effect.
"""
import hashlib

import scheduler_allocator_state as state
import descriptor_partial_word_prerequisite as partial

SELECTOR = 'conditional-scheduler-post-state-copy-exposure-v1'
COPY = bytes.fromhex('6946 4846 38c8 38c1 38c8 38c1 0068 0860 6946 0020 0880')
LOCAL = (False, False, True)


def _word(value):
    return type(value) is tuple and len(value) == 4 and all(state._cell(v) for v in value)


def _constant(value):
    return tuple((value >> (8*i)) & 255 for i in range(4))


def _pointer(value):
    return tuple(('base-plus-byte', value, i) for i in range(4))


def observe(word):
    """Classify bits without granting code identity, access or initialization."""
    if not _word(word):
        raise ValueError('exact four byte origins required')
    if all(type(v) is int for v in word):
        return dict(kind='constant', value=sum(v << (8*i) for i, v in enumerate(word)))
    if all(type(v) is tuple and v[0] == 'base-plus-byte' and v[2] == i
           for i, v in enumerate(word)) and all(v[1] == word[0][1] for v in word):
        return dict(kind='base-plus', coordinate=word[0][1])
    return dict(kind='opaque-or-partial', bytes=word)


def _transport(source):
    """Reuse the frozen copy decoder with a reversible payload-only renaming."""
    if type(source) is not tuple or len(source) != 28 or any(not state._cell(v) for v in source):
        raise ValueError('complete 28-byte reaching descriptor required')
    # Retain the old partial-pointer overwrite refusal. The new adapter does
    # not use payload erasure to bypass that guard at the phase halfword store.
    if any(type(v) is tuple and v[0] == 'base-plus-byte' for v in source[:4]):
        raise ValueError('phase word partial pointer overwrite remains unsupported')
    names = {}
    reverse = {}
    def encode(v):
        if type(v) is int:
            return ('constant', v)
        if v not in names:
            atom = ('unproved', 'transport-byte:' + str(len(names)), 0)
            names[v] = atom
            reverse[atom] = v
        return names[v]
    def decode(word):
        result = []
        for atom in word.bytes:
            if atom[0] == 'constant':
                result.append(atom[1])
            elif atom in reverse:
                result.append(reverse[atom])
            else:
                raise ValueError('copy produced a payload origin absent from the reaching source')
        return tuple(result)
    # Destination [-56,-28), source [-28,0); MOV R1,SP requires SP=-56.
    # Every payload is data in this closed instruction string. None is used
    # as an address, branch target, count, or initialized scalar witness.
    words = {-28+4*i: partial.Word(tuple(encode(v) for v in source[4*i:4*i+4])) for i in range(7)}
    result = partial.replay(COPY, {9: partial.Word.pointer(-28), 13: partial.Word.pointer(-56)},
                            [LOCAL]*14, words)
    copied = tuple(v for i in range(7) for v in decode(result['words'][-56+4*i]))
    return dict(bytes=copied, R4=decode(result['registers'][4]), R5=decode(result['registers'][5]),
                shadow_reads=result['reads'], shadow_writes=result['writes'])


def derive(layout, size_word, cells, scheduler_offset, descriptor_offset, callback_word,
           entry_sp, ambient_registers, *, selector, zero12_receipt=None, zero92_receipt=None,
           observed_zero_target=None, protected_spans=(), max_links=128,
           max_search_transitions=256, max_median_links=256):
    """New composition on a new state; do not replay a frozen actual derive.

All coordinates retain069's common symbolic heap base. R10..R12 must carry
their supplied exact byte origins; absence cannot mean absence of live aliases.
Actual entry state, source access/lifetime and external effects stay premises.
"""
    if type(selector) is not str or selector != SELECTOR or type(layout) is not state.Layout:
        raise ValueError('explicit post-state copy selector and retained state layout required')
    if type(ambient_registers) is not dict or set(ambient_registers) != {10, 11, 12} or any(
            type(k) is not int or not _word(v) for k, v in ambient_registers.items()):
        raise ValueError('all ambient R10..R12 byte origins are required')
    prefix = state.derive(layout, size_word, cells, scheduler_offset, descriptor_offset,
        callback_word, entry_sp, selector=state.SELECTOR, zero12_receipt=zero12_receipt,
        zero92_receipt=zero92_receipt, observed_zero_target=observed_zero_target,
        protected_spans=protected_spans, max_links=max_links,
        max_search_transitions=max_search_transitions, max_median_links=max_median_links)
    c = layout.address
    sp = entry_sp-56
    allocation = prefix['allocation']
    boundary = prefix['boundary']
    events = []
    registers = None
    copied = None
    observed = None
    # Parent protected word and the own saved frame are not local-copy bytes.
    protected = tuple(protected_spans) + ((entry_sp-28, entry_sp+4),)
    memory = dict(cells)
    memory.update({int(k): v for k, v in prefix['changed_cells'].items()})
    changes = {}
    def guard(at, width, site, role):
        if not -(2**31) <= at <= 2**31-width or width in (2, 4, 28) and at % (4 if width == 28 else width):
            raise state.remove._Boundary(site, 'unaligned or nonwrapping copy/exposure coordinate', at)
        if any(at < end and at+width > start for start, end in protected):
            raise state.remove._Boundary(site, role + ' overlaps protected caller/saved state', at)
    try:
        if boundary is not None:
            raise state.remove._Boundary(boundary['site'], boundary['reason'], boundary.get('coordinate'))
        if prefix['descriptor_intersects_unmodeled_frame']:
            raise state.remove._Boundary(c+158, 'descriptor source intersects unmodeled private-frame bytes', descriptor_offset)
        guard(descriptor_offset, 28, c+158, 'descriptor source')
        guard(sp, 28, c+160, 'descriptor destination')
        source = tuple(prefix['descriptor_snapshot'])
        try:
            transport = _transport(source)
        except ValueError as error:
            raise state.remove._Boundary(c+158, str(error), descriptor_offset) from error
        # These are exactly the two LDM/STM triples and final LDR/STR. Source
        # and destination disjointness follows from the checked069 frame
        # exclusion, not from allocator identity or a nominal object name.
        for site, offsets, writing in [(158, (0,4,8), False), (160, (0,4,8), True),
                                      (162, (12,16,20), False), (164, (12,16,20), True),
                                      (166, (24,), False), (168, (24,), True)]:
            for offset in offsets:
                at = sp+offset if writing else descriptor_offset+offset
                value = source[offset:offset+4]
                if writing:
                    for i, v in enumerate(value):
                        memory[at+i] = v
                        changes[at+i] = v
                events.append(dict(site=c+site, operation='write32' if writing else 'read32',
                                   coordinate=at, bytes=value))
        memory[sp] = memory[sp+1] = changes[sp] = changes[sp+1] = 0
        events.append(dict(site=c+174, operation='write16', coordinate=sp, value=0))
        copied = tuple(memory[sp+i] for i in range(28))
        if copied != transport['bytes']:
            raise ValueError('composed byte effects differ from retained copy semantics')
        # LDR R3,[R7] is after all real descriptor writes, not the incoming R8.
        guard(allocation, 4, c+176, 'observed callback slot')
        observed = tuple(memory.get(allocation+i) for i in range(4))
        if not _word(observed):
            raise state.remove._Boundary(c+176, 'actual callback slot has incomplete byte origins', allocation)
        events.append(dict(site=c+176, operation='read32', coordinate=allocation, bytes=observed))
        incoming_callback = _constant(callback_word) if type(callback_word) is int else tuple(
            ('opaque-byte', callback_word[1], i) for i in range(4))
        registers = dict(ambient_registers)
        registers.update({0: _pointer(allocation), 1: _pointer(sp), 2: _pointer(allocation+24),
            3: observed, 4: transport['R4'], 5: transport['R5'],
            6: _constant(0) if prefix['parent'] is None else _pointer(prefix['parent']),
            7: _pointer(allocation), 8: incoming_callback, 9: _pointer(descriptor_offset),
            13: _pointer(sp), 14: _constant((c+184)|1)})
    except state.remove._Boundary as error:
        boundary = error.report
    return dict(schema=SELECTOR, bodies=dict(scheduler=layout.sha256, copy=hashlib.sha256(COPY).hexdigest()),
        reaches_callback_thunk=boundary is None, callback_entry_reached=False, boundary=boundary, prefix=prefix,
        copy_events=events, changed_cells={str(k): v for k, v in sorted(changes.items())},
        descriptor_bytes=copied, callback_registers=registers,
        observed_callback_word=observed, callback_word_observation=None if observed is None else observe(observed),
        descriptor_phase_under_conditions=None if copied is None else copied[0] | copied[1] << 8,
        scheduler_phase_under_conditions=prefix['phase_after_effects'],
        descriptor_source=descriptor_offset, descriptor_local=sp,
        callback_site=c+180, callback_thunk=layout.callback_thunk,
        all_ambient_register_origins_retained=registers is not None,
        actual_observed_phase_proved=False, actual_callback_target_proved=False,
        actual_source_initialization_proved=False, actual_memory_or_frame_proved=False,
        installed_identity_proved=False, callback_effects_closed=False,
        callback_return_or_nonescape_proved=False, full_scheduler_proved=False, native_admission=False,
        obligations=prefix['obligations'] + [dict(id=k, proved=False, text=t) for k,t in [
            ('copy-source', 'The supplied post-effect bytes describe the actual readable live source, including opaque bytes; shadow-local classification grants no physical source permission.'),
            ('copy-frame', 'The numeric frame/source checks and complete protected spans hold for actual addresses, with no wrap, interference or expired objects.'),
            ('callback-entry', 'The reloaded R3 word, ambient register origins and local descriptor bytes equal actual reaching state. A constant or pointer-token classification is not executable-code authority.'),
            ('callback-effects', 'Actual callback saves/reads/effects/termination, R7 survival, local nonescape and continuation restoration remain to be composed. Descriptor lifetime ends at actual frame retirement; a snapshot extends no lifetime.')]])
