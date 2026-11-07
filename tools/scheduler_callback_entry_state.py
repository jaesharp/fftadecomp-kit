"""Conditional callback saves and the phase actually read after those saves.

Coordinates share the scheduler's symbolic heap base. Register words carry
byte origins, including aliases. This relation stops before the first phase
comparison and grants no memory, executable-target or initialization witness.
"""
from dataclasses import dataclass
import hashlib

import scheduler_copy_state as copy
import scheduler_allocator_state as state
from scheduler_callback_zero_phase import DISPATCH

SELECTOR = 'conditional-scheduler-callback-save-entry-v1'


@dataclass(frozen=True)
class Binding:
    address: int
    body: bytes
    sha256: str


def _validate(binding):
    if type(binding) is not Binding or type(binding.address) is not int or \
            binding.address % 4 or not 0 <= binding.address <= 2**32-658 or \
            type(binding.body) is not bytes or len(binding.body) != 658 or \
            binding.body[:12] != DISPATCH[:12] or \
            binding.sha256 != hashlib.sha256(binding.body).hexdigest():
        raise ValueError('complete aligned callback identity and exact save/read prefix required')


def bind(body, address, *, selector):
    if type(selector) is not str or selector != SELECTOR or type(body) is not bytes:
        raise ValueError('explicit callback entry selector required')
    binding = Binding(address, body, hashlib.sha256(body).hexdigest())
    _validate(binding)
    return binding


def derive(binding, cells, registers, *, selector, protected_spans=()):
    """Execute only the first six Thumb instructions on a supplied new state."""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit callback entry selector required')
    _validate(binding)
    if type(registers) is not dict or set(registers) != set(range(15)) or \
            any(type(k) is not int or not copy._word(v) for k, v in registers.items()) or \
            type(cells) is not dict or any(type(k) is not int or not -(2**31) <= k < 2**31 or
                                         not state._cell(v) for k, v in cells.items()):
        raise ValueError('complete R0..R14 origins and bounded byte state required')
    if type(protected_spans) is not tuple or any(type(v) is not tuple or len(v) != 2 or
            any(type(n) is not int for n in v) or not -(2**31) <= v[0] < v[1] <= 2**31
            for v in protected_spans):
        raise ValueError('bounded protected intervals required')
    c = binding.address
    working, memory, changed, events = dict(registers), dict(cells), {}, []
    boundary, entry_sp, descriptor, phase, unmodeled = None, None, None, None, None

    def refuse(site, reason, coordinate=None):
        raise state.remove._Boundary(site, reason, coordinate)

    def address(word, site, role):
        observation = copy.observe(word)
        if observation['kind'] != 'base-plus':
            refuse(site, role+' requires complete common-base pointer origin')
        return observation['coordinate']

    try:
        if copy.observe(registers[3]) != dict(kind='constant', value=c | 1):
            refuse(c, 'observed R3 does not identify this Thumb callback')
        entry_sp = address(registers[13], c, 'entry SP')
        if entry_sp % 4 or not -(2**31)+36 <= entry_sp <= 2**31-1:
            refuse(c, 'callback frame coordinate is unaligned or wraps', entry_sp)
        unmodeled = (entry_sp-36, entry_sp-20)
        for i, r in enumerate((4, 5, 6, 7, 14)):
            at = entry_sp-20+4*i
            if any(at < end and at+4 > start for start, end in protected_spans):
                refuse(c, 'callback save overlaps protected bytes', at)
            word = registers[r]
            for n, value in enumerate(word):
                memory[at+n] = changed[at+n] = value
            events.append(dict(site=c, operation='write32', coordinate=at, bytes=word))
        working[13] = copy._pointer(entry_sp-36)
        working[6], working[7], working[5] = registers[0], registers[1], registers[2]
        descriptor = address(working[7], c+10, 'descriptor')
        if descriptor % 2 or not -(2**31) <= descriptor <= 2**31-2:
            refuse(c+10, 'phase read is unaligned or wraps', descriptor)
        if descriptor < unmodeled[1] and descriptor+2 > unmodeled[0]:
            refuse(c+10, 'phase read overlaps unmodeled private-frame bytes', descriptor)
        phase = tuple(memory.get(descriptor+i) for i in range(2))
        if any(value is None for value in phase):
            refuse(c+10, 'phase read has missing byte origins', descriptor)
        if any(type(value) is tuple and value[0] == 'base-plus-byte' for value in phase):
            refuse(c+10, 'pointer phase bytes cannot become a scalar witness', descriptor)
        working[1] = phase+(0, 0)
        events.append(dict(site=c+10, operation='read16', coordinate=descriptor, bytes=phase))
    except state.remove._Boundary as error:
        boundary = error.report
    return dict(schema=SELECTOR, callback=dict(address=c, sha256=binding.sha256, bytes=658),
        reaches_phase_comparison=boundary is None, stop_before=c+12 if boundary is None else None,
        boundary=boundary, registers=working, changed_cells={str(k): v for k, v in sorted(changed.items())},
        memory_events=events, entry_SP=entry_sp, descriptor_coordinate=descriptor,
        unmodeled_private_frame=unmodeled, observed_phase_bytes=phase,
        conditional_phase_value=sum(value << (8*i) for i, value in enumerate(phase))
            if boundary is None and all(type(value) is int for value in phase) else None,
        incoming_phase_may_be_overwritten=True, actual_phase_zero_proved=False,
        actual_reaching_state_proved=False, actual_target_executability_proved=False,
        physical_permissions_proved=False, source_initialization_proved=False,
        callback_effects_closed=False, source_or_ELF_admission=False, native_admission=False,
        obligations=[dict(id=name, proved=False, text=text) for name, text in (
            ('reaching-state', 'The supplied common-base byte state and all register origins equal actual callback entry state.'),
            ('code-and-target', 'The bound complete code remains installed, executable and unchanged at the observed Thumb target.'),
            ('memory', 'Actual live frame and descriptor accesses are permitted, aligned, nonwrapping and free of interference.'),
            ('continuation', 'Phase branches, nested calls, payload effects, saved-origin restoration and frame retirement remain open.'),
        )])
