"""Conditional scheduler interface with two distinct bounded private payloads.

The three adjacent frame intervals establish bounds, not C object sizes,
initialization, physical permission or actual callback effects.
"""
import hashlib
from pathlib import Path

import match

SELECTOR = 'conditional-scheduler-two-payload-calls-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
SCHEDULER = 0x08005B6C
MAX_PRIVATE_BYTES = 256


def require(condition, message):
    if not condition:
        raise ValueError(message)


def layout(stack, descriptor, slots):
    local = [i for i, word in enumerate(stack) if word[2]]
    count = len(local)
    require(9 <= count <= MAX_PRIVATE_BYTES//4 and local == list(range(count))
            and all(not word[0] and not word[1] for word in stack[:count]),
            'two payloads require contiguous bounded unprotected private words')
    base, end = -4*len(stack), -4*len(stack)+4*count
    require(set(slots) == {descriptor+4, descriptor+8},
            'two payloads require exactly descriptor+4 and descriptor+8 pointer words')
    starts = [descriptor, slots[descriptor+4], slots[descriptor+8]]
    require(len(set(starts)) == 3 and min(starts) == base
            and all(start % 4 == 0 and base <= start < end for start in starts),
            'two payload starts must be distinct aligned private boundaries covering SP')
    ordered = sorted(starts)
    bounds = dict(zip(ordered, ordered[1:]+[end]))
    require(bounds[descriptor]-descriptor == 28,
            'the descriptor must occupy exactly 28 bytes between payload boundaries')
    return dict(base=base, end=end, descriptor=descriptor, descriptor_bytes=28,
        payloads=[dict(descriptor_field=field, offset=slots[descriptor+field],
                       frame_bound_bytes=bounds[slots[descriptor+field]]-slots[descriptor+field])
                  for field in (4, 8)])


def check_call(proof, address, aliases, stack, slots, *, site):
    r2 = match.ARM_REG_R0+2
    require(address == SCHEDULER and
            {reg for reg in aliases if reg in match.CALLER_CLOBBERED} == {r2},
            'two payload scheduler excludes other outgoing register aliases')
    frame = layout(stack, aliases[r2], slots or {})
    for offset in aliases.values():
        proof.access(offset, 1, stack)
    for offset in range(frame['base'], frame['end']):
        proof.access(offset, 1, stack)
    observation = dict(site=site, target=address, frame=frame,
        aliases=sorted(aliases.items()), pointer_words=sorted(slots.items()),
        payload_extent='disjoint-private-frame-upper-bounds')
    require(site not in proof.observations or proof.observations[site] == observation,
            'two payload interface differs across incoming paths')
    proof.observations[site] = observation
    return {}


def manifest(proof):
    require(set(proof.observations) == set(proof.calls),
            'every two payload scheduler call must be observed')
    return dict(schema=SCHEMA, environment=proof.environment,
        runtime_dependencies=proof.runtime_dependencies,
        observations=[proof.observations[site] for site in sorted(proof.observations)],
        assumptions=[
            'Actual calls return with compatible ARM ABI, exact SP and protected saved/caller words preserved. '
            'Scheduler allocator/zero/list prefix and callback obey frame noninterference; the returned '
            'allocation is separate from every caller stack word. Actual callback effects are not proved.',
            'The scheduler reads the complete 28-byte descriptor as representation bytes. Descriptor+4 and '
            'descriptor+8 each address only their recorded distinct private payload interval. Each '
            'frame_bound_bytes is an upper bound, not a C type size or initialized-value guarantee. '
            'Unknown local representation bytes, including bitfield read/modify/write inputs and padding, '
            'are not thereby initialized scalars or trusted pointers.',
            'Physical access permission and initialized values for every interpreted payload member are '
            'required separately. No heap/stack, named-global separation or memory readability is inferred.',
            'The synchronous phase-0 callback accesses payloads only within their recorded bounds and '
            'before the scheduler returns, retaining no local pointer and returning none in caller-clobbered '
            'registers. The copied descriptor, ambient original R9 and all recorded preserved-register '
            'aliases are exposed; the callback must not access other private or saved caller bytes through '
            'them. Copying the descriptor alone does not prove these lifetime or nonescape conditions.'],
        actual_callback_effects_proved=False, nonescape_proved=False,
        termination_proved=False, physical_memory_claim=False,
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
