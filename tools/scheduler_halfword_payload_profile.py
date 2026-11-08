"""Exact two-halfword leaf effects before a conditional scheduler payload call.

The caller frame has a leading payload, a 28-byte descriptor and a trailing
four-byte output pair. The named reads and scheduler lifetime/access contract
remain explicit premises. No source initialization or physical separation is
inferred from a literal, pointer, frame offset or successful byte comparison.
"""
import hashlib
from pathlib import Path

import match
import formal_r0_r1_named_leaf_inventory as leaf
from scheduler_predicate_profile import acyclic

SELECTOR = 'conditional-scheduler-halfword-output-payload-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
SCHEDULER = 0x08005B6C
MAX_PRIVATE_BYTES = 256
MAX_OBSERVATIONS = 8


def require(condition, message):
    if not condition:
        raise ValueError(message)


def phases(edges, calls):
    require(len(calls) == 2 and sorted(calls.values()) == sorted((leaf.IDENTITY[0], SCHEDULER))
            and set(calls) <= set(edges),
            'halfword payload requires one exact output leaf and one scheduler site')
    after = dict.fromkeys(edges, False)
    for site in acyclic(edges):
        require(not (after[site] and site in calls),
                'halfword payload excludes calls after scheduler return')
        for target in edges[site]:
            after[target] |= after[site] or calls.get(site) == SCHEDULER


def bind(proof, edges, calls):
    phases(edges, calls)
    address = leaf.IDENTITY[0]
    data = proof.span(address)
    evidence, instructions = leaf.verify(data, address, proof.rom, proof.mapping,
        proof.index, proof.objects, selector=leaf.SELECTOR,
        readonly_named_buffer_policy=leaf.second.second_named_policy(),
        formal_output_policy=leaf.output_policy())
    # Exact straight-line leaf proof has already established every instruction,
    # memory origin and return. Track incoming register observations in order,
    # including scratch aliases overwritten before their first use.
    written, incoming = set(), set()
    for instruction in instructions:
        reads, writes = instruction.regs_access()
        incoming.update(set(reads) - written)
        written.update(writes)
    general = set(range(match.ARM_REG_R0, match.ARM_REG_R12 + 1))
    require(incoming & general == {match.ARM_REG_R0, match.ARM_REG_R0+1},
            'output leaf observes an additional incoming general register')
    require(not written & (general - set(match.CALLER_CLOBBERED)),
            'output leaf modifies a preserved general register')
    proof.dependencies[address] = data
    proof.records[address] = dict(address=address, end=address+len(data), bytes=len(data),
        body_sha256=hashlib.sha256(data).hexdigest(), **proof.identities,
        structure={'kind': 'complete-formal-halfword-output-leaf', 'proof': evidence})
    return dict(leaf=evidence, incoming_registers=sorted(incoming & general),
        written_registers=sorted(written & general),
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


def layout(stack):
    local = [i for i, word in enumerate(stack) if word[2]]
    count = len(local)
    require(9 <= count <= MAX_PRIVATE_BYTES//4 and local == list(range(count)),
            'halfword payload requires a contiguous bounded private frame')
    require(all(not word[0] and not word[1] for word in stack[:count]),
            'halfword payload excludes protected words from its private frame')
    base, end = -4*len(stack), -4*len(stack)+4*count
    return dict(base=base, descriptor=end-32, outputs=end-4, end=end,
                payload_bytes=4*count-32)


def observe(proof, site, value):
    alternatives = proof.observations.setdefault(site, [])
    if value not in alternatives:
        require(len(alternatives) < MAX_OBSERVATIONS,
                'halfword payload call-state bound exceeded')
        alternatives.append(value)


def check_call(proof, address, aliases, stack, slots, *, site):
    frame = layout(stack)
    r0, r1, r2 = match.ARM_REG_R0, match.ARM_REG_R0+1, match.ARM_REG_R0+2
    for offset in aliases.values():
        proof.access(offset, 1, stack)
    observation = dict(site=site, target=address, frame=frame,
        aliases=sorted(aliases.items()), pointer_words=sorted((slots or {}).items()))
    if address == leaf.IDENTITY[0]:
        require(r0 in aliases and r1 in aliases and
                {aliases[r0], aliases[r1]} == {frame['outputs'], frame['outputs']+2} and not slots,
                'output leaf requires the two trailing private halfwords and no pointer words')
        for register in (r0, r1):
            proof.access(aliases[register], 2, stack)
        facts = proof.halfword_payload
        require(set(aliases) & set(facts['incoming_registers']) <= {r0, r1},
                'output leaf observes an unsupported incoming local alias')
        # Preserve actual output-leaf return aliases, including R1. ABI scratch
        # clobbering alone is not evidence that a pointer disappeared.
        returned = {reg: offset for reg, offset in aliases.items()
                    if reg in match.CALLER_CLOBBERED and reg not in facts['written_registers']}
        observation.update(kind='proved-halfword-output',
            writes=[[aliases[r0], 2], [aliases[r1], 2]], returned_aliases=sorted(returned.items()))
    else:
        require(address == SCHEDULER and
                {reg for reg in aliases if reg in match.CALLER_CLOBBERED} == {r2} and
                aliases[r2] == frame['descriptor'] and
                slots == {frame['descriptor']+4: frame['base']},
                'scheduler requires its complete descriptor, leading payload pointer and no extra outgoing aliases')
        for offset in range(frame['base'], frame['end']):
            proof.access(offset, 1, stack)
        observation.update(kind='conditional-scheduler-payload', descriptor_bytes=28,
            payload_frame_bytes=frame['payload_bytes'], payload_extent='private-prefix-upper-bound',
            output_pair_excluded_from_payload=True)
        returned = {}
    observe(proof, site, observation)
    return returned


def manifest(proof):
    require(set(proof.observations) == set(proof.calls),
            'every halfword payload call must be observed')
    return dict(schema=SCHEMA, environment=proof.environment,
        runtime_dependencies=proof.runtime_dependencies, halfword_output=proof.halfword_payload,
        observations=[item for site in sorted(proof.observations)
                      for item in sorted(proof.observations[site], key=repr)],
        assumptions=[leaf.PREMISE,
            'Actual caller local halfword and descriptor/payload accesses require physical access permission; '
            'bounded frame offsets alone do not prove that permission or initialized payload members.',
            'Scheduler calls return with compatible ARM ABI, exact SP and protected saved/caller words preserved. '
            'Allocator/zero/list prefix and callback obey frame noninterference; the returned allocation is '
            'separate from every caller stack word. Callback effects and termination are not proved.',
            'The scheduler reads the 28-byte descriptor as representation bytes. Its descriptor+4 pointer '
            'addresses only the private prefix before the descriptor; payload_frame_bytes is an upper bound, '
            'not a proved C type size or initialization. The trailing output pair is excluded from this bound.',
            'The phase-0 callback reads initialized payload values only within that explicit prefix and before '
            'the scheduler returns. It retains no local pointer and returns none in caller-clobbered registers. '
            'The copied descriptor, ambient original R9 and every recorded preserved-register alias are exposed; '
            'the callback may not access any other caller private or saved bytes through them. '
            'No heap/stack or named-global separation is inferred.'],
        actual_output_leaf_effects_proved=True, actual_callback_effects_proved=False,
        nonescape_proved=False, termination_proved=False, physical_memory_claim=False,
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
