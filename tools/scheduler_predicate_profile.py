"""Bounded read-only Thumb predicates preceding a conditional scheduler call.

This proves instruction, call, frame and phase closure, not the readability or
values of incoming memory. Only private PUSH saves may write memory. The
existing scheduler effect/ABI assumptions remain explicit and unchanged.
"""
import hashlib
from pathlib import Path
import struct

import match
import owner_graph_profile as graph
from local_long_branch_profile import prove_frame

MAX_HELPERS = 8
MAX_HELPER_BYTES = 512
SCHEDULER = 0x08005B6C


def require(condition, message):
    if not condition:
        raise ValueError(message)


def acyclic(edges):
    """Return a topological order; reject every back edge, including self loops."""
    incoming = dict.fromkeys(edges, 0)
    for successors in edges.values():
        for target in successors:
            require(target in incoming, 'predicate CFG edge leaves the complete owner')
            incoming[target] += 1
    pending = [site for site, count in incoming.items() if not count]
    order = []
    while pending:
        site = pending.pop()
        order.append(site)
        for target in edges[site]:
            incoming[target] -= 1
            if incoming[target] == 0:
                pending.append(target)
    require(len(order) == len(edges), 'predicate composition excludes CFG cycles')
    return order


def phases(edges, calls):
    require(sum(target == SCHEDULER for target in calls.values()) == 1 and
            len(calls) > 1 and set(calls) <= set(edges),
            'guarded scheduler requires predicates and exactly one scheduler site')
    after = dict.fromkeys(edges, False)
    for site in acyclic(edges):
        require(not (after[site] and site in calls),
                'guarded scheduler excludes calls after scheduler return')
        scheduled = after[site] or calls.get(site) == SCHEDULER
        for target in edges[site]:
            after[target] |= scheduled


def readonly_instruction(instruction):
    """Closed ARMv4T encoding set; frame proof validates PUSH/POP/BX provenance."""
    raw = bytes(instruction.bytes)
    half, = struct.unpack_from('<H', raw)
    if len(raw) == 4:
        second, = struct.unpack_from('<H', raw, 2)
        return half & 0xF800 == 0xF000 and second & 0xF800 == 0xF800
    if len(raw) != 2:
        return False
    return (half < 0x4400 or                         # low-register scalar operations
            half & 0xF800 == 0x4800 or              # local literal load
            half & 0xFE00 in (0x5600, 0x5800, 0x5A00, 0x5C00, 0x5E00) or
            half & 0xF800 in (0x6800, 0x7800, 0x8800) or
            half & 0xFE00 in (0xB400, 0xBC00) or    # private save / proven restoration
            half & 0xFF87 == 0x4700 or              # BX, proven entry return only
            0xD000 <= half < 0xDE00 or              # conditional branch, excludes SWI
            half & 0xF800 == 0xE000)                # local unconditional branch


def close(proof, targets):
    """Authenticate every unique indexed body and close the entire call DAG."""
    import owner_admission_profile as owner
    active, complete = set(), {}

    def visit(address):
        require(address not in active, 'predicate helper call cycle')
        if address in complete:
            return
        require(len(active) + len(complete) < MAX_HELPERS,
                'predicate helper budget exceeded')
        require(not match.function_thunk.reserved(address) and
                address not in match.RUNTIME_HELPERS.values(),
                'predicate closure excludes runtime and indirect calls')
        active.add(address)
        data = proof.span(address)
        require(len(data) <= MAX_HELPER_BYTES, 'predicate helper byte budget exceeded')
        refinement = owner.refine(data, address, proof.mapping)
        ins, edges, branches, calls, words = graph.graph(data, address, refinement)
        require(not branches and not words, 'predicate closure excludes local BL and switches')
        acyclic(edges)
        require(all(readonly_instruction(item) for item in ins.values()),
                'predicate helper contains an unsupported or memory-writing instruction')
        partition = graph.partition(data, address, refinement, ins, words)
        for target in sorted(set(calls.values())):
            visit(target)
        frame = prove_frame(ins, edges, address, {}, calls)
        record = dict(address=address, end=address+len(data), bytes=len(data),
            body_sha256=hashlib.sha256(data).hexdigest(), **proof.identities,
            structure=dict(kind='complete-acyclic-read-only-predicate-v1',
                instructions=len(ins), partition=partition, frame=frame,
                calls=[[site-address, target] for site, target in sorted(calls.items())]))
        complete[address] = record
        proof.records[address] = record
        proof.dependencies[address] = bytes(data)
        active.remove(address)

    for target in sorted(set(targets)):
        visit(target)
    return dict(helper_budget=MAX_HELPERS, helper_byte_budget=MAX_HELPER_BYTES,
        helpers=sorted(complete),
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        conditional_memory=('Every reached load addresses live readable ordinary memory with '
            'a defined scalar value; reads have no device effects. Stack saves use valid aligned '
            'nonwrapping storage separate from live caller objects. These are premises, not '
            'inferred from addresses or argument registers.'),
        actual_memory_readability_proved=False, actual_predicate_values_proved=False)
