"""One guarded u16 scheduler loop under explicit returning-call contracts.

The ranking argument is structural and register based. It does not establish
external memory permissions, callback effects, allocation separation, or that
the invoked callees return. The existing full frame/alias replay is mandatory.
"""
import hashlib
from pathlib import Path

import match
from scheduler_branch_profile import SCHEDULER, MAX_ORDINARY_TARGETS, MAX_CALL_SITES
from scheduler_predicate_profile import acyclic


def require(ok, message):
    if not ok:
        raise ValueError(message)


def layout(instructions, edges, calls, address):
    require(0 < len(instructions) <= 256 and set(instructions) == set(edges),
            'counted scheduler loop requires a complete bounded instruction graph')
    require(address in edges and all(t in edges for ts in edges.values() for t in ts),
            'counted scheduler edge leaves its complete owner')
    predecessors = {s: set() for s in edges}
    for s, targets in edges.items():
        for t in targets:
            predecessors[t].add(s)

    def raw(site):
        require(site in instructions and instructions[site].size == 2,
                'counted scheduler control must be exact Thumb16')
        return int.from_bytes(instructions[site].bytes, 'little')

    def sequence(sites):
        for previous, current in zip(sites, sites[1:]):
            require(edges[previous] == (current,) and predecessors[current] == {previous},
                    'counted scheduler control sequence has an alternate entry')

    def writes(sites, registers):
        registers = {match.ARM_REG_R0 + r for r in registers}
        return any(registers & set(instructions[s].regs_access()[1]) for s in sites)

    backedges = [(s, t) for s, ts in edges.items() for t in ts if t <= s]
    require(len(backedges) == 1, 'counted scheduler requires exactly one backward edge')
    latch, header = backedges[0]
    require(raw(latch) & 0xff00 == 0xd300 and edges[latch] == (header, latch + 2),
            'counted scheduler latch must use unsigned strict less-than')
    tail = list(range(latch - 8, latch + 2, 2))
    sequence(tail)
    add, left, right, compare, _ = map(raw, tail)
    require(add & 0xfe00 == 0x1c00 and (add >> 6) & 7 == 1,
            'counted scheduler successor must add exactly one')
    counter, temporary = (add >> 3) & 7, add & 7
    require(counter != temporary and 4 <= counter <= 7 and
            left & 0xf800 == 0 and (left >> 6) & 31 == 16 and
            (left >> 3) & 7 == temporary and
            right & 0xf800 == 0x0800 and (right >> 6) & 31 == 16 and
            (right >> 3) & 7 == left & 7 and right & 7 == counter,
            'counted scheduler needs an ABI-preserved counter and exact u16 successor')
    require(compare & 0xffc0 == 0x4280 and compare & 7 == counter,
            'counted scheduler latch compares a different counter')
    limit = (compare >> 3) & 7
    require(4 <= limit <= 7 and len({counter, limit, temporary, left & 7}) >= 3 and
            limit not in (counter, temporary, left & 7),
            'counted scheduler limit must be distinct and ABI-preserved')
    exit_site = latch + 2

    # The only entry path initializes the counter and tests the same unsigned
    # limit. Its taken arm bypasses the loop, including count == 0.
    prefix, site = [], address
    while site != header:
        require(site in edges and site not in prefix and site not in tail and
                site not in calls, 'counted scheduler entry is not a call-free finite prefix')
        prefix.append(site)
        targets = edges[site]
        if len(targets) == 2:
            require(raw(site) & 0xff00 == 0xd200 and targets == (exit_site, header),
                    'counted scheduler entry must bypass on unsigned greater-or-equal')
            break
        require(len(targets) == 1, 'counted scheduler prefix exits before its guard')
        site = targets[0]
    require(len(prefix) >= 5 and edges[prefix[-1]] == (exit_site, header),
            'counted scheduler requires its initial unsigned guard')
    guard = prefix[-1]
    require(prefix[-3:] == [guard - 4, guard - 2, guard] and
            raw(guard - 4) == 0x2000 | (counter << 8) and raw(guard - 2) == compare,
            'counted scheduler entry lacks zero initialization and the same comparison')
    sequence(prefix[-3:])
    require(predecessors[address] == set() and
            all(predecessors[s] == {p} for p, s in zip(prefix, prefix[1:])),
            'counted scheduler prefix has an alternate entry')

    # Authenticate the last limit definition, not its incoming prototype.
    limit_writers = [s for s in prefix[:-3] if writes((s,), (limit,))]
    require(limit_writers, 'counted scheduler limit has no actual u16 narrowing')
    narrow = limit_writers[-1]
    nr = raw(narrow)
    require(nr & 0xf800 == 0x0800 and (nr >> 6) & 31 == 16 and nr & 7 == limit,
            'counted scheduler limit must be a logical right16 result')
    nl = raw(narrow - 2)
    require(nl & 0xf800 == 0 and (nl >> 6) & 31 == 16 and nl & 7 == (nr >> 3) & 7,
            'counted scheduler limit lacks matching left16 narrowing')
    require(narrow - 2 in prefix, 'counted scheduler bound narrowing is not on entry')
    sequence([narrow - 2, narrow])
    require(not writes(tail, (limit,)), 'counted scheduler tail changes its bound')

    # All body paths must reach the update. No additional cycle, early return,
    # external entry, or bypass of the update is permitted.
    body, pending = set(), [header]
    forbidden = set(prefix) | set(tail[1:]) | {exit_site}
    while pending:
        site = pending.pop()
        if site == tail[0] or site in body:
            continue
        require(site not in forbidden and edges[site],
                'counted scheduler body bypasses its update')
        body.add(site)
        pending.extend(edges[site])
    body_edges = {s: tuple(t for t in edges[s] if t != tail[0]) for s in body}
    acyclic(body_edges)
    require(not writes(body, (counter, limit)),
            'counted scheduler body modifies its counter or bound')
    nodes = body | set(tail)
    for s in nodes:
        require(all(p in nodes or (p == guard and s == header) for p in predecessors[s]),
                'counted scheduler loop has an unguarded external entry')
    require(predecessors[header] == {guard, latch},
            'counted scheduler header has an alternate entry')

    suffix, site = [], exit_site
    while True:
        require(site not in nodes and site not in prefix and site not in suffix and site not in calls,
                'counted scheduler exit is not a call-free finite suffix')
        suffix.append(site)
        if not edges[site]:
            break
        require(len(edges[site]) == 1, 'counted scheduler suffix branches')
        site = edges[site][0]
    require(set(prefix) | nodes | set(suffix) == set(edges),
            'counted scheduler does not cover the complete owner')
    require(set(calls) <= body and len(calls) <= MAX_CALL_SITES and
            sum(t == SCHEDULER for t in calls.values()) == 1,
            'counted scheduler requires one scheduler site inside its body')
    ordinary = sorted(set(calls.values()) - {SCHEDULER})
    require(1 <= len(ordinary) <= MAX_ORDINARY_TARGETS,
            'counted scheduler ordinary target budget exceeded')
    return dict(kind='zero-based-u16-strict-bound-scheduler-loop', header=header,
        entry_guard=guard, tail=tail, exit=exit_site, prefix=prefix,
        body=sorted(body), suffix=suffix, counter_register=counter, limit_register=limit,
        bound_narrowing=[narrow - 2, narrow], limit_range=[0, 65535],
        maximum_iterations=65535, maximum_scheduler_calls=65535,
        maximum_scheduler_calls_per_iteration=1, ordinary_targets=ordinary,
        rank='limit-counter at each guarded body entry; 0 <= counter < limit <= 65535',
        increment_wrap_impossible=True, actual_count_or_capacity_proved=False,
        conditional_loop_control_proved=True, unconditional_termination_proved=False,
        instruction_completion_and_returning_ABI_required=True)


def bind(proof, instructions, edges, calls, address):
    result = layout(instructions, edges, calls, address)
    for target in result['ordinary_targets']:
        require(not match.function_thunk.reserved(target) and target not in match.RUNTIME_HELPERS.values(),
                'counted scheduler requires ordinary indexed Thumb targets')
        body = proof.span(target)
        proof.dependencies[target] = body
        proof.records[target] = dict(address=target, end=target + len(body), bytes=len(body),
            body_sha256=hashlib.sha256(body).hexdigest(), **proof.identities,
            structure=dict(kind='complete-indexed-body-conditional-ordinary-call',
                callee_effects_proved=False, nested_execution_proved=False))
    result.update(source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        conditions=[
            'Each call and instruction completes under the existing ARM ABI and physical-access premises.',
            'All iterations preserve the complete live caller frame and loop registers; ordinary calls receive no tracked local alias or pointer word.',
            'The descriptor is consumed only during each scheduler invocation; previous invocations retain no local pointer or stale descriptor lifetime.',
            'External arrays and returned allocations have the actual access extents and do not alias live private or protected frame words. Count narrowing proves no capacity or memory permission.'])
    return result
