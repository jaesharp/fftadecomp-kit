"""Acyclic caller composition with one scheduler invocation per path.

Other calls use the existing ordinary indexed-call ABI summary. Their complete
body identities are authenticated, but their effects and nested execution are
not proved. No tracked local pointer may be present at those call sites.
"""
import hashlib
from pathlib import Path

import match
from scheduler_predicate_profile import acyclic

SCHEDULER = 0x08005B6C
MAX_SCHEDULER_SITES = 2
MAX_CALL_SITES = 8
MAX_ORDINARY_TARGETS = 4


def require(condition, message):
    if not condition:
        raise ValueError(message)


def phases(edges, calls):
    schedulers = sorted(site for site, target in calls.items() if target == SCHEDULER)
    ordinary = sorted(set(calls.values()) - {SCHEDULER})
    require(1 <= len(schedulers) <= MAX_SCHEDULER_SITES and
            1 <= len(ordinary) <= MAX_ORDINARY_TARGETS and
            len(calls) <= MAX_CALL_SITES and set(calls) <= set(edges),
            'scheduler branches exceed the explicit call-site or target bounds')
    after = dict.fromkeys(edges, False)
    for site in acyclic(edges):
        # Union at joins: an ordinary call or second scheduler reachable after
        # any scheduler return is refused, even if another arm has no call.
        require(not (after[site] and site in calls),
                'scheduler branches exclude every call after a scheduler return')
        scheduled = after[site] or calls.get(site) == SCHEDULER
        for target in edges[site]:
            after[target] |= scheduled
    return dict(scheduler_sites=schedulers, ordinary_targets=ordinary,
        scheduler_site_budget=MAX_SCHEDULER_SITES, call_site_budget=MAX_CALL_SITES,
        ordinary_target_budget=MAX_ORDINARY_TARGETS,
        maximum_scheduler_calls_per_path=1, ordinary_calls_after_scheduler=False)


def bind(proof, edges, calls):
    result = phases(edges, calls)
    for target in result['ordinary_targets']:
        require(not match.function_thunk.reserved(target) and
                target not in match.RUNTIME_HELPERS.values(),
                'scheduler branches require ordinary indexed Thumb call targets')
        body = proof.span(target)
        proof.dependencies[target] = body
        proof.records[target] = dict(address=target, end=target+len(body), bytes=len(body),
            body_sha256=hashlib.sha256(body).hexdigest(), **proof.identities,
            structure=dict(kind='complete-indexed-body-conditional-ordinary-call',
                callee_effects_proved=False, nested_execution_proved=False))
    result.update(source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        ordinary_call_contract=(
            'Each ordinary indexed call uses the existing returning ARM ABI summary: '
            'compatible registers, exact SP and protected caller/saved words preserved. '
            'No tracked local-register alias, pointer word or word-provenance fact may '
            'enter it. Complete body identity does not prove purity, memory effects, '
            'nested execution, readability, allocation separation or termination.'),
        ordinary_callee_effects_proved=False, nested_execution_proved=False)
    return result
