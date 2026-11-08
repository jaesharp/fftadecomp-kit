"""Compose complete initialized queries across checked scratch boundaries.

Each incoming local pointer is killed without observation before the nested
query. The possible expired nested R2 value is separately checked through the
actual consumer and direct callees until killed or an ordinary root return.
External memory validity, frame separation and returning ABI remain conditions.
"""
import match
import named_data_buffer_profile as named
import known_list_query_continuation_profile as query
import owner_graph_profile as graph
import function_thunk_profile as thunk

SELECTOR = 'conditional-nested-known-query-continuation-v1'
SCHEMA = 'elf-symbol-thumb-conditional-nested-known-query-continuation-v1'
CONTROL_FLOW = 'complete nested initialized queries with actual scratch nonobservation and conditional returning ABI'
MAX_STATES = 4096
MAX_DEPTH = 8
R2 = match.ARM_REG_R0 + 2
require = query.require


class ScratchObservation:
    """Reject every read of a watched value until an actual killing write.

Calls are never treated as a killing ABI summary: their complete actual
instructions are followed, returning the union of surviving watched origins.
Moving, spilling, comparing or dereferencing a watched origin is observation.
"""
    def __init__(self, load):
        self.load = load
        self.active = set()
        self.memo = {}
        self.states = 0
        self.observations = []

    def run(self, address, start, watched, depth=0):
        watched = frozenset(watched)
        require(watched <= {R2}, 'nested query watches only non-result R2')
        key = address, start, watched
        if key in self.memo:
            return self.memo[key]
        require(address not in self.active and depth < MAX_DEPTH,
                'scratch observation recursion or depth bound exceeded')
        ins, edges, calls = self.load(address)
        require(start in ins, 'scratch continuation must start in actual complete code')
        self.active.add(address)
        pending, seen, returned = [(start, watched)], set(), set()
        try:
            while pending:
                site, live = pending.pop()
                if not live or (site, live) in seen:
                    continue
                require(self.states < MAX_STATES, 'scratch observation state budget exceeded')
                self.states += 1
                seen.add((site, live))
                item = ins[site]
                read, written = item.regs_access()
                require(not set(read) & live,
                        'nested query scratch is observed before an actual killing write')
                if site in calls:
                    require(not thunk.reserved(calls[site]),
                            'live nested query scratch cannot cross an indirect thunk')
                    live = self.run(calls[site], calls[site], live, depth+1)
                else:
                    live -= set(written)
                if not edges[site]:
                    returned.update(live)
                else:
                    pending.extend((target, live) for target in edges[site] if live)
            result = frozenset(returned)
            self.memo[key] = result
            self.observations.append(dict(address=address, start=start,
                incoming=[r-match.ARM_REG_R0 for r in sorted(watched)],
                surviving_normal_returns=[r-match.ARM_REG_R0 for r in sorted(result)],
                states=len(seen)))
            return result
        finally:
            self.active.remove(address)


class NestedKnownQueryProof(query.KnownListQueryContinuationProof):
    def bind_query_root(self, data, address, instructions, edges, calls, partition):
        super().bind_query_root(data, address, instructions, edges, calls, partition)
        self._nested_queries = {}
        self._observation_graphs = {address: (instructions, edges, calls)}

    def observation_graph(self, address):
        if address in self._observation_graphs:
            return self._observation_graphs[address]
        import owner_admission_profile as owner
        data = self.span(address)
        refinement = owner.refine(data, address, self.mapping)
        ins, edges, branches, calls, words = graph.graph(data, address, refinement)
        require(not branches and not words,
                'scratch observation requires complete ordinary direct-call CFG')
        checked = match.verify_leaf_instructions(data, address, True, call_resolver=self.target)
        require(set(ins) == {item.address for item in checked},
                'scratch observation structure differs from complete verified instructions')
        self.dependencies[address] = data
        self.records[address] = dict(address=address, end=address+len(data), bytes=len(data),
            body_sha256=query.sha(data), structure=dict(kind='actual-scratch-nonobservation',
                instructions=len(ins), partition=graph.partition(data, address, refinement, ins, words)),
            **self.identities)
        self._observation_graphs[address] = ins, edges, calls
        return ins, edges, calls

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if address == query.ITERATOR or not aliases or thunk.reserved(address):
            return super().check_call(address, aliases, stack, slots,
                                     constants=constants, site=site, words=words)
        import owner_admission_profile as owner
        data = self.span(address)
        refinement = owner.refine(data, address, self.mapping)
        ins, edges, branches, calls, table = graph.graph(data, address, refinement)
        if query.ITERATOR not in calls.values():
            return super().check_call(address, aliases, stack, slots,
                                     constants=constants, site=site, words=words)
        require(not self.active and not branches and not table and not slots and not words
                and set(aliases) == {R2},
                'nested query requires its exact root call and sole local R2 origin')
        root_ins, _, root_calls = self._observation_graphs[self._query_root[0]]
        require(root_calls.get(site) == address and address != self._query_root[0],
                'nested query differs from authenticated root call')
        self.validate_pointer_value(aliases[R2], stack)
        prefix = query.query_prefix(data, address, ins, edges, calls)
        live, current = {R2}, address
        while current < prefix['site']:
            read, written = ins[current].regs_access()
            require(not set(read) & live,
                    'nested query prefix observes the incoming caller-local origin')
            live -= set(written)
            current += ins[current].size
        require(not live, 'nested query must kill incoming local R2 before its first call')

        # This is an actual-ROM helper composition, not a fabricated original
        # ELF relocation. Root original bindings remain checked by the caller.
        helper = query.prove(data, address, self.rom, self.mapping, self.index, self.objects,
            dict(functions=[[prefix['callback_literal'], f'func_{query.CALLBACK:08X}']], switches=[]))
        for target in helper['buffers']['dependencies']:
            body = self.span(target['address'])
            require(query.sha(body) == target['body_sha256'], 'nested query dependency changed')
            self.dependencies[target['address']] = body
            self.records[target['address']] = target
        self.dependencies[address] = data
        self.records[address] = dict(address=address, end=address+len(data), bytes=len(data),
            body_sha256=query.sha(data), structure=dict(kind='complete-nested-initialized-query',
                proof=helper, literal_authority='actual indexed ROM; no original ELF claim'),
            **self.identities)
        observer = ScratchObservation(self.observation_graph)
        observer.run(self._query_root[0], site+root_ins[site].size, {R2})
        self._nested_queries[site] = dict(site=site, target=address,
            incoming_aliases=[[2, aliases[R2]]], prefix=prefix,
            helper_body_sha256=query.sha(data), consumer=observer.observations,
            observations=observer.states,
            result_contract='Possible expired nested R2 is never read, copied, stored, '
                'compared or dereferenced before actual killing writes or a normal root '
                'return. Every reached direct callee is checked; no arity or purity premise.')
        return {}


def root_return_aliases(proof, data, address, site, aliases):
    if type(proof) is not NestedKnownQueryProof:
        return aliases
    require(not proof.active and proof._query_calls and
            proof._query_root[:2] == (address, data) and site in proof._query_root[2],
            'nested query scratch requires its exact inactive normal root return')
    if R2 in aliases:
        proof._query_returns.add((site, aliases[R2]))
    return {r: value for r, value in aliases.items() if r != R2}


def prove(data, address, rom, mapping, index, objects, bindings):
    import owner_admission_profile as owner
    refinement = owner.refine(data, address, mapping)
    ins, edges, branches, calls, words = graph.graph(data, address, refinement)
    require(not branches and not words, 'nested query root excludes local BL/switches')
    partition = graph.partition(data, address, refinement, ins, words)
    proof = NestedKnownQueryProof(rom, mapping, index, objects)
    proof.bind_query_root(data, address, ins, edges, calls, partition)
    require(bindings is not None and bindings['functions'] == [
        [proof._query_prefix['callback_literal'], f'func_{query.CALLBACK:08X}']]
        and not bindings['switches'], 'nested query root needs its genuine callback binding')
    verified = match.verify_leaf_instructions(data, address, True, calls, buffer_proof=proof)
    require(set(ins) == {item.address for item in verified}, 'nested query root CFG differs')
    require(proof._nested_queries, 'nested query policy requires an actual nested query')
    result = dict(schema=SCHEMA, instructions=len(verified), calls=[
        [site-address, next((name for name, value in thunk.ALIASES.items() if value == target),
                           f'func_{target:08X}')]
        for site, target in sorted(calls.items())], runtime_calls=[], partition=partition,
        query=proof.query_manifest(), nested_queries=[proof._nested_queries[site]
            for site in sorted(proof._nested_queries)], buffers=dict(
                dependencies=[proof.records[target] for target in sorted(proof.records)],
                normal_return_scratch=proof.scratch_manifest()))
    if proof._has_thunks:
        result['buffers']['conditional_thunks'] = proof.thunk_manifest()
    return result
