"""Initialized search queries composed with a complete ordinary continuation.

External object validity, frame separation, compatible returning calls and the
non-result R2 ABI boundary remain explicit conditions. No allocator, callback
installation, arbitrary-memory or termination theorem is supplied.
"""
import hashlib
import struct
from pathlib import Path

import match
import named_data_buffer_profile as named
import known_list_query_closure_profile as known
import owner_graph_profile as graph
import function_thunk_profile as thunk
from software_double_profile import indices, span_record

SELECTOR = 'conditional-known-list-query-continuation-v1'
SCHEMA = 'elf-symbol-thumb-conditional-known-list-query-continuation-v1'
CONTROL_FLOW = 'initialized known search callback with bounded continuation aliases and conditional returning ABI'
ITERATOR, CALLBACK = 0x080C7CC0, 0x0809AB5C


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def query_prefix(data, address, instructions, edges, calls):
    """Interpret the actual straight entry path through its first query call."""
    sites = [site for site, target in calls.items() if target == ITERATOR]
    require(len(sites) == 1 and sites[0] == min(calls),
            'one known query must be the first complete root call')
    stop = sites[0]
    require(all(target > stop or source < stop and target == source + instructions[source].size
                for source, targets in edges.items() for target in targets),
            'query prefix cannot be reentered or reached through another path')
    regs = [('entry', n) for n in range(16)]
    stack, local, stores = [], set(), {}
    query_literal = None
    site = address
    while site < stop:
        require(site in instructions and site-address <= 128,
                'query prefix leaves its bounded complete code')
        item = instructions[site]
        code = int.from_bytes(item.bytes, 'little')
        require(item.size == 2 and edges[site] == (site+2,),
                'query initialization requires a straight entry path')
        if code & 0xfe00 == 0xb400:
            numbers = [n for n in range(8) if code & (1 << n)]
            if code & 0x100:
                numbers.append(14)
            require(not stack and numbers and 14 in numbers and
                    all(n in (4, 5, 6, 7, 14) for n in numbers),
                    'query prefix requires ordinary protected saves')
            stack = [regs[n] for n in numbers]
        elif code & 0xff80 == 0xb080:
            count = code & 0x7f
            require(stack and not local and 3 <= count <= 32,
                    'query prefix requires one bounded private allocation')
            stack[:0] = [('uninitialized',)] * count
            local = set(range(-4*len(stack), -4*len(stack)+4*count))
        elif code & 0xf800 == 0x2000:
            regs[(code >> 8) & 7] = ('constant', code & 255)
        elif code & 0xfe00 == 0x1c00:
            require((code >> 6) & 7 == 0, 'query prefix ADD must preserve an origin')
            regs[code & 7] = regs[(code >> 3) & 7]
        elif code & 0xff00 == 0x4600:
            destination = (code & 7) | ((code >> 4) & 8)
            source = (code >> 3) & 15
            require(destination < 13 and source < 14,
                    'query prefix MOV cannot alter stack or control')
            regs[destination] = ('stack', -4*len(stack)) if source == 13 else regs[source]
        elif code & 0xf800 == 0x9000:
            register = (code >> 8) & 7
            offset = -4*len(stack) + 4*(code & 255)
            require(set(range(offset, offset+4)) <= local,
                    'query initialization cannot overwrite protected saves')
            stores[offset] = regs[register]
        elif code & 0xf800 == 0x4800:
            register = (code >> 8) & 7
            literal = ((site+4) & ~3) + 4*(code & 255) - address
            require(0 <= literal <= len(data)-4, 'query literal leaves complete root')
            value = struct.unpack_from('<I', data, literal)[0]
            regs[register] = ('constant', value)
            if register == 1:
                query_literal = literal
        elif code & 0xf800 == 0x6800:
            register, base = code & 7, (code >> 3) & 7
            require(regs[base][0] in ('entry', 'external-word') and
                    regs[base] not in (('entry', 13), ('entry', 14), ('entry', 15)),
                    'query context must come from an ordinary external object')
            regs[register] = ('external-word', regs[base], 4*((code >> 6) & 31))
        else:
            raise ValueError('unsupported operation before initialized known query')
        site += 2
    require(regs[0][0] == 'external-word' and regs[1] == ('constant', CALLBACK | 1)
            and regs[2][0] == 'stack' and query_literal is not None,
            'known query requires actual list, immutable callback and local R2')
    offset = regs[2][1]
    require(set(range(offset, offset+12)) <= local,
            'complete query must lie in allocated local words')
    key = stores.get(offset, ('uninitialized',))
    require(key[0] in ('entry', 'external-word', 'constant') and
            key not in (('entry', 13), ('entry', 14), ('entry', 15)) and
            stores.get(offset+8) == ('constant', 0),
            'query key and null result must be initialized by actual stores')
    return dict(site=stop, offset=offset, frame_words=len(stack),
                key_origin=key, result_initial_value=0, callback_literal=query_literal,
                opaque_unread_offsets=[4, 5, 6, 7], bytes=12)


class KnownListQueryContinuationProof(named.ConditionalThunkSelectiveScratchBufferProof):
    def bind_query_root(self, data, address, instructions, edges, calls, partition):
        require(not hasattr(self, '_query_root'), 'known query context is single use')
        self._query_prefix = query_prefix(data, address, instructions, edges, calls)
        self._query_root = (address, data, frozenset(site for site in edges if not edges[site]))
        self._query_calls, self._query_returns = [], set()
        self._query_partition = partition
        self._has_thunks = any(thunk.reserved(target) for target in calls.values())
        if self._has_thunks:
            super().bind_root(data, address, calls)

    def check_indirect_target(self, address, aliases, returns, *, site):
        if thunk.reserved(address):
            require(self._has_thunks, 'query continuation has no authenticated root thunk')
            return super().check_indirect_target(address, aliases, returns, site=site)

    def query_dependencies(self):
        if hasattr(self, '_query_dependencies'):
            return self._query_dependencies
        entries, rows = indices(self.mapping, self.index)
        for target in (ITERATOR, CALLBACK, 0x080C7B74, 0x0814225C):
            count, encoded = known.DEPENDENCIES[target]
            raw = bytes.fromhex(encoded)
            row = span_record(target, target+len(raw), entries, rows, self.rom)
            require(row['mode'] == 'thumb' and row['instrs'] == count and
                    self.span(target) == raw, 'complete known query dependency or count differs')
            self.dependencies[target] = raw
            self.records[target] = dict(address=target, end=target+len(raw), bytes=len(raw),
                body_sha256=sha(raw), structure=dict(kind='complete-known-query-dependency',
                instructions=count), **self.identities)
        require(self.rom[0x14225e:0x142260] == bytes.fromhex('c046') and not any(
                int(row['rom'], 16) < 0x08142260 and int(row['end'], 16) > 0x0814225e
                for row in entries) and not any(
                int(row[0], 16) < 0x08142260 and int(row[1], 16) > 0x0814225e for row in rows),
                'known R6 thunk requires separate unowned external padding')
        self._query_dependencies = known.callback_effects(
            self.dependencies[CALLBACK], CALLBACK, 'search')
        return self._query_dependencies

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if address != ITERATOR:
            return super().check_call(address, aliases, stack, slots,
                                     constants=constants, site=site, words=words)
        prefix = self._query_prefix
        r2 = match.ARM_REG_R0+2
        require(site == prefix['site'] and len(stack) == prefix['frame_words'] and
                {reg: offset for reg, offset in aliases.items() if reg in match.CALLER_CLOBBERED}
                == {r2: prefix['offset']} and not slots and not words,
                'query replay differs from initialized actual caller frame')
        for offset in range(prefix['offset'], prefix['offset']+12, 4):
            self.access(offset, 4, stack)
        effects = self.query_dependencies()
        self._query_calls.append(dict(site=site, target=address, prefix=prefix,
            callback_effects=effects, conservative_return_aliases=[[2, prefix['offset']]],
            nested_private_saved_bytes=24,
            query_writes=[[prefix['offset']+8, 4]], result='null or reached external object'))
        # Empty iteration retains R2=query. Nonempty iteration can replace R2
        # with the external object. Keep the possible local origin for all later
        # reads, calls and indirect arguments rather than treating it as dead.
        return {r2: prefix['offset']}

    def query_manifest(self):
        require(self._query_calls, 'query continuation requires an actual query composition')
        return dict(calls=self._query_calls, root_return_R2=sorted(self._query_returns),
            contract='Exact initialized query key/result, actual complete iterator/getter/callback; '
                'opaque query bytes4..7 are never read. Live local R2 remains tracked through '
                'every continuation access/call; only an exact normal root return discards it '
                'under the explicit non-result R2 ABI. Reached external objects must be live, '
                'initialized, readable and separate from private/saved frames; returning calls '
                'must satisfy compatible ABI and frame noninterference. No heap allocation, '
                'physical access, IWRAM installation, whole-program nonescape or termination '
                'is established.',
            source_sha256={p.name: sha(p.read_bytes()) for p in (
                Path(__file__), Path(known.__file__))})


def root_return_aliases(proof, data, address, site, aliases):
    if type(proof) is not KnownListQueryContinuationProof:
        return aliases
    require(not proof.active and proof._query_calls and
            proof._query_root[:2] == (address, data) and site in proof._query_root[2],
            'known query scratch requires its exact inactive normal root return')
    r2 = match.ARM_REG_R0+2
    if r2 in aliases:
        proof._query_returns.add((site, aliases[r2]))
    return {reg: offset for reg, offset in aliases.items() if reg != r2}


def prove(data, address, rom, mapping, index, objects, bindings):
    import owner_admission_profile as owner
    refinement = owner.refine(data, address, mapping)
    ins, edges, branches, calls, words = graph.graph(data, address, refinement)
    require(not branches and not words, 'known query continuation excludes local BL/switches')
    partition = graph.partition(data, address, refinement, ins, words)
    proof = KnownListQueryContinuationProof(rom, mapping, index, objects)
    proof.bind_query_root(data, address, ins, edges, calls, partition)
    require(bindings is not None and bindings['functions'] == [
        [proof._query_prefix['callback_literal'], f'func_{CALLBACK:08X}']]
        and not bindings['switches'], 'query requires its sole genuine callback relocation')
    verified = match.verify_leaf_instructions(data, address, True, calls, buffer_proof=proof)
    require(set(ins) == {item.address for item in verified}, 'query continuation CFG differs')
    result = dict(schema=SCHEMA, instructions=len(verified), calls=[
        [site-address, next((name for name, value in thunk.ALIASES.items() if value == target),
                           f'func_{target:08X}')]
        for site, target in sorted(calls.items())], runtime_calls=[], partition=partition,
        query=proof.query_manifest(), buffers=dict(
            dependencies=[proof.records[target] for target in sorted(proof.records)],
            normal_return_scratch=proof.scratch_manifest()))
    if proof._has_thunks:
        result['buffers']['conditional_thunks'] = proof.thunk_manifest()
    return result
