"""Explicit named-data buffer composition with exact read-only switch callees."""
import hashlib
import json
import struct

import match
import owner_graph_profile as graph
from inert_spin_profile import validate_span

SELECTOR = 'named-data-buffer-v1'
SCHEMA = 'elf-symbol-thumb-named-data-buffer-calls-v1'
SCRATCH_SELECTOR = 'bounded-buffer-discarded-return-scratch-v1'
SCRATCH_SCHEMA = 'elf-symbol-thumb-bounded-buffer-discarded-return-scratch-v1'
SCRATCH_CONTROL_FLOW = 'bounded buffer calls with exact unobserved R2/R3 normal-return scratch'
SELECTORS = (SELECTOR, SCRATCH_SELECTOR)
SCHEMAS = (SCHEMA, SCRATCH_SCHEMA)
CONTROL_FLOW = 'complete Thumb owner with typed data literals and ROM-proved bounded buffer callees'
MAX_DEPENDENCIES = 8
MAX_BYTES = 4096


def validate_owner(data, address, rom, mapping, index):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError('duplicate named-data buffer mapping key')
            result[key] = value
        return result
    json.loads(mapping, object_pairs_hook=unique)
    entries = validate_span(data, address, rom, mapping, index)
    entry = next(row for row in entries if int(row['rom'], 16) == address)
    fields = next(line.split() for line in index.decode().splitlines()
                  if line.split() and not line.lstrip().startswith('#') and
                  int(line.split()[0], 16) == address)
    # Legacy counts include literal words in some rows. They remain bounded
    # numeric annotations; the complete native CFG establishes the real count.
    if type(entry.get('instrs')) is not int or not 0 <= entry['instrs'] <= len(data)//2 or \
            len(fields) < 4 or not fields[3].isdigit() or not 0 <= int(fields[3]) <= len(data)//2:
        raise ValueError('malformed named-data buffer instruction-count annotation')


class NamedDataBufferProof(match.BufferCallProof):
    """Keep existing alias rules; add only an independently proved finite dispatch."""

    dependency_budget = MAX_DEPENDENCIES

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, stack_arguments=True)
        self.mapping, self.index, self.objects = mapping, index, objects
        self.requested = set()
        self.records = {}
        self.identities = {'rom_sha256': hashlib.sha256(rom).hexdigest(),
                           'mapping_sha256': hashlib.sha256(mapping).hexdigest(),
                           'index_sha256': hashlib.sha256(index).hexdigest(),
                           'objects_sha256': None if objects is None else hashlib.sha256(objects).hexdigest()}

    def span(self, address):
        if address not in self.requested and len(self.requested) >= self.dependency_budget:
            raise ValueError('named-data buffer dependency budget exceeded')
        self.requested.add(address)
        entry = self.target(address)
        if not 0 < int(entry['end'], 16) - address <= MAX_BYTES:
            raise ValueError('named-data buffer dependency exceeds bounded owner size')
        data = super().span(address)
        validate_owner(data, address, self.rom, self.mapping, self.index)
        return data

    def inspect(self, address, data):
        candidates = []
        for literal in range((-address) % 4, len(data) - 3, 4):
            encoding = match.preloaded_switch_encoding(data, address, literal)
            if encoding is not None:
                candidates.append((literal, encoding[-1]))
        if len(candidates) > 1:
            raise ValueError('ambiguous preloaded buffer switch')
        transfers = {}
        if candidates:
            literal, bound = candidates[0]
            end = literal + 4 * (bound + 2)
            if end > len(data):
                raise ValueError('preloaded buffer switch leaves complete owner')
            words = {offset: struct.unpack_from('<I', data, offset)[0] - address
                     for offset in range(literal, end, 4)}
            # This is a ROM-checked literal role, not an invented named object.
            # The existing complete read-only CFG proof and the alias replay
            # independently establish effects; literal identity grants no alias fact.
            value = struct.unpack_from('<I', data, literal - 4)[0]
            object_word = {literal - 4: ('ROM-checked literal word', value)}
            switch = match.preloaded_switch_layout(data, address, words, object_word)
            instructions = match.verify_leaf_instructions(data, address, True,
                switch_relocations=words, switch_data_relocations=object_word,
                preloaded_switch=True)
            transfers[address + switch['transfer']] = tuple(sorted(
                {address + target for offset, target in words.items() if offset != literal}))
            structure = {'kind': 'existing-complete-read-only-preloaded-switch-v1',
                         'switch': switch, 'instructions': len(instructions),
                         'object_word_sha256': hashlib.sha256(data[literal-4:literal]).hexdigest()}
        else:
            instructions, transfers = super().inspect(address, data)
            import owner_admission_profile as owner
            refinement = owner.refine(data, address, self.mapping)
            ins, _, branches, calls, words = graph.graph(data, address, refinement)
            if branches or words or set(ins) != {item.address for item in instructions}:
                raise ValueError('buffer dependency differs from complete ordinary CFG')
            structure = {'kind': 'complete-ordinary-buffer-owner-v1',
                         'instructions': len(instructions),
                         'partition': graph.partition(data, address, refinement, ins, words)}
        self.records[address] = {
            'address': address, 'end': address + len(data), 'bytes': len(data),
            'body_sha256': hashlib.sha256(data).hexdigest(), 'structure': structure,
            **self.identities}
        return instructions, transfers


class DiscardedReturnScratchProof(NamedDataBufferProof):
    """Project R2/R3 only after checking their complete actual continuation."""

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self._consumers = []
        self._scratch_returns = {}

    def check_arguments(self, address, arguments, stack, incoming, protected,
                        *, constants=None, site=None, **context):
        self._consumers.append((address, site))
        try:
            return super().check_arguments(address, arguments, stack, incoming,
                protected, constants=constants, site=site, **context)
        finally:
            self._consumers.pop()

    def normal_return_aliases(self, address, site, aliases):
        scratch = {match.ARM_REG_R0 + 2, match.ARM_REG_R0 + 3}
        projected = {register: offset for register, offset in aliases.items()
                     if register in scratch}
        if not projected:
            return aliases
        if not self._consumers or self._consumers[-1][0] != address:
            raise ValueError('discarded return scratch requires its active exact callee')
        call_site = self._consumers[-1][1]
        if type(call_site) is not int:
            raise ValueError('discarded return scratch requires the actual consumer call site')
        owners = [row for row in self.entries
                  if int(row['rom'], 16) <= call_site < int(row['end'], 16)]
        if len(owners) != 1:
            raise ValueError('discarded return scratch requires one complete consumer')
        consumer = int(owners[0]['rom'], 16)
        data = match.BufferCallProof.span(self, consumer)
        if len(data) > MAX_BYTES:
            raise ValueError('discarded return scratch consumer exceeds bounded owner size')
        validate_owner(data, consumer, self.rom, self.mapping, self.index)
        import owner_admission_profile as owner
        refinement = owner.refine(data, consumer, self.mapping)
        ins, edges, branches, calls, words = graph.graph(data, consumer, refinement)
        if branches or words or calls.get(call_site) != address:
            raise ValueError('discarded return scratch differs from the exact ordinary consumer')
        pending = [(call_site + ins[call_site].size, frozenset(projected))]
        seen = set()
        while pending:
            current, live = pending.pop()
            if (current, live) in seen:
                continue
            seen.add((current, live))
            instruction = ins[current]
            read, written = instruction.regs_access()
            if set(read) & live or current in calls and live:
                raise ValueError('consumer observes discarded return scratch before a killing write')
            live -= set(written)
            pending.extend((target, live) for target in edges[current] if live)
        receipt = dict(address=address, site=site, consumer=consumer,
            call_site=call_site, call_target=address,
            consumer_sha256=hashlib.sha256(data).hexdigest(),
            partition=graph.partition(data, consumer, refinement, ins, words),
            projected=[[register-match.ARM_REG_R0, offset]
                       for register, offset in sorted(projected.items())],
            continuation_states=len(seen))
        self._scratch_returns[json.dumps(receipt, sort_keys=True)] = receipt
        return {register: offset for register, offset in aliases.items()
                if register not in scratch}

    def scratch_manifest(self):
        from local_long_branch_profile import DISCARDED_SCRATCH_SCHEMA, DISCARDED_SCRATCH_CONTRACT
        from pathlib import Path
        import importlib
        producers = ('named_data_buffer_profile', 'owner_admission_profile',
                     'owner_graph_profile', 'analyze', 'inert_spin_profile',
                     'local_long_branch_profile', 'match')
        return dict(schema=DISCARDED_SCRATCH_SCHEMA, registers=[2, 3],
            contract=DISCARDED_SCRATCH_CONTRACT +
                '; every actual consumer path leaves projected values unobserved until '
                'a killing write or normal return; existing bounded alias/effect proof '
                'unchanged; conditional compatible returning ABI only, no memory '
                'initialization, physical readability, nonalias or termination theorem',
            source_sha256={name+'.py': hashlib.sha256(
                Path(importlib.import_module(name).__file__).read_bytes()).hexdigest()
                for name in producers},
            observations=[self._scratch_returns[key] for key in sorted(self._scratch_returns)])
