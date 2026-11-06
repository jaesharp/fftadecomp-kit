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
BIOS_SQRT_SELECTOR = 'bounded-buffer-bios-sqrt-scratch-v1'
BIOS_SQRT_SCHEMA = 'elf-symbol-thumb-bounded-buffer-bios-sqrt-scratch-v1'
BIOS_SQRT_CONTROL_FLOW = 'bounded buffer calls with an exact scalar BIOS Sqrt wrapper and killed return scratch'
GUARDED_SWITCH_SELECTOR = 'bounded-buffer-guarded-switch-v1'
GUARDED_SWITCH_SCHEMA = 'elf-symbol-thumb-bounded-buffer-guarded-switch-v1'
GUARDED_SWITCH_CONTROL_FLOW = 'bounded buffer calls with an exact unsigned-guarded local word switch'
SELECTORS = (SELECTOR, SCRATCH_SELECTOR, BIOS_SQRT_SELECTOR, GUARDED_SWITCH_SELECTOR)
SCHEMAS = (SCHEMA, SCRATCH_SCHEMA, BIOS_SQRT_SCHEMA, GUARDED_SWITCH_SCHEMA)
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


class GuardedSwitchBufferProof(DiscardedReturnScratchProof):
    """Compose the existing scalar switch CFG and bounded alias replay."""

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self._guarded_switches = {}

    def inspect(self, address, data):
        import analyze
        refinement = analyze.refine_function(data, address, json.loads(self.mapping),
            max_bytes=len(data), max_instructions=len(data)//2, rom_end=0x09000000,
            same_owner_long_branches=True, two_constant_word_switch=True)
        switches = refinement['word_switches']
        if not switches:
            return super().inspect(address, data)
        if len(switches) != 1 or switches[0].get('interposed_words', 0) not in (0, 2):
            raise ValueError('buffer switch requires one guarded table with zero or two scalar words')
        two_constants = switches[0].get('interposed_words', 0) == 2
        ins, edges, branches, calls, words = graph.graph(
            data, address, refinement, two_constant_word_switch=two_constants)
        if branches:
            raise ValueError('buffer switch excludes local BL control')
        for destination in calls.values():
            match.function_address_target(f'func_{destination:08X}', self.entries,
                                          address, len(data), len(self.rom))
        # This first pass proves saved-register/SP/return provenance and the
        # exact guarded dispatch. The caller's existing alias replay below
        # independently checks every actual buffer access and nested call.
        instructions = match.verify_leaf_instructions(data, address, True, calls,
            switch_relocations=words, allow_switch_constants=two_constants)
        if set(ins) != {item.address for item in instructions}:
            raise ValueError('buffer switch differs from complete verified instructions')
        partition = graph.partition(data, address, refinement, ins, words)
        transfer = address + switches[0]['dispatch'] + 8
        structure = dict(kind='complete-guarded-buffer-switch-v1',
            switch=switches[0], instructions=len(instructions), partition=partition,
            transfer=transfer, successors=list(edges[transfer]),
            table_words_sha256=hashlib.sha256(b''.join(
                data[offset:offset+4] for offset in sorted(words))).hexdigest())
        self.records[address] = dict(address=address, end=address+len(data), bytes=len(data),
            body_sha256=hashlib.sha256(data).hexdigest(), structure=structure, **self.identities)
        self._guarded_switches[address] = self.records[address]
        return instructions, {transfer: edges[transfer]}

    def guarded_manifest(self):
        from pathlib import Path
        import importlib
        producers = ('named_data_buffer_profile', 'owner_admission_profile',
                     'owner_graph_profile', 'switch_constants_profile', 'analyze',
                     'inert_spin_profile', 'local_long_branch_profile', 'match')
        return dict(schema=GUARDED_SWITCH_SCHEMA,
            contract='one exact unsigned-guarded complete local Thumb word table per '
                'inspected buffer callee, zero or two reached scalar constants; '
                'existing bounded alias accesses, escapes and return provenance '
                'are checked on all actual finite successors; ordinary direct calls '
                'use only conditional compatible returning ABI summaries; no physical '
                'readability, initialization, nonalias, numerical or termination theorem',
            source_sha256={name+'.py': hashlib.sha256(
                Path(importlib.import_module(name).__file__).read_bytes()).hexdigest()
                for name in producers},
            observations=[self._guarded_switches[key] for key in sorted(self._guarded_switches)])


class BiosSqrtScratchProof(DiscardedReturnScratchProof):
    """An explicit conditional scalar ABI for one exact two-instruction wrapper."""

    wrapper_bytes = b'\x08\xdf\x70\x47'
    bios_contract = (
        'conditional compatible BIOS service 8 normal-return ABI: R0 is a scalar '
        'input and scalar result, no memory access or pointer result, R4-R11/SP '
        'are preserved; R1-R3 may be clobbered and must each be killed on every '
        'consumer path before any observation or normal return; no numerical '
        'Sqrt equivalence, BIOS implementation, physical memory, initialization, '
        'nonalias or termination theorem')

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self._bios_calls = {}

    def check_arguments(self, address, arguments, stack, incoming, protected,
                        *, constants=None, site=None, **context):
        offset = address - match.ROM_BASE
        prefix = self.rom[offset:offset + 2] if offset >= 0 else b''
        if len(prefix) != 2 or prefix[1] != 0xdf:
            return super().check_arguments(address, arguments, stack, incoming,
                protected, constants=constants, site=site, **context)
        data = self.span(address)
        if data != self.wrapper_bytes:
            raise ValueError('BIOS Sqrt requires exact complete svc #8; bx lr wrapper')
        scratch = {match.ARM_REG_R0 + n for n in (1, 2, 3)}
        if set(arguments) - scratch:
            raise ValueError('BIOS Sqrt requires scalar R0 and excludes control-register aliases')
        if context.get('words'):
            raise ValueError('BIOS Sqrt excludes word-provenance composition')
        # The exact wrapper never reads SP or memory. Incoming pointer slots
        # remain untouched under this explicit memory-free BIOS ABI premise.
        for value in (*arguments.values(), *incoming.values()):
            self.validate_pointer_value(value, stack)
        if type(site) is not int:
            raise ValueError('BIOS Sqrt requires an actual direct consumer call site')
        owners = [row for row in self.entries
                  if int(row['rom'], 16) <= site < int(row['end'], 16)]
        if len(owners) != 1:
            raise ValueError('BIOS Sqrt requires one complete consumer')
        consumer = int(owners[0]['rom'], 16)
        consumer_data = match.BufferCallProof.span(self, consumer)
        if len(consumer_data) > MAX_BYTES:
            raise ValueError('BIOS Sqrt consumer exceeds bounded owner size')
        validate_owner(consumer_data, consumer, self.rom, self.mapping, self.index)
        import owner_admission_profile as owner
        refinement = owner.refine(consumer_data, consumer, self.mapping)
        ins, edges, branches, calls, words = graph.graph(consumer_data, consumer, refinement)
        if branches or words or calls.get(site) != address:
            raise ValueError('BIOS Sqrt differs from the exact ordinary consumer call')
        pending = [(site + ins[site].size, frozenset(scratch))]
        seen = set()
        while pending:
            current, live = pending.pop()
            if (current, live) in seen:
                continue
            if len(seen) >= 4096:
                raise ValueError('BIOS Sqrt continuation state budget exceeded')
            seen.add((current, live))
            instruction = ins[current]
            read, written = instruction.regs_access()
            if set(read) & live or current in calls and live:
                raise ValueError('consumer observes BIOS Sqrt scratch before a killing write')
            live -= set(written)
            if live and not edges[current]:
                raise ValueError('BIOS Sqrt scratch reaches normal return before a killing write')
            pending.extend((target, live) for target in edges[current] if live)
        self.dependencies[address] = data
        self.records[address] = dict(address=address, end=address + len(data),
            bytes=len(data), body_sha256=hashlib.sha256(data).hexdigest(),
            structure=dict(kind='exact-scalar-bios-sqrt-wrapper-v1', instructions=2,
                           bytes_hex=data.hex(), conditional_ABI=self.bios_contract),
            **self.identities)
        receipt = dict(address=address, call_site=site, consumer=consumer,
            consumer_sha256=hashlib.sha256(consumer_data).hexdigest(),
            partition=graph.partition(consumer_data, consumer, refinement, ins, words),
            incoming_aliases=[[r-match.ARM_REG_R0, v] for r, v in sorted(arguments.items())],
            untouched_incoming_slots=sorted(incoming.items()),
            protected_slots=sorted(protected),
            killed_registers=[1, 2, 3], continuation_states=len(seen))
        self._bios_calls[json.dumps(receipt, sort_keys=True)] = receipt
        return self.word_result({}, {})

    def bios_manifest(self):
        from pathlib import Path
        import importlib
        producers = ('named_data_buffer_profile', 'owner_admission_profile',
                     'owner_graph_profile', 'analyze', 'inert_spin_profile',
                     'local_long_branch_profile', 'match')
        return dict(schema='exact-scalar-bios-sqrt-conditional-abi-v1',
            wrapper_hex=self.wrapper_bytes.hex(), contract=self.bios_contract,
            source_sha256={name+'.py': hashlib.sha256(
                Path(importlib.import_module(name).__file__).read_bytes()).hexdigest()
                for name in producers},
            observations=[self._bios_calls[key] for key in sorted(self._bios_calls)])
