"""Explicit ordinary R2 formal output saved in one live SP0 pointer word."""
import hashlib
import json
from pathlib import Path

import match
import owner_graph_profile as graph
import function_thunk_profile as thunk
import descriptor_output_alias_profile as frames
import protected_descriptor_word_profile as words

SELECTOR = 'ordinary-formal-output-spill-v1'
SCHEMA = 'elf-symbol-thumb-ordinary-formal-output-spill-v1'
CONTROL_FLOW = ('complete Thumb owner; fixed-SP0 R2 formal output spill; '
                'conditional returning ordinary ARM ABI, no numeric or global-effect theorem')
MAX_DEPENDENCIES = 8
BIOS_SELECTOR = 'ordinary-formal-output-spill-bios-remainder-v1'
BIOS_SCHEMA = 'elf-symbol-thumb-ordinary-formal-output-spill-bios-remainder-v1'
BIOS_CONTROL_FLOW = 'fixed-SP0 formal output with an exact conditional scalar BIOS remainder wrapper'
SELECTORS = (SELECTOR, BIOS_SELECTOR)
SCHEMAS = (SCHEMA, BIOS_SCHEMA)


class FormalOutputSpillProof(frames.DescriptorOutputAliasProof):
    """Reuse frame and aligned-word utilities behind a closed, default-off policy."""
    dependency_budget = MAX_DEPENDENCIES

    def __init__(self, *args):
        super().__init__(*args)
        self.scopes, self.graphs = [], {}
        self.spills, self.reloads, self.writes = set(), set(), set()

    def target(self, address):
        if thunk.reserved(address):
            raise ValueError('formal output excludes callbacks and indirect thunks')
        return match.BufferCallProof.target(self, address)

    def inspect(self, address, data):
        import owner_admission_profile as owner
        refinement = owner.refine(data, address, self.mapping)
        instructions, edges, branches, calls, switch_words = graph.graph(data, address, refinement)
        partition = graph.partition(data, address, refinement, instructions, switch_words)
        if branches or switch_words or partition['words']:
            raise ValueError('formal output requires ordinary complete code without switches or literals')
        self.check_lifetime(data, address, list(instructions.values()))
        self.graphs[address] = edges
        self.records[address] = dict(address=address, end=address+len(data), bytes=len(data),
            body_sha256=hashlib.sha256(data).hexdigest(), **self.identities,
            structure=dict(kind='complete-closed-CFG-before-actual-effects-and-native-frame-v1',
                           instructions=len(instructions), partition=partition))
        return list(instructions.values()), {}

    def check_call(self, address, aliases, stack, slots=None, *, site=None, words=None, **kwargs):
        arguments = {reg:offset for reg,offset in aliases.items() if reg in match.CALLER_CLOBBERED}
        if set(arguments) != {match.ARM_REG_R2} or slots or words:
            raise ValueError('formal output requires only one register R2 local output, no descriptor words')
        return super().check_call(address, aliases, stack, site=site)

    def check_arguments(self, address, arguments, stack, incoming, protected, *, constants=None,
                        site=None, words=None, frame_base=None, root_frame=None, watched=()):
        outer = not self.scopes
        if incoming or protected or watched or (set(arguments) != {match.ARM_REG_R2} if outer else bool(arguments)):
            raise ValueError('formal output excludes nested pointer forwarding and stack/descriptor arguments')
        scope = dict(address=address, entry=-4*len(stack),
                     formal=arguments.get(match.ARM_REG_R2), spill=None)
        self.scopes.append(scope)
        try:
            result = match.BufferCallProof.check_arguments(self, address, arguments, stack, incoming,
                protected, constants=constants, site=site, words=words, frame_base=frame_base,
                root_frame=root_frame, watched=watched)
            if outer and (scope['spill'] is None or not any(row[0] == address for row in self.writes)):
                raise ValueError('formal output requires an actual spilled formal and u16 write')
            # This narrow profile exports no pointer result, including scratch residue.
            if result:
                raise ValueError('formal output cannot escape through a result register')
            return result
        finally:
            self.scopes.pop()

    def observe_frame_alias(self, *args):
        raise ValueError('formal output excludes construction of helper-local buffer aliases')

    def word_memory(self, instruction, aliases, constants, stack, facts, sp_offset, protected,
                    *, root_frame=None):
        operands = instruction.operands
        memories = [op for op in operands if op.type == match.ARM_OP_MEM]
        if not memories:
            return None, None, False, False
        if not self.scopes:
            if instruction.mnemonic.startswith('str') and operands[0].type == match.ARM_OP_REG and operands[0].reg in aliases:
                raise ValueError('formal output caller cannot create pointer descriptors')
            return words.ProtectedDescriptorWordProof.word_memory(self, instruction, aliases, constants,
                stack, facts, sp_offset, protected, root_frame=root_frame)
        scope = self.scopes[-1]
        memory = memories[0].mem
        reading = instruction.mnemonic.startswith('ldr')
        writing = instruction.mnemonic.startswith('str')
        register = operands[0].reg if operands[0].type == match.ARM_OP_REG else None
        if instruction.mnemonic.startswith(('stm', 'ldm', 'swp')):
            raise ValueError('formal output excludes block/atomic effects')
        pointer_store = writing and register in aliases
        if pointer_store:
            if scope['formal'] is None or instruction.mnemonic != 'str' or register != match.ARM_REG_R2 or \
                    memory.base != match.ARM_REG_SP or memory.disp or memory.index or instruction.writeback or \
                    aliases[register] != scope['formal'] or sp_offset >= scope['entry']:
                raise ValueError('formal output pointer requires the allocated fixed SP0 word')
            if scope['spill'] is not None and scope['spill'] != (instruction.address, sp_offset):
                raise ValueError('formal output permits one exact spill site and slot')
            scope['spill'] = instruction.address, sp_offset
            self.spills.add((scope['address'], instruction.address, sp_offset, scope['formal']))
        elif writing and memory.base == match.ARM_REG_SP and any(
                sp_offset+memory.disp < slot+4 and sp_offset+memory.disp+4 > slot for slot in facts):
            raise ValueError('formal output spilled pointer word was overwritten')
        if reading and memory.base == match.ARM_REG_SP and not memory.disp and scope['formal'] is not None:
            if instruction.mnemonic != 'ldr' or register not in (match.ARM_REG_R1, match.ARM_REG_R2) or \
                    memory.index or instruction.writeback or facts.get(sp_offset) != ('pointer', scope['formal']) or \
                    scope['spill'] is None or sp_offset != scope['spill'][1]:
                raise ValueError('formal output reload lacks its exact initialized surviving pointer word')
            self.reloads.add((scope['address'], instruction.address, sp_offset, register, scope['formal']))
        if memory.base in aliases:
            if scope['formal'] is None or not writing or pointer_store or instruction.mnemonic != 'strh' or \
                    memory.disp or memory.index or instruction.writeback or aliases[memory.base] != scope['formal']:
                raise ValueError('formal output requires only its exact offset-zero u16 write')
            self.writes.add((scope['address'], instruction.address, scope['formal'], 2))
        elif writing and memory.base != match.ARM_REG_SP:
            raise ValueError('formal output excludes unknown nested/global memory writes')
        return words.ProtectedDescriptorWordProof.word_memory(self, instruction, aliases, constants,
            stack, facts, sp_offset, protected, root_frame=root_frame)

    def complete_frame(self, address, data, instructions):
        super().complete_frame(address, data, instructions)
        # The formal write must occur on each normal return, not merely one path.
        if self.scopes[-1]['formal'] is not None:
            sites = {row[1] for row in self.writes if row[0] == address}
            if len(sites) != 1:
                raise ValueError('formal output requires one exact all-path write site')
            edges = self.graphs[address]
            pending, seen = [address], set()
            while pending:
                site = pending.pop()
                if site in sites or site in seen:
                    continue
                seen.add(site)
                if not edges[site]:
                    raise ValueError('formal output normal return precedes its u16 write')
                pending.extend(edges[site])

    def spill_manifest(self):
        if not self.spills or not self.reloads or not self.writes:
            raise ValueError('formal output requires actual spill/reload/write observations')
        return dict(schema=SCHEMA, output_width=2,
            spills=[list(row) for row in sorted(self.spills)],
            reloads=[list(row) for row in sorted(self.reloads)],
            writes=[list(row) for row in sorted(self.writes)],
            native_frames=self.native_frame_observations(),
            source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            premise='conditional returning ordinary ARM ABI; no numeric, nonalias, global-effect, readability or allocation theorem')


class BiosRemainderSpillProof(FormalOutputSpillProof):
    """One exact scalar service wrapper, without extending ordinary frame rules."""

    wrapper_address = 0x08141874
    wrapper_bytes = b'\x06\xdf\x08\x1c\x70\x47'
    contract = ('conditional compatible BIOS service6 normal-return ABI: scalar register '
        'inputs/results, no memory access or pointer result, R4-R11/SP and the wrapper '
        'return link preserved; R0-R3/R12 unknown after return. No division/remainder '
        'numerical equivalence, BIOS implementation, physical effects, initialization, '
        'nonalias or termination theorem')

    def __init__(self, *args):
        super().__init__(*args)
        self.bios_calls = {}

    def check_arguments(self, address, arguments, stack, incoming, protected, *,
                        constants=None, site=None, **context):
        if address != self.wrapper_address:
            return super().check_arguments(address, arguments, stack, incoming, protected,
                constants=constants, site=site, **context)
        if arguments or incoming or context.get('watched') or not self.scopes or \
                type(site) is not int:
            raise ValueError('BIOS remainder requires an actual nested scalar call without live register aliases')
        parent = self.scopes[-1]['address']
        if site not in self.graphs[parent]:
            raise ValueError('BIOS remainder requires its actual reached consumer instruction')
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        item = next(decoder.disasm(self.rom[site-match.ROM_BASE:site-match.ROM_BASE+4], site), None)
        if item is None or item.id != match.ARM_INS_BL or item.size != 4 or \
                item.operands[0].imm != address:
            raise ValueError('BIOS remainder differs from the actual direct consumer call')
        data = self.span(address)
        if data != self.wrapper_bytes:
            raise ValueError('BIOS remainder requires its exact complete svc6; adds r0,r1,0; bx lr body')
        words = dict(context.get('words') or {})
        for kind, value in words.values():
            if kind == 'pointer':
                self.validate_pointer_value(value, stack)
        self.dependencies[address] = data
        self.records[address] = dict(address=address, end=address+len(data), bytes=len(data),
            body_sha256=hashlib.sha256(data).hexdigest(), **self.identities,
            structure=dict(kind=BIOS_SCHEMA, instructions=3, wrapper_hex=data.hex(),
                conditional_ABI=self.contract))
        row = dict(site=site, target=address, consumer=parent,
            consumer_body_sha256=self.records[parent]['body_sha256'],
            untouched_pointer_word_slots=sorted(slot for slot, value in words.items() if value[0]=='pointer'),
            protected_slots=sorted(protected), unknown_results=[0,1,2,3,12])
        self.bios_calls[site] = row
        return self.word_result({}, words)

    def bios_manifest(self):
        if not self.bios_calls:
            raise ValueError('BIOS remainder profile requires an actual nested wrapper call')
        return dict(schema=BIOS_SCHEMA, conditional_ABI=self.contract,
            wrapper_address=self.wrapper_address, wrapper_hex=self.wrapper_bytes.hex(),
            source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            observations=[self.bios_calls[key] for key in sorted(self.bios_calls)])
