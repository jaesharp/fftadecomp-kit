"""Opt-in structural division composition; no quotient or termination theorem."""
import hashlib
import json
from pathlib import Path

import match
import owner_graph_profile as graph
import local_long_branch_profile as frame
import canonical_integer_scalar_inventory as integer
import named_data_buffer_profile as named
import three_halfword_output_buffer_profile as three
import zero_index_stack_profile as zero_index

SELECTOR = 'bounded-buffer-three-output-dynamic-division-v1'
SCHEMA = 'elf-symbol-thumb-bounded-buffer-three-output-dynamic-division-v1'
CONTROL_FLOW = 'three bounded halfword outputs and closed dynamic division frame/alias effects'
MAX_DEPENDENCIES = 10
DIV, ZERO = integer.OPERATIONS['__divsi3'], integer.ZERO
SCALAR, UNINITIALIZED, RETURN = ('scalar',), ('uninitialized',), ('entry-lr',)
SCRATCH_POLICY = {'schema': 'thumb-discarded-exit-scratch-v1', 'registers': [2, 3]}


def scalar(value):
    return value[0] in ('scalar', 'constant')


def number(register):
    if register == match.ARM_REG_SP:
        return 13
    if register == match.ARM_REG_LR:
        return 14
    if register == match.ARM_REG_PC:
        return 15
    if match.ARM_REG_R0 <= register <= match.ARM_REG_R0 + 12:
        return register - match.ARM_REG_R0
    raise ValueError('dynamic division excludes non-general register operands')


class OriginReplay:
    """Finite exact alternatives, private initialized bytes, opaque saved origins.

    Scalar computations deliberately forget their result. Only immediate MOV
    constants and exact copies survive, for the existing proven-zero local load.
    No incoming memory is accessible. PUSH/POP are the only opaque word transport.
    Every recursive call uses its supplied complete CFG, never an ABI clobber rule.
    """

    def __init__(self, programs):
        self.programs = programs
        self.cache, self.active, self.observations = {}, set(), {}

    def run(self, address, entry):
        entry = tuple(entry)
        key = address, entry
        if key in self.cache:
            return self.cache[key]
        if address in self.active or len(entry) != 15 or entry[13] != ('local', 0) or entry[14] != RETURN:
            raise ValueError('dynamic division requires an exact nonrecursive entry context')
        self.active.add(address)
        try:
            result = self._run(address, entry)
            self.cache[key] = result
            return result
        finally:
            self.active.remove(address)

    def _run(self, address, entry):
        instructions, edges, calls = self.programs[address]
        # State: registers, top-first saved/local words, initialized local bytes,
        # and whether condition flags depend on a pointer/opaque value.
        initial = (entry, (), (), False)
        pending, seen, returns = [(address, initial)], set(), set()
        read_sites, write_sites, call_sites = set(), set(), set()
        while pending:
            site, state = pending.pop()
            if (site, state) in seen:
                continue
            if len(seen) >= 4096:
                raise ValueError('dynamic division origin state budget exceeded')
            seen.add((site, state))
            item = instructions[site]
            values, stack, memory, dirty_flags = state
            values, stack, memory = list(values), list(stack), dict(memory)
            values[13] = ('local', -4 * len(stack))
            code = int.from_bytes(item.bytes, 'little')
            operands, name = item.operands, item.mnemonic
            alternatives = None
            terminal = not edges[site]

            def reject(message):
                raise ValueError(f'dynamic division 0x{site:08X}: {message}')

            def finish_return(value):
                if value != RETURN or stack or any(values[n] != entry[n] for n in range(4, 12)):
                    reject('saved/control/frame restoration differs')
                if dirty_flags:
                    reject('return exposes opaque/pointer-dependent flags')
                if not terminal:
                    reject('return has unexpected outgoing edges')
                values[13] = ('local', 0)
                returns.add((site, tuple(values)))

            if site in calls:
                if item.size != 4 or name != 'bl' or calls[site] not in self.programs:
                    reject('unproved nested call')
                child = list(values)
                child[13], child[14] = ('local', 0), RETURN
                if calls[site] == DIV and not all(scalar(child[n]) for n in (0, 1)):
                    reject('division operand interprets an opaque or pointer origin')
                child_returns = self.run(calls[site], tuple(child))
                alternatives = []
                for _, returned in child_returns:
                    returned = list(returned)
                    returned[13], returned[14] = values[13], ('call-lr', site)
                    alternatives.append((tuple(returned), tuple(stack), tuple(sorted(memory.items())), False))
                call_sites.add(site)
            elif item.size != 2:
                reject('non-Thumb1 instruction width')
            elif code & 0xFE00 in (0xB400, 0xBC00):
                registers = [n for n in range(8) if code & (1 << n)]
                push = code & 0xFE00 == 0xB400
                if code & 0x100:
                    registers.append(14 if push else 15)
                if push:
                    if any(values[n][0] == 'local' for n in registers):
                        reject('local address pushed into a protected saved word')
                    stack[:0] = [('saved', values[n]) for n in registers]
                else:
                    if len(registers) > len(stack) or any(row[0] != 'saved' for row in stack[:len(registers)]):
                        reject('pop does not consume exact protected saved words')
                    popped = stack[:len(registers)]
                    del stack[:len(registers)]
                    for n, (_, value) in zip(registers, popped):
                        if n == 15:
                            finish_return(value)
                        else:
                            values[n] = value
            elif code & 0xFF00 == 0xB000:
                count = code & 0x7F
                old_sp = -4 * len(stack)
                if not code & 0x80:
                    if count > len(stack) or any(row != ('local',) for row in stack[:count]):
                        reject('deallocation touches protected saved words')
                    del stack[:count]
                    for offset in range(old_sp, old_sp + count * 4):
                        memory.pop(offset, None)
                else:
                    stack[:0] = [('local',)] * count
                    for offset in range(old_sp-count*4, old_sp):
                        memory[offset] = UNINITIALIZED
            elif code & 0xFF00 == 0x4600:
                destination, source = (code & 7) | ((code >> 4) & 8), (code >> 3) & 15
                if destination == 15:
                    finish_return(values[source])
                elif destination == 13 or source == 15:
                    reject('unsupported control register MOV')
                else:
                    values[destination] = values[source]
            elif code & 0xFF87 == 0x4700:
                finish_return(values[(code >> 3) & 15])
            elif code & 0xF800 == 0x2000:
                values[(code >> 8) & 7] = ('constant', code & 255)
                dirty_flags = False
            elif code & 0xF800 == 0xA800:
                values[(code >> 8) & 7] = ('local', -4 * len(stack) + 4 * (code & 255))
            elif code & 0xF800 == 0x3000 and values[(code >> 8) & 7][0] == 'local':
                n = (code >> 8) & 7
                values[n] = ('local', values[n][1] + (code & 255))
                dirty_flags = True
            elif code & 0xFE00 == 0x1C00 and code & 0x01C0 == 0:
                # ADDS #0 copies bits but flags retain the origin sensitivity.
                source, destination = (code >> 3) & 7, code & 7
                values[destination] = values[source]
                dirty_flags = not scalar(values[source])
            elif any(op.type == match.ARM_OP_MEM for op in operands):
                memories = [op.mem for op in operands if op.type == match.ARM_OP_MEM]
                if len(memories) != 1 or name not in ('ldr', 'ldrb', 'ldrh', 'ldrsb', 'ldrsh', 'str', 'strb', 'strh'):
                    reject('unsupported memory transfer')
                mem = memories[0]
                base = values[number(mem.base)]
                if base[0] != 'local':
                    reject('memory base is not an allocated private local')
                if mem.index and values[number(mem.index)] != ('constant', 0):
                    reject('indexed local access lacks exact zero index')
                width = 1 if name in ('ldrb', 'ldrsb', 'strb') else 2 if name in ('ldrh', 'ldrsh', 'strh') else 4
                offset = base[1] + mem.disp
                if offset % width or offset < -4*len(stack) or offset+width > 0 or any(
                        stack[(byte + 4*len(stack))//4] != ('local',) for byte in range(offset, offset+width)):
                    reject('local access crosses a protected, incoming or dead frame byte')
                n = number(operands[0].reg)
                if name.startswith('str'):
                    if not scalar(values[n]):
                        reject('opaque/pointer origin stored into local bytes')
                    for byte in range(offset, offset+width):
                        memory[byte] = SCALAR
                    write_sites.add(site)
                else:
                    if any(memory.get(byte, UNINITIALIZED) == UNINITIALIZED for byte in range(offset, offset+width)):
                        reject('uninitialized local byte observed')
                    values[n] = SCALAR
                    read_sites.add(site)
            elif name.startswith('b') and name != 'bic' and name != 'bics':
                if name != 'b' and dirty_flags:
                    reject('conditional branch observes opaque/pointer flags')
            else:
                # Full operation/CFG verification precedes this replay. Do not
                # use unknown opcodes to manufacture initialized scalar facts.
                if name not in ('lsl', 'lsls', 'lsr', 'lsrs', 'asr', 'asrs', 'add', 'adds',
                        'sub', 'subs', 'cmp', 'cmn', 'tst', 'neg', 'negs', 'rsb', 'rsbs', 'and', 'ands',
                        'eor', 'eors', 'orr', 'orrs', 'bic', 'bics', 'mvn', 'mvns',
                        'mul', 'muls', 'adc', 'adcs', 'sbc', 'sbcs', 'ror', 'rors'):
                    reject('unsupported scalar operation')
                read, written = item.regs_access()
                general_reads = [number(r) for r in read if r in (*range(match.ARM_REG_R0, match.ARM_REG_R0+13), match.ARM_REG_SP, match.ARM_REG_LR, match.ARM_REG_PC)]
                if any(n >= 13 or not scalar(values[n]) for n in general_reads):
                    reject('scalar operation observes an opaque/pointer origin')
                if name in ('adc', 'adcs', 'sbc', 'sbcs') and dirty_flags:
                    reject('arithmetic observes opaque/pointer carry')
                for r in written:
                    if match.ARM_REG_R0 <= r <= match.ARM_REG_R0+12:
                        values[number(r)] = SCALAR
                if item.update_flags or name in ('cmp', 'cmn', 'tst'):
                    dirty_flags = False
            if terminal:
                if not any(row[0] == site for row in returns):
                    reject('terminal instruction is not a checked return')
                continue
            if alternatives is None:
                values[13] = ('local', -4 * len(stack))
                alternatives = [(tuple(values), tuple(stack), tuple(sorted(memory.items())), dirty_flags)]
            pending.extend((target, result) for target in edges[site] for result in alternatives)
        if {site for site, _ in seen} != set(instructions) or not returns:
            raise ValueError('dynamic division replay lacks complete instruction/return coverage')
        result = tuple(sorted(returns))
        self.observations[(address, entry)] = dict(address=address, states=len(seen),
            local_reads=sorted(read_sites), local_writes=sorted(write_sites), calls=sorted(call_sites),
            entry=entry, returns=result)
        return result


def prove(data, address, rom, mapping, index, *, selector):
    """Closed local-memory callee prerequisite, including the canonical zero path."""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('dynamic division requires its explicit selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('dynamic division requires immutable byte inputs and integer address')
    import owner_admission_profile as owner
    import owner_runtime_profile as operations
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    ins, edges, branches, calls, words = graph.graph(data, address, refinement)
    if branches or words or not calls or set(calls.values()) != {DIV} or len(data) > named.MAX_BYTES:
        raise ValueError('dynamic division requires a bounded complete ordinary DIV-only callee')
    operations.verify_operations(ins, edges, address, branches, calls, refinement)
    entries, rows = integer.canonical.indices(mapping, index)
    if integer.canonical.span_record(address, address+len(data), entries, rows, rom)['instrs'] != len(ins):
        raise ValueError('dynamic division complete dual-index instruction count differs')
    closure, frames, components = integer.prove_called_closures(rom, mapping, index, {'__divsi3'})
    programs = {address: (ins, edges, calls)}
    for target, end in ((DIV, integer.SPECS['__divsi3'][0]), (ZERO, ZERO+2)):
        raw = rom[target-match.ROM_BASE:end-match.ROM_BASE]
        child_ins, child_edges, child_branches, child_calls, child_words = graph.graph(raw, target, owner.refine(raw, target, mapping))
        if child_branches or child_words or set(child_calls.values()) - {ZERO}:
            raise ValueError('dynamic division runtime graph differs from canonical closure')
        programs[target] = child_ins, child_edges, child_calls
    restored = frame.prove_frame(ins, edges, address, {}, calls, stack_aliases=True,
        zero_index_profile=zero_index.SELECTOR, discarded_exit_scratch=SCRATCH_POLICY)
    entry = tuple(SCALAR if n < 2 else ('entry', n) for n in range(13)) + (('local', 0), RETURN)
    replay = OriginReplay(programs)
    returned = replay.run(address, entry)
    if sorted({site for site, _ in returned}) != restored['returns']:
        raise ValueError('dynamic division origin/frame return coverage differs')
    # A remaining private address is never exported as a caller-local offset.
    # It must be discharged independently at the exact consumer continuation.
    residual = sorted({(site, n, value[1]) for site, values in returned
                       for n, value in enumerate(values[:13]) if value[0] == 'local'})
    if any(n not in (2, 3) for _, n, _ in residual):
        raise ValueError('dynamic division local return address outside R2/R3 scratch')
    if sorted({(site, n, offset) for site, n, offset, _ in restored['discarded_exit_scratch']['residual_aliases']}) != residual:
        raise ValueError('dynamic division local return aliases disagree with strict frame proof')
    return dict(schema=SCHEMA, selector=SELECTOR, address=address, end=address+len(data),
        body_sha256=hashlib.sha256(data).hexdigest(), instructions=len(ins),
        partition=graph.partition(data,address,refinement,ins,words), frame=restored,
        runtime_closure=[[a,p] for a,p in sorted(closure.items())],
        runtime_frames=[[a,p] for a,p in sorted(frames.items())], runtime_components=components,
        maximum_additional_stack_bytes=restored['maximum_frame_bytes'] + frames[DIV]['maximum_additional_stack_bytes'],
        origin_replay=[v for _,v in sorted(replay.observations.items())],
        returns=returned, residual_local_scratch=residual,
        numeric_operand_preconditions=[], numeric_return_facts=[], termination_claim=False,
        external_memory_reads=[], external_memory_writes=[], incoming_stack_reads=[],
        caller_observation_obligation='Exact continuation must discharge every residual local or incoming R2/R3 alias; other incoming aliases must be retained.',
        caller_composition=False, physical_nonalias_claim=False)


class DynamicDivisionBufferProof(three.ThreeOutputBufferProof):
    """Existing three outputs plus the closed, actual-consumer DIV prerequisite."""

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self._division = {}

    def control_overwrites(self, address, site, registers):
        """Returned control bits require real overwrites, not scalar facts."""
        if not registers:
            return None
        import owner_admission_profile as owner
        owners = [row for row in self.entries if int(row['rom'],16) <= site < int(row['end'],16)]
        if len(owners) != 1:
            raise ValueError('dynamic division control origin needs one actual caller')
        caller = int(owners[0]['rom'],16)
        data = match.BufferCallProof.span(self, caller)
        named.validate_owner(data,caller,self.rom,self.mapping,self.index)
        refinement = owner.refine(data,caller,self.mapping)
        ins, edges, branches, calls, words = graph.graph(data,caller,refinement)
        if len(data) > named.MAX_BYTES or branches or words or calls.get(site) != address:
            raise ValueError('dynamic division control origin lacks its exact bounded continuation')
        pending, seen = [(site+ins[site].size,frozenset(registers))], set()
        while pending:
            current, live = pending.pop()
            if (current,live) in seen:
                continue
            if len(seen) >= 4096:
                raise ValueError('dynamic division control continuation budget exceeded')
            seen.add((current,live))
            read,written = ins[current].regs_access()
            if set(read) & live or current in calls:
                raise ValueError('consumer observes returned control origin before overwrite')
            live -= set(written)
            if live and not edges[current]:
                raise ValueError('returned control origin reaches caller return before overwrite')
            pending.extend((target,live) for target in edges[current] if live)
        return dict(caller=caller,call_site=site,registers=sorted(registers),states=len(seen),
            body_sha256=hashlib.sha256(data).hexdigest(),
            partition=graph.partition(data,caller,refinement,ins,words))

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if address == three.WRAPPER[0]:
            return super().check_call(address, aliases, stack, slots,
                constants=constants, site=site, words=words)
        if type(site) is not int or slots or words or any(number(r) in (0, 1, 13, 14, 15) for r in aliases):
            raise ValueError('dynamic division requires scalar operands, exact caller and no incoming pointer words')
        for offset in aliases.values():
            self.validate_pointer_value(offset, stack)
        data = self.span(address)
        proof = prove(data, address, self.rom, self.mapping, self.index, selector=SELECTOR)
        incoming = {number(r): offset for r, offset in aliases.items()}
        returned_aliases = None
        control_receipts = []
        self._consumers.append((address, site))
        try:
            for return_site, values in proof['returns']:
                actual, scratch, control = {}, {}, set()
                for n, value in enumerate(values[:13]):
                    if n not in (0, 1, 2, 3, 12):
                        continue  # independently proved exact saved-register restoration
                    if value[0] == 'entry' and value[1] in incoming:
                        actual[match.ARM_REG_R0+n] = incoming[value[1]]
                    elif value[0] == 'local':
                        scratch[match.ARM_REG_R0+n] = value[1]
                    elif value == RETURN:
                        control.add(match.ARM_REG_R0+n)
                    elif value[0] not in ('scalar', 'constant', 'entry'):
                        raise ValueError('dynamic division return has unsupported control provenance')
                control_receipts.append(self.control_overwrites(address,site,control))
                # A callee-local offset has a different frame origin; projection
                # checks only register observations and must remove it entirely.
                result = self.normal_return_aliases(address, return_site, actual | scratch)
                if set(result) & set(scratch):
                    raise ValueError('dynamic division private local pointer escapes consumer')
                if returned_aliases is not None and result != returned_aliases:
                    raise ValueError('dynamic division return alternatives have incompatible aliases')
                returned_aliases = result
        finally:
            self._consumers.pop()
        for target, end in ((DIV, integer.SPECS['__divsi3'][0]), (ZERO, ZERO+2)):
            self.dependencies[target] = self.rom[target-match.ROM_BASE:end-match.ROM_BASE]
        self.dependencies[address] = data
        self.records[address] = dict(address=address, end=address+len(data), bytes=len(data),
            body_sha256=hashlib.sha256(data).hexdigest(), structure=proof, **self.identities)
        self._division[(address, site)] = dict(proof, caller_composition=True, call_site=site,
            incoming_aliases=sorted(incoming.items()), returned_aliases=sorted(returned_aliases.items()),
            control_overwrites=control_receipts)
        return returned_aliases

    def division_manifest(self):
        if not self._division:
            raise ValueError('dynamic division profile requires an actual composed DIV callee')
        return dict(schema=SCHEMA, observations=[self._division[k] for k in sorted(self._division)],
            source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            numeric_equivalence_claim=False, termination_claim=False)
