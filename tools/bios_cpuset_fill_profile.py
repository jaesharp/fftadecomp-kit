"""Explicit conditional BIOS CpuSet fill source within a live local frame.

Only the source read is bounded here. The BIOS operation and ordinary return
are explicit premises, not consequences of the SWI wrapper's four bytes.
"""
import hashlib
import json
from capstone import CS_GRP_CALL
from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_OP_IMM,
    ARM_OP_MEM, ARM_OP_REG, ARM_REG_PC, ARM_REG_R0)

ADDRESS = 0x0814186C
NAME = 'func_0814186C'
WRAPPER = bytes.fromhex('0bdf7047')
SCHEMA = 'conditional-bios-cpuset-local-fill-source-v1'
CONTRACT = ('conditional returning GBA BIOS CpuSet fill boundary: bit24 selects '
            'one source unit, bit26 selects 16/32-bit width; local source span '
            'only, external destination is caller supplied; no initialization, '
            'physical readability, physical nonalias, destination bounds, '
            'numeric result or termination theorem')
MASK = 0xFFFFFFFF
MAX_UPDATES = 4096


def exact(value):
    value &= MASK
    return value, MASK ^ value


def transfer(instruction, incoming, data, address):
    """Introduce bits only from authenticated native Thumb encodings."""
    if instruction.size != 2 or instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID):
        return None
    op = instruction.operands
    code = int.from_bytes(instruction.bytes, 'little')
    name = instruction.mnemonic
    if code & 0xF800 == 0x2000 and name == 'movs' and len(op) == 2 and \
            op[0].type == ARM_OP_REG and op[1].type == ARM_OP_IMM and \
            op[0].reg == ARM_REG_R0 + ((code >> 8) & 7) and op[1].imm == (code & 255):
        return op[0].reg, exact(op[1].imm)
    if code & 0xFF00 == 0x4600 and name == 'mov' and len(op) == 2 and \
            all(p.type == ARM_OP_REG for p in op):
        destination = ARM_REG_R0 + (code & 7) + ((code >> 4) & 8)
        source = ARM_REG_R0 + ((code >> 3) & 15)
        if (op[0].reg, op[1].reg) == (destination, source):
            return destination, incoming.get(source, (0, 0))
    if code & 0xFFC0 == 0x1C00 and name == 'adds' and len(op) == 3 and \
            op[0].type == op[1].type == ARM_OP_REG and op[2].type == ARM_OP_IMM and op[2].imm == 0:
        destination, source = ARM_REG_R0 + (code & 7), ARM_REG_R0 + ((code >> 3) & 7)
        if (op[0].reg, op[1].reg) == (destination, source):
            return destination, incoming.get(source, (0, 0))
    kind = code & 0xF800
    if kind in (0x0000, 0x0800) and name in ('lsls', 'lsrs') and len(op) == 3 and \
            op[0].type == op[1].type == ARM_OP_REG and op[2].type == ARM_OP_IMM:
        destination, source = ARM_REG_R0 + (code & 7), ARM_REG_R0 + ((code >> 3) & 7)
        shift = (code >> 6) & 31
        if kind == 0x0800 and shift == 0:
            shift = 32
        if (op[0].reg, op[1].reg, op[2].imm) == (destination, source, shift) and \
                name == ('lsls' if kind == 0 else 'lsrs'):
            ones, zeros = incoming.get(source, (0, 0))
            bits = (((ones << shift) & MASK, ((zeros << shift) | ((1 << shift)-1)) & MASK)
                    if kind == 0 else (ones >> shift, (zeros >> shift) | (MASK ^ (MASK >> shift))))
            return destination, bits
    kind = code & 0xFFC0
    if kind in (0x4000, 0x4300, 0x4380) and name == {0x4000:'ands', 0x4300:'orrs', 0x4380:'bics'}[kind] and \
            len(op) == 2 and all(p.type == ARM_OP_REG for p in op):
        destination, source = ARM_REG_R0 + (code & 7), ARM_REG_R0 + ((code >> 3) & 7)
        if (op[0].reg, op[1].reg) == (destination, source):
            ao, az = incoming.get(destination, (0, 0))
            bo, bz = incoming.get(source, (0, 0))
            bits = ((ao & bo, az | bz) if kind == 0x4000 else
                    (ao | bo, az & bz) if kind == 0x4300 else (ao & bz, az | bo))
            return destination, bits
    if code & 0xF800 == 0x4800 and name == 'ldr' and len(op) == 2 and \
            op[0].type == ARM_OP_REG and op[1].type == ARM_OP_MEM and \
            op[0].reg == ARM_REG_R0 + ((code >> 8) & 7) and \
            op[1].mem.base == ARM_REG_PC and not op[1].mem.index and \
            op[1].mem.disp == (code & 255)*4 and not instruction.writeback:
        offset = ((instruction.address + 4) & ~3) + op[1].mem.disp - address
        if not 0 <= offset <= len(data)-4:
            raise ValueError('BIOS fill control literal escapes the complete owner')
        return op[0].reg, exact(int.from_bytes(data[offset:offset+4], 'little'))
    return None


def prove_bits(instructions, edges, address, data):
    """Intersect known bits at every join; any call destroys every bit fact."""
    if address not in instructions or set(edges) != set(instructions):
        raise ValueError('BIOS fill bits require an exact closed native CFG')
    states, pending, updates = {address:{}}, [address], 0
    while pending:
        site = pending.pop()
        instruction, incoming = instructions[site], states[site]
        outgoing = dict(incoming)
        if CS_GRP_CALL in instruction.groups:
            outgoing.clear()
        else:
            for register in instruction.regs_access()[1]:
                outgoing.pop(register, None)
            result = transfer(instruction, incoming, data, address)
            if result is not None and result[1] != (0, 0):
                outgoing[result[0]] = result[1]
        for successor in edges[site]:
            if successor not in instructions:
                raise ValueError('BIOS fill CFG escapes an instruction boundary')
            previous = states.get(successor)
            merged = dict(outgoing) if previous is None else {
                register:(ones & outgoing[register][0], zeros & outgoing[register][1])
                for register,(ones,zeros) in previous.items() if register in outgoing}
            merged = {register:bits for register,bits in merged.items() if bits != (0,0)}
            if merged != previous:
                updates += 1
                if updates > MAX_UPDATES:
                    raise ValueError('BIOS fill bit proof-state budget exhausted')
                states[successor] = merged
                pending.append(successor)
    if set(states) != set(instructions):
        raise ValueError('BIOS fill facts omit reached native instructions')
    return states


class BiosFillProof:
    def __init__(self, data, address, rom, mapping, index, calls):
        import match
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        owner.validate_span(data, address, rom, mapping, index)
        refinement = owner.refine(data, address, mapping)
        instructions, edges, branches, actual, words = graph.graph(data, address, refinement)
        if branches or words or calls != actual or ADDRESS not in calls.values():
            raise ValueError('BIOS fill requires an actual direct call in its closed owner')
        graph.partition(data, address, refinement, instructions, words)
        offset = ADDRESS - match.ROM_BASE
        body = rom[offset:offset+len(WRAPPER)]
        if body != WRAPPER:
            raise ValueError('BIOS fill requires the exact CpuSet SWI 0x0B return wrapper')
        owner.validate_span(body, ADDRESS, rom, mapping, index)
        self.data, self.address = data, address
        self.rom, self.mapping, self.index = rom, mapping, index
        self.calls = dict(calls)
        self.wrapper = body
        self.states = prove_bits(instructions, edges, address, data)
        self.observations = set()

    def check_call(self, site, aliases, stack):
        import match
        if type(site) is not int or self.calls.get(site) != ADDRESS or \
                set(aliases) != {ARM_REG_R0}:
            raise ValueError('BIOS fill requires only a local R0 source and an external destination')
        ones, zeros = self.states[site].get(ARM_REG_R0 + 2, (0, 0))
        if not ones & (1 << 24):
            raise ValueError('BIOS fill mode bit24 is not set on every reaching path')
        # Unknown width is conservatively a complete aligned 32-bit source unit.
        width = 2 if zeros & (1 << 26) else 4
        offset = aliases[ARM_REG_R0]
        match.BufferCallProof.access(offset, width, stack)
        self.observations.add((site, offset, width, ones, zeros))
        return {}

    def manifest(self):
        return dict(schema=SCHEMA, contract=CONTRACT,
                    owner=[self.address, len(self.data), hashlib.sha256(self.data).hexdigest()],
                    dependency=[ADDRESS, len(self.wrapper), hashlib.sha256(self.wrapper).hexdigest()],
                    sites=[list(row) for row in sorted(self.observations)])

    def fingerprint(self):
        return hashlib.sha256(json.dumps(self.manifest(), sort_keys=True,
                                         separators=(',', ':')).encode()).hexdigest()
