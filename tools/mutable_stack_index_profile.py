"""Opt-in exact path contexts for four mutable allocated local words.

Structural prerequisite only. No C equivalence, whole-source admission, memory
safety, numeric callee result or unconditional termination theorem is granted.
"""
from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_OP_IMM,
    ARM_OP_REG, ARM_REG_R0, ARM_REG_R4, ARM_REG_R11, ARM_REG_SP)

SELECTOR = 'mutable-four-local-word-index-v1'
ALIAS_SLOT_SELECTOR = 'mutable-four-local-word-alias-slot-v1'
LOW_HALFWORD_SELECTOR = 'mutable-four-local-word-alias-slot-low-signed-halfword-read-v1'
HALFWORD_ACCESS_SELECTOR = 'mutable-four-local-word-alias-slot-halfword-access-v1'
SCALAR_SLOT_SELECTOR = 'mutable-four-local-word-alias-slot-halfword-scalar-slot-v1'
CONSUMER_SCRATCH_SELECTOR = 'mutable-four-local-word-alias-slot-halfword-scalar-slot-consumer-scratch-v1'
LEAF_OVERWRITE_SELECTOR = 'mutable-four-local-word-alias-slot-halfword-scalar-slot-leaf-overwrite-v1'
THREE_CALL_SELECTOR = 'mutable-four-local-word-three-call-v1'
SCHEMA = 'thumb-mutable-four-local-word-index-v1'
MAX_VALUES, MAX_UPDATES = 4, 16384
INDEX_BYTES = frozenset((0, 4, 8, 12))
HALFWORD_INDEX_BYTES = INDEX_BYTES | frozenset((2, 6))


def validate(policy):
    if type(policy) is not str or policy not in (SELECTOR, ALIAS_SLOT_SELECTOR, LOW_HALFWORD_SELECTOR, HALFWORD_ACCESS_SELECTOR, SCALAR_SLOT_SELECTOR, CONSUMER_SCRATCH_SELECTOR, LEAF_OVERWRITE_SELECTOR, THREE_CALL_SELECTOR):
        raise ValueError('mutable local indices require their explicit versioned policy')


def offsets(values):
    if not values or len(values) > MAX_VALUES or any(type(offset) is not int or live is not True
            for offset, live in values):
        raise ValueError('mutable local alias has unknown, expired or excessive alternatives')
    return tuple(sorted(offset for offset, _ in values))


def assignment(instruction, aliases, depth, constants, *, halfword_access=False):
    """Authenticated local additions with the explicitly selected exact index domain."""
    if type(halfword_access) is not bool:
        raise ValueError("halfword address capability requires an explicit Boolean selection")
    index_bytes = HALFWORD_INDEX_BYTES if halfword_access else INDEX_BYTES
    from match import stack_alias_assignment
    operands = instruction.operands
    raw = int.from_bytes(instruction.bytes, 'little')
    pair = None
    if instruction.size == 2 and instruction.cc in (ARM_CC_AL, ARM_CC_INVALID) and \
            operands and all(op.type == ARM_OP_REG and not op.shift.type and
                not op.shift.value and not op.subtracted for op in operands):
        if raw & 0xFE00 == 0x1800 and instruction.mnemonic == 'adds' and len(operands) == 3:
            destination, left, right = (ARM_REG_R0 + (raw & 7), ARM_REG_R0 + ((raw >> 3) & 7),
                                       ARM_REG_R0 + ((raw >> 6) & 7))
            if tuple(op.reg for op in operands) == (destination, left, right):
                pair = destination, left, right
        elif raw & 0xFF00 == 0x4400 and instruction.mnemonic == 'add' and len(operands) == 2:
            destination = ARM_REG_R0 + (raw & 7) + ((raw >> 4) & 8)
            right = ARM_REG_R0 + ((raw >> 3) & 15)
            if tuple(op.reg for op in operands) == (destination, right):
                pair = destination, destination, right
    if pair is not None:
        destination, left, right = pair
        local = {**aliases, ARM_REG_SP: frozenset(((-4 * depth, True),))}
        if (left in local) != (right in local):
            source, index = (left, right) if left in local else (right, left)
            if constants.get(index) not in index_bytes:
                raise ValueError('mutable local index is unknown or outside its exact selected domain')
            values = frozenset((offset + constants[index], True) for offset in offsets(local[source]))
            return destination, values, source
    # Capstone expands the high-register ADD-to-SP encoding to three operands.
    if instruction.size == 2 and raw & 0xFF00 == 0x4400 and instruction.mnemonic == 'add' and \
            instruction.cc in (ARM_CC_AL, ARM_CC_INVALID) and len(operands) == 3 and \
            all(op.type == ARM_OP_REG and not op.shift.type and not op.shift.value and not op.subtracted
                for op in operands):
        destination = ARM_REG_R0 + (raw & 7) + ((raw >> 4) & 8)
        if ARM_REG_R0 <= destination <= ARM_REG_R0 + 7 and \
                ((raw >> 3) & 15) == 13 and \
                tuple(op.reg for op in operands) == (destination, ARM_REG_SP, destination):
            if constants.get(destination) not in index_bytes:
                raise ValueError('mutable SP index is unknown or outside its exact selected domain')
            return destination, frozenset(((constants[destination] - 4 * depth, True),)), ARM_REG_SP
    read, _ = instruction.regs_access()
    sources = set(read) & aliases.keys()
    if len(sources) > 1:
        return None
    exact = {register: offsets(values)[0] for register, values in aliases.items() if register in sources}
    first = stack_alias_assignment(instruction, exact, depth, constants)
    if first is None:
        return None
    source = first[2]
    if source == ARM_REG_SP:
        values = frozenset(((first[1], True),))
    else:
        values = frozenset((stack_alias_assignment(instruction, {source: offset}, depth, constants)[1], True)
                           for offset in offsets(aliases[source]))
    return first[0], values, source


def halfword(instruction):
    """Authenticate only zero-displacement STRH/LDRH or existing signed-load encoding."""
    import zero_index_stack_profile as zero_index
    signed = zero_index.signed_load(instruction)
    if signed is not None and signed[2] == 2:
        return False, instruction.operands[0].reg, signed[0], signed[1]
    from capstone.arm_const import ARM_OP_MEM
    operands = instruction.operands
    raw = int.from_bytes(instruction.bytes, 'little')
    if instruction.size != 2 or instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
            raw & 0xF800 not in (0x8000, 0x8800) or raw & 0x07C0 or \
            len(operands) != 2 or operands[0].type != ARM_OP_REG or operands[1].type != ARM_OP_MEM or \
            instruction.writeback or any(op.shift.type or op.shift.value or op.subtracted for op in operands):
        raise ValueError('halfword array requires exact zero-displacement Thumb STRH/LDRH or zero-index LDRSH')
    writing = not bool(raw & 0x0800)
    register, base = ARM_REG_R0 + (raw & 7), ARM_REG_R0 + ((raw >> 3) & 7)
    memory = operands[1].mem
    if instruction.mnemonic != ('strh' if writing else 'ldrh') or operands[0].reg != register or \
            memory.base != base or memory.index or memory.disp:
        raise ValueError('halfword array instruction bytes and decoded operands differ')
    return writing, register, base, 0


def transfer(instruction, constants, comparison, *, call=False):
    """Exact architectural words only; unknown writes kill facts, calls kill scratch.

    Contexts are never unioned to bound a counter. A fixed resource cap refuses
    instead of assuming loop iteration bounds. No facts are recovered from memory.
    """
    if call:
        return (tuple(sorted((r, v) for r, v in constants.items() if ARM_REG_R4 <= r <= ARM_REG_R11)), None)
    _, written = instruction.regs_access()
    outgoing = {r: v for r, v in constants.items() if r not in written}
    operands = instruction.operands
    raw = int.from_bytes(instruction.bytes, 'little')
    # A comparison is useful only until the next flag-setting operation.
    if instruction.update_flags:
        comparison = None
    if instruction.size != 2 or instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID):
        return tuple(sorted(outgoing.items())), comparison
    if raw & 0xF800 == 0x2000 and instruction.mnemonic == 'movs' and len(operands) == 2 and \
            operands[0].type == ARM_OP_REG and operands[0].reg == ARM_REG_R0 + ((raw >> 8) & 7) and \
            operands[1].type == ARM_OP_IMM and operands[1].imm == raw & 255:
        outgoing[operands[0].reg] = raw & 255
    elif raw & 0xFF00 == 0x4600 and instruction.mnemonic == 'mov' and len(operands) == 2 and \
            all(op.type == ARM_OP_REG for op in operands):
        destination = ARM_REG_R0 + (raw & 7) + ((raw >> 4) & 8)
        source = ARM_REG_R0 + ((raw >> 3) & 15)
        if tuple(op.reg for op in operands) == (destination, source) and source in constants:
            outgoing[destination] = constants[source]
    elif raw & 0xFE00 == 0x1C00 and instruction.mnemonic == 'adds' and len(operands) == 3 and \
            operands[0].type == operands[1].type == ARM_OP_REG and operands[2].type == ARM_OP_IMM:
        destination, source, immediate = ARM_REG_R0 + (raw & 7), ARM_REG_R0 + ((raw >> 3) & 7), (raw >> 6) & 7
        if (operands[0].reg, operands[1].reg, operands[2].imm) == (destination, source, immediate) and source in constants:
            outgoing[destination] = (constants[source] + immediate) & 0xFFFFFFFF
    elif raw & 0xF800 == 0x3000 and instruction.mnemonic == 'adds' and len(operands) == 2 and \
            operands[0].type == ARM_OP_REG and operands[1].type == ARM_OP_IMM:
        destination = ARM_REG_R0 + ((raw >> 8) & 7)
        if (operands[0].reg, operands[1].imm) == (destination, raw & 255) and destination in constants:
            outgoing[destination] = (constants[destination] + (raw & 255)) & 0xFFFFFFFF
    elif raw & 0xF800 in (0x0000, 0x0800) and instruction.mnemonic in ('lsls', 'lsrs') and len(operands) == 3 and \
            operands[0].type == operands[1].type == ARM_OP_REG and operands[2].type == ARM_OP_IMM:
        destination, source = ARM_REG_R0 + (raw & 7), ARM_REG_R0 + ((raw >> 3) & 7)
        count = (raw >> 6) & 31
        if raw & 0xF800 == 0x0800 and count == 0: count = 32
        expected = 'lsrs' if raw & 0xF800 else 'lsls'
        if instruction.mnemonic == expected and (operands[0].reg, operands[1].reg, operands[2].imm) == \
                (destination, source, count) and source in constants:
            outgoing[destination] = ((constants[source] << count) & 0xFFFFFFFF if expected == 'lsls'
                                     else constants[source] >> count)
    elif instruction.mnemonic == 'cmp' and len(operands) == 2 and operands[0].type == ARM_OP_REG:
        left, right = operands
        if raw & 0xF800 == 0x2800 and left.reg == ARM_REG_R0 + ((raw >> 8) & 7) and \
                right.type == ARM_OP_IMM and right.imm == raw & 255 and left.reg in constants:
            comparison = (constants[left.reg], right.imm)
        elif raw & 0xFFC0 == 0x4280 and right.type == ARM_OP_REG and \
                (left.reg, right.reg) == (ARM_REG_R0 + (raw & 7), ARM_REG_R0 + ((raw >> 3) & 7)) and \
                left.reg in constants and right.reg in constants:
            comparison = (constants[left.reg], constants[right.reg])
    return tuple(sorted(outgoing.items())), comparison


def successors(instruction, edges, comparison):
    """Only exact Thumb BEQ/BNE/BHI/BLS following a still-live known CMP."""
    raw = int.from_bytes(instruction.bytes, 'little')
    conditions = {0xD000: ('beq', lambda a, b: a == b), 0xD100: ('bne', lambda a, b: a != b),
                  0xD800: ('bhi', lambda a, b: a > b), 0xD900: ('bls', lambda a, b: a <= b)}
    condition = conditions.get(raw & 0xFF00)
    if comparison is None or condition is None:
        return edges
    if instruction.size != 2 or instruction.mnemonic != condition[0] or len(instruction.operands) != 1 or \
            instruction.operands[0].type != ARM_OP_IMM or len(edges) != 2:
        raise ValueError('mutable local condition requires exact decoded Thumb branch')
    delta = raw & 255
    if delta & 128: delta -= 256
    target = instruction.address + 4 + 2 * delta
    if instruction.operands[0].imm != target or edges != (target, instruction.address + 2):
        raise ValueError('mutable local condition differs from its complete CFG')
    return (edges[0] if condition[1](*comparison) else edges[1],)
