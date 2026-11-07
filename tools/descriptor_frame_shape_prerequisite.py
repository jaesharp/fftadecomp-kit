"""Conditional stack shape, without value preservation or memory effects.

This component reconstructs a previously authenticated code/data partition and
checks every CFG path. Call continuations are obligations, never assertions that
a callee restores SP or preserves any register or stack byte. Indirect memory
effects and saved-value/return-control replay must independently complete.
"""
import hashlib

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_CALL
from capstone.arm import (ARM_INS_B, ARM_OP_IMM, ARM_OP_REG, ARM_OP_MEM,
                          ARM_REG_R0, ARM_REG_SP, ARM_REG_PC, ARM_REG_LR,
                          ARM_CC_AL, ARM_CC_INVALID)

SELECTOR = 'bounded-descriptor-frame-shape-prerequisite-v1'
LOCAL = (False, False, True)
MAX_WORDS = 256
MAX_BODY = 4096


def decode_partition(data, address, partition):
    """Reconstruct instructions from a supplied authenticated partition.

This is not a replacement for owner structural admission. The caller must pin
the prior structural receipt and complete body; no proof is obtained merely by
supplying a partition which decodes successfully.
"""
    if type(data) is not bytes or type(address) is not int or address % 2 or \
            not 2 <= len(data) <= MAX_BODY or type(partition) is not dict:
        raise ValueError('frame shape requires bounded immutable body and partition')
    excluded = set()
    for interval in partition.get('alignment', ()):
        if type(interval) not in (tuple, list) or len(interval) != 2:
            raise ValueError('invalid authenticated alignment interval')
        low, high = interval
        if type(low) is not int or type(high) is not int or low % 2 or high-low != 2:
            raise ValueError('frame shape permits exact halfword alignment slots only')
        span = set(range(low, high))
        if excluded & span or not address <= low < high <= address+len(data):
            raise ValueError('overlapping or out-of-body partition interval')
        excluded.update(span)
    for word in partition.get('words', ()):
        low = word.get('address')
        if type(low) is not int or low % 4 or not address <= low <= address+len(data)-4 or \
                word.get('switch_word') is not False or \
                int.from_bytes(data[low-address:low-address+4], 'little') != word.get('value'):
            raise ValueError('frame shape requires exact literal words without switches')
        span = set(range(low, low+4))
        if excluded & span:
            raise ValueError('overlapping partition words')
        excluded.update(span)
    if partition.get('alignment_bytes') != 2*len(partition.get('alignment', ())) or \
            partition.get('literal_and_table_bytes') != 4*len(partition.get('words', ())) or \
            partition.get('code_bytes') != len(data)-len(excluded):
        raise ValueError('frame shape partition byte counts differ')
    md = Cs(CS_ARCH_ARM, CS_MODE_THUMB); md.detail = True
    instructions = {}; site = address
    while site < address+len(data):
        if site in excluded:
            site += 1
            continue
        item = next(md.disasm(data[site-address:], site, count=1), None)
        if item is None or site % 2 or item.size not in (2, 4) or \
                any(byte in excluded for byte in range(site, site+item.size)):
            raise ValueError('frame shape instruction crosses authenticated partition')
        instructions[site] = item; site += item.size
    edges, calls = {}, {}
    for site, item in instructions.items():
        regs = tuple(op.reg for op in item.operands if op.type == ARM_OP_REG)
        if CS_GRP_CALL in item.groups:
            if item.mnemonic != 'bl' or len(item.operands) != 1 or item.operands[0].type != ARM_OP_IMM:
                raise ValueError('frame shape requires explicit direct call edges')
            target = item.operands[0].imm
            if address <= target < address+len(data):
                raise ValueError('frame shape excludes local BL continuations')
            calls[site] = target; edges[site] = (site+item.size,)
        elif item.id == ARM_INS_B:
            if len(item.operands) != 1 or item.operands[0].type != ARM_OP_IMM:
                raise ValueError('frame shape excludes unresolved branch targets')
            edges[site] = (item.operands[0].imm,)
            if item.cc not in (ARM_CC_AL, ARM_CC_INVALID): edges[site] += (site+item.size,)
        elif item.mnemonic == 'bx' or item.mnemonic == 'pop' and ARM_REG_PC in regs:
            edges[site] = ()
        else:
            if ARM_REG_PC in item.regs_access()[1]:
                raise ValueError('frame shape excludes unresolved PC writes')
            edges[site] = (site+item.size,)
        if any(target not in instructions for target in edges[site]):
            raise ValueError('frame shape CFG leaves authenticated code')
    return instructions, edges, calls


def prove(data, address, partition, incoming_stack, *, selector):
    if selector != SELECTOR or type(selector) is not str:
        raise ValueError('frame shape requires its explicit prerequisite selector')
    if type(incoming_stack) not in (tuple, list) or len(incoming_stack) > MAX_WORDS or any(
            type(row) not in (tuple, list) or len(row) != 3 or
            any(type(bit) is not bool for bit in row) for row in incoming_stack):
        raise ValueError('frame shape requires exact bounded incoming stack classifications')
    instructions, edges, calls = decode_partition(data, address, partition)
    states = {address: ()}; pending = [address]
    materializations, incoming_reads, call_obligations, returns, memory_sites = [], [], [], [], []
    while pending:
        site = pending.pop(); private = states[site]; item = instructions[site]
        following = private
        encoded = int.from_bytes(bytes(item.bytes), 'little')
        regs = tuple(op.reg for op in item.operands if op.type == ARM_OP_REG)
        read, changed = map(set, item.regs_access())
        if item.mnemonic in ('push', 'pop'):
            loading = item.mnemonic == 'pop'
            if item.size != 2 or encoded & 0xfe00 != (0xbc00 if loading else 0xb400):
                raise ValueError('frame shape requires exact Thumb PUSH/POP encoding')
            numbers = [i for i in range(8) if encoded & (1 << i)]
            expected = tuple(ARM_REG_R0+i for i in numbers)
            if encoded & 0x100:
                numbers.append(15 if loading else 14)
                expected += (ARM_REG_PC if loading else ARM_REG_LR,)
            if not numbers or regs != expected:
                raise ValueError('frame shape PUSH/POP operands differ from bytes')
            if loading:
                if len(private) < len(numbers) or any(row[0] != 'saved' for row in private[:len(numbers)]):
                    raise ValueError('frame POP consumes locals or incoming caller words')
                following = private[len(numbers):]
            else:
                following = tuple(('saved', number) for number in numbers)+private
        elif item.size == 2 and encoded & 0xff00 == 0xb000:
            count = encoded & 127
            if not count:
                raise ValueError('frame adjustment must allocate or deallocate positive words')
            if encoded & 128:
                following = (('local', None),)*count+private
            else:
                if count > len(private) or any(row[0] != 'local' for row in private[:count]):
                    raise ValueError('frame deallocation consumes saved or incoming words')
                following = private[count:]
        elif item.size == 2 and encoded & 0xf000 == 0x9000:
            word = encoded & 255; loading = bool(encoded & 0x800)
            if word < len(private):
                if private[word][0] != 'local':
                    raise ValueError('direct SP access observes or overwrites saved words')
            else:
                relative = word-len(private)
                if not loading or relative >= len(incoming_stack) or tuple(incoming_stack[relative]) != LOCAL:
                    raise ValueError('direct SP access exceeds allocated incoming local word bound')
                incoming_reads.append(dict(site=site, caller_word=relative, value='unproved'))
        elif ARM_REG_SP in read | changed:
            displacement = None; destination = None
            if item.size == 2 and encoded & 0xff00 == 0x4600 and ((encoded >> 3) & 15) == 13:
                destination = (encoded & 7) | ((encoded >> 4) & 8)
                if destination < 13: displacement = 0
            elif item.size == 2 and encoded & 0xf800 == 0xa800:
                destination = (encoded >> 8) & 7; displacement = 4*(encoded & 255)
            if displacement is None or ARM_REG_SP in changed:
                raise ValueError('frame shape excludes unbounded SP read/write')
            first = displacement//4; end = first
            while end < len(private) and private[end][0] == 'local': end += 1
            if first == end:
                raise ValueError('SP materialization does not point into a private local allocation')
            origin = -4*(len(incoming_stack)+len(private))
            materializations.append(dict(site=site, register=destination, origin=origin,
                offset=origin+displacement, contiguous_private_bytes=4*(end-first),
                pointer_value_survival=False, memory_effects_proved=False))
        if len(following)+len(incoming_stack) > MAX_WORDS:
            raise ValueError('frame shape exceeds bounded total live stack')
        if site in calls:
            live = [(False,False,True) if row[0]=='local' else (False,True,False) for row in private]
            live += [tuple(row) for row in incoming_stack]
            call_obligations.append(dict(site=site,target=calls[site],incoming_stack=live,
                required_return_SP=-4*len(live),SP_contract_discharged=False,
                memory_effects_discharged=False,register_preservation_discharged=False))
        if any(op.type == ARM_OP_MEM and op.mem.base not in (ARM_REG_SP,ARM_REG_PC) for op in item.operands) or \
                item.mnemonic.startswith(('ldm','stm')):
            memory_sites.append(site)
        if not edges[site]:
            if following:
                raise ValueError('frame return leaves private allocations or saved words live')
            returns.append(site)
        for target in edges[site]:
            if target in states and states[target] != following:
                raise ValueError('frame CFG join has inconsistent exact stack shape')
            if target not in states:
                states[target] = following; pending.append(target)
    if set(states) != set(instructions) or not returns:
        raise ValueError('frame shape omits reached instructions or normal returns')
    return dict(schema=SELECTOR,body=[address,len(data),hashlib.sha256(data).hexdigest()],
        instructions=len(instructions),states=len(states),returns=sorted(returns),
        materializations=sorted(materializations,key=lambda row:row['site']),
        incoming_reads=sorted(incoming_reads,key=lambda row:row['site']),
        call_obligations=sorted(call_obligations,key=lambda row:row['site']),
        unresolved_memory_sites=sorted(memory_sites),conditional_stack_shape=True,
        saved_values_preserved=False,return_control_proved=False,complete_frame_replay=False,
        reaching_state_authenticated=False,owner_admission=False,
        limits='Conditional shape only: every call return-SP and memory/register effect obligation remains open. '
               'Materialization proves only a private allocation window under those obligations. No pointer survival, '
               'saved-value preservation, initialized bytes, callback identity, nonalias or native admission.')
