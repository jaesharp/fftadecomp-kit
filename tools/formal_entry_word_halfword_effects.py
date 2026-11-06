"""Closed straight-line halfword outputs through arg3 and incoming ABI word0.

This proves abstract origins and initialized accesses only. The distinct native
frame proof, actual ROM/index ownership, and caller argument bounds are separate.
"""
from match import parse_data_symbols

SCHEMA = 'thumb-formal-entry-word-halfword-effects-v1'
POLICY_SCHEMA = 'thumb-four-readonly-named-halfwords-v1'
NAME = 'g_state_02007F40'
GLOBAL = 0x02007F40
READS = [[32, 2], [34, 2], [36, 2], [38, 2]]


def named_policy():
    return dict(schema=POLICY_SCHEMA, symbol=NAME, reads=[list(r) for r in READS],
                readable=True, initialized=True)


def prove_origins(instructions, edges, address, data, partition, data_mapping, policy):
    if type(policy) is not dict or policy != named_policy() or \
            type(policy.get('reads')) is not list or any(type(row) is not list or
                any(type(v) is not int for v in row) for row in policy['reads']) or \
            policy.get('readable') is not True or policy.get('initialized') is not True or \
            type(data_mapping) is not bytes or parse_data_symbols(data_mapping).get(NAME) != GLOBAL:
        raise ValueError('outputs require the distinct exact four-halfword named-read premise')
    ordered = sorted(instructions)
    words = partition.get('words', [])
    if not ordered or ordered[0] != address or set(edges) != set(instructions) or \
            len(words) != 1 or words[0]['value'] != GLOBAL or words[0]['switch_word']:
        raise ValueError('outputs require a complete straight-line CFG and one owned named literal')
    scalar = ('scalar',)
    values = {n: scalar if n < 3 else ('formal', 3) if n == 3 else ('entry', n)
              for n in range(13)}
    values[14] = ('entry-lr',)
    constants, stack, initialized = {}, [], set()
    reads, writes, local_reads, local_writes, loads, incoming_reads = [], [], [], [], [], []

    def assign(n, value=scalar, constant=None):
        values[n] = value
        constants.pop(n, None)
        if constant is not None:
            constants[n] = constant

    def value(n):
        return ('local', -4 * len(stack)) if n == 13 else values.get(n)

    def local(offset, width):
        start = offset + 4 * len(stack)
        if offset % width or start < 0 or offset + width > 0 or any(
                stack[i][0] != 'local' for i in range(start // 4, (start + width - 1) // 4 + 1)):
            raise ValueError('halfword access leaves live local bytes or reaches saved words')

    def scalars(*numbers):
        if any(value(n) != scalar for n in numbers):
            raise ValueError('scalar operation consumes a pointer or saved entry origin')

    for position, site in enumerate(ordered):
        item = instructions[site]
        raw = bytes(item.bytes)
        code = int.from_bytes(raw, 'little')
        terminal = position == len(ordered) - 1
        expected = () if terminal else (site + 2,)
        if len(raw) != 2 or item.size != 2 or data[site-address:site-address+2] != raw or tuple(edges[site]) != expected or \
                not terminal and ordered[position + 1] != site + 2:
            raise ValueError('outputs require every exact narrow straight-line instruction')
        if code & 0xFE00 in (0xB400, 0xBC00):
            push = code & 0xFE00 == 0xB400
            numbers = [n for n in range(8) if code & (1 << n)]
            if code & 0x100:
                numbers.append(14 if push else 15)
            if push:
                if any(value(n)[0] not in ('entry', 'entry-lr') for n in numbers):
                    raise ValueError('formal/local/named pointers cannot be pushed')
                stack[:0] = [('saved', value(n)) for n in numbers]
            else:
                if len(numbers) > len(stack) or any(row[0] != 'saved' for row in stack[:len(numbers)]):
                    raise ValueError('pop overlaps unallocated or local words')
                for n, row in zip(numbers, stack):
                    if n == 15:
                        raise ValueError('outputs require the explicit restored-register BX return')
                    assign(n, row[1])
                del stack[:len(numbers)]
        elif code & 0xFF00 == 0xB000:
            count = code & 0x7F
            if not count:
                raise ValueError('empty stack adjustment')
            if code & 0x80:
                stack[:0] = [('local', None)] * count
            else:
                if count > len(stack) or any(row[0] != 'local' for row in stack[:count]):
                    raise ValueError('deallocation reaches saved frame')
                del stack[:count]
                initialized = {o for o in initialized if o >= -4 * len(stack)}
        elif code & 0xFC00 == 0x4400 and (code >> 8) & 3 in (0, 2):
            operation = (code >> 8) & 3
            destination, source = (code & 7) + ((code >> 4) & 8), (code >> 3) & 15
            if destination >= 13 or source in (14, 15):
                raise ValueError('copy cannot modify control or expose return origins')
            if operation == 2:
                assign(destination, value(source), constants.get(source))
            elif operation == 0 and source == 13 and value(destination) == scalar and destination in constants:
                offset = -4 * len(stack) + constants[destination]
                local(offset, 1)
                assign(destination, ('local', offset))
            else:
                raise ValueError('unsupported high-register pointer operation')
        elif code & 0xF800 == 0xA800:
            destination, offset = (code >> 8) & 7, -4 * len(stack) + 4 * (code & 255)
            local(offset, 1)
            assign(destination, ('local', offset))
        elif code & 0xF800 == 0x2000:
            assign((code >> 8) & 7, constant=code & 255)
        elif code & 0xF800 == 0x4800:
            target = ((site + 4) & ~3) + 4 * (code & 255)
            if target != words[0]['address'] or words[0]['load_sites'] != [site] or \
                    int.from_bytes(data[target-address:target-address+4], 'little') != GLOBAL:
                raise ValueError('named load lacks exact owned literal bytes')
            assign((code >> 8) & 7, ('named', NAME))
            loads.append([site, target, NAME, GLOBAL])
        elif code & 0xF800 == 0x9800:
            offset = -4 * len(stack) + 4 * (code & 255)
            if offset != 0:
                raise ValueError('incoming pointer must be exactly entry word0')
            assign((code >> 8) & 7, ('incoming', 0))
            incoming_reads.append([site, 0, 4])
        elif code & 0xF800 in (0x8000, 0x8800) or code & 0xFE00 == 0x5E00:
            signed = code & 0xFE00 == 0x5E00
            load = signed or code & 0xF800 == 0x8800
            destination, base = code & 7, (code >> 3) & 7
            if signed:
                index = (code >> 6) & 7
                scalars(index)
                if constants.get(index) != 0:
                    raise ValueError('signed halfword load requires exact scalar zero index')
                offset = 0
            else:
                offset = 2 * ((code >> 6) & 31)
            origin = value(base)
            if not load:
                scalars(destination)
            if origin[0] == 'local':
                absolute = origin[1] + offset
                local(absolute, 2)
                if load:
                    if not set(range(absolute, absolute + 2)) <= initialized:
                        raise ValueError('local halfword read precedes its own initialization')
                    local_reads.append([site, absolute, 2])
                else:
                    initialized.update(range(absolute, absolute + 2))
                    local_writes.append([site, absolute, 2])
            elif origin == ('named', NAME):
                if not load or signed or [offset, 2] not in READS:
                    raise ValueError('named access exceeds its readonly halfword premise')
                reads.append([site, NAME, offset, 2])
            elif origin in (('formal', 3), ('incoming', 0)):
                if load or offset:
                    raise ValueError('output pointer allows only scalar halfword write at offset0')
                writes.append([site, list(origin), 0, 2])
            else:
                raise ValueError('halfword memory base has no proved accessible origin')
            if load:
                assign(destination)
        elif code & 0xF800 in (0x0000, 0x1000):
            destination, source = code & 7, (code >> 3) & 7
            scalars(source)
            assign(destination)
        elif code & 0xF800 == 0x1800:
            destination, left = code & 7, (code >> 3) & 7
            right = (code >> 6) & 7
            scalars(left, *(() if code & 0x400 else (right,)))
            assign(destination)
        elif code & 0xFF87 == 0x4700:
            source = (code >> 3) & 15
            if not terminal or value(source) != ('entry-lr',) or stack or any(
                    values[n] != ('entry', n) for n in range(4, 12)):
                raise ValueError('return does not restore saved entry frame/control origins')
        else:
            raise ValueError('unsupported output-effect instruction')
        if len(stack) > 1024:
            raise ValueError('output frame exceeds bounded word budget')
        if terminal and code & 0xFF87 != 0x4700:
            raise ValueError('outputs require a terminal authenticated BX')
    if [[r[2], r[3]] for r in reads] != READS or \
            [r[1:] for r in writes] != [[['formal', 3], 0, 2], [['incoming', 0], 0, 2]] or \
            len(loads) != 1 or len(incoming_reads) != 1 or not local_reads or not local_writes:
        raise ValueError('observed origins/reads/writes differ from the closed output policy')
    if any(v[0] in ('local', 'formal', 'incoming', 'named') for v in values.values()):
        raise ValueError('output/local/named pointer remains after return restoration')
    return dict(schema=SCHEMA, named_reads=reads, named_read_policy=policy,
        named_loaded_values='unknown scalars', formal_writes=writes,
        incoming_pointer_word_reads=incoming_reads, local_halfword_reads=local_reads,
        local_halfword_writes=local_writes, typed_literal_loads=loads,
        return_entry_origins=[[n, v[1]] for n, v in sorted(values.items())
                              if n < 4 and v[0] == 'entry'],
        pointer_return_rule='propagate actual caller aliases for every retained entry origin',
        named_writes=[], physical_nonalias_claim=False, source_or_ELF_admission=False,
        arithmetic_C_equivalence=False, caller_bounds_proved=False)
