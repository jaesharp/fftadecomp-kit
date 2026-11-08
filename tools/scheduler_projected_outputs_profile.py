"""Ordered coordinate outputs before an explicitly conditional scheduler call.

Helper effects follow complete indexed instructions. The scheduler's physical
access, allocation, frame noninterference and nonretention remain premises.
Outgoing pointer words are retained and recorded at every subsequent call.
"""
import hashlib
import json
from pathlib import Path
import struct

import match
import owner_graph_profile as graph
import owner_admission_profile as owner
import formal_entry_word_halfword_effects as direct
import three_halfword_output_buffer_profile as three

SELECTOR = 'conditional-scheduler-projected-outputs-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
SCHEDULER = 0x08005B6C
PAIR = (0x080D8B5C, 30, 14, '32a7c12f9eb450e5668c759244d23a498228f759bd6d6e6f08375dd8ede5214a')
NOOP = (0x080A880C, 2, 1, 'c7dfbb7d02759eacb64dbc916c1bb6f21eabaff1c1032ea5c9176abf7fd28df8')
TABLE = (0x0801CC18, 32, 13, 'fb28c2146d6dc491a40a37a9b029c7e76ffa3d474a673790ec6ad544c143f72e')
WORLD = (0x0801CA78, 32, 16, 'dbde99fd245e7c42708043685bb3836d3d84a6baa034ba92cb9fdd062ac9a273')
SCREEN = (0x0801C984, 108, 51, '47eb591d35b6ba7c424b639d7ce66e979b48c2c95441cd621ea2869070c596ee')
TABLE_NAME, TABLE_POINT = 'data_02007F10', 0x02007F10


def require(condition, message):
    if not condition:
        raise ValueError(message)


def straight(instructions, edges, address, data):
    ordered = sorted(instructions)
    require(ordered and ordered[0] == address and set(edges) == set(instructions),
            'projected helper requires its complete straight-line CFG')
    for index, site in enumerate(ordered):
        item = instructions[site]
        raw = bytes(item.bytes)
        terminal = index + 1 == len(ordered)
        require(item.size == len(raw) and raw == data[site-address:site-address+len(raw)]
                and tuple(edges[site]) == (() if terminal else (site+len(raw),))
                and (terminal or ordered[index+1] == site+len(raw)),
                'projected helper bytes or complete edges differ')
        yield site, item, terminal


def pair_origins(instructions, edges, calls, address, data, noop_address, noop_data):
    """Prove actual BX-LR transport and ordered byte reads/halfword writes."""
    require(noop_data == bytes.fromhex('7047') and type(noop_address) is int
            and noop_address % 2 == 0 and len(calls) == 1,
            'pair helper requires one complete BX-LR child')
    scalar = ('scalar',)
    values = {n: ('entry', n) for n in range(13)}
    values.update({0: ('object', 0), 1: ('formal', 1), 2: ('formal', 2),
                   14: ('entry-lr',)})
    constants, stack, events = {}, [], []
    observed_calls = set()

    def assign(register, value=scalar, constant=None):
        values[register] = value
        constants.pop(register, None)
        if constant is not None:
            constants[register] = constant

    last_end = address
    for site, item, terminal in straight(instructions, edges, address, data):
        raw = bytes(item.bytes)
        code = int.from_bytes(raw, 'little')
        last_end = site + len(raw)
        if site in calls:
            require(len(raw) == 4 and item.mnemonic == 'bl' and len(item.operands) == 1
                    and item.operands[0].type == match.ARM_OP_IMM
                    and calls[site] == item.operands[0].imm == noop_address and not terminal,
                    'pair helper child target or call differs')
            # BL changes LR. The complete child changes no general register,
            # SP, flag or memory cell; its BX uses precisely this new LR.
            assign(14, ('child-continuation', site+4))
            observed_calls.add(site)
            continue
        require(len(raw) == 2, 'pair helper excludes other wide instructions')
        if code & 0xFE00 in (0xB400, 0xBC00):
            push = code & 0xFE00 == 0xB400
            numbers = [n for n in range(8) if code & (1 << n)]
            if code & 0x100:
                numbers.append(14 if push else 15)
            require(numbers, 'pair helper excludes empty stack operations')
            if push:
                require(all(values[n][0] in ('entry', 'entry-lr') for n in numbers),
                        'pair helper cannot spill a formal pointer or computed value')
                stack[:0] = [values[n] for n in numbers]
            else:
                require(15 not in numbers and len(numbers) <= len(stack),
                        'pair helper pop leaves its protected frame')
                for n, value in zip(numbers, stack):
                    assign(n, value)
                del stack[:len(numbers)]
        elif code & 0xFE00 == 0x1C00 and (code >> 6) & 7 == 0:
            source, destination = (code >> 3) & 7, code & 7
            assign(destination, values[source], constants.get(source))
        elif code & 0xF800 == 0x2000:
            assign((code >> 8) & 7, constant=code & 255)
        elif code & 0xFE00 == 0x5600 or code & 0xF800 == 0x7800:
            destination, base = code & 7, (code >> 3) & 7
            signed = code & 0xFE00 == 0x5600
            index = (code >> 6) & 7
            offset = constants.get(index) if signed else (code >> 6) & 31
            require(values[base] == ('object', 0) and type(offset) is int
                    and (not signed or values[index] == scalar),
                    'pair byte read lacks object and constant-offset origins')
            events.append(dict(site=site, kind='read', formal=0, offset=offset,
                               bytes=1, signed=signed))
            assign(destination)
        elif code & 0xE000 == 0 and (code >> 11) & 3 in (0, 2):
            source, destination = (code >> 3) & 7, code & 7
            require(values[source] == scalar, 'pair shift observes a pointer or saved origin')
            assign(destination)
        elif code & 0xF800 == 0x8000:
            source, base, offset = code & 7, (code >> 3) & 7, 2*((code >> 6) & 31)
            require(values[source] == scalar and values[base] in (('formal', 1), ('formal', 2))
                    and offset == 0, 'pair store lacks its exact formal halfword bound')
            events.append(dict(site=site, kind='write', formal=values[base][1], offset=0, bytes=2))
        elif code & 0xFF87 == 0x4700:
            require(terminal and values.get((code >> 3) & 15) == ('entry-lr',)
                    and not stack and all(values[n] == ('entry', n) for n in range(4, 12)),
                    'pair return fails protected frame or control restoration')
        else:
            raise ValueError('unsupported pair helper operation')
        require(not terminal or code & 0xFF87 == 0x4700,
                'pair helper requires its terminal authenticated BX')
    require(last_end == address+len(data) and observed_calls == set(calls)
            and [e['kind'] for e in events] == ['read', 'write', 'read', 'write']
            and [e['formal'] for e in events if e['kind'] == 'write'] == [1, 2],
            'pair complete extent, nested call or ordered effects differ')
    returned = []
    for n in (0, 1, 2, 3, 12):
        if values[n][0] in ('entry', 'formal'):
            returned.append([n, values[n][1]])
    require(returned == [[2, 2], [3, 3], [12, 12]],
            'pair helper exact residual origins differ')
    return dict(ordered_effects=events, return_entry_origins=returned,
        noop=dict(address=noop_address, bytes=2, body_sha256=hashlib.sha256(noop_data).hexdigest()),
        protected_registers=list(range(4, 12)), incoming_stack_reads=[],
        physical_memory_claim=False, numeric_equivalence_claim=False)


def table_origins(instructions, edges, address, data, partition, objects):
    """Close the read-only indexed load, including overwritten incoming R2/R3."""
    expected = [0x0600, 0x0609, 0x0E09, None, 0x7A1A, 0x434A, 0x0052,
                0x6859, 0x1889, 0x0DC0, 0x1809, 0x7808, 0x4770]
    rows = list(straight(instructions, edges, address, data))
    require(len(rows) == len(expected) and len(data) == 32 and data[26:28] == b'\0\0'
            and partition['code_bytes'] == 26 and partition['alignment_bytes'] == 2
            and partition['literal_and_table_bytes'] == 4 and len(partition['words']) == 1,
            'table helper complete code/padding/literal partition differs')
    word = partition['words'][0]
    require(word['address'] == address+28 and word['value'] == TABLE_POINT
            and not word['switch_word'] and word['load_sites'] == [address+6]
            and struct.unpack_from('<I', data, 28)[0] == TABLE_POINT,
            'table helper named literal differs')
    mapping = match.parse_data_symbols(objects)
    require(mapping.get(TABLE_NAME) == TABLE_POINT
            and sum(v == TABLE_POINT for v in mapping.values()) == 1,
            'table helper requires the unique existing canonical data identity')
    for index, (site, item, terminal) in enumerate(rows):
        code = int.from_bytes(item.bytes, 'little')
        require(item.size == 2 and site == address+2*index,
                'table helper requires complete narrow instructions')
        if index == 3:
            require(code & 0xFF00 == 0x4B00
                    and ((site+4) & ~3)+4*(code & 255) == word['address'],
                    'table helper literal addressing differs')
        else:
            require(code == expected[index], 'table helper operation or register differs')
    return dict(named_reads=[[TABLE_NAME, 8, 1], [TABLE_NAME, 4, 4]],
        indexed_read='one byte at u32(load32(named+4) + 2*(u8(arg1)*load8(named+8) + u8(arg0)))',
        incoming_general_reads=[0, 1], overwritten_before_observation=[2, 3],
        return_entry_origins=[[12, 12]], writes=[], incoming_stack_reads=[],
        physical_memory_claim=False, table_extent_proved=False)


def body(proof, identity):
    address, size, count, digest = identity
    data = proof.span(address)
    require(len(data) == size and hashlib.sha256(data).hexdigest() == digest,
            'projected output requires an actual complete immutable helper')
    refinement = owner.refine(data, address, proof.mapping)
    ins, edges, branches, calls, words = graph.graph(data, address, refinement)
    require(len(ins) == count and not branches and not words and not refinement['word_switches'],
            'projected helper complete instruction inventory differs')
    partition = graph.partition(data, address, refinement, ins, words)
    return data, ins, edges, calls, partition


def phases(edges, calls):
    expected = [PAIR[0], TABLE[0], WORLD[0], SCREEN[0], SCHEDULER]
    require(list(t for _, t in sorted(calls.items())) == expected,
            'projected outputs require four ordered helpers and one scheduler')
    ordered = sorted(edges)
    require(ordered and set(calls) <= set(edges), 'projected root is incomplete')
    for n, site in enumerate(ordered):
        require(tuple(edges[site]) == (() if n+1 == len(ordered) else (ordered[n+1],)),
                'projected root excludes branches, skipped calls and cycles')


def bind(proof, edges, calls):
    phases(edges, calls)
    evidence = {}
    raw = {identity[0]: body(proof, identity) for identity in (PAIR, NOOP, TABLE, WORLD, SCREEN)}
    require(not raw[NOOP[0]][3] and raw[NOOP[0]][0] == b'\x70\x47',
            'projected pair child is not complete BX LR')
    for identity in (PAIR, NOOP, TABLE, WORLD, SCREEN):
        address, size, count, digest = identity
        data, ins, helper_edges, helper_calls, partition = raw[address]
        if address == PAIR[0]:
            effects = pair_origins(ins, helper_edges, helper_calls, address, data, NOOP[0], raw[NOOP[0]][0])
        elif address == TABLE[0]:
            require(not helper_calls, 'projected table helper must be call-free')
            effects = table_origins(ins, helper_edges, address, data, partition, proof.objects)
        elif address == WORLD[0]:
            require(not helper_calls, 'projected world helper must be call-free')
            effects = three.prove_leaf_origins(ins, helper_edges, address, data, scalar_immediate_add=True)
        elif address == SCREEN[0]:
            require(not helper_calls, 'projected screen helper must be call-free')
            effects = direct.prove_origins(ins, helper_edges, address, data, partition,
                                          proof.objects, direct.named_policy())
            require(effects['return_entry_origins'] == [[3, 8]] and not any(
                    match.ARM_REG_R12 in i.regs_access()[1] for i in ins.values()),
                    'projected screen helper return origins differ')
            effects = dict(effects, return_entry_origins=[[3, 8], [12, 12]])
        else:
            effects = dict(complete_BX_LR=True, memory_effects=[], register_writes=[])
        record = dict(address=address, end=address+size, bytes=size, body_sha256=digest,
            structure=dict(kind=SCHEMA, instructions=count, partition=partition, effects=effects), **proof.identities)
        proof.dependencies[address] = data
        proof.records[address] = record
        evidence[address] = record
    return evidence


def layout(stack):
    local = [i for i, word in enumerate(stack) if word[2]]
    require(local == list(range(13)) and all(not word[0] and not word[1] for word in stack[:13]),
            'projected outputs require thirteen contiguous unprotected private words')
    base = -4*len(stack)
    return dict(base=base, descriptor=base+8, tile=[base+36, base+38],
        world=[base+40, base+42, base+44], screen=[base+46, base+48], end=base+52)


def check_call(proof, address, aliases, stack, slots, *, site):
    frame = layout(stack)
    slots = slots or {}
    r0 = match.ARM_REG_R0
    for offset in aliases.values():
        proof.access(offset, 1, stack)
    for offset, target in slots.items():
        proof.access(offset, 4, stack)
        proof.access(target, 2, stack)
    caller = {r-r0 for r in aliases if r in match.CALLER_CLOBBERED}
    require(match.ARM_REG_LR not in aliases, 'projected call cannot carry a control alias')
    writes, returned = [], {}
    if address == PAIR[0]:
        require(0 not in caller and all(aliases.get(r0+i+1) == frame['tile'][i] for i in range(2))
                and not slots, 'pair call requires its two tile outputs and no pointer words')
        writes = [[x, 2] for x in frame['tile']]
    elif address == TABLE[0]:
        require(not caller & {0, 1} and not slots,
                'table call requires scalar coordinates and no pointer words')
    elif address == WORLD[0]:
        require(not caller & {0, 1, 2} and aliases.get(r0+3) == frame['world'][0]
                and slots == {frame['base']:frame['world'][1], frame['base']+4:frame['world'][2]},
                'world call requires three bounded outputs and both exact pointer words')
        writes = [[x, 2] for x in frame['world']]
    elif address == SCREEN[0]:
        require(not caller & {0, 1, 2} and aliases.get(r0+3) == frame['screen'][0]
                and slots == {frame['base']:frame['screen'][1], frame['base']+4:frame['world'][2]},
                'screen call requires its outputs and retained unused second pointer word')
        writes = [[x, 2] for x in frame['screen']]
    else:
        require(address == SCHEDULER and caller == {2} and aliases[r0+2] == frame['descriptor']
                and slots == {frame['base']:frame['screen'][1], frame['base']+4:frame['world'][2]},
                'scheduler requires its descriptor and both retained outgoing pointer words')
        for offset in range(frame['descriptor'], frame['descriptor']+28):
            proof.access(offset, 1, stack)
    for offset, width in writes:
        proof.access(offset, width, stack)
        require(not any(offset < s+4 and offset+width > s for s in slots),
                'projected output overlaps a live pointer word')
    if address != SCHEDULER:
        effects = proof.projected_outputs[address]['structure']['effects']
        for destination, source in effects['return_entry_origins']:
            if r0+source in aliases:
                returned[r0+destination] = aliases[r0+source]
    observation = dict(site=site, target=address, frame=frame,
        aliases=sorted(aliases.items()), pointer_words=sorted(slots.items()),
        writes=writes, returned_aliases=sorted(returned.items()),
        pointer_words_preserved=True, scheduler_effects_conditional=address == SCHEDULER)
    require(site not in proof.observations or proof.observations[site] == observation,
            'projected helper call state differs across paths')
    proof.observations[site] = observation
    return returned


def manifest(proof):
    require(set(proof.observations) == set(proof.calls), 'every projected call must be observed')
    return dict(schema=SCHEMA, environment=proof.environment,
        runtime_dependencies=proof.runtime_dependencies, helpers=proof.projected_outputs,
        observations=[proof.observations[s] for s in sorted(proof.observations)],
        assumptions=[
            'All reached byte, halfword and word accesses require physical permission and the actual alignment; '
            'bounded frame offsets do not prove physical separation or initialized source values.',
            'The object bytes read by the pair helper and the named/table cells read by the indexed helper '
            'are readable at their recorded ordered access points. The loaded table pointer and indexed byte '
            'remain conditional; the fixed named point grants no table extent or nonalias fact.',
            'Named g_state_02007F40 halfwords at offsets32/34/36/38 are initialized and readable at each reached load; their values remain unknown.',
            'Scheduler allocator/zero/list prefix and synchronous callback return with the compatible ARM ABI, '
            'exact SP and protected saved/caller words preserved. Its returned allocation is separate from '
            'all caller stack words. The complete 28-byte descriptor is readable as representation bytes.',
            'The two retained outgoing pointer words and all preserved-register aliases are recorded exposure, '
            'not dropped arguments. Scheduler and callback access caller memory only within the descriptor, '
            'never by following those two pointer words or the recorded aliases into output storage. '
            'The copied descriptor and ambient original R9 pointer are exposed. No caller-local pointer is '
            'retained after the call or returned in a caller-clobbered register. These access/nonretention '
            'conditions are premises, not inferred from copying, the allocation size or the ABI.'],
        actual_helper_origin_effects_proved=True, actual_callback_effects_proved=False,
        nonescape_proved=False, physical_memory_claim=False, termination_proved=False,
        source_sha256={Path(m.__file__).name:hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
                       for m in (direct, three, __import__(__name__))})
