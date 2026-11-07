"""Closed eight-byte ROM-to-local copy and valid-index halfword return.

This selector proves a conditional machine relation. In particular, narrowing
an input to u8 does not prove that it indexes a four-element local array.
No physical stack, source readability or asynchronous noninterference follows
from a named data point. Those conditions remain explicit in every report.
"""
import hashlib
import json
from pathlib import Path
import struct

import match
import owner_graph_profile as graph
from inert_spin_profile import validate_span

SELECTOR = 'local-rom-halfword-table-v1'
SCHEMA = 'elf-symbol-thumb-local-rom-halfword-table-v1'
CONTROL_FLOW = 'complete eight-byte ROM copy into live local frame; conditional low8 index below four and explicit source/frame access and separation'
COPY_SHA256 = 'aa822d873bad381a62e3c3e07b06003a41beea59bc3edc791f7e316eb08b7ebb'
ROOT_WORDS = {0: 0xb510, 2: 0xb082, 4: 0x1c04, 6: 0x0624,
              8: 0x0e24, 10: 0x4906, 12: 0x4668, 14: 0x2208,
              20: 0x0064, 22: 0x4669, 24: 0x1908, 26: 0x8800,
              28: 0xb002, 30: 0xbc10, 32: 0xbc02, 34: 0x4708}
# Only these helper instructions execute when R2 is eight. The whole helper
# also has an exact indexed identity; its larger-copy paths are not assumed.
COPY_PATH = {0: 0xb530, 2: 0x1c05, 4: 0x1c2c, 6: 0x1c0b,
             8: 0x2a0f, 10: 0xd919, 64: 0x3a01, 66: 0x2001,
             68: 0x4240, 70: 0x4282, 72: 0xd007, 74: 0x1c01,
             76: 0x7818, 78: 0x7020, 80: 0x3301, 82: 0x3401,
             84: 0x3a01, 86: 0x428a, 88: 0xd1f8, 90: 0x1c28,
             92: 0xbc30, 94: 0xbc02, 96: 0x4708}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def _word(value):
    return list(struct.pack('<I', value)) if type(value) is int else [f'{value}.{i}' for i in range(4)]


def relation(table, index):
    """Symbolic common-byte stack, relative to arbitrary aligned entry SP.

    Entry saved registers are uninterpreted byte tokens. Reads from ROM are
    separate only under the reported source/frame nonoverlap condition.
    """
    require(type(table) is bytes and len(table) == 8, 'exact eight-byte source required')
    require(type(index) is int and 0 <= index < 4, 'valid low8 index below four required')
    cells, writes, reads = {}, [], []

    def put(offset, values, phase):
        require(-28 <= offset and offset + len(values) <= 0, 'write outside live combined frame')
        for i, value in enumerate(values):
            cells[offset + i] = value
            writes.append([phase, offset + i, value])

    def get(offset, size):
        require(all(i in cells for i in range(offset, offset + size)), 'uninitialized local read')
        reads.append([offset, size])
        return [cells[i] for i in range(offset, offset + size)]

    # Root PUSH, root allocation, helper PUSH, then actual byte loop.
    put(-8, _word('entry_R4'), 'root-save')
    put(-4, _word('entry_LR'), 'root-save')
    put(-28, _word(index), 'helper-save')
    put(-24, _word('entry_R5'), 'helper-save')
    put(-20, _word('root_BL_return'), 'helper-save')
    remaining = 7  # SUBS R2,#1 before the byte loop; sentinel R1=-1.
    cursor = 0
    while remaining != 0xffffffff:
        require(cursor < 8, 'copy exceeds actual eight-byte count')
        put(-16 + cursor, [table[cursor]], 'copy')
        cursor += 1
        remaining = (remaining - 1) & 0xffffffff
    require(cursor == 8, 'copy did not initialize the complete local table')
    require(get(-28, 4) == _word(index) and get(-24, 4) == _word('entry_R5') and
            get(-20, 4) == _word('root_BL_return'), 'helper saves were overwritten')
    result_bytes = get(-16 + 2 * index, 2)
    require(get(-8, 4) == _word('entry_R4') and get(-4, 4) == _word('entry_LR'),
            'root protected saves were overwritten')
    return dict(index=index, R0=result_bytes[0] | (result_bytes[1] << 8),
                writes=writes, reads=reads, post_cells=sorted(cells.items()),
                restored=['entry_R4', 'entry_R5', 'entry_SP', 'entry_LR_return'],
                final_R1='entry_LR', final_R2=0xffffffff, final_R3='source+8',
                escaped_local_pointers=[], helper_iterations=cursor)


def concrete_domain(entry_sp, entry_r0, source, root, helper):
    """Check numeric premises only; never manufacture physical permissions."""
    require(all(type(n) is int and 0 <= n <= 0xffffffff
                for n in (entry_sp, entry_r0, source, root, helper)), 'u32 addresses and input required')
    require(entry_sp % 4 == 0 and entry_sp >= 28, 'aligned nonwrapping 28-byte frame required')
    require((entry_r0 & 255) < 4, 'valid low8 index below four required')
    lo, hi = entry_sp - 28, entry_sp
    for base, size in ((source, 8), (root, 40), (helper, 98)):
        require(base + size <= 0x100000000 and (hi <= base or lo >= base + size),
                'active frame overlaps immutable source or code')
    return dict(frame=[lo, hi], index=entry_r0 & 255,
                physical_access_granted=False, noninterference_granted=False)


def _indexed(body, address, count, rom, mapping, index):
    entries = validate_span(body, address, rom, mapping, index)
    row = next(row for row in entries if int(row['rom'], 16) == address)
    text = [line.split() for line in index.decode().splitlines()
            if line.split() and line.split()[0] == f'{address:08X}']
    require(type(row.get('instrs')) is int and row['instrs'] == count and
            len(text) == 1 and len(text[0]) >= 4 and int(text[0][3]) == count,
            'both exact indexed instruction counts required')


def prove(data, address, rom, mapping, index, objects, *, bindings, source_fingerprint):
    import owner_admission_profile as owner
    require(type(source_fingerprint) is str and len(source_fingerprint) == 64 and
            all(c in '0123456789abcdef' for c in source_fingerprint), 'current source fingerprint required')
    require(type(data) is bytes and len(data) == 40 and address % 4 == 0,
            'complete aligned forty-byte local table owner required')
    _indexed(data, address, 17, rom, mapping, index)
    require(all(struct.unpack_from('<H', data, p)[0] == word for p, word in ROOT_WORDS.items()),
            'closed local table root instruction grammar differs')
    refinement = owner.refine(data, address, mapping)
    ins, _, branches, calls, words = graph.graph(data, address, refinement)
    require(len(ins) == 17 and not branches and not words and set(calls) == {address + 16},
            'one actual direct copy call and complete root CFG required')
    helper = calls[address + 16]
    body = rom[helper - match.ROM_BASE:helper - match.ROM_BASE + 98]
    _indexed(body, helper, 49, rom, mapping, index)
    require(len(body) == 98 and sha(body) == COPY_SHA256 and all(
            struct.unpack_from('<H', body, p)[0] == word for p, word in COPY_PATH.items()),
            'complete canonical copy helper identity or eight-byte path differs')
    helper_refinement = owner.refine(body, helper, mapping)
    hi, _, hb, hc, hw = graph.graph(body, helper, helper_refinement)
    require(len(hi) == 49 and not hb and not hc and not hw, 'complete copy helper CFG required')
    source = struct.unpack_from('<I', data, 36)[0]
    require(match.ROM_BASE <= source <= match.ROM_BASE + len(rom) - 8,
            'source eight-byte slice is outside current ROM')
    names = match.parse_data_symbols(objects)
    identities = [name for name, value in names.items() if value == source]
    require(len(identities) == 1, 'one canonical source point identity required')
    expected = dict(calls=[[16, f'func_{helper:08X}']],
                    data=[[36, identities[0], 0]], functions=[], switches=[])
    require(type(bindings) is dict and bindings == expected, 'exact original zero-addend typed bindings required')
    table = rom[source - match.ROM_BASE:source - match.ROM_BASE + 8]
    effect = dict(source=source, source_bytes_sha256=sha(table),
        source_point=identities[0], helper=helper, helper_sha256=sha(body),
        root_sha256=sha(data), source_sha256=source_fingerprint,
        input_pins={name: sha(raw) for name, raw in
                    (('rom', rom), ('mapping', mapping), ('index', index), ('objects', objects))},
        producer_sha256=sha(Path(__file__).read_bytes()),
        combined_frame=[-28, 0], root_saves=[-8, 0], local_table=[-16, -8],
        helper_saves=[-28, -16], cases=[relation(table, i) for i in range(4)],
        conditions=[
            '(entry_R0 & 255) < 4; no bound is inferred from u8 narrowing',
            'entry_SP is four-byte aligned and [entry_SP-28,entry_SP) does not wrap',
            'the active frame has valid ordinary byte/word read/write access and lifetimes',
            'the eight source bytes are readable ordinary memory with the captured ROM values',
            'the active frame is disjoint from the source slice and both complete code bodies',
            'code and source are immutable and active frames suffer no external interference',
            'entry return continuation and the C object/type/ABI compatibility are valid'],
        physical_access_proved=False, all_u8_inputs_in_bounds=False,
        termination='eight byte-loop iterations under the explicit access conditions',
        local_lifetime='helper saves expire before local read; local array expires only after read')
    return dict(schema=SCHEMA, instructions=17, calls=expected['calls'], runtime_calls=[],
                partition=graph.partition(data, address, refinement, ins, words),
                helper_partition=graph.partition(body, helper, helper_refinement, hi, hw),
                local_rom_halfword_table=effect)
