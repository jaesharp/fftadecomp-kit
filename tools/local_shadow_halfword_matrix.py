"""Conditional common-byte relation for a copied four-by-two local matrix.

This prerequisite does not admit source or ELF. RAM halfwords remain arbitrary;
valid indices, physical access, frame separation and C compatibility are explicit
conditions. The expired frame pointer left in R3 is retained in the poststate.
"""
import hashlib
import struct

import match
import owner_graph_profile as graph
from local_rom_halfword_table_profile import COPY_SHA256, _indexed

SCHEMA = 'conditional-local-shadow-halfword-matrix-v1'
ROOT_WORDS = {
    0:0xb530, 2:0xb088, 4:0x1c05, 6:0x1c0c, 8:0x062d, 10:0x0e2d,
    12:0x0624, 14:0x0e24, 16:0x4b12, 18:0x8958, 20:0xa904, 22:0x8008,
    24:0x899a, 26:0x4668, 28:0x3012, 30:0x8002, 32:0xaa05, 34:0x89d8,
    36:0x8010, 38:0x8a18, 40:0x8050, 42:0xaa06, 44:0x8a58, 46:0x8010,
    48:0x8a98, 50:0x8050, 52:0xaa07, 54:0x8ad8, 56:0x8010, 58:0x8b18,
    60:0x8050, 62:0x4668, 64:0x2210, 70:0x0064, 72:0x00ad, 74:0x1964,
    76:0x4669, 78:0x1908, 80:0x2100, 82:0x5e40, 84:0xb008,
    86:0xbc30, 88:0xbc02, 90:0x4708,
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def word(value):
    return list(struct.pack('<I', value)) if type(value) is int else [f'{value}.{i}' for i in range(4)]


def relation(source_bytes, row, column, *, saved=None):
    """Execute the ordered stores and four-word copy on one relative byte map."""
    require(type(source_bytes) in (bytes, tuple) and len(source_bytes) == 16 and
            all(type(x) is int and 0 <= x <= 255 or type(x) is str for x in source_bytes),
            'sixteen concrete or opaque source bytes required')
    require(type(row) is int and 0 <= row < 4 and type(column) is int and 0 <= column < 2,
            'independent valid row and column bounds required')
    if saved is None:
        saved = dict(R4='entry_R4', R5='entry_R5', LR='entry_LR', BL='root_BL_return')
    require(type(saved) is dict and set(saved) == {'R4','R5','LR','BL'} and all(
        type(v) is int and 0 <= v <= 0xffffffff or type(v) is str for v in saved.values()),
        'complete saved-word identities required')
    cells, reads, writes = {}, [], []

    def put(offset, values, phase):
        require(-56 <= offset and offset+len(values) <= 0, 'write exceeds live combined frame')
        for i, value in enumerate(values):
            cells[offset+i] = value
            writes.append([phase, offset+i, value])

    def get(offset, size, phase):
        require(all(i in cells for i in range(offset, offset+size)), 'uninitialized frame read')
        values = [cells[i] for i in range(offset, offset+size)]
        reads.append([phase, offset, size, values])
        return values

    for off, name in ((-12,'R4'),(-8,'R5'),(-4,'LR')):
        put(off, word(saved[name]), 'root-save')
    for i in range(8):
        put(-28+2*i, source_bytes[2*i:2*i+2], 'halfword-initializer')
    for off, value in ((-56,column),(-52,row),(-48,saved['BL'])):
        put(off, word(value), 'helper-save')
    # Count16 and both aligned local addresses select exactly four LDM/STM pairs.
    for i in range(4):
        put(-44+4*i, get(-28+4*i, 4, 'copy-read'), 'copy-write')
    for off, value in ((-56,column),(-52,row),(-48,saved['BL'])):
        require(get(off,4,'helper-restore') == word(value), 'protected helper save changed')
    selected = get(-44+4*row+2*column, 2, 'indexed-read')
    result = dict(operation='sign_extend_16_to_32', little_endian_bytes=selected)
    if all(type(x) is int for x in selected):
        value = selected[0] | selected[1]<<8
        result['u32'] = (value if value < 0x8000 else value-0x10000) & 0xffffffff
    for off, name in ((-12,'R4'),(-8,'R5'),(-4,'LR')):
        require(get(off,4,'root-restore') == word(saved[name]), 'protected root save changed')
    return dict(row=row, column=column, result=result, reads=reads, writes=writes,
        cells=sorted(cells.items()), restored=['entry_R4','entry_R5','entry_SP','entry_LR_return'],
        final_R1=saved['LR'], final_R2=0xffffffff,
        final_R3=dict(kind='entry_SP_relative_pointer', offset=-12, lifetime='expired', dereference_permission=False),
        copy_words=4, live_source=[-28,-12], live_destination=[-44,-28],
        lifetime='initializer and destination live through the read; root deallocation follows read')


def concrete_domain(entry_sp, entry_r0, entry_r1, shadow, root, helper):
    require(all(type(x) is int and 0 <= x <= 0xffffffff
                for x in (entry_sp,entry_r0,entry_r1,shadow,root,helper)), 'u32 inputs required')
    require(entry_sp >= 56 and entry_sp % 4 == 0, 'aligned nonwrapping56-byte combined frame required')
    require((entry_r0 & 255) < 4 and (entry_r1 & 255) < 2, 'valid low8 row and column required')
    require(shadow % 2 == 0 and shadow+26 <= 0x100000000, 'nonwrapping aligned source halfwords required')
    lo, hi = entry_sp-56, entry_sp
    for base, size in ((shadow+10,16),(root,96),(helper,98)):
        require(base+size <= 0x100000000 and (hi <= base or lo >= base+size),
                'combined active frame overlaps source halfwords or code')
    return dict(frame=[lo,hi], row=entry_r0&255, column=entry_r1&255,
                physical_access_granted=False, initialized_values_assumed=False)


def prove(data, address, rom, mapping, index, objects):
    """Bind complete indexed instructions; no compiler or source invocation."""
    import owner_admission_profile as owner
    require(type(data) is bytes and len(data) == 96 and address % 4 == 0,
            'complete aligned96-byte matrix owner required')
    _indexed(data,address,45,rom,mapping,index)
    require(all(struct.unpack_from('<H',data,p)[0] == value for p,value in ROOT_WORDS.items()),
            'closed matrix owner instruction grammar differs')
    refinement = owner.refine(data,address,mapping)
    ins,_,branches,calls,words = graph.graph(data,address,refinement)
    require(len(ins)==45 and not branches and not words and set(calls)=={address+66},
            'complete owner CFG and single actual copy call required')
    helper = calls[address+66]
    body = rom[helper-match.ROM_BASE:helper-match.ROM_BASE+98]
    _indexed(body,helper,49,rom,mapping,index)
    require(len(body)==98 and hashlib.sha256(body).hexdigest()==COPY_SHA256,
            'complete actual copy helper identity differs')
    hr = owner.refine(body,helper,mapping)
    hi,_,hb,hc,hw = graph.graph(body,helper,hr)
    require(len(hi)==49 and not hb and not hc and not hw, 'complete helper CFG required')
    shadow = struct.unpack_from('<I',data,92)[0]
    names = match.parse_data_symbols(objects)
    identities = [name for name,value in names.items() if value==shadow]
    require(len(identities)==1 and shadow%2==0 and shadow+26<=0x100000000,
            'unique canonical aligned shadow point required')
    symbolic = tuple(f'shadow_halfword_{i//2}.byte{i%2}' for i in range(16))
    return dict(schema=SCHEMA, address=address, instructions=45, helper=helper,
        helper_instructions=49, shadow_point=shadow, shadow_identity=identities[0],
        partition=graph.partition(data,address,refinement,ins,words),
        helper_partition=graph.partition(body,helper,hr,hi,hw),
        cases=[relation(symbolic,row,col) for row in range(4) for col in range(2)],
        source_bytes_known=False, actual_entry_SP_known=False,
        source_or_ELF_admission=False, physical_access_proved=False,
        input_pins={key:hashlib.sha256(value).hexdigest() for key,value in
                    (('owner',data),('rom',rom),('mapping',mapping),('index',index),('objects',objects))},
        conditions=['low8(entry_R0)<4 and low8(entry_R1)<2; narrowing alone establishes neither bound',
            'entry_SP is aligned4 and [entry_SP-56,entry_SP) does not wrap',
            'the active root and helper frames have ordinary byte/halfword/word read-write access and valid lifetimes',
            'shadow+10 through shadow+25 are readable ordinary halfword storage; contents remain arbitrary',
            'the combined frame is disjoint from those source halfwords and both complete code bodies',
            'no asynchronous interference with code, input halfwords or active frame',
            'valid entry return continuation; C source/type correspondence and original ELF transport remain separate',
            'expired R3 frame pointer remains in machine poststate and grants no later access'])
