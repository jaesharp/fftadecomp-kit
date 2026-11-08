"""Initialized local descriptors whose callback word is a typed function literal.

Three exact root forms reach one of a closed table of pinned read-only node
iterators (the 080C7CC0 list walk or the 080C7D18/080C7D70 in-order tree
walks) and either the two-word scalar adapter admitted by
conditional-two-word-callback-closure-v1 or a pinned framed two-output adapter
whose getter effect is interpreted. Descriptor
word zero is the constant zero, the entry R0 value, or the address of a private
two-word state. Only the state form passes private-frame provenance, so only an
exact pinned state callback is admitted there and its complete effect is
interpreted; the root then returns the state word it reads back after the call.
Opaque callbacks retain the explicit compatible returning ABI and memory
noninterference premises. No iteration bound or termination is assumed.
"""
import hashlib
import json
from pathlib import Path
import struct

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import function_thunk_profile as thunk
import local_long_branch_profile as frame
import scalar_callback_adapter_inventory as adapter
from software_double_profile import indices, span_record

SELECTOR = 'conditional-two-word-literal-callback-closure-v1'
SCHEMA = 'elf-symbol-thumb-conditional-two-word-literal-callback-closure-v1'
CONTROL_FLOW = 'complete initialized two-word local descriptor with typed callback literal and read-only callback iterator; private state only through an interpreted pinned callback; compatible returning indirect ABI and memory noninterference conditional; termination unproved'
PRESERVED = adapter.PRESERVED
# Closed table of read-only callback iterators. Each body is pinned by size,
# refined count and SHA-256 and its structure is re-derived below: the entry
# copies of the adapter (R1) and descriptor (R2) into callee-saved registers,
# which nothing else writes; the one call through the adapter register's thunk
# with R0 = current node and R1 = descriptor; no stores; and exactly the listed
# word reads, from the list object (entry R0, first load only) or the current
# node (R4).
ITERATORS = {
    0x080C7CC0: dict(size=34, count=16, call=20, adapter_register=6, descriptor_register=5,
        sha256='47422d610f242091222c8c8e303ea235eede92f9a9c9cc40cd8552e8f44f45d1',
        kind='singly linked list: first node at list+4, next node at node+8',
        reads=(('list', 4), ('node', 8)), descriptor_in_r2_on_empty_path=True,
        loop_invariant='R6 is the exact adapter Thumb pointer; R5 is the original initialized descriptor; R4 is null or the current ordinary node. Each returning adapter preserves R4-R11/SP. Only node+8 advances the loop; callback R0 selects continuation.'),
    0x080C7D18: dict(size=86, count=42, call=50, adapter_register=7, descriptor_register=6,
        sha256='ee7686daca5c7774589a5795bd17453d4f109674942402d1a7fcc13296e78da2',
        kind='parent-linked binary tree, in order: root at list+8, parent at node+8, node+12 subtree visited before node+16',
        reads=(('list', 8), ('node', 8), ('node', 12), ('node', 16)), descriptor_in_r2_on_empty_path=False,
        loop_invariant='R7 is the exact adapter Thumb pointer; R6 is the original initialized descriptor; R5 is the root node; R4 is null or the current ordinary node; R2 is -1 or the previous node. Moves are only to node+12, node+16 or the node+8 parent; each returning adapter preserves R4-R11/SP. The adapter is called with the current nonnull node and the descriptor; callback R0 zero stops, as does ascending from the root.'),
    0x080C7D70: dict(size=86, count=42, call=50, adapter_register=7, descriptor_register=6,
        sha256='6af858bb8def974b2ad9e56dce5bc14c3d6a4b8c5a3570e9f6478c9d8ccf07c5',
        kind='parent-linked binary tree, in order: root at list+8, parent at node+8, node+16 subtree visited before node+12',
        reads=(('list', 8), ('node', 8), ('node', 12), ('node', 16)), descriptor_in_r2_on_empty_path=False,
        loop_invariant='R7 is the exact adapter Thumb pointer; R6 is the original initialized descriptor; R5 is the root node; R4 is null or the current ordinary node; R2 is -1 or the previous node. Moves are only to node+16, node+12 or the node+8 parent; each returning adapter preserves R4-R11/SP. The adapter is called with the current nonnull node and the descriptor; callback R0 zero stops, as does ascending from the root.'),
}
# Closed table of framed two-output adapters. The adapter and its getter are
# pinned byte for byte and interpreted by framed_adapter_effects. Scalar
# adapters still go through scalar_callback_adapter_inventory unchanged.
FRAMED_ADAPTERS = {
    0x0809AC00: dict(count=14, body='10b582b00c1c01aa69462cf0b5ff009821686268a7f01afb02b010bc02bc0847',
        getter=0x080C7B78, getter_count=5, getter_body='43680b60006810607047'),
}
FRAMED_SCHEMA = 'two-word-framed-two-output-callback-adapter-v1'
# Exact root forms. 'xx' marks the one aligned owner word-load halfword, the
# iterator BL and the two typed literal words; every other byte is fixed.
FORMS = {
    'private-state': dict(size=44, count=17, call=24, owner=20, callback=36, adapter=40,
        stack_words=5, frame_bytes=16, descriptor=-12, state=-20, word0='address of private state at entry SP-20',
        code='00b584b000220092019106496a46029202aa5160xxxx0449xxxxxxxx009804b002bc0847'),
    'entry-object': dict(size=40, count=15, call=22, owner=16, callback=32, adapter=36,
        stack_words=3, frame_bytes=8, descriptor=-12, state=None, word0='root entry R0',
        code='00b582b0011c80310a68054900900191xxxx04496a46xxxxxxxx02b001bc0047'),
    'null': dict(size=36, count=13, call=18, owner=12, callback=28, adapter=32,
        stack_words=3, frame_bytes=8, descriptor=-12, state=None, word0='constant zero',
        code='00b582b0054a002100910192xxxx04496a46xxxxxxxx02b001bc0047'),
}
# The only private-state callback admitted: it receives the state address in
# R1, so its complete body is pinned and interpreted below.
STATE_CALLBACKS = {0x0809AC20: (8, '4a6801c20868013008604a6001207047')}


def sha(data): return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok: raise ValueError(message)


def complete(address, size, count, rom, mapping, index):
    # count is the refined reachable-instruction count (literal pools excluded,
    # as analyze.refine_function reports); both indexes must carry it.
    data = rom[address-match.ROM_BASE:address-match.ROM_BASE+size]
    owner.validate_span(data, address, rom, mapping, index)
    entries, rows = indices(mapping, index)
    identity = span_record(address, address+size, entries, rows, rom)
    refinement = owner.refine(data, address, mapping)
    ins, edges, branches, calls, words = graph.graph(data, address, refinement)
    partition = graph.partition(data, address, refinement, ins, words)
    require(not branches and not words and len(ins) == count and identity['instrs'] == count,
            'literal closure requires exact complete owner/count')
    return data, ins, edges, calls, partition


def form_of(data):
    """Return the unique exact root form; masked halfwords are decoded later."""
    found = []
    for name, form in FORMS.items():
        code = form['code']
        if len(data) == form['size'] and len(code) == 2*(form['size']-8) and all(
                code[2*n:2*n+2] == 'xx' or bytes.fromhex(code[2*n:2*n+2])[0] == data[n]
                for n in range(form['size']-8)):
            found.append(name)
    require(len(found) == 1, 'literal closure requires one complete natural root form')
    return found[0]


def state_callback_effects(body, address):
    """Interpret the complete straight-line state callback on symbolic tokens.

    R0 is the getter word, R1 the private state address. State words 0 and 4
    hold their entry tokens. Every access through R1 must be an aligned word
    of the two-word state; the only other store is through the value loaded
    from state word 4. The callback must return 1 by BX LR with R4-R11, SP and
    LR unchanged and no state address stored in memory.
    """
    require(type(body) is bytes and type(address) is int and address in STATE_CALLBACKS and
            body == bytes.fromhex(STATE_CALLBACKS[address][1]), 'pinned state callback body differs')
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB); decoder.detail = True
    code = list(decoder.disasm(body, address))
    require(sum(item.size for item in code) == len(body) and len(code) == STATE_CALLBACKS[address][0],
            'complete code-only state callback required')
    regs = {n: ('entry', n) for n in range(13)}
    regs[0], regs[1], regs[14] = ('object',), ('state',), ('return',)
    state = {0: ('state-word', 0), 4: ('state-word', 4)}
    reads, writes, external = [], [], []
    for number, item in enumerate(code):
        raw = int.from_bytes(item.bytes, 'little')
        last = number == len(code)-1
        require(item.size == 2 and raw != 0x4770 and not last or raw == 0x4770 and last,
                'state callback must be one linear block ending in BX LR')
        if raw == 0x4770:
            break
        if raw & 0xf000 == 0x6000:  # LDR/STR Rd,[Rb,#imm5*4]
            rd, rb, offset = raw & 7, (raw >> 3) & 7, 4*((raw >> 6) & 31)
            require(regs[rb] == ('state',) and offset in state,
                    'state callback word access leaves the private two-word state')
            if raw & 0x800:
                regs[rd] = state[offset]; reads.append([item.address, offset, 4])
            else:
                require(regs[rd] != ('state',), 'state callback stores the private state address')
                state[offset] = regs[rd]; writes.append([item.address, offset, 4])
        elif raw & 0xf800 == 0xc000:  # STMIA Rb!,{Rlist}
            rb, rlist = (raw >> 8) & 7, raw & 255
            require(regs[rb] == ('state-word', 4) and rlist & ~(1 << rb) == rlist and
                    bin(rlist).count('1') == 1, 'state callback external store requires the loaded cursor')
            rs = rlist.bit_length()-1
            require(regs[rs] == ('object',), 'state callback external store must be the getter word')
            external.append([item.address, 'state word 4 on entry', 0, 4, regs[rs][0]])
            regs[rb] = ('cursor-plus', 4)
        elif raw & 0xf800 == 0x3000:  # ADDS Rd,#imm8
            rd = (raw >> 8) & 7
            require(regs[rd] == ('state-word', 0), 'state callback arithmetic must update state word 0')
            regs[rd] = ('state-word-0-plus', raw & 255)
        elif raw & 0xf800 == 0x2000:  # MOVS Rd,#imm8
            regs[(raw >> 8) & 7] = ('constant', raw & 255)
        else:
            raise ValueError('unsupported state callback instruction')
    require(regs[0] == ('constant', 1) and regs[14] == ('return',) and
            all(regs[n] == ('entry', n) for n in range(4, 12)),
            'state callback return/frame differs')
    require(state == {0: ('state-word-0-plus', 1), 4: ('cursor-plus', 4)} and
            sorted(row[1] for row in reads) == [0, 4] and sorted(row[1] for row in writes) == [0, 4] and
            len(external) == 1, 'state callback effect relation differs')
    return dict(address=address, end=address+len(body), instructions=len(code), body_sha256=sha(body),
        state_reads=reads, state_writes=writes, external_writes=external, return_value=1,
        relation='state word 0 becomes its incoming value plus 1 modulo 2**32; the object word is stored at the incoming state word 4 cursor, which then advances by 4; R0 is 1',
        frame_bytes=0, protected_registers=[], leaf=True,
        private_state_address_stored=False, all_paths_interpreted=True)


def iterator_structure(body, address, entry, calls):
    """Check one pinned iterator entry and re-derive its structural facts."""
    require(len(body) == entry['size'] and sha(body) == entry['sha256'],
            'literal closure iterator body differs from its pinned identity')
    a, d = entry['adapter_register'], entry['descriptor_register']
    selected = thunk.ALIASES[f'_call_via_r{a}']
    require(calls == {address+entry['call']: selected}, 'literal closure iterator call differs')
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB); decoder.detail = True
    code = list(decoder.disasm(body, address))
    require(sum(item.size for item in code) == len(body) and len(code) == entry['count'],
            'literal closure iterator must decode completely')
    raw = [int.from_bytes(item.bytes[:2], 'little') for item in code]
    site = next(n for n, item in enumerate(code) if item.address == address+entry['call'])
    r0, r4 = match.ARM_REG_R0, match.ARM_REG_R0+4
    require(code[0].mnemonic == 'push' and raw[1] == 0x1C08 | a and raw[2] == 0x1C10 | d and
            raw[site-2] == 0x1C20 and raw[site-1] == 0x1C01 | d << 3 and
            [item.mnemonic for item in code[-3:]] == ['pop', 'pop', 'bx'],
            'literal closure iterator entry copies, call arguments or exit differ')
    reads, r0_live = set(), True
    for number, item in enumerate(code):
        require(not item.mnemonic.startswith(('str', 'stm')) and (number == 0 or item.mnemonic != 'push'),
                'literal closure iterator must not store')
        written = set(item.regs_access()[1])
        if 3 <= number < len(code)-3:
            require(not written & {r0+a, r0+d}, 'literal closure iterator overwrites its adapter or descriptor')
        if item.mnemonic == 'ldr':
            mem = item.operands[1]
            require(mem.type == match.ARM_OP_MEM and not mem.mem.index and mem.mem.disp % 4 == 0 and
                    (mem.mem.base == r0 and r0_live or mem.mem.base == r4),
                    'literal closure iterator reads outside the list object and current node')
            reads.add(('list' if mem.mem.base == r0 else 'node', mem.mem.disp))
        if r0 in written:
            r0_live = False
    require(reads == set(entry['reads']), 'literal closure iterator read set differs')
    return selected


def framed_adapter_effects(body, address, getter_body, getter):
    """Interpret the complete pinned framed adapter and its leaf getter.

    Entry R0 is the current node and R1 the descriptor. The adapter saves R4
    and LR, reserves eight private bytes, passes their two word addresses to
    the getter, forwards private word zero and descriptor word zero to the
    descriptor word-four target through the R2 thunk, and returns that
    target's R0 through its saved LR. The getter may only read node words and
    store them into the adapter's private bytes.
    """
    require(type(body) is bytes and type(getter_body) is bytes and address in FRAMED_ADAPTERS and
            body == bytes.fromhex(FRAMED_ADAPTERS[address]['body']) and
            getter == FRAMED_ADAPTERS[address]['getter'] and
            getter_body == bytes.fromhex(FRAMED_ADAPTERS[address]['getter_body']),
            'pinned framed adapter or getter body differs')
    target = thunk.ALIASES['_call_via_r2']
    regs = {n: ('entry', n) for n in range(13)}
    regs[0], regs[1], regs[14] = ('node',), ('descriptor',), ('return',)
    sp, frame, local, getter_record, callback, reads, number = 0, {}, None, None, None, [], 0
    halfwords = struct.unpack(f'<{len(body)//2}H', body)
    while number < len(halfwords):
        raw, here = halfwords[number], address+2*number
        last = number == len(halfwords)-1
        require(raw & 0xFF00 != 0x4700 or last, 'framed adapter must return only at its end')
        if raw & 0xFE00 == 0xB400:  # PUSH {Rlist[,LR]}
            saved = [r for r in range(8) if raw >> r & 1] + ([14] if raw & 0x100 else [])
            sp -= 4*len(saved)
            for n, r in enumerate(saved): frame[sp+4*n] = regs[r]
        elif raw & 0xFF80 == 0xB080:  # SUB SP,#imm7*4
            require(local is None, 'framed adapter allows one private local area')
            sp -= 4*(raw & 0x7F); local = (sp, sp+4*(raw & 0x7F))
        elif raw & 0xFF80 == 0xB000:  # ADD SP,#imm7*4
            sp += 4*(raw & 0x7F)
        elif raw & 0xFFC0 == 0x1C00:  # ADDS Rd,Rn,#0
            regs[raw & 7] = regs[raw >> 3 & 7]
        elif raw & 0xF800 == 0xA800:  # ADD Rd,SP,#imm8*4
            regs[raw >> 8 & 7] = ('frame', sp+4*(raw & 0xFF))
        elif raw & 0xFFF8 == 0x4668:  # MOV Rd,SP
            regs[raw & 7] = ('frame', sp)
        elif raw & 0xF800 == 0x9800:  # LDR Rd,[SP,#imm8*4]
            offset = sp+4*(raw & 0xFF)
            require(local and local[0] <= offset < local[1] and offset in frame,
                    'framed adapter reads an unwritten or nonlocal frame word')
            regs[raw >> 8 & 7] = frame[offset]
        elif raw & 0xF800 == 0x6800:  # LDR Rd,[Rb,#imm5*4]
            offset = 4*(raw >> 6 & 31)
            require(regs[raw >> 3 & 7] == ('descriptor',) and offset in (0, 4),
                    'framed adapter reads outside the two descriptor words')
            regs[raw & 7] = ('descriptor-word', offset); reads.append(dict(site=here, offset=offset, width=4))
        elif raw & 0xF800 == 0xF000 and number+1 < len(halfwords) and halfwords[number+1] & 0xF800 == 0xF800:
            low = halfwords[number+1]
            delta = ((raw & 0x7FF) << 12 | (low & 0x7FF) << 1)
            destination = here+4+(delta - (1 << 23) if delta & (1 << 22) else delta)
            if destination == getter and getter_record is None and callback is None:
                getter_record = _framed_getter(getter_body, getter, regs, frame, local)
            elif destination == target and getter_record is not None and callback is None:
                callback = dict(site=here, thunk=target, target=regs[2], arguments=[regs[0], regs[1]])
            else:
                raise ValueError('framed adapter calls differ')
            for r in (0, 1, 2, 3, 12): regs[r] = ('clobbered',)
            regs[14] = ('clobbered',)
            if destination == target: regs[0] = ('callback-result',)
            number += 2; continue
        elif raw & 0xFE00 == 0xBC00:  # POP {Rlist} without PC
            require(not raw & 0x100, 'framed adapter must not pop PC')
            for r in [r for r in range(8) if raw >> r & 1]:
                regs[r] = frame[sp]; sp += 4
        elif raw & 0xFF87 == 0x4700 and last:  # BX Rm
            require(regs[raw >> 3 & 15] == ('return',), 'framed adapter must return through its saved LR')
        else:
            raise ValueError('unsupported framed adapter instruction')
        number += 1
    require(sp == 0 and local == (-16, -8) and regs[0] == ('callback-result',) and
            all(regs[n] == ('entry', n) for n in range(4, 12)), 'framed adapter return/frame differs')
    require(callback == dict(site=callback and callback['site'], thunk=target, target=('descriptor-word', 4),
            arguments=[('node-word', 4), ('descriptor-word', 0)]) and
            sorted(row['offset'] for row in reads) == [0, 4], 'framed adapter effect relation differs')
    return dict(schema=FRAMED_SCHEMA, address=address, end=address+len(body), instructions=FRAMED_ADAPTERS[address]['count'],
        body_sha256=sha(body), descriptor_register=4, descriptor_reads=reads,
        frame=dict(saved=['entry R4', 'entry LR'], local_bytes=8, local_offsets=[-16, -12],
                   established_by='pinned bytes and the interpreter, not the frame prover'),
        getter=getter_record,
        callback=dict(site=callback['site'], thunk=target,
            target='descriptor word at offset 4',
            arguments=['node word at offset 4, copied through private word -16', 'descriptor word at offset 0'],
            descriptor_address_passed_as_argument=False, result='unchanged callback R0'),
        private_frame_addresses_passed=['private word -16 to the getter in R1', 'private word -12 to the getter in R2'],
        all_paths_interpreted=True)


def _framed_getter(body, address, caller, frame, local):
    """Interpret the straight-line leaf getter on the adapter's symbolic state."""
    regs = {n: caller[n] for n in range(13)}
    regs[14] = ('getter-return',)
    reads, writes = [], []
    halfwords = struct.unpack(f'<{len(body)//2}H', body)
    for number, raw in enumerate(halfwords):
        here, last = address+2*number, number == len(halfwords)-1
        require((raw == 0x4770) == last, 'framed getter must be one linear block ending in BX LR')
        if raw == 0x4770:
            break
        rd, rb, offset = raw & 7, raw >> 3 & 7, 4*(raw >> 6 & 31)
        if raw & 0xF800 == 0x6800:
            require(regs[rb] == ('node',), 'framed getter reads outside the current node')
            regs[rd] = ('node-word', offset); reads.append(dict(site=here, base='current node', offset=offset, width=4))
        elif raw & 0xF800 == 0x6000:
            base = regs[rb]
            require(base[0] == 'frame' and local and local[0] <= base[1]+offset < local[1],
                    'framed getter store leaves the adapter private frame')
            require(regs[rd][0] == 'node-word', 'framed getter may store only node words')
            frame[base[1]+offset] = regs[rd]
            writes.append(dict(site=here, frame_offset=base[1]+offset, width=4, value=f'node word {regs[rd][1]}'))
        else:
            raise ValueError('unsupported framed getter instruction')
    require(sorted(row['frame_offset'] for row in writes) == [-16, -12] and len(writes) == 2 and
            frame.get(-16) == ('node-word', 4) and frame.get(-12) == ('node-word', 0),
            'framed getter effect relation differs')
    return dict(address=address, end=address+len(body), instructions=len(halfwords), body_sha256=sha(body),
        reads=reads, writes=writes, leaf=True, frame_bytes=0,
        relation='private word -16 becomes node word 4 and private word -12 becomes node word 0; nothing else is written')


class _LiteralContextRead(match.BufferCallProof):
    def __init__(self, rom, mapping, site, target, form):
        super().__init__(rom, mapping, stack_arguments=True)
        self.site, self.call_target, self.form = site, target, form
        self.observed = []

    def check_call(self, address, aliases, stack, slots=None, *, site=None, words=None, **kwargs):
        r2 = match.ARM_REG_R0+2
        form = FORMS[self.form]
        expected = {} if form['state'] is None else {form['descriptor']: form['state']}
        if site != self.site or address != self.call_target or (slots or {}) != expected or words or \
                aliases != {r2: form['descriptor']} or len(stack) != form['stack_words']:
            raise ValueError('literal closure call differs from its complete initialized root context')
        self.access(form['descriptor'], 4, stack)
        self.access(form['descriptor']+4, 4, stack)
        if form['state'] is not None:
            self.access(form['state'], 4, stack)
            self.access(form['state']+4, 4, stack)
        self.observed.append(dict(site=site, target=address, descriptor_offset=form['descriptor'], width=8,
                                  pointer_slots=[[offset, value] for offset, value in sorted(expected.items())]))
        return {}


def prove(data, address, rom, mapping, index, *, selector):
    require(type(selector) is str and selector == SELECTOR and type(address) is int and
            all(type(v) is bytes for v in (data, rom, mapping, index)),
            'literal closure requires its exact explicit policy and immutable inputs')
    name = form_of(data); form = FORMS[name]
    body, ins, edges, calls, partition = complete(address, form['size'], form['count'], rom, mapping, index)
    r0, r1, r2 = match.ARM_REG_R0, match.ARM_REG_R0+1, match.ARM_REG_R0+2
    iterator = calls.get(address+form['call'])
    require(data == body and len(calls) == 1 and iterator in ITERATORS and
            partition['literal_and_table_bytes'] == 8 and not partition['alignment_bytes'] and
            sorted(row['address']-address for row in partition['words']) == [form['callback'], form['adapter']],
            'literal closure requires the exact iterator call and two complete literals')
    source = ins[address+form['owner']]
    base = r2 if name == 'entry-object' else r0
    require(len(source.operands) == 2 and source.operands[1].type == match.ARM_OP_MEM and
            adapter.load(source, r0, base, source.operands[1].mem.disp) and
            source.operands[1].mem.disp >= 0 and not source.operands[1].mem.disp % 4,
            'literal closure requires an aligned incoming object word load')
    callback_value, adapter_value = (struct.unpack_from('<I', body, form[key])[0] for key in ('callback', 'adapter'))
    require(callback_value % 2 == 1 and adapter_value % 2 == 1,
            'literal closure literals must be typed odd Thumb pointers')
    entries = json.loads(mapping)
    callback = match.function_address_target(f'func_{callback_value&~1:08X}', entries, address, len(data), len(rom))
    adapter_address = match.function_address_target(f'func_{adapter_value&~1:08X}', entries, address, len(data), len(rom))
    shape = ITERATORS[iterator]
    worker, wi, we, wc, wp = complete(iterator, shape['size'], shape['count'], rom, mapping, index)
    require(not wp['literal_and_table_bytes'] and not wp['alignment_bytes'],
            'literal closure requires the complete read-only node iterator')
    selected = iterator_structure(worker, iterator, shape, wc)
    selected_name = f"_call_via_r{shape['adapter_register']}"
    index_entries, rows = indices(mapping, index)
    if adapter_address in FRAMED_ADAPTERS:
        pinned = FRAMED_ADAPTERS[adapter_address]
        getter = pinned['getter']
        adapter_data, ai, ae, ac, ap = complete(adapter_address, len(pinned['body'])//2, pinned['count'],
                                                rom, mapping, index)
        gdata, gi, ge, gc, gp = complete(getter, len(pinned['getter_body'])//2, pinned['getter_count'],
                                         rom, mapping, index)
        require(not ap['literal_and_table_bytes'] and not ap['alignment_bytes'] and not gc and
                not gp['literal_and_table_bytes'] and not gp['alignment_bytes'] and
                ac == {adapter_address+10: getter, adapter_address+20: thunk.ALIASES['_call_via_r2']},
                'literal closure requires its complete pinned framed adapter')
        adapter_proof = dict(framed_adapter_effects(adapter_data, adapter_address, gdata, getter),
            partition=ap, explicit_conditions=[
                'Each node passed to the adapter is nonnull and its words 0 and 4 are aligned, live, initialized and readable.',
                'The adapter\'s private eight-byte local area and saved words form a valid frame that does not wrap or alias the node, the descriptor, callback-visible memory or code; the getter\'s two out-pointers address only that local area, as interpreted, and no frame address is retained or returned.',
                'The getter and the descriptor target are compatible returning Thumb code; the target preserves R4-R11 and SP, the private frame and continuation code.',
                'Loaded input words carry no tracked private-frame or saved-return provenance; ordinary memory noninterference remains a premise.'])
        adapter_shape = 'framed-two-output'
        getter_reads = [4, 0]
    else:
        adapter_data = rom[adapter_address-match.ROM_BASE:adapter_address-match.ROM_BASE+22]
        refinement = owner.refine(adapter_data, adapter_address, mapping)
        ai, ae, ab, ac, aw = graph.graph(adapter_data, adapter_address, refinement)
        require(not ab and not aw and len(ac) == 2 and adapter_address+4 in ac,
                'literal closure requires its complete two-call scalar adapter')
        getter = ac[adapter_address+4]
        adapter_proof = adapter.verify(adapter_address, getter, rom, mapping, index, selector=adapter.SELECTOR)
        adapter_shape = 'scalar-inventory'
        getter_reads = [0]
    for thunk_name in (selected_name, '_call_via_r2'):
        target = thunk.ALIASES[thunk_name]
        tdata = rom[target-match.ROM_BASE:target-match.ROM_BASE+2]
        owner.validate_span(tdata, target, rom, mapping, index)
        require(span_record(target, target+2, index_entries, rows, rom)['instrs'] == 1 and not any(
                int(row['rom'], 16) < target+4 and int(row['end'], 16) > target+2 for row in index_entries),
                'literal closure call thunk requires separate indexed padding')
    canonical, = thunk.dependencies([selected_name], rom)
    adapter_canonical, = thunk.dependencies(['_call_via_r2'], rom)
    addresses = [address, iterator, adapter_address, getter, callback, selected, thunk.ALIASES['_call_via_r2']]
    require(len(set(addresses)) == len(addresses), 'literal closure requires distinct complete dependency owners')
    if form['state'] is None:
        require(callback not in STATE_CALLBACKS, 'pinned state callback requires the private-state root form')
        end = next((row['end'] for row in index_entries if int(row['rom'], 16) == callback), None)
        require(end is not None, 'literal closure callback requires its complete indexed span')
        entry = span_record(callback, int(end, 16), index_entries, rows, rom)
        cbody = rom[callback-match.ROM_BASE:int(entry['end'], 16)-match.ROM_BASE]
        callback_record = dict(address=callback, end=int(entry['end'], 16), instructions=entry['instrs'],
            body_sha256=sha(cbody), effects='opaque',
            arguments=['word loaded by getter from each node', form['word0']],
            private_provenance_passed=False)
    else:
        require(callback in STATE_CALLBACKS and adapter_data[-4:] == bytes.fromhex('02bc0847'),
                'private state requires a pinned state callback and adapter return through R1')
        require(adapter_proof['descriptor_register'] == 4,
                'private state requires the adapter descriptor in R4')
        count = STATE_CALLBACKS[callback][0]
        size = len(bytes.fromhex(STATE_CALLBACKS[callback][1]))
        cbody, _, _, ccalls, cpartition = complete(callback, size, count, rom, mapping, index)
        require(not ccalls and not cpartition['literal_and_table_bytes'], 'state callback must be a code-only leaf')
        callback_record = dict(state_callback_effects(cbody, callback), partition=cpartition,
            arguments=['word loaded by getter from each node', form['word0']],
            private_provenance_passed=True,
            alias_erasure='The adapter restores R4 and overwrites R1 with its saved return before BX R1; the iterator overwrites R0/R1 before any later callback. No private state address is stored outside the root\'s own expired frame.')
    worker_frame = frame.prove_frame(wi, we, iterator, {}, wc, call_preservation={site: PRESERVED for site in wc})
    context = _LiteralContextRead(rom, mapping, address+form['call'], iterator, name)
    verified = match.verify_leaf_instructions(data, address, True, calls, buffer_proof=context)
    require({item.address for item in verified} == set(ins) and context.observed,
            'literal closure requires exact native root and descriptor access evidence')
    stores = ([dict(offset=form['state'], source='constant zero'), dict(offset=form['state']+4, source='root entry R1'),
               dict(offset=form['descriptor'], source='address of private state'),
               dict(offset=form['descriptor']+4, source='typed callback literal')]
              if form['state'] is not None else
              [dict(offset=form['descriptor'], source=form['word0']),
               dict(offset=form['descriptor']+4, source='typed callback literal')])
    lifted = 'Loaded input words carry no tracked private-frame or saved-return provenance; ordinary memory noninterference remains a premise.'
    require(lifted in adapter_proof['explicit_conditions'], 'literal closure adapter premise differs')
    conditions = [condition for condition in adapter_proof['explicit_conditions']
                  if form['state'] is None or condition != lifted] + ([] if form['state'] is None else [
        'The getter word carries no tracked private-frame or saved-return provenance. Descriptor word zero is the private state address: the exact adapter loads it and passes it to the pinned callback in R1 without dereferencing it. The no-private-provenance adapter premise is replaced for that word by the interpreted callback effects, not asserted satisfied; ordinary memory noninterference remains a premise.']) + [
        'Every reached list/node load is aligned, live, initialized and physically readable at its recorded width; null is tested only as a word value.',
        'All private root, iterator, adapter and callback frames and continuation code satisfy compatible returning ABI validity and noninterference; external values carry no private-frame/saved-return provenance.']
    if form['state'] is None:
        conditions.append('The typed literal callback is compatible returning Thumb code preserving R4-R11 and SP, the private frames and continuation code; its identity is pinned but its effects are not interpreted.')
    else:
        conditions += [
            'The private state is reachable only through descriptor word zero; the iterator, getter and adapter pass it to the pinned callback without dereferencing it, and no ordinary call or external access reads or writes the state or descriptor.',
            'Each callback store through the state word-4 cursor is aligned, live and writable, and does not overlap the private state, descriptor, any active frame, saved return, reached list/node word or code. The incoming entry R1 cursor carries no private-frame provenance.']
    proof = dict(schema=SCHEMA, instructions=len(ins),
        calls=[[form['call'], f'func_{iterator:08X}']], runtime_calls=[], partition=partition,
        literal_callback_closure=dict(schema=SELECTOR, form=name,
            root_frame=dict(saved=['entry LR'], local_bytes=form['frame_bytes'],
                            established_by='exact byte template, not the frame prover',
                            template_sha256=sha(form['code'].encode())),
            root_descriptor=dict(offset=form['descriptor'], width=8, initialized_words=stores,
                actual_buffer_checks=context.observed),
            private_state=None if form['state'] is None else dict(offset=form['state'], width=8,
                initialized=[dict(offset=0, value=0), dict(offset=4, entry_register=1)],
                result=dict(site=address+form['call']+4, offset=0, width=4, register=0,
                    relation='zero plus one per returning callback invocation, modulo 2**32')),
            callback=callback_record,
            iterator=dict(address=iterator, end=iterator+shape['size'], instructions=shape['count'],
                body_sha256=sha(worker), pinned_sha256=shape['sha256'], kind=shape['kind'],
                adapter_register=shape['adapter_register'], descriptor_register=shape['descriptor_register'],
                call_site=iterator+shape['call'], partition=wp, frame=worker_frame, thunk=canonical,
                reads=[dict(base='list object' if base == 'list' else 'current node', offset=offset, width=4)
                       for base, offset in shape['reads']], stores=[],
                loop_invariant=shape['loop_invariant'],
                iteration_bound_assumed=False, termination_proved=False),
            adapter_shape=adapter_shape,
            adapter=adapter_proof,
            adapter_thunk=adapter_canonical,
            external_read_obligations=[dict(base='root entry R0' if name != 'entry-object' else 'word at root entry R0+128',
                    offset=source.operands[1].mem.disp, width=4)] +
                [dict(base='loaded list object' if base == 'list' else 'each node reached by the iterator',
                      offset=offset, width=4) for base, offset in shape['reads']] +
                [dict(base='each nonnull current node passed to getter', offset=offset, width=4) for offset in getter_reads] +
                ([dict(base='root entry R0', offset=128, width=4)] if name == 'entry-object' else []),
            outward_expired_aliases=[dict(register=2, origin='root descriptor on the empty-list path',
                accessible_after_return=False, observed_by_root_continuation=False)]
                if shape['descriptor_in_r2_on_empty_path'] else [],
            explicit_conditions=conditions,
            source_sha256={**{Path(module.__file__).name: sha(Path(module.__file__).read_bytes())
                for module in (match, owner, graph, thunk, frame, adapter)},
                Path(__file__).name: sha(Path(__file__).read_bytes())},
            physical_memory_permission=False, numeric_nonalias_proved=False,
            actual_callback_ABI_established=False, termination_proved=False))
    return proof
