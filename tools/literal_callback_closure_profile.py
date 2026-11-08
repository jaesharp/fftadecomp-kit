"""Initialized local descriptors whose callback word is a typed function literal.

Three exact root forms reach the complete read-only list iterator and two-word
scalar adapter admitted by conditional-two-word-callback-closure-v1. Descriptor
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
ITERATOR = 0x080C7CC0
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
    require(data == body and calls == {address+form['call']: ITERATOR} and
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
    worker, wi, we, wc, wp = complete(ITERATOR, 34, 16, rom, mapping, index)
    selected = thunk.ALIASES['_call_via_r6']
    if worker[:20] != bytes.fromhex('70b50e1c151c446800e0a468002c05d0201c291c') or \
            worker[24:] != bytes.fromhex('0028f6d170bc01bc0047') or wc != {ITERATOR+20: selected} or \
            wp['literal_and_table_bytes'] or wp['alignment_bytes']:
        raise ValueError('literal closure requires the complete read-only node iterator')
    adapter_data = rom[adapter_address-match.ROM_BASE:adapter_address-match.ROM_BASE+22]
    refinement = owner.refine(adapter_data, adapter_address, mapping)
    ai, ae, ab, ac, aw = graph.graph(adapter_data, adapter_address, refinement)
    require(not ab and not aw and len(ac) == 2 and adapter_address+4 in ac,
            'literal closure requires its complete two-call scalar adapter')
    getter = ac[adapter_address+4]
    adapter_proof = adapter.verify(adapter_address, getter, rom, mapping, index, selector=adapter.SELECTOR)
    tdata = rom[selected-match.ROM_BASE:selected-match.ROM_BASE+2]
    owner.validate_span(tdata, selected, rom, mapping, index)
    index_entries, rows = indices(mapping, index)
    require(span_record(selected, selected+2, index_entries, rows, rom)['instrs'] == 1 and not any(
            int(row['rom'], 16) < selected+4 and int(row['end'], 16) > selected+2 for row in index_entries),
            'literal closure R6 thunk requires separate indexed padding')
    canonical, = thunk.dependencies(['_call_via_r6'], rom)
    addresses = [address, ITERATOR, adapter_address, getter, callback, selected, thunk.ALIASES['_call_via_r2']]
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
    worker_frame = frame.prove_frame(wi, we, ITERATOR, {}, wc, call_preservation={site: PRESERVED for site in wc})
    context = _LiteralContextRead(rom, mapping, address+form['call'], ITERATOR, name)
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
        calls=[[form['call'], f'func_{ITERATOR:08X}']], runtime_calls=[], partition=partition,
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
            iterator=dict(address=ITERATOR, end=ITERATOR+34, instructions=16, body_sha256=sha(worker),
                partition=wp, frame=worker_frame, thunk=canonical,
                loop_invariant='R6 is the exact adapter Thumb pointer; R5 is the original initialized descriptor; R4 is null or the current ordinary node. Each returning adapter preserves R4-R11/SP. Only node+8 advances the loop; callback R0 selects continuation.',
                iteration_bound_assumed=False, termination_proved=False),
            adapter=adapter_proof,
            external_read_obligations=[dict(base='root entry R0' if name != 'entry-object' else 'word at root entry R0+128',
                    offset=source.operands[1].mem.disp, width=4),
                dict(base='loaded list object', offset=4, width=4),
                dict(base='each nonnull current node passed to getter', offset=0, width=4),
                dict(base='each current node followed after nonzero callback result', offset=8, width=4)] +
                ([dict(base='root entry R0', offset=128, width=4)] if name == 'entry-object' else []),
            outward_expired_aliases=[dict(register=2, origin='root descriptor on the empty-list path',
                accessible_after_return=False, observed_by_root_continuation=False)],
            explicit_conditions=conditions,
            source_sha256={**{Path(module.__file__).name: sha(Path(module.__file__).read_bytes())
                for module in (match, owner, graph, thunk, frame, adapter)},
                Path(__file__).name: sha(Path(__file__).read_bytes())},
            physical_memory_permission=False, numeric_nonalias_proved=False,
            actual_callback_ABI_established=False, termination_proved=False))
    return proof
