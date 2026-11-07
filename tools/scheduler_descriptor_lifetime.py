"""Conditional scheduler descriptor transfer and return-frame kernel.

This is a cutpoint relation, not scheduler admission. Retained full-owner
structural authorities supply the partition. The allocator/zero/list prefix
must separately establish the stated cutpoint, and an ordinary callback must
satisfy the explicit continuation/frame conditions. No booleans can discharge
those conditions here. All bytes, including opaque bytes and pointer bytes,
remain visible to the callback interface. Source initialization, permissions,
installed code, termination, and nonescape are not consequences of copying.
"""
from dataclasses import dataclass
import hashlib
import json

import descriptor_frame_shape_prerequisite as frames
import descriptor_partial_word_prerequisite as partial

SELECTOR = 'conditional-scheduler-descriptor-lifetime-v1'
Word = partial.Word
LOCAL = (False, False, True)
SAVED = (False, True, False)
MAX_WORDS = 256

# Closed instruction shapes, with BL destinations and literal values bound
# independently. No ROM address is accepted merely because it is on a list.
WRAPPER_HEAD = bytes.fromhex(
    '70b5 4646 40b4 81b0 061c 0c1c 9046 2404 240c 094d '
    '2868 0093 311c 221c 4346')
WRAPPER_TAIL = bytes.fromhex(
    '2968 8989 0122 5140 c182 01b0 08bc 9846 70bc 02bc 0847')
CALLEE_HEAD = bytes.fromhex(
    'f0b5 4f46 4646 c0b4 87b0 051c 8846 141c 9946 0e9e '
    '2404 e020 4003 2418 240c 2868 211c')
COPY = bytes.fromhex('6946 4846 38c8 38c1 38c8 38c1 0068 0860 6946 0020 0880')
CALL_SETUP = bytes.fromhex('3b68 381c')
CALLEE_RETURN = bytes.fromhex('8020 4000 b882 381c 07b0 18bc 9846 a146 f0bc 02bc 0847')


def _digest(data):
    return hashlib.sha256(data).hexdigest()


def _authority(data, address, receipt, expected_sha, role):
    if type(data) is not bytes or type(address) is not int or address % 4 or \
            not 0 <= address < address+len(data) <= 0x100000000 or \
            type(receipt) is not bytes or type(expected_sha) is not str or \
            len(expected_sha) != 64 or _digest(receipt) != expected_sha:
        raise ValueError('immutable body and exact retained authority pin required')
    try:
        envelope = json.loads(receipt)
        evidence = envelope['evidence']
        record = evidence['owner' if role == 'wrapper' else 'caller']
        required_schema = ('conditional-thumb-saved-alias-obligations-v1' if role == 'wrapper'
                           else 'complete-thumb-rom-zero-call-interface-v1')
        if evidence.get('schema') != required_schema:
            raise ValueError('retained authority producer schema differs')
        if record['address'] != address or record['bytes'] != len(data) or \
                record['sha256'] != _digest(data):
            raise ValueError('retained authority body identity differs')
        partition = record['partition']
        instructions, edges, calls = frames.decode_partition(data, address, partition)
        if type(record['instructions']) is not int or record['instructions'] != len(instructions):
            raise ValueError('retained authority complete instruction count differs')
    except (KeyError, TypeError, json.JSONDecodeError) as error:
        raise ValueError('malformed retained full-owner authority') from error
    # Receipt trust is an external premise; matching its hash does not itself
    # authenticate the producer or its source/runtime context.
    return record, instructions, edges, calls


def _closed_reachable(instructions, edges, entry, terminal):
    pending = [entry]
    seen = set()
    while pending:
        site = pending.pop()
        if site in seen:
            continue
        seen.add(site)
        pending.extend(edges[site])
    if seen != set(instructions) or {site for site in instructions if not edges[site]} != {terminal}:
        raise ValueError('conditional kernel requires complete reachable CFG and one return')


@dataclass(frozen=True)
class Layout:
    wrapper: int
    callee: int
    copy_site: int
    callback_site: int
    callback_thunk: int
    allocator_site: int
    allocator_target: int
    scheduler_point: int
    prefix_calls: tuple
    body_pins: tuple
    authority_pins: tuple


def bind_layout(wrapper_data, wrapper_address, wrapper_receipt, wrapper_sha,
                callee_data, callee_address, callee_receipt, callee_sha, *, selector):
    """Bind the new relation to retained partitions without old producer replay.

The full prefix CFG remains an explicit effect/termination obligation. It
cannot jump into the copy, callback setup, or epilogue interior. Every normal
return must pass the exact copy and synchronous call. This never validates
fresh ROM/index context; Primary must supply that independent binding.
"""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('scheduler lifetime kernel requires explicit selector')
    wr, wi, we, wc = _authority(wrapper_data, wrapper_address, wrapper_receipt, wrapper_sha, 'wrapper')
    cr, ci, ce, cc = _authority(callee_data, callee_address, callee_receipt, callee_sha, 'callee')
    w, c = wrapper_address, callee_address
    if len(wrapper_data) != 60 or wrapper_data[:30] != WRAPPER_HEAD or \
            wrapper_data[34:56] != WRAPPER_TAIL or wc != {w+30: c} or len(wi) != 27:
        raise ValueError('wrapper instruction, call, or complete extent shape differs')
    words = wr['partition'].get('words', ())
    if len(words) != 1 or words[0]['address'] != w+56 or \
            words[0].get('load_sites') != [w+18] or words[0]['value'] % 4:
        raise ValueError('wrapper scheduler literal binding differs')
    _closed_reachable(wi, we, w, w+54)
    # The suffix is relative to the complete end, not a hard-coded address.
    suffix = COPY + CALL_SETUP
    copy = c+len(callee_data)-len(suffix)-4-len(CALLEE_RETURN)
    call = copy+len(suffix)
    if len(callee_data) < len(CALLEE_HEAD)+len(suffix)+4+len(CALLEE_RETURN) or \
            callee_data[:len(CALLEE_HEAD)] != CALLEE_HEAD or \
            callee_data[copy-c:call-c] != suffix or \
            callee_data[call-c+4:] != CALLEE_RETURN or call not in cc or c+34 not in cc:
        raise ValueError('callee frame, size arithmetic, copy, callback, or return shape differs')
    if set(site for site in cc if site >= copy) != {call}:
        raise ValueError('callee suffix contains an unmodeled call')
    _closed_reachable(ci, ce, c, c+len(callee_data)-2)
    for site, targets in ce.items():
        for target in targets:
            if site < copy and target >= copy and target != copy:
                raise ValueError('prefix bypasses descriptor copy or enters suffix interior')
            if site >= c+34 and target < c+34:
                raise ValueError('prefix reenters prologue and changes saved-frame meaning')
    tail_sites = set(range(copy, call+2, 2)) | set(range(call+4, c+len(callee_data), 2))
    tail_sites.discard(call+2)
    if set(site for site in ci if site >= copy) != tail_sites:
        raise ValueError('suffix instruction boundaries differ')
    for site in tail_sites:
        expected = () if site == c+len(callee_data)-2 else (site+ci[site].size,)
        if ce[site] != expected:
            raise ValueError('suffix is not an uninterrupted synchronous continuation')
    return Layout(w, c, copy, call, cc[call], c+34, cc[c+34], words[0]['value'],
                  tuple(sorted((site, target) for site, target in cc.items() if site < copy)),
                  ((w, len(wrapper_data), _digest(wrapper_data)),
                   (c, len(callee_data), _digest(callee_data))), (wrapper_sha, callee_sha))


def _word_record(word):
    return [list(atom) for atom in word.bytes]


def _words_record(words):
    return {str(offset): _word_record(value) for offset, value in sorted(words.items())}


@dataclass(frozen=True)
class Transfer:
    """Immutable conditional transfer; snapshots do not extend object lifetime."""
    layout: Layout
    entry_sp: int
    source: int
    size_word: int
    allocation_count: int
    callback_words: tuple
    callback_registers: tuple
    returned_registers: tuple
    caller_words: tuple
    pre_callback_private_snapshot: tuple
    reads: tuple
    writes: tuple
    protected: tuple
    saved: tuple

    @property
    def copy_base(self):
        return self.entry_sp-80

    def scalar_at_callback(self, offset, width, *, signed=False):
        if type(offset) is not int or type(width) is not int or width not in (1, 2, 4) or \
                not 0 <= offset < offset+width <= 28 or offset % width:
            raise ValueError('callback scalar slice outside aligned descriptor')
        return self.callback_words[offset//4].read_scalar(offset % 4, width, signed=signed)

    def scalar_after_return(self, offset, width):
        raise ValueError('descriptor copy lifetime ended before wrapper return')

    def report(self):
        regs = dict(self.callback_registers)
        return dict(schema=SELECTOR, relation='copy cutpoint through conditional callback and wrapper return',
            bodies=self.layout.body_pins, retained_authorities=self.layout.authority_pins,
            frame=dict(wrapper_entry_SP=self.entry_sp, wrapper_private=[self.entry_sp-24,self.entry_sp],
                callee_private=[self.entry_sp-80,self.entry_sp-24],
                descriptor_copy=[self.copy_base,self.copy_base+28], source=[self.source,self.source+28],
                saved_words=_words_record(dict(self.saved)), protected_words=list(self.protected)),
            size=dict(incoming_u32=self.size_word, wrapper_u16=self.size_word & 65535,
                allocator_u16=self.allocation_count,
                derivation='((incoming_u32 & 65535) + 28) & 65535',
                minimum_header_extent_numeric=self.allocation_count >= 24,
                payload_extent_numeric=max(0,self.allocation_count-24), object_permission=False),
            copy=dict(reads=list(self.reads), writes=list(self.writes), bytes=28,
                overwritten_bytes=[0,1], words=[_word_record(v) for v in self.callback_words],
                initialized_source_bytes_proved=False, C_copy_permission=False),
            callback=dict(site=self.layout.callback_site, thunk=self.layout.callback_thunk,
                required_thunk='complete authenticated Thumb BX R3',
                registers=_words_record(regs),
                explicit_local_aliases={'R1':self.copy_base,'R9':self.source},
                all_registers_exposed=True, all_descriptor_bytes_exposed=True,
                source_descriptor_pointer_is_still_live=True,
                behavior='uninterpreted ordinary call; effects and termination remain open'),
            conditional_external_accesses=[
                dict(phase='callback setup', operation='read32', base='allocation', offset=0,
                     required_value='original callback word'),
                dict(phase='callee continuation', operation='write16', base='allocation', offset=20,value=256),
                dict(phase='wrapper continuation', operation='read32',base='fixed numeric point',
                     point=self.layout.scheduler_point, required_value='post-callback scheduler pointer'),
                dict(phase='wrapper continuation',operation='read16',base='post-callback scheduler pointer',offset=12),
                dict(phase='wrapper continuation',operation='write16',base='allocation',offset=22,
                     value='post-callback read16 xor 1')],
            conditional_return=dict(registers=_words_record(dict(self.returned_registers)),
                caller_words=_words_record(dict(self.caller_words)), SP=self.entry_sp,
                restored_from_actual_saves=[4,5,6,7,8,9],
                unknown_ordinary_effect_registers=[10,11,12], flags='unknown',
                R1='outer entry LR', R2=1, R3='outer entry R8', R0='allocation result'),
            lifetime=dict(copy_dead_on_callee_add_SP=True, wrapper_private_dead_on_wrapper_return=True,
                caller_source_live_only_until_caller_deallocation=True,
                dead_memory_erased=False,
                retired_local_contents='unknown after ordinary callback; no current value assertion',
                historical_pre_callback_private_words=_words_record(dict(self.pre_callback_private_snapshot)),
                possible_escaped_aliases=['callback-retained R1 copy pointer',
                    'callback-retained R9 source pointer', 'pointer-valued copied bytes',
                    'callback outputs or ambient registers, including R10/R11/R12',
                    'unknown prefix/callback external memory effects'],
                nonescape_proved=False, expired_aliases_may_be_observed=False),
            obligations=[
                dict(id='authority-and-context', proved=False, scope='retained complete-owner receipts are trusted; '
                     'bind complete bodies, current ROM/index, canonical thunk and source/runtime pins independently'),
                dict(id='physical-stack', proved=False, scope='entry SP and all live private/caller ranges '
                     'are aligned, nonwrapping, physically accessible; saved words keep exact origins'),
                dict(id='prefix-reaching-state', proved=False, scope='allocator/zero/list prefix reaches copy '
                     'normally with exact SP=wrapper_entry_SP-80, R7=allocation, R9=source, '
                     'R2=allocation+24; source and all saved/caller '
                     'bytes unchanged; allocation callback slot equals original callback'),
                dict(id='prefix-effects', proved=False, sites=self.layout.prefix_calls,
                     scope='full allocator, installed zero and list read/write/termination effects; '
                     'no purity, allocator success, object separation or installed identity is implied'),
                dict(id='zero-count', proved=False, count=self.allocation_count,
                     scope='R4 numeric count must survive the allocator and reach the installed-zero call; '
                     'zero effect must cover this exact count; a different retained count is insufficient'),
                dict(id='representation-access', proved=False, scope='28 source bytes may be read and copied '
                     'as machine representations, including unproved bytes; no C initialization theorem'),
                dict(id='callback-continuation', proved=False, scope='actual target via allocation slot and '
                     'BX R3 is compatible, returns normally to continuation with exact SP, preserves R7 '
                     'allocation and every saved/caller word; its other effects remain visible and unproved'),
                dict(id='external-accesses', proved=False, scope='each listed read/write has valid provenance '
                     'and access permission, does not wrap or overlap protected/caller state, and obeys '
                     'ordered values; scheduler pointer is freshly loaded after callback'),
                dict(id='lifetime-and-escape', proved=False, scope='actual prefix/callback effects must '
                     'account for every possible alias and reject later observation of either retired frame '
                     'or eventually retired caller descriptor; copying is not nonescape')],
            conditional_copy_and_return_relation=True, prefix_effects_closed=False,
            callback_effects_closed=False, full_scheduler_effects_closed=False,
            actual_reaching_state_proved=False, physical_permissions_proved=False,
            allocator_or_installed_image_proved=False, unconditional_termination=False,
            source_or_ELF_admission=False, native_admission=False)


def derive(layout, caller_stack, caller_words, entry_registers, *, protected=(), selector):
    """Derive every copy byte and saved origin under named, undischarged premises.

Offsets use the enclosing caller's entry-SP origin. The wrapper entry SP is
minus four times caller_stack length. Entry R2 must be a complete local pointer;
entry R1 must be a concrete u32 for this bounded numeric specialization. An
unproved payload may be copied but cannot become a value or pointer theorem.
"""
    if type(selector) is not str or selector != SELECTOR or type(layout) is not Layout:
        raise ValueError('explicit selector and bound scheduler layout required')
    if type(caller_stack) not in (tuple,list) or not 7 <= len(caller_stack) <= MAX_WORDS-20 or any(
            type(row) not in (tuple,list) or len(row) != 3 or any(type(bit) is not bool for bit in row)
            for row in caller_stack):
        raise ValueError('bounded classified caller frame required')
    if type(entry_registers) is not dict or set(entry_registers) != set(range(13)) | {14} or any(
            type(k) is not int or type(v) is not Word for k,v in entry_registers.items()):
        raise ValueError('all incoming register origins R0..R12 and LR are required')
    e = -4*len(caller_stack)
    if type(caller_words) is not dict or any(type(k) is not int or k % 4 or not e <= k <= -4 or
            type(v) is not Word for k,v in caller_words.items()):
        raise ValueError('caller word facts must fit the complete live frame')
    if type(protected) not in (tuple,list) or any(type(k) is not int or k % 4 or not e <= k <= -4
                                               for k in protected):
        raise ValueError('protected caller words must be live aligned slots')
    source = entry_registers[2].require_pointer()
    if source % 4 or not e <= source <= -28:
        raise ValueError('source descriptor does not fit live caller frame')
    for offset in range(source,source+28,4):
        if tuple(caller_stack[(offset-e)//4]) != LOCAL or offset in protected:
            raise ValueError('source descriptor overlaps saved/protected caller state')
    size = entry_registers[1].known_value()
    if size is None:
        raise ValueError('allocation count specialization requires concrete incoming u32')
    for value in (*entry_registers.values(),*caller_words.values()):
        p = value.pointer_offset()
        if p is not None and not e <= p <= 0:
            raise ValueError('incoming local pointer origin is outside live caller frame')
    # Origin spelling is relational identity, not an incidental debug label.
    # Fresh existential words must never unify with supplied arbitrary bytes.
    input_origins = {atom[1] for value in (*entry_registers.values(),*caller_words.values())
                     for atom in value.bytes if atom[0] == 'unproved'}
    reserved = ({f'caller-word:{offset}' for offset in range(e,0,4)} |
                {f'prefix-register:{reg}' for reg in range(13)} |
                {f'callback-output:{reg}' for reg in range(13)} |
                {'allocation','allocation-plus-24','prefix-LR','callback-output:LR'})
    namespace = ''
    generation = 0
    while {namespace+name for name in reserved} & input_origins:
        generation += 1
        namespace = f'scheduler-{generation}:'
    def unknown(name):
        return Word.unproved(namespace+name)
    count = ((size & 65535)+28) & 65535
    caller = {offset:unknown(f'caller-word:{offset}') for offset in range(e,0,4)}
    caller.update(caller_words)
    r = entry_registers
    # Exact architectural PUSH order. These words are conditional invariants
    # across all unknown prefix/callback effects, never inferred ABI promises.
    saved = {e-16:r[4],e-12:r[5],e-8:r[6],e-4:r[14],e-20:r[8],
             e-44:Word.constant(size & 65535), e-40:Word.constant(layout.scheduler_point),
             e-36:r[0], e-32:r[7], e-28:Word.constant((layout.wrapper+34)|1),
             e-52:r[2], e-48:r[9]}
    stack = [LOCAL]*7+[SAVED]*7+[LOCAL]+[SAVED]*5+list(caller_stack)
    words = dict(caller)
    words.update(saved)
    words[e-24] = r[3]
    protected_all = tuple(sorted(set(protected) | set(saved)))
    registers = {i:unknown(f'prefix-register:{i}') for i in range(13)}
    registers.update({2:unknown('allocation-plus-24'),7:unknown('allocation'),
                      9:r[2],13:Word.pointer(e-80),14:unknown('prefix-LR')})
    transfer = partial.replay(COPY, registers, stack, words, protected=protected_all)
    copied = tuple(transfer['words'][e-80+4*i] for i in range(7))
    callback = dict(transfer['registers'])
    callback.update({0:unknown('allocation'),3:r[0],
                     14:Word.constant((layout.callback_site+4)|1)})
    # R7 survival is an explicit callback premise. R4..R9 come from actual
    # saved slots; R10..R12 have no such justification and retain alias risk.
    returned = {i:unknown(f'callback-output:{i}') for i in range(13)}
    returned.update({0:unknown('allocation'),1:r[14],2:Word.constant(1),3:r[8],
                     4:r[4],5:r[5],6:r[6],7:r[7],8:r[8],9:r[9],13:Word.pointer(e),
                     14:unknown('callback-output:LR')})
    retired = {offset:value for offset,value in transfer['words'].items() if offset < e}
    return Transfer(layout,e,source,size,count,copied,tuple(sorted(callback.items())),
                    tuple(sorted(returned.items())),tuple(sorted(caller.items())),
                    tuple(sorted(retired.items())),tuple(transfer['reads']),tuple(transfer['writes']),
                    protected_all,tuple(sorted(saved.items())))
