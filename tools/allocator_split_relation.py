"""Closed conditional allocator search/remove/split/insert composition.

One relative byte arena preserves ordered field effects. The complete potential
stack envelope is excluded from heap-field accesses, including after a helper
returns: old heap bytes cannot reappear underneath opaque saved registers.
This checked, conservative guard supplies no actual heap/SP separation.
"""
from dataclasses import dataclass
import hashlib
import json

import allocator_search_relation as search
import allocator_remove_relation as remove
import allocator_insert_relation as insert

SELECTOR = 'conditional-allocator-split-zero12-frame-v1'
# Frozen count12 certificate, independently produced once in Primary3486.
# This is receipt authentication, not an accepted-owner-address whitelist.
ZERO12_SHA256 = '6614130b4ab577b71f084c8eb86da1695906eef9c27f74c9858858f450042593'
HEAD = bytes.fromhex('f0b5 4746 80b4 82b0 8046 0904 0d0c 01ab 291c 6a46')
AFTER_SEARCH = bytes.fromhex('019c 002c 01d1 0020 6de0 4046 211c')
AFTER_REMOVE = bytes.fromhex('''
a179 e079 0002 0843 401b 0004 070c e81c ff26 a071 000a e071 6c20 2071
6120 6071 032f 4bd9 a179 e079 0002 0843 8000 2518 1a48 0268 281c 0c21
''')
AFTER_ZERO = bytes.fromhex('''
7020 2871 7320 6871 f91e 0904 080c 3040 a871 090e e971 4046 211a 8903
090c 081c 3040 2870 090a 6970 a078 e178 0902 0143 081c 3040 a870 090a
e970 4146 681a 8003 000c 0640 a670 000a e070 a978 e878 0002 0843 0028
05d0 8000 4246 1118 02e0
''')
AFTER_POOL = bytes.fromhex('0021 0029 06d0 4246 a81a 8003 000c 0870 000a 4870 4046 291c')
TAIL = bytes.fromhex('''
0ae0 a079 e179 0902 0143 7918 0904 080c 3040 a071 090e e171 201c 02b0
08bc 9846 f0bc 02bc 0847
''')


@dataclass(frozen=True)
class Layout:
    address: int
    sha256: str
    insertion: insert.Layout
    thunk: int
    pointer_literal: int


def _encoded(address, insertion, thunk, pointer_literal):
    return (HEAD + remove._bl(address+20, insertion.search.address) + AFTER_SEARCH +
            remove._bl(address+38, insertion.median.removal) + AFTER_REMOVE +
            remove._bl(address+98, thunk) + AFTER_ZERO + pointer_literal.to_bytes(4, 'little') +
            AFTER_POOL + remove._bl(address+224, insertion.address) + TAIL)


def _identity(address, insertion, thunk, pointer_literal):
    if type(insertion) is not insert.Layout:
        raise ValueError('retained complete insertion layout required')
    insert._validate_dependencies(insertion.search, insertion.median)
    if any(type(a) is not int or a % 2 or not 0 <= a < 2**32 for a in (address, insertion.address, thunk)) or \
            address % 4 or address+266 > 2**32 or insertion.address+150 > 2**32 or thunk+2 > 2**32 or \
            type(pointer_literal) is not int or pointer_literal % 4 or not 0 <= pointer_literal <= 2**32-4:
        raise ValueError('aligned closed owners and literal-word address required')
    expected = (insert.HEAD + remove._bl(insertion.address+22, insertion.search.address) + insert.MIDDLE +
                remove._bl(insertion.address+138, insertion.median.median) + insert.TAIL)
    if insertion.sha256 != hashlib.sha256(expected).hexdigest():
        raise ValueError('retained insertion identity changed')
    spans = sorted([(address, address+266), (insertion.address, insertion.address+150),
                    (insertion.search.address, insertion.search.address+174),
                    (insertion.median.removal, insertion.median.removal+134),
                    (insertion.median.median, insertion.median.median+102), (thunk, thunk+2)])
    if any(a[1] > b[0] for a, b in zip(spans, spans[1:])):
        raise ValueError('complete owners overlap')
    return _encoded(address, insertion, thunk, pointer_literal)


def bind(data, address, instruction_count, insertion_layout, thunk_address, thunk_bytes, pointer_literal, *, selector):
    expected = _identity(address, insertion_layout, thunk_address, pointer_literal)
    if type(selector) is not str or selector != SELECTOR or type(data) is not bytes or data != expected or \
            type(instruction_count) is not int or instruction_count != 127 or \
            type(thunk_bytes) is not bytes or thunk_bytes != b'\x10\x47':
        raise ValueError('complete266-byte/127-instruction split shape, literal and R2 thunk required')
    return Layout(address, hashlib.sha256(data).hexdigest(), insertion_layout, thunk_address, pointer_literal)


class _Arena(insert._Memory):
    def __init__(self, cells, protected, envelope):
        super().__init__(cells, protected)
        self.envelope = envelope

    def field_guard(self, offset, width, site):
        lo, hi = self.envelope
        if offset < hi and offset+width > lo:
            raise remove._Boundary(site, 'heap field intersects reserved full frame envelope; stale saved bytes are not reused', offset)

    def read(self, offset, site, role):
        self.field_guard(offset, 1, site)
        return super().read(offset, site, role)

    def write(self, offset, value, site, role):
        self.field_guard(offset, 1, site)
        super().write(offset, value, site, role)


def _save_guard(memory, low, high, site):
    memory.guard(low, high-low, site, 'nested private save/output writes')


def _replay(memory, report, frame_origin):
    """Apply retained helper effects to the new arena, in their original order."""
    for event in report['memory_events']:
        op = event['operation']
        if op == 'write32':
            value = event['value']
            memory.store_pointer(event['coordinate'], None if value == 0 else value[1], event['site'], event['role'])
        elif op == 'read32':
            pointer = memory.load_pointer(event['coordinate'], event['site'], event['role'])
            value = 0 if pointer is None else ['base-plus', pointer]
            if value != event['value']:
                raise ValueError('retained pointer reload differs from new composed state')
        elif op == 'read8':
            if memory.read(event['coordinate'], event['site'], event['role']) != event['value']:
                raise ValueError('retained byte read differs from new composed state')
        elif op == 'write8':
            memory.write(event['coordinate'], event['value'], event['site'], event['role'])
        else:
            memory.events.append(dict(event, composition_frame_origin=frame_origin))


def _known(memory, *, removal=False):
    lo, hi = memory.envelope
    return {k: v for k, v in memory.cells.items() if type(v) is int and not lo <= k < hi and
            not any(a <= k < b for a, b in memory.protected) and (not removal or 0 <= k <= 0x40010)}


def _zero(memory, receipt, target, destination, sp, site):
    if type(receipt) is not bytes or hashlib.sha256(receipt).hexdigest() != ZERO12_SHA256:
        raise remove._Boundary(site, 'retained first count12 zero certificate absent or changed')
    rule = json.loads(receipt)
    if type(target) is not int or target != (rule['entry'] | 1):
        raise remove._Boundary(site, 'actual loaded R2 word lacks the retained installed-zero Thumb identity')
    _save_guard(memory, sp-4, sp, site)
    memory.field_guard(destination, 12, site)
    memory.guard(destination, 12, site, 'zero destination write')
    # Word alignment follows only under the explicit symbolic-base alignment
    # condition. It is not inferred from a literal RAM address or role name.
    case = rule['alignment_cases'][0]
    memory.events.append(dict(site=site, operation='conditional-installed-zero12',
        target=target, destination=destination, receipt_sha256=ZERO12_SHA256,
        private_save_coordinates=[sp-4, sp], alignment_case=0,
        installed_identity_proved=False, physical_permission_proved=False,
        preserved_registers=rule['preserved_registers']))
    for region, offset, width in case['writes']:
        if region != 'destination':
            continue
        for i in range(width):
            memory.cells[destination+offset+i] = 0
            memory.changed.add(destination+offset+i)
        memory.events.append(dict(site=site, operation='zero-write', coordinate=destination+offset,
                                  width=width, value=0, origin='retained count12 effect'))


def derive(layout, request_word, cells, entry_sp, *, selector, zero12_receipt=None,
           observed_zero_target=None, protected_spans=(), max_search_transitions=256, max_median_links=256):
    """Conditional whole relation; byte witnesses grant no physical permission.

The symbolic base must be word aligned and all base-plus operations nonwrapping.
Potential frame bytes [entrySP-72,entrySP) are never admitted as heap fields,
even after a nested return. Ordinary word outputs are handled separately.
"""
    if type(selector) is not str or selector != SELECTOR or type(layout) is not Layout:
        raise ValueError('explicit split selector and retained layout required')
    expected = _identity(layout.address, layout.insertion, layout.thunk, layout.pointer_literal)
    if layout.sha256 != hashlib.sha256(expected).hexdigest():
        raise ValueError('split layout identity changed')
    if type(request_word) is not int or not 0 <= request_word < 2**32 or \
            type(cells) is not dict or len(cells) > 4096 or any(type(k) is not int or not -(2**31) <= k < 2**31 or not insert._cell(v) for k, v in cells.items()) or \
            type(entry_sp) is not int or entry_sp % 4 or not -(2**31)+72 <= entry_sp <= 2**31-4 or \
            type(protected_spans) is not tuple or len(protected_spans) > 30 or any(type(p) is not tuple or len(p) != 2 or
                any(type(x) is not int for x in p) or not -(2**31) <= p[0] < p[1] <= 2**31 for p in protected_spans) or \
            type(max_search_transitions) is not int or not 1 <= max_search_transitions <= search.MAX_TRANSITIONS or \
            type(max_median_links) is not int or not 0 <= max_median_links <= remove.MAX_LINK_READS:
        raise ValueError('bounded byte/token state, aligned relative SP and retained budgets required')
    c = layout.address
    sp = entry_sp-32
    own_save = (entry_sp-24, entry_sp)
    memory = _Arena(cells, protected_spans, (entry_sp-72, entry_sp))
    summary = dict(request_word=request_word, request_u16=request_word & 65535)
    reports = {}
    boundary = None
    result_pointer = None
    try:
        _save_guard(memory, *own_save, c)
        memory.protected.append(own_save)
        memory.events.extend([
            dict(site=c, operation='save-entry-registers', registers=[4, 5, 6, 7, 14], stack_span=[-20, 0]),
            dict(site=c+4, operation='save-entry-R8-via-R7', stack_span=[-24, -20]),
            dict(site=c+6, operation='allocate-output-locals', coordinates=[sp, sp+8], initialization_granted=False)])
        _save_guard(memory, sp-20, sp, c+20)
        memory.events.append(dict(site=c+20, operation='ordinary-call', target=layout.insertion.search.address, SP=sp))
        try:
            sr = search.derive(layout.insertion.search, summary['request_u16'], _known(memory), sp, sp+4,
                               selector=search.SELECTOR, max_transitions=max_search_transitions)
        except ValueError as error:
            memory.store_pointer(sp+4, None, layout.insertion.search.address+14, 'initial selected zero')
            memory.store_pointer(sp, None, layout.insertion.search.address+16, 'initial predecessor zero')
            raise remove._Boundary(c+20, 'search witness refused: '+str(error)) from error
        reports['search'] = sr
        _replay(memory, sr, sp)
        if not sr['returns_under_witness']:
            raise remove._Boundary(c+20, 'search continuation refused: '+sr['status'])
        selected = memory.load_pointer(sp+4, c+24, 'selected output reload')
        summary['selected'] = selected
        if selected is not None:
            _save_guard(memory, sp-24, sp, c+38)
            memory.events.append(dict(site=c+38, operation='ordinary-call', target=layout.insertion.median.removal, SP=sp))
            rr = remove.derive_removal(layout.insertion.median, _known(memory, removal=True), selected,
                                       selector=remove.SELECTOR, max_link_reads=max_median_links)
            reports['removal'] = rr
            _replay(memory, rr, sp)
            if not rr['returns_under_witness']:
                raise remove._Boundary(c+38, 'removal continuation refused: '+rr['boundary']['reason'])
            old_size = memory.word(selected+6, (c+42, c+44), 'size reloaded after removal')
            remaining = (old_size-summary['request_u16']) & 65535
            memory.putword(selected+6, summary['request_u16']+3, (c+60, c+64), 'allocated size with header modulo16')
            memory.write(selected+4, 0x6c, c+68, 'allocated tag low')
            memory.write(selected+5, 0x61, c+72, 'allocated tag high')
            summary.update(size_after_removal=old_size, remaining_u16=remaining, subtraction_underflow=old_size < summary['request_u16'], split=remaining > 3)
            if remaining > 3:
                allocated_size = memory.word(selected+6, (c+78, c+80), 'allocated size reloaded for split address')
                new_block = selected+4*allocated_size
                summary['new_block'] = new_block
                memory.events.append(dict(site=c+90, operation='literal-address', pool=c+196, value=layout.pointer_literal))
                memory.events.append(dict(site=c+92, operation='conditional-ROM-pointer-read', address=layout.pointer_literal,
                                          value=observed_zero_target, origin_proved=False))
                _zero(memory, zero12_receipt, observed_zero_target, new_block, sp, c+98)
                memory.write(new_block+4, 0x70, c+104, 'split tag low')
                memory.write(new_block+5, 0x73, c+108, 'split tag high')
                memory.putword(new_block+6, remaining-3, (c+118, c+122), 'split remaining size')
                memory.putword(new_block, (selected//4) & 65535, (c+136, c+140), 'split physical predecessor')
                physical_next = memory.word(selected+2, (c+142, c+144), 'selected physical successor after zero')
                memory.putword(new_block+2, physical_next, (c+154, c+158), 'copy physical successor')
                new_index = (new_block//4) & 65535
                memory.putword(selected+2, new_index, (c+170, c+174), 'selected new physical successor')
                next_reload = memory.word(new_block+2, (c+176, c+178), 'split physical successor reload after selected writes')
                if next_reload:
                    memory.putword(4*next_reload, new_index, (c+214, c+218), 'physical successor predecessor')
                summary.update(split_index=new_index, physical_successor_reload=next_reload)
                _save_guard(memory, sp-40, sp, c+224)
                memory.events.append(dict(site=c+224, operation='ordinary-call', target=layout.insertion.address, SP=sp))
                ir = insert.derive(layout.insertion, memory.cells, new_block, sp, selector=insert.SELECTOR,
                                   protected_spans=tuple(memory.protected), max_search_transitions=max_search_transitions,
                                   max_median_links=max_median_links)
                reports['insertion'] = ir
                _replay(memory, ir, sp)
                if not ir['returns_under_witness']:
                    raise remove._Boundary(c+224, 'insertion continuation refused: '+ir['boundary']['reason'])
            else:
                size_reload = memory.word(selected+6, (c+230, c+232), 'no-split size reload')
                memory.putword(selected+6, size_reload+remaining, (c+246, c+250), 'no-split size including remainder')
            result_pointer = selected
        memory.events.extend([
            dict(site=c+254, operation='deallocate-output-locals', coordinates=[sp, sp+8], aliases_expire=True),
            dict(site=c+256, operation='restore-entry-R8-via-R3', stack_span=[-24, -20]),
            dict(site=c+260, operation='restore-entry-registers', registers=[4, 5, 6, 7], stack_span=[-20, -4]),
            dict(site=c+262, operation='restore-entry-LR-into-R1', stack_span=[-4, 0]),
            dict(site=c+264, operation='return-saved-entry-LR')])
    except remove._Boundary as error:
        boundary = error.report
    except ValueError as error:
        # A retained helper's bounded input policy remains a refusal, not a
        # reason to enlarge its budget or manufacture additional byte facts.
        boundary = dict(site=None, reason='retained helper input boundary: '+str(error), coordinate=None)
    return dict(schema=SELECTOR, returns_under_witness=boundary is None, boundary=boundary,
        result_pointer=(0 if result_pointer is None else ['base-plus', result_pointer]) if boundary is None else None,
        summary=summary, helpers=reports, memory_events=memory.events,
        changed_cells={str(k): memory.cells[k] for k in sorted(memory.changed)},
        frame=dict(entry_SP_coordinate=entry_sp, local_SP_coordinate=sp, own_private_bytes=32,
                   maximum_private_bytes=72, heap_field_exclusion=[entry_sp-72, entry_sp],
                   policy='checked conservative exclusion includes expired helper saves; no actual separation inferred'),
        conditional_preserved_registers=list(range(4, 13)) if boundary is None else None,
        SP_restored_under_conditions=boundary is None, output_local_lifetime='expired on return; ambient aliases remain unproved',
        actual_heap_or_SP_proved=False, actual_byte_origins_proved=False, physical_access_proved=False,
        allocation_extent_proved=False, installed_identity_proved=False, actual_frame_noninterference_proved=False,
        actual_termination_proved=False, source_or_native_admission=False,
        obligations=[dict(id=key, proved=False, text=text) for key, text in [
            ('actual-binding', 'Complete indexed bodies and supplied request, bytes, relative SP and zero-target word equal actual reaching state.'),
            ('physical-memory', 'The symbolic heap base is word aligned. Every base-plus coordinate is valid, nonwrapping ordinary RAM with required permissions; numeric offsets grant no allocation extent.'),
            ('complete-frame', 'All live saves, output locals and actual caller/source/ambient regions are correctly identified and accessible. The numeric72-byte exclusion is only a checked condition on supplied coordinates.'),
            ('installed-zero', 'When the split branch is taken, all retained zero12 installed-image, physical destination, private-save, valid continuation and noninterference premises hold.'),
            ('helper-contracts', 'Frozen search/removal/median/insertion saved-register and complete effect conditions apply to these new states; no ABI-only survival premise is used.'),
            ('no-interference', 'Executing code and byte witnesses stay stable except for listed writes; no interrupt/device/hidden callback changes state.'),
            ('lifetime', 'Output aliases expire with their frames. Returned pointer and ambient aliases require independent allocation lifetime and future-use justification.')]])
