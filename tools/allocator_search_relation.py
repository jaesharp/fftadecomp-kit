"""Conditional byte-field and output relation for a closed median list search.

Coordinates are relative to ONE symbolic base; role names never grant disjoint
objects. Concrete input bytes are conditional reaching-state witnesses, not
proof of actual initialization or permission. Pointer representations remain
opaque byte tokens because no numeric base address has been supplied.
"""
from dataclasses import dataclass
import hashlib

SELECTOR = 'conditional-byte-offset-median-search-v1'
MAX_CELLS = 4096
MAX_TRANSITIONS = 256
# Relocatable, complete 87-instruction shape. No absolute owner address is used
# as an admission shortcut. Branch encodings and every read/write are fixed.
SHAPE = bytes.fromhex('''
f0b5 051c 161c 1f1c 0904 0c0c 0020 3860 3060 a978 e878 0002 0843 0028
02d0 8000 2818 00e0 0020 031c 002b 3dd0 9979 d879 0002 0843 8442 28d8
0be0 9979 d879 0002 0843 8442 05d9 9179 d079 0002 0843 8442 28d9 1a1c
117a 507a 0002 0843 0028 02d0 8000 2818 00e0 0020 031c 002b e5d1 19e0
9979 d879 0002 0843 8442 05d9 9179 d079 0002 0843 8442 0dd9 131c 997a
 d87a 0002 0843 0028 02d0 8000 2818 00e0 0020 021c 002a e5d1 3360 3a60
f0bc 01bc 0047
''')


@dataclass(frozen=True)
class Layout:
    address: int
    sha256: str


def bind(data, address, instruction_count, *, selector):
    """Bind the complete shape; indexed ownership remains a caller obligation."""
    if type(selector) is not str or selector != SELECTOR or type(data) is not bytes or \
            type(address) is not int or address % 2 or not 0 <= address < address+len(data) <= 2**32 or \
            type(instruction_count) is not int or instruction_count != 87 or data != SHAPE:
        raise ValueError('exact complete 174-byte/87-instruction search shape required')
    return Layout(address, hashlib.sha256(data).hexdigest())


def derive(layout, request_word, cells, previous_output, selected_output, *,
           selector, max_transitions=MAX_TRANSITIONS):
    """Execute exact field/branch equations under an explicit byte witness.

Initial zero stores and all final pointer writes share the heap coordinate
space. Missing or opaque field bits cause refusal. A budget is a refusal
boundary, never a termination argument; deterministic cycles are reported only
under the same unchanged-memory premise as all reads.
"""
    if type(selector) is not str or selector != SELECTOR or type(layout) is not Layout or \
            type(request_word) is not int or not 0 <= request_word < 2**32 or \
            type(cells) is not dict or len(cells) > MAX_CELLS or \
            any(type(k) is not int or not -(2**31) <= k < 2**31 or type(v) is not int or not 0 <= v <= 255
                for k, v in cells.items()) or \
            any(type(v) is not int or v % 4 or not -(2**31) <= v <= 2**31-4
                for v in (previous_output, selected_output)) or \
            type(max_transitions) is not int or not 1 <= max_transitions <= MAX_TRANSITIONS:
        raise ValueError('bounded immutable byte witness and aligned symbolic output coordinates required')
    # Frozen Layout carries no opaque privilege. Recheck its defining content.
    if type(layout.address) is not int or layout.address % 2 or \
            not 0 <= layout.address <= 2**32-len(SHAPE) or layout.sha256 != hashlib.sha256(SHAPE).hexdigest():
        raise ValueError('search layout identity changed')
    memory = dict(cells)
    events = []
    path = []
    request = request_word & 0xffff
    c = layout.address
    last_low_byte = None

    def store(offset, pointer, site, role):
        # None is literal null. An offset0 pointer means the symbolic base and
        # remains distinct from null; no numeric pointer value is fabricated.
        values = [0]*4 if pointer is None else [('base-plus-byte', pointer, i) for i in range(4)]
        for i, value in enumerate(values):
            memory[offset+i] = value
        events.append(dict(site=c+site, operation='write32', coordinate=offset,
                           value=0 if pointer is None else ['base-plus', pointer], role=role))

    def u16(offset, low_site, high_site, role):
        nonlocal last_low_byte
        values = []
        for at, site in ((offset, low_site), (offset+1, high_site)):
            value = memory.get(at)
            if type(value) is not int or not 0 <= value <= 255:
                raise ValueError(f'field at coordinate{at} lacks justified concrete byte bits')
            events.append(dict(site=c+site, operation='read8', coordinate=at, value=value, role=role))
            values.append(value)
        last_low_byte = values[0]
        return values[0] | (values[1] << 8)

    def node(index):
        return None if index == 0 else index*4

    def snapshot(offset):
        return [memory[offset+i] for i in range(4)]

    # Saved words are not inserted into a supposedly separate heap region.
    # Their actual address/access/noninterference remains an explicit condition.
    events.append(dict(site=c, operation='save-entry-registers', registers=[4,5,6,7,14],
                       stack_span=[-20,0], physical_coordinate_unproved=True))
    store(selected_output, None, 14, 'initial selected zero')
    store(previous_output, None, 16, 'initial predecessor zero')
    median = node(u16(2, 18, 20, 'heap median index'))
    previous = median
    selected = None
    stages = {}
    status = 'conditional returned relation'
    terminated = True
    transitions = 0
    cycle = None
    if median is not None:
        size = u16(median+6, 44, 46, 'initial median size')
        stage = 'forward-step' if request > size else 'backward-step'
        while True:
            state = (stage, previous, selected)
            if state in stages:
                status = 'conditional stable-memory cycle'
                terminated = False
                cycle = dict(first_transition=stages[state], repeated_transition=transitions,
                             state=list(state), no_actual_termination_claim=True)
                break
            if transitions >= max_transitions:
                status = 'refused at explicit transition bound'
                terminated = False
                break
            stages[state] = transitions
            transitions += 1
            path.append(dict(stage=stage, R3_previous=previous, R2_selected=selected))
            if stage == 'backward-step':
                selected = previous
                previous = node(u16(selected+8, 84, 86, 'previous index'))
                if previous is None:
                    break
                stage = 'backward-check'
            elif stage == 'backward-check':
                size = u16(previous+6, 58, 60, 'backward predecessor size')
                if request <= size:
                    stage = 'backward-step'
                else:
                    size = u16(selected+6, 70, 72, 'backward selected size')
                    if request <= size:
                        break
                    stage = 'backward-step'
            elif stage == 'forward-step':
                selected = node(u16(previous+10, 138, 140, 'next index'))
                if selected is None:
                    break
                stage = 'forward-check'
            elif stage == 'forward-check':
                size = u16(previous+6, 112, 114, 'forward predecessor size')
                if request > size:
                    size = u16(selected+6, 124, 126, 'forward selected size')
                    if request <= size:
                        break
                previous = selected
                stage = 'forward-step'
            else:
                raise AssertionError('closed stage enumeration')
        if terminated:
            store(previous_output, previous, 164, 'final predecessor pointer')
            store(selected_output, selected, 166, 'final selected pointer')
    if terminated:
        events.extend([dict(site=c+168, operation='restore-entry-registers', registers=[4,5,6,7], stack_span=[-20,-4]),
                       dict(site=c+170, operation='restore-return-into-R0', stack_span=[-4,0]),
                       dict(site=c+172, operation='return-saved-entry-LR')])
    return dict(schema=SELECTOR, status=status, body=dict(address=c, bytes=len(SHAPE), instructions=87, sha256=layout.sha256),
        request_word=request_word, request_u16=request, median_offset=median,
        conditional_output_equations=dict(previous=previous, selected=selected) if terminated else None,
        output_snapshots=dict(previous_coordinate=previous_output, previous_bytes=snapshot(previous_output),
                              selected_coordinate=selected_output, selected_bytes=snapshot(selected_output),
                              same_slot=previous_output == selected_output),
        conditional_exit_registers=(dict(R0='saved incoming ThumbLR', R1=last_low_byte,
            R2=['base-plus', previous_output] if median is None else (0 if selected is None else ['base-plus',selected]),
            R3=0 if previous is None else ['base-plus',previous], SP='entry SP',
            R4_R12='entry origins under protected-save condition') if terminated else None),
        memory_events=events, stages=path, transitions=transitions, cycle=cycle,
        exact_modified_coordinates=sorted(set(range(previous_output,previous_output+4)) | set(range(selected_output,selected_output+4))),
        modified_coordinates_scope='symbolic byte arena only; private save also writes20bytes at entrySP[-20,0)',
        input_cell_count=len(cells), heap_write_purity_proved=False,
        returns_under_witness=terminated, actual_termination_proved=False,
        sorted_list_assumed=False, physical_access_proved=False, numeric_base_or_output_addresses_proved=False,
        initialization_proved=False, allocation_extent_proved=False, source_or_native_admission=False,
        obligations=[
            dict(id='indexed-owner', proved=False, text='Complete bytes, count and unchanged owner extent match the authenticated current index/ROM; executing code remains unchanged throughout all accesses and output writes.'),
            dict(id='entry-bytes-and-coordinates', proved=False, text='Every supplied byte equals actual reaching memory; symbolic base plus each coordinate denotes the actual pointer, with no invented initialization.'),
            dict(id='physical-access', proved=False, text='All byte reads and word stores are permitted, little-endian, ordinary synchronous RAM accesses; base and output words are aligned, nonwrapping and valid.'),
            dict(id='saved-frame', proved=False, text='EntrySP is word-aligned and incoming LR is a valid Thumb continuation. Private20-byte save is live, accessible and unaffected by either output write or any heap/code/ambient alias; no separation follows from role names.'),
            dict(id='stable-memory', proved=False, text='No interrupt, concurrent writer or volatile device changes read bytes during this execution. Explicit output writes are included in order.'),
            dict(id='pointer-representation', proved=False, text='Final base-plus byte tokens retain representation/lifetime obligations; they are not numeric initialized scalar bytes.'),
            dict(id='actual-list-path', proved=False, text='Only the finite or cycle path of this explicit byte witness is derived; it does not establish actual heap shape, sorting, valid allocation or termination.')])
