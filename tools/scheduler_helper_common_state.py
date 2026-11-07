"""Bounded common-byte execution of the descriptor helper's nonzero branch.

Complete bodies close the local descriptor setup, guarded table dispatch,
subject getter and coordinate-call prefix. Unknown nested callees remain real
entry cutpoints with their actual arguments, saves and return continuation.
"""
from dataclasses import dataclass
import hashlib

import scheduler_copy_state as words
import scheduler_allocator_state as atoms
import scheduler_callback_zero_phase as shapes

SELECTOR = 'conditional-scheduler-helper-common-byte-state-v1'
HELPER = bytes.fromhex('f0b58db0061c0c1c129d1206120e1b061b0e002a03d1072b01d1002077e0120409490b98084010430b900baa546007490b9808400b90171c062b5ed8980004494018006887460000ffff00ff0000ffff4c040e0868040e088c040e0894040e089c040e08a2040e08aa040e08d4040e08301cfdf707f808ac6d46223509ab211c2a1cfbf791fc2088783800040014298860391ee0301cf8f721fc25e0301cf8f71dfc2ae0f8f780f81ee0301cfbf794fe1ae06c4626340aad6b462a33301c211c2a1cf8f78dfb20887838000400142988783909040914f8f72bfb0ee00021685e0222a95ef8f724fb0006002805d00a480b990140142001430b910297074800680749139a00920c2201ab25f727fa0db0f0bc02bc084700000000ffff30f4000205ff0d08')
GETTER = bytes.fromhex('00b5cbf7c5f9006802bc0847')
COORDINATES = bytes.fromhex('f0b582b00e1c0821445e0a25415f0c27c55f00920193201c2a1c331c40f7acfd02b0f0bc01bc0047')
CALL_OFFSETS = (114, 130, 150, 158, 164, 172, 194, 214, 228, 266)
TABLE_OFFSETS = (112, 148, 156, 164, 170, 178, 220)


@dataclass(frozen=True)
class Layout:
    helper: int
    helper_data: bytes
    getter: int
    getter_data: bytes
    identity: int
    identity_data: bytes
    coordinates: int
    coordinates_data: bytes


def _validate(layout):
    if type(layout) is not Layout:
        raise ValueError('four complete helper owners required')
    owners = [(layout.helper, layout.helper_data, 292), (layout.getter, layout.getter_data, 12),
              (layout.identity, layout.identity_data, 2), (layout.coordinates, layout.coordinates_data, 40)]
    for i, (address, data, size) in enumerate(owners):
        if type(address) is not int or address % 4 or not 0 <= address <= 2**32-size or \
                type(data) is not bytes or len(data) != size:
            raise ValueError('complete aligned292/12/2/40B code owners required')
        if any(address < a+n and address+size > a for a, _, n in owners[:i]):
            raise ValueError('complete helper owners overlap')
    h, b = layout.helper, layout.helper_data
    expected = bytearray(HELPER)
    calls = {}
    for offset in CALL_OFFSETS:
        target = shapes._call(b, h, offset)
        if target is None or target % 2 or not 0 <= target < 2**32:
            raise ValueError('real Thumb call identity required')
        calls[h+offset] = target
        expected[offset:offset+4] = atoms.remove._bl(h+offset, target)
    expected[80:84] = (h+84).to_bytes(4, 'little')
    for i, offset in enumerate(TABLE_OFFSETS):expected[84+4*i:88+4*i] = (h+offset).to_bytes(4, 'little')
    point = int.from_bytes(b[284:288], 'little')
    callback = int.from_bytes(b[288:292], 'little')
    if point % 4 or point > 2**32-4 or not callback & 1:
        raise ValueError('aligned fixed point and Thumb callback word required')
    expected[284:292] = b[284:292]
    if b != bytes(expected) or calls[h+114] != layout.getter or calls[h+130] != layout.coordinates:
        raise ValueError('complete descriptor helper shape/table/call identities differ')
    if layout.getter_data != GETTER[:2]+atoms.remove._bl(layout.getter+2, layout.identity)+GETTER[6:] or \
            layout.identity_data != b'\x70\x47':
        raise ValueError('actual subject getter and BX LR identity differ')
    target = shapes._call(layout.coordinates_data, layout.coordinates, 28)
    if target is None or not 0 <= target < 2**32 or target % 2 or \
            layout.coordinates_data != COORDINATES[:28]+atoms.remove._bl(layout.coordinates+28, target)+COORDINATES[32:]:
        raise ValueError('complete coordinate prefix/call/return shape differs')
    calls[layout.getter+2] = layout.identity
    calls[layout.coordinates+28] = target
    # Unsupported callees are opaque code identities, never admitted as one
    # of these kernels merely because an address happens to fall inside it.
    known = {h+114, h+130, layout.getter+2}
    for site, destination in calls.items():
        if site not in known and any(a <= destination < a+n for a, _, n in owners):
            raise ValueError('unsupported call aliases a bound owner')
    return dict(calls=calls, scheduler_point=point, callback_word=callback)


def bind(helper_data, helper_address, getter_data, getter_address, identity_data,
         identity_address, coordinates_data, coordinates_address, *, selector):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit helper common-byte selector required')
    layout = Layout(helper_address, helper_data, getter_address, getter_data,
                    identity_address, identity_data, coordinates_address, coordinates_data)
    _validate(layout)
    return layout


def derive(layout, arena_base, cells, registers, *, selector, protected_spans=(), retired_spans=()):
    """Start at helper entry; execute real saves and opaque local allocation."""
    return _derive(layout, arena_base, cells, registers, selector=selector,
                   protected_spans=protected_spans, retired_spans=retired_spans, entry_sp=None)


def continue_from_gate(layout, arena_base, cells, registers, *, entry_sp, selector,
                       protected_spans=(), retired_spans=()):
    """Start at helper+30 using actual072 cutpoint state, without prefix replay.

The supplied entry SP and live saves remain premises. The preceding gate has
made no local stores, so no pre-allocation byte can initialize its52B locals.
"""
    if type(entry_sp) is not int:
        raise ValueError('actual helper-entry SP coordinate required')
    return _derive(layout, arena_base, cells, registers, selector=selector,
                   protected_spans=protected_spans, retired_spans=retired_spans, entry_sp=entry_sp)


def _derive(layout, arena_base, cells, registers, *, selector, protected_spans, retired_spans, entry_sp):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit helper common-byte selector required')
    facts = _validate(layout)
    if type(arena_base) is not int or arena_base % 4 or not 0 <= arena_base < 2**32 or \
            type(registers) is not dict or set(registers) != set(range(15)) or \
            any(type(k) is not int or not words._word(v) for k, v in registers.items()) or \
            type(cells) is not dict or len(cells) > 4096 or any(type(k) is not int or
                not -(2**31) <= k < 2**31 or not atoms._cell(v) for k, v in cells.items()):
        raise ValueError('bounded complete origins and numeric common base required')
    for spans in (protected_spans, retired_spans):
        if type(spans) is not tuple or len(spans) > 32 or any(type(p) is not tuple or len(p) != 2 or
                any(type(v) is not int for v in p) or not -(2**31) <= p[0] < p[1] <= 2**31 for p in spans):
            raise ValueError('bounded explicit protection/lifetime spans required')
    h, g, ident, coord = layout.helper, layout.getter, layout.identity, layout.coordinates
    owners = {h:layout.helper_data, g:layout.getter_data, ident:layout.identity_data, coord:layout.coordinates_data}
    r, m, trace, events = dict(registers), dict(cells), [], []
    retired = list(retired_spans)
    pc = h if entry_sp is None else h+30
    start = pc
    returns = []
    boundary = call_cutpoint = None
    selected_nonzero = False
    mode = dispatch = None
    initial_sp = entry_sp
    flags = None

    def stop(reason, at=None, **extra):
        error = atoms.remove._Boundary(pc, reason, at)
        error.report.update(extra)
        raise error

    def span_guard(at, width, writing=False, allocating=False):
        if not -(2**31) <= at <= 2**31-width or not 0 <= arena_base+at <= 2**32-width:
            stop('access/frame wraps the numeric common base', at)
        if not allocating and any(at < hi and at+width > lo for lo, hi in retired):
            stop('access overlaps retired private bytes', at)
        if writing and any(at < hi and at+width > lo for lo, hi in protected_spans):
            stop('actual write overlaps protected bytes', at)

    def addr(reg, offset=0):
        value = words.observe(r[reg])
        if value['kind'] != 'base-plus':stop('address R'+str(reg)+' lacks intact common-base provenance')
        return value['coordinate']+offset

    def number(reg):
        value = words.observe(r[reg])
        if value['kind'] != 'constant':stop('scalar/control R'+str(reg)+' has opaque or pointer bits')
        return value['value']

    def load(at, width, signed=False):
        span_guard(at, width)
        if at % width:stop('unaligned byte-state read', at)
        value = tuple(m.get(at+i) for i in range(width))
        if any(v is None for v in value):stop('read has missing reaching byte origins', at)
        if width < 4 and any(type(v) is not int for v in value):stop('scalar load observes opaque or pointer bytes', at)
        events.append(dict(site=pc, operation='read'+str(width*8), coordinate=at, bytes=value, signed=signed))
        if width == 4:return value
        scalar = sum(v << (8*i) for i, v in enumerate(value))
        if signed and scalar & (1 << (8*width-1)):scalar -= 1 << (8*width)
        return words._constant(scalar & 0xffffffff)

    def store(at, value):
        span_guard(at, len(value), True)
        if at % len(value):stop('unaligned byte-state write', at)
        if len(set(m) | set(range(at, at+len(value)))) > 4096:stop('byte state exceeds4096 cells', at)
        m.update({at+i:v for i, v in enumerate(value)})
        events.append(dict(site=pc, operation='write'+str(len(value)*8), coordinate=at, bytes=value))

    def activate(lo, hi, opaque=False):
        nonlocal retired
        span_guard(lo, hi-lo, allocating=True)
        if opaque and len(set(m) | set(range(lo, hi))) > 4096:
            stop('local byte state exceeds4096 cells', lo)
        remaining = []
        for a, b in retired:
            if hi <= a or lo >= b:remaining.append((a, b))
            else:
                if a < lo:remaining.append((a, lo))
                if hi < b:remaining.append((hi, b))
        retired = remaining
        if opaque:
            names = {v[1] for v in [*m.values(), *(v for w in r.values() for v in w)]
                     if type(v) is tuple and v[0] == 'opaque-byte'}
            name = 'unmodeled helper local'; n = 0
            while name in names:n += 1; name = 'unmodeled helper local:'+str(n)
            for at in range(lo, hi):m[at] = ('opaque-byte', name, at-lo)
        events.append(dict(site=pc, operation='allocate-frame', coordinates=[lo, hi],
                           initialization_granted=False, opaque_locals=opaque))

    def retire(lo, hi):
        retired.append((lo, hi))
        events.append(dict(site=pc, operation='retire-frame', coordinates=[lo, hi]))

    def bitwise(a, b, operation):
        out = []
        for x, y in zip(a, b):
            if type(x) is int and type(y) is int:out.append(x & y if operation == 'and' else x | y)
            elif operation == 'and' and (x == 0 or y == 0):out.append(0)
            elif operation == 'and' and x == 255:out.append(y)
            elif operation == 'and' and y == 255:out.append(x)
            elif operation == 'or' and x == 0:out.append(y)
            elif operation == 'or' and y == 0:out.append(x)
            elif operation == 'or' and (x == 255 or y == 255):out.append(255)
            elif x == y:out.append(x)
            else:stop('bitwise operation requires unsupported partial opaque bits')
        return tuple(out)

    try:
        if initial_sp is None:initial_sp = addr(13)
        span_guard(initial_sp, 1)
        if initial_sp % 4:stop('entry SP is not word aligned', initial_sp)
        if start == h+30:
            if r[13] != words._pointer(initial_sp-72):stop('gate SP differs from helper entry minus72')
            if number(2) > 255 or number(3) > 255 or (number(2) == 0 and number(3) == 7):
                stop('gate state does not establish the actual non-early branch')
            if any(initial_sp-72 < hi and initial_sp > lo for lo, hi in retired):
                stop('supplied retired spans overlap the live helper gate frame')
            activate(initial_sp-72, initial_sp-20, True)
        for _ in range(180):
            owner = next((a for a, data in owners.items() if a <= pc < a+len(data)), None)
            if owner is None:stop('control outside complete composed owners')
            body = owners[owner]; offset = pc-owner
            if owner == h:
                allowed = set(range(0,70,2)) | set(range(112,270,2))
                if offset not in allowed:stop('helper early return or other path remains outside075')
                if offset == 30:mode, dispatch = number(2), number(3); selected_nonzero = True
            elif owner == coord and offset >= 32:stop('coordinate return requires unsupported nested effect')
            trace.append(pc)
            op = int.from_bytes(body[offset:offset+2], 'little'); nxt = pc+2
            if op & 0xfe00 == 0xb400:
                selected = [i for i in range(8) if op & (1 << i)]+([14] if op & 256 else [])
                top = addr(13); low = top-4*len(selected)
                if low % 4:stop('unaligned PUSH SP', low)
                span_guard(low, 4*len(selected), True, True)
                if len(set(m) | set(range(low, top))) > 4096:
                    stop('PUSH byte state exceeds4096 cells', low)
                values = [r[i] for i in selected]
                activate(low, top)
                for i, value in enumerate(values):store(low+4*i, value)
                r[13] = words._pointer(low)
            elif op & 0xff00 == 0xb000:
                old = addr(13); size = 4*(op & 127); new = old-size if op & 128 else old+size
                if op & 128:activate(new, old, True)
                else:retire(old, new)
                r[13] = words._pointer(new)
            elif op & 0xff00 == 0xbc00:
                selected = [i for i in range(8) if op & (1 << i)]; low = addr(13)
                values = [load(low+4*i, 4) for i in range(len(selected))]
                for i, value in zip(selected, values):r[i] = value
                r[13] = words._pointer(low+4*len(selected)); retire(low, low+4*len(selected))
            elif op & 0xf800 == 0x2000:r[(op >> 8) & 7] = words._constant(op & 255); flags = None
            elif op & 0xfe00 == 0x1c00:
                if (op >> 6) & 7:stop('unsupported nonzero three-register immediate')
                r[op & 7] = r[(op >> 3) & 7]; flags = None
            elif op & 0xf800 in (0x0000, 0x0800, 0x1000):
                src = r[(op >> 3) & 7]; shift = (op >> 6) & 31; kind = op & 0xf800
                if kind == 0 and shift == 24:r[op & 7] = (0, 0, 0, src[0])
                elif kind == 0x0800 and shift == 24:r[op & 7] = (src[3], 0, 0, 0)
                else:
                    value = number((op >> 3) & 7)
                    if kind == 0:value <<= shift
                    elif kind == 0x0800:value >>= shift or 32
                    else:
                        if value & 0x80000000:value -= 2**32
                        value >>= shift or 32
                    r[op & 7] = words._constant(value & 0xffffffff)
                flags = None
            elif op & 0xf800 in (0x3000, 0x3800):
                reg = (op >> 8) & 7; delta = op & 255
                if op & 0xf800 == 0x3800:delta = -delta
                value = words.observe(r[reg])
                if value['kind'] == 'base-plus':
                    at = value['coordinate']+delta; span_guard(at, 1); r[reg] = words._pointer(at)
                else:r[reg] = words._constant((number(reg)+delta) & 0xffffffff)
                flags = None
            elif op & 0xffc0 in (0x4000, 0x4300):
                reg = op & 7; r[reg] = bitwise(r[reg], r[(op >> 3) & 7], 'and' if op & 0xffc0 == 0x4000 else 'or'); flags = None
            elif op & 0xf800 == 0x2800:
                a, b = number((op >> 8) & 7), op & 255; flags = (a == b, a >= b)
            elif op & 0xf000 == 0xd000:
                if flags is None:stop('branch lacks actual comparison flags')
                z, carry = flags; condition = (op >> 8) & 15
                take = {0:z, 1:not z, 8:carry and not z}.get(condition)
                if take is None:stop('unsupported branch condition')
                delta = op & 255
                if delta & 128:delta -= 256
                if take:nxt = pc+4+2*delta
            elif op & 0xf800 == 0xe000:nxt = shapes._branch(body, owner, offset)
            elif op & 0xf800 == 0x4800:
                literal = ((pc+4) & ~3)+4*(op & 255)
                if owner != h or literal-h not in (72, 76, 80, 280, 284, 288):stop('literal outside complete helper data words')
                value = int.from_bytes(body[literal-owner:literal-owner+4], 'little')
                r[(op >> 8) & 7] = words._constant(value)
                events.append(dict(site=pc, operation='read-ROM32', address=literal, value=value))
            elif op & 0xf800 == 0x1800:
                r[op & 7] = words._constant((number((op >> 3) & 7)+number((op >> 6) & 7)) & 0xffffffff); flags = None
            elif op & 0xff00 == 0x4600:
                dst = (op & 7) | ((op >> 4) & 8); value = r[(op >> 3) & 15]
                if dst == 15:
                    target = number((op >> 3) & 15)
                    if owner != h or offset != 68 or target not in [h+n for n in TABLE_OFFSETS]:stop('MOV PC lacks guarded owned table target')
                    nxt = target
                    events.append(dict(site=pc, operation='guarded-table-branch', target=target))
                else:r[dst] = value
            elif op & 0xf800 == 0xa800:r[(op >> 8) & 7] = words._pointer(addr(13, 4*(op & 255)))
            elif op & 0xf000 == 0x9000:
                reg = (op >> 8) & 7; at = addr(13, 4*(op & 255))
                if op & 0x800:r[reg] = load(at, 4)
                else:store(at, r[reg])
            elif op & 0xfe00 == 0x5e00:r[op & 7] = load(addr((op >> 3) & 7, number((op >> 6) & 7)), 2, True)
            elif op & 0xf800 in (0x6000, 0x6800, 0x8800):
                reg, base = op & 7, (op >> 3) & 7; kind = op & 0xf800
                width = 2 if kind == 0x8800 else 4; displacement = width*((op >> 6) & 31)
                if owner == h and offset == 66:
                    at = number(base)+displacement
                    if at % 4 or not h+84 <= at <= h+108:stop('table read escapes guarded seven entries')
                    value = int.from_bytes(body[at-h:at-h+4], 'little'); r[reg] = words._constant(value)
                    events.append(dict(site=pc, operation='read-ROM32', address=at, value=value))
                else:
                    if owner == h and offset == 254:
                        if r[base] != words._constant(facts['scheduler_point']):stop('fixed-point register no longer equals actual literal')
                        at = facts['scheduler_point']-arena_base
                    else:at = addr(base, displacement)
                    if kind == 0x6000:store(at, r[reg])
                    else:r[reg] = load(at, width)
            elif op & 0xf800 == 0xf000:
                destination = facts['calls'].get(pc)
                if destination is None:stop('call is not in the complete bound shape')
                site = pc; r[14] = words._constant((pc+4) | 1)
                events.append(dict(site=pc, operation='ordinary-call', target=destination, SP=addr(13), return_word=r[14]))
                if site in (h+114, h+130, g+2):
                    returns.append((destination, pc+4)); nxt = destination
                else:
                    call_cutpoint = dict(call_site=site, target=destination, return_word=r[14], SP=addr(13),
                        register_arguments={i:r[i] for i in range(4)}, callee_executed=False,
                        reason='no exact common-byte callee effect kernel is composed')
                    pc = destination
                    stop(call_cutpoint['reason'], call_site=site, cutpoint='callee-entry')
            elif op & 0xff87 == 0x4700:
                target = r[(op >> 3) & 15]
                if not returns or returns[-1][0] != owner:stop('unmatched nested return owner')
                expected = returns[-1][1]
                if target != words._constant(expected | 1):stop('actual nested return word differs from its BL continuation')
                returns.pop(); nxt = expected
                events.append(dict(site=pc, operation='bx-known-continuation', target=expected, executable_authority_proved=False))
            else:stop('instruction outside closed common-byte subset')
            pc = nxt
        else:stop('bounded acyclic helper step limit exhausted')
    except atoms.remove._Boundary as error:boundary = error.report
    stale = {}
    for reg, value in r.items():
        observed = words.observe(value)
        if observed['kind'] == 'base-plus' and any(lo <= observed['coordinate'] < hi for lo, hi in retired):
            stale[str(reg)] = observed['coordinate']
    return dict(schema=SELECTOR, starts_at=start, boundary=boundary, nested_call_cutpoint=call_cutpoint,
        reaches_explicit_nested_call=call_cutpoint is not None, selected_nonzero_branch=selected_nonzero,
        observed_mode=mode, observed_dispatch=dispatch, entry_SP=initial_sp, registers=r,
        post_cells={str(k):v for k, v in sorted(m.items())},
        changed_cells={str(k):v for k, v in sorted(m.items()) if cells.get(k) != v},
        changed_cells_include_explicit_forgetting=True, trace=trace, memory_events=events,
        retired_spans=retired, known_retired_alias_registers=stale,
        complete_owner_pins=[dict(address=a, bytes=len(b), sha256=hashlib.sha256(b).hexdigest()) for a, b in owners.items()],
        fabricated_callee_results=False, fabricated_saved_words=False, role_separation_assumed=False,
        ABI_preservation_assumed=False, flags_proved=False, actual_reaching_state_proved=False,
        physical_access_proved=False, actual_heap_or_SP_proved=False, actual_lifetime_proved=False,
        actual_code_execution_proved=False, actual_termination_proved=False, returns_to_caller=False,
        full_CFG_closed=False, source_or_ELF_admission=False, native_admission=False,
        obligations=[dict(id=k, proved=False, text=t) for k, t in (
            ('state', 'Supplied entry or actual072 gate state and live saves equal the real reaching state; no root case0 transport is supplied here.'),
            ('access', 'The numeric common base maps every access to live permitted physical memory with complete caller/code protections and no interference.'),
            ('callees', 'Each explicit nested entry cutpoint requires its own actual callee effect kernel. No return, output-buffer initialization, allocation or ABI survival is inferred.'),
            ('lifetime', 'Actual allocations grant no prior initialization. All retired and escaped pointer aliases retain their lifetime obligations.'),
            ('control', 'Bound complete owners/literals have actual executable authority; observed nested return equality grants no installation or execution witness.'),
            ('scope', 'The relation stops at exact unsupported calls/paths. Processor flags, whole-owner closure, termination and native admission remain open.'),
        )])
