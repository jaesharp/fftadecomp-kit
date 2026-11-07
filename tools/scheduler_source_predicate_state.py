"""Conditional source-helper continuation on the scheduler's shared bytes.

The small predicate callees execute their actual loads and saved returns.
Creation stops before the scheduler BL; a null result returns only to the
observed parent continuation. Neither boundary supplies execution authority.
"""
from dataclasses import dataclass
import hashlib

import scheduler_phase256_state as phase

words = phase.words
atoms = phase.atoms
SELECTOR = 'conditional-scheduler-source-predicate-bytes-v1'
SHAPES = {
    'predicate': bytes.fromhex('10b5041cd4f758fe818808200840002801d0012000e0002000280ed1201c202109f090fd0006002807d1201c09f088fc0006002801d1012000e0002010bc02bc0847'),
    'identity': bytes.fromhex('7047'),
    'flag_test': bytes.fromhex('10b50c04240ccbf7b5f880880440002c01d1002000e0012010bc02bc0847'),
    'byte_test': bytes.fromhex('00b5cbf7cbf90006000e02bc0847'),
    'byte_load': bytes.fromhex('b0218900401800787047'),
}
EDGES = {'predicate': {4: 'identity', 32: 'flag_test', 44: 'byte_test'},
         'flag_test': {6: 'identity'}, 'byte_test': {2: 'byte_load'}}


@dataclass(frozen=True)
class Layout:
    prior: phase.Layout
    owners: tuple


def _pins(owners):
    return [dict(role=role, address=a, bytes=len(b), sha256=hashlib.sha256(b).hexdigest())
            for role, (a, b) in sorted(owners.items())]


def _validate(layout):
    if type(layout) is not Layout or type(layout.owners) is not tuple or len(layout.owners) != len(SHAPES):
        raise ValueError('complete source-predicate layout required')
    prior = phase._validate(layout.prior)
    owners = {}
    for row in layout.owners:
        if type(row) is not tuple or len(row) != 3:
            raise ValueError('exact owner record required')
        role, address, data = row
        if type(role) is not str or role not in SHAPES or role in owners or \
                type(address) is not int or address % 4 or type(data) is not bytes or \
                len(data) != len(SHAPES[role]) or not 0 <= address <= 2**32-len(data):
            raise ValueError('complete distinct aligned predicate owners required')
        owners[role] = (address, data)
    for role, (address, data) in owners.items():
        expected = bytearray(SHAPES[role])
        for offset, target in EDGES.get(role, {}).items():
            expected[offset:offset+4] = phase.removal._bl(address+offset, owners[target][0])
        if bytes(expected) != data:
            raise ValueError('complete predicate shape or exact call target differs: ' + role)
    all_owners = dict(prior, **owners)
    spans = sorted((a, a+len(b)) for a, b in all_owners.values())
    if any(a[1] > b[0] for a, b in zip(spans, spans[1:])):
        raise ValueError('complete prior and predicate owners overlap')
    address, body = prior['next']
    if phase._call(body, address, 16) != owners['predicate'][0]:
        raise ValueError('source helper must call the bound predicate')
    target = phase._call(body, address, 44)
    if not 0 <= target < 2**32 or target % 2 or any(a <= target < a+len(b) for a, b in all_owners.values()):
        raise ValueError('scheduler boundary must be a separate direct Thumb target')
    return prior, owners, target


def bind(prior, owners, *, selector):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit source-predicate selector required')
    result = Layout(prior, owners)
    _validate(result)
    return result


def _spans(value):
    return type(value) is tuple and len(value) <= 128 and all(
        type(s) is tuple and len(s) == 2 and all(type(v) is int for v in s)
        and -(2**31) <= s[0] < s[1] <= 2**31 for s in value)


def derive(layout, arena_base, cells, registers, *, selector, protected_spans=(),
           retired_spans=(), reusable_frame_spans=(), unavailable_spans=(), max_steps=512):
    """Relate one conditional helper entry to its next unproved boundary.

Retired bytes remain inaccessible. A stack allocation can reuse only explicit
retired-frame intervals; unavailable payloads cannot be revived that way.
Existing bytes survive local allocation, including aliases into stack saves.
"""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit source-predicate selector required')
    prior, predicate, scheduler_target = _validate(layout)
    if type(arena_base) is not int or arena_base % 4 or not 0 <= arena_base < 2**32 or \
            type(cells) is not dict or len(cells) > 4096 or any(
                type(k) is not int or not -(2**31) <= k < 2**31 or not atoms._cell(v)
                for k, v in cells.items()) or type(registers) is not dict or \
            set(registers) != set(range(15)) or any(type(k) is not int or not words._word(v)
                for k, v in registers.items()) or type(max_steps) is not int or not 1 <= max_steps <= 512:
        raise ValueError('bounded shared bytes, all registers and numeric arena required')
    if not all(_spans(s) for s in (protected_spans, retired_spans, reusable_frame_spans, unavailable_spans)):
        raise ValueError('bounded explicit intervals required')
    owners = dict(prior, **predicate)
    executable = dict(predicate, helper=prior['next'])
    r, m = dict(registers), dict(cells)
    retired, reusable = list(retired_spans), list(reusable_frame_spans)
    pc = prior['next'][0]
    trace, events, calls, returns = [], [], [], []
    boundary, zero, returned, entry_sp = None, None, False, None

    def stop(reason, at=None, **extra):
        error = phase.removal._Boundary(pc, reason, at)
        error.report.update(extra)
        raise error

    def numeric(w):
        value = words.observe(w)
        if value['kind'] != 'constant':
            stop('scalar bits are opaque or retain pointer origins')
        return value['value']

    def address(w):
        value = words.observe(w)
        if value['kind'] != 'base-plus':
            stop('address lacks intact common-base provenance')
        return value['coordinate']

    def physical(at, width, write=False, allocating=False):
        if not -(2**31) <= at <= 2**31-width or not 0 <= arena_base+at <= 2**32-width:
            stop('common-base access wraps', at)
        if width in (2, 4) and at % width:
            stop('unaligned common-byte access', at)
        if width and any(at < hi and at+width > lo for lo, hi in unavailable_spans):
            stop('access intersects unavailable payload/frame bytes', at)
        if width and not allocating and any(at < hi and at+width > lo for lo, hi in retired):
            stop('access intersects retired bytes', at)
        if write and any(at < hi and at+width > lo for lo, hi in protected_spans):
            stop('write intersects protected bytes', at)
        if write and any(arena_base+at < a+len(b) and arena_base+at+width > a for a, b in owners.values()):
            stop('write intersects immutable complete owner', at)

    def load(at, width):
        physical(at, width)
        value = tuple(m.get(at+i) for i in range(width))
        if any(v is None for v in value):
            stop('read lacks reaching byte origins', at)
        if width < 4 and any(type(v) is not int for v in value):
            stop('narrow read observes opaque or pointer byte origins', at)
        events.append(dict(site=pc, operation='read'+str(width*8), coordinate=at, bytes=value))
        return value+(0,)*(4-width)

    def store(at, value):
        physical(at, len(value), True)
        if len(value) < 4 and any(type(v) is not int for v in value):
            stop('narrow store requires scalar byte origins', at)
        if len(set(m) | set(range(at, at+len(value)))) > 4096:
            stop('byte state exceeds4096 cells', at)
        m.update({at+i: v for i, v in enumerate(value)})
        events.append(dict(site=pc, operation='write'+str(8*len(value)), coordinate=at, bytes=value))

    def covered(lo, hi):
        cursor = lo
        for start, end in sorted(reusable):
            if start <= cursor < end:
                cursor = max(cursor, end)
        return cursor >= hi

    def allocate(lo, hi, local=False):
        nonlocal retired
        physical(lo, hi-lo, allocating=True)
        if lo % 4 or hi % 4:
            stop('unaligned stack allocation', lo)
        for a, b in retired:
            start, end = max(a, lo), min(b, hi)
            if start < end and not covered(start, end):
                stop('stack allocation intersects nonreusable retired bytes', start)
        retired = [piece for a, b in retired for piece in ((a, min(b, lo)), (max(a, hi), b)) if piece[0] < piece[1]]
        if local:
            if len(set(m) | set(range(lo, hi))) > 4096:
                stop('local byte state exceeds4096 cells', lo)
            names = {v[1] for v in [*m.values(), *(v for w in r.values() for v in w)]
                     if type(v) is tuple and v[0] == 'opaque-byte'}
            suffix = len(trace)
            name = 'source helper local '+str(suffix)
            while name in names:
                suffix += 1
                name = 'source helper local '+str(suffix)
            for at in range(lo, hi):
                m.setdefault(at, ('opaque-byte', name, at-lo))
        events.append(dict(site=pc, operation='allocate-frame', coordinates=[lo, hi], initialization_granted=False))

    def retire(lo, hi):
        retired.append((lo, hi))
        reusable.append((lo, hi))
        events.append(dict(site=pc, operation='retire-frame', coordinates=[lo, hi]))

    def add(a, b):
        av, bv = words.observe(a), words.observe(b)
        if bv == dict(kind='constant', value=0):
            return a
        if av['kind'] == 'base-plus' and bv['kind'] == 'constant':
            n = av['coordinate']+bv['value']
            if not -(2**31) <= n < 2**31 or not 0 <= arena_base+n < 2**32:
                stop('pointer arithmetic wraps')
            return words._pointer(n)
        return words._constant((numeric(a)+numeric(b)) & 0xffffffff)

    try:
        entry_sp = address(r[13])
        physical(entry_sp, 0)
        if r[14] != words._constant((prior['root'][0]+124) | 1):
            stop('helper entry LR differs from actual parent call continuation')
        for _ in range(max_steps):
            found = next(((name, a, b) for name, (a, b) in executable.items() if a <= pc < a+len(b)), None)
            if found is None:
                stop('control outside bound source/predicate bodies')
            role, a, data = found
            offset = pc-a
            trace.append(pc)
            if offset % 2 or role == 'helper' and offset in (50, 52, 54):
                stop('control reaches padding, literal or noninstruction')
            if role == 'helper' and offset == 44:
                stop('scheduler creation call requires independent byte-state closure', target=scheduler_target)
            h = int.from_bytes(data[offset:offset+2], 'little')
            nxt = pc+2
            if h & 0xf800 == 0xf000:
                target = phase._call(data, a, offset)
                target_role = next((name for name, (start, _) in predicate.items() if start == target), None)
                if target_role is None or len(calls) >= 16:
                    stop('unbound or excessive nested predicate call', target=target)
                nxt = pc+4
                calls.append(dict(role=target_role, return_pc=nxt, entry_sp=address(r[13])))
                r[14] = words._constant(nxt | 1)
                nxt = target
            elif h & 0xfe00 == 0xb400:
                regs = [i for i in range(8) if h & (1 << i)]+([14] if h & 256 else [])
                hi = address(r[13]); lo = hi-4*len(regs)
                allocate(lo, hi)
                values = [r[i] for i in regs]
                for j, value in enumerate(values):
                    store(lo+4*j, value)
                r[13] = words._pointer(lo)
            elif h & 0xfe00 == 0xbc00:
                if h & 256:
                    stop('POP PC is outside selected shapes')
                regs = [i for i in range(8) if h & (1 << i)]
                lo = address(r[13])
                values = [load(lo+4*j, 4) for j in range(len(regs))]
                for reg, value in zip(regs, values):
                    r[reg] = value
                hi = lo+4*len(regs)
                retire(lo, hi)
                r[13] = words._pointer(hi)
            elif h & 0xff00 == 0xb000:
                amount = (h & 127)*4
                old = address(r[13]); new = old-amount if h & 128 else old+amount
                if h & 128:
                    allocate(new, old, True)
                else:
                    physical(new, 0); retire(old, new)
                r[13] = words._pointer(new)
            elif h & 0xfc00 == 0x4400:
                op = (h >> 8) & 3; rd = (h & 7) | ((h >> 4) & 8); rs = (h >> 3) & 15
                if op == 2 and rd != 15 and rs != 15:
                    r[rd] = r[rs]
                elif op == 3 and rs != 15:
                    target = numeric(r[rs])
                    if not target & 1:
                        stop('actual return word is not Thumb tagged')
                    if calls:
                        record = calls[-1]
                        if target != record['return_pc'] | 1 or address(r[13]) != record['entry_sp']:
                            stop('actual saved return word or restored nested SP differs', observed_target=target)
                        calls.pop(); returns.append(dict(role=record['role'], site=pc, observed_target=target))
                        nxt = target & ~1
                    else:
                        if role != 'helper' or target != (prior['root'][0]+124) | 1 or address(r[13]) != entry_sp:
                            stop('actual helper return word or restored entry SP differs', observed_target=target)
                        returned = True; pc = target & ~1
                        boundary = dict(site=pc, reason='parent continuation requires independent byte-state closure')
                        break
                else:
                    stop('unsupported high-register operation')
            elif h & 0xf800 == 0x1800:
                if h & 512:
                    stop('unsupported selected subtraction')
                b = words._constant((h >> 6) & 7) if h & 1024 else r[(h >> 6) & 7]
                r[h & 7] = add(r[(h >> 3) & 7], b)
                zero = None
            elif h & 0xe000 == 0x0000:
                op = (h >> 11) & 3; count = (h >> 6) & 31; source = r[(h >> 3) & 7]
                if op > 1:
                    stop('unsupported selected shift')
                count = count or 32 if op else count
                if count % 8 == 0:
                    lanes = count//8
                    value = (0,)*lanes+source[:4-lanes] if op == 0 else source[lanes:]+(0,)*lanes
                else:
                    bits = numeric(source)
                    value = words._constant((bits << count) & 0xffffffff if op == 0 else bits >> count)
                r[h & 7] = value
                observed = words.observe(value)
                zero = observed['value'] == 0 if observed['kind'] == 'constant' else None
            elif h & 0xe000 == 0x2000:
                op = (h >> 11) & 3; d = (h >> 8) & 7; value = words._constant(h & 255)
                if op == 0:
                    r[d] = value; zero = (h & 255) == 0
                elif op == 1:
                    zero = numeric(r[d]) == (h & 255)
                else:
                    stop('unsupported selected immediate arithmetic')
            elif h & 0xfc00 == 0x4000:
                if (h >> 6) & 15:
                    stop('unsupported selected scalar operation')
                d = h & 7
                r[d] = words._constant(numeric(r[d]) & numeric(r[(h >> 3) & 7]))
                zero = numeric(r[d]) == 0
            elif h & 0xf800 == 0x4800:
                at = ((pc+4) & ~3)+(h & 255)*4
                if role != 'helper' or at != a+52:
                    stop('literal outside selected complete owner')
                value = int.from_bytes(data[52:56], 'little')
                r[(h >> 8) & 7] = words._constant(value)
                events.append(dict(site=pc, operation='read-code-literal', address=at, value=value, grants_access=False))
            elif h & 0xe000 == 0x6000 or h & 0xf000 == 0x8000:
                width = 2 if h & 0xf000 == 0x8000 else 1 if h & 4096 else 4
                at = address(r[(h >> 3) & 7])+((h >> 6) & 31)*width
                d = h & 7
                if h & 2048:
                    r[d] = load(at, width)
                else:
                    store(at, r[d][:width])
            elif h & 0xf000 == 0x9000:
                at = address(r[13])+(h & 255)*4; d = (h >> 8) & 7
                if h & 2048:
                    r[d] = load(at, 4)
                else:
                    store(at, r[d])
            elif h & 0xf000 == 0xd000:
                cond = (h >> 8) & 15
                if cond not in (0, 1) or zero is None:
                    stop('conditional branch needs observed scalar flags')
                imm = h & 255; imm = imm-256 if imm & 128 else imm
                if zero == (cond == 0):
                    nxt = pc+4+2*imm
            elif h & 0xf800 == 0xe000:
                imm = h & 2047; imm = imm-2048 if imm & 1024 else imm
                nxt = pc+4+2*imm
            else:
                stop('unsupported actual selected instruction', halfword=h)
            pc = nxt
        else:
            stop('explicit instruction budget exhausted')
    except phase.removal._Boundary as error:
        boundary = error.report
    return dict(schema=SELECTOR, complete_owner_pins=_pins(owners), trace=trace, final_PC=pc,
                registers=r, post_cells={str(k): v for k, v in sorted(m.items())},
                changed_cells={str(k): v for k, v in sorted(m.items()) if cells.get(k) != v},
                memory_events=events, retired_spans=retired, reusable_frame_spans=reusable,
                unavailable_spans=unavailable_spans, observed_returns=returns, pending_calls=calls,
                conditional_helper_return=returned, boundary=boundary,
                actual_reaching_proved=False, physical_access_proved=False,
                actual_heap_lifetime_proved=False, actual_termination_proved=False,
                whole_CFG_closed=False, native_admission=False,
                obligations=[
                    'All incoming origins, exact owners, numeric base and shared aliases must describe the actual reaching state.',
                    'All reads, stores and frame ranges require independent live physical permission and synchronous noninterference.',
                    'Reusable intervals authorize only conditional stack reuse, never payload revival or new physical access.',
                    'Creation stops before its BL. Callback literals are copied bits, without callback effects or access authority.',
                    'A null helper return leaves the parent continuation open. No whole-CFG, C/ELF or native admission follows.'])


def continue_from_phase256(layout, prefix, arena_base, *, selector, protected_spans=(),
                           unavailable_spans=(), max_steps=512):
    """Consume a new conditional phase256 state, preserving bytes and releases.

The supplied report and the original protected/unavailable premises remain
conditional inputs. This adapter is not authentication of actual execution.
"""
    prior, _, _ = _validate(layout)
    if type(prefix) is not dict or prefix.get('schema') != phase.SELECTOR or \
            prefix.get('complete_owner_pins') != _pins(prior) or \
            prefix.get('final_PC') != prior['next'][0] or \
            type(prefix.get('boundary')) is not dict or prefix['boundary'].get('site') != prior['next'][0] or \
            prefix['boundary'].get('reason') != 'next source helper entry requires independent closure' or \
            type(prefix.get('pending_calls')) is not list or not prefix['pending_calls']:
        raise ValueError('exact conditional phase256 next-entry report required')
    registers = prefix.get('registers')
    if type(registers) is not dict or not words._word(registers.get(13)):
        raise ValueError('reported entry SP origins required')
    sp = words.observe(registers[13])
    expected = dict(role='next', return_pc=prior['root'][0]+124,
                    entry_sp=sp.get('coordinate'))
    if sp['kind'] != 'base-plus' or prefix['pending_calls'][-1] != expected:
        raise ValueError('actual next-call continuation and SP relation required')
    if not _spans(unavailable_spans):
        raise ValueError('explicit original unavailable premises required')
    reusable = tuple(tuple(event['coordinates']) for event in prefix.get('memory_events', ())
                     if event.get('operation') == 'retire-frame')
    retired = tuple(tuple(span) for span in prefix.get('retired_spans', ()))
    freed = tuple(tuple(span) for span in prefix.get('conditional_released_payloads', ()))
    result = derive(layout, arena_base, {int(k): v for k, v in prefix['post_cells'].items()},
                    registers, selector=selector, protected_spans=protected_spans,
                    retired_spans=retired, reusable_frame_spans=reusable,
                    unavailable_spans=unavailable_spans+freed, max_steps=max_steps)
    result['conditional_phase256_input'] = True
    result['prefix_calls_remaining'] = prefix['pending_calls'][:-1] if result['conditional_helper_return'] else prefix['pending_calls']
    return result
