"""Conditional actual motion-record initializer on one ordered byte state.

The complete leaf used by both motion calls is interpreted without object
separation, initialized output, callee-saved ABI or BIOS-result assumptions.
Its caller entry remains a premise: this module never crosses the Sqrt cut.
"""
from dataclasses import dataclass
import hashlib

import scheduler_coordinate_common_state as coordinate
import scheduler_copy_state as words
import scheduler_allocator_state as atoms

SELECTOR = 'conditional-scheduler-motion-record-byte-state-v1'
BODY = bytes.fromhex('30b5041c039d21606260a360e560581aa061002804da4042a0610120404200e001202061a81ae061002804da4042e0610120404200e001206061e0694110616200212162a062002800d1236030bc01bc0047')


@dataclass(frozen=True)
class Layout:
    coordinate: coordinate.Layout
    initializer: int
    initializer_data: bytes


def _validate(layout):
    if type(layout) is not Layout:
        raise ValueError('complete coordinate context and initializer required')
    facts = coordinate._validate(layout.coordinate)
    a, data, c = layout.initializer, layout.initializer_data, layout.coordinate
    if type(a) is not int or a % 2 or not 0 <= a <= 2**32 - 82 or type(data) is not bytes or data != BODY:
        raise ValueError('exact complete aligned82B initializer required')
    owners = [(c.transform, 72), (c.predicate, 36), (c.motion, 256),
              (c.helper.helper, 292), (c.helper.getter, 12),
              (c.helper.identity, 2), (c.helper.coordinates, 40)]
    if any(a < s + n and a + 82 > s for s, n in owners):
        raise ValueError('initializer overlaps a complete continuation owner')
    if any(facts['calls'][c.motion + offset] != a for offset in (206, 226)):
        raise ValueError('both actual motion call identities must reach this initializer')
    if a <= facts['calls'][c.motion + 128] < a + 82:
        raise ValueError('unresolved Sqrt target overlaps initializer')
    return facts


def bind(coordinate_layout, initializer_data, initializer_address, *, selector):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit motion record selector required')
    result = Layout(coordinate_layout, initializer_address, initializer_data)
    _validate(result)
    return result


def derive(layout, arena_base, cells, registers, *, call_site, selector,
           protected_spans=(), retired_spans=()):
    """Conditional leaf-entry relation, not a witness of the post-Sqrt state.

Input registers carry scalar, common-base pointer or opaque byte words. The
fifth argument is loaded from the current stack after the real PUSH. Stores
may overwrite incoming words and saves; the actual later reads see them.
"""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit motion record selector required')
    _validate(layout)
    if type(call_site) is not int or call_site not in (layout.coordinate.motion + 206, layout.coordinate.motion + 226):
        raise ValueError('one of the two complete motion call sites required')
    if type(arena_base) is not int or arena_base % 4 or not 0 <= arena_base < 2**32:
        raise ValueError('aligned numeric common base required')
    if type(registers) is not dict or set(registers) != set(range(15)) or any(
            type(k) is not int or not words._word(v) for k, v in registers.items()):
        raise ValueError('complete exact entry register origins required')
    if type(cells) is not dict or len(cells) > 4096 or any(
            type(k) is not int or not -(2**31) <= k < 2**31 or not atoms._cell(v) for k, v in cells.items()):
        raise ValueError('bounded common byte state required')
    for spans in (protected_spans, retired_spans):
        if type(spans) is not tuple or len(spans) > 40 or any(
                type(s) is not tuple or len(s) != 2 or any(type(v) is not int for v in s)
                or not -(2**31) <= s[0] < s[1] <= 2**31 for s in spans):
            raise ValueError('bounded protection/lifetime intervals required')
    r, m, retired = dict(registers), dict(cells), list(retired_spans)
    trace, events = [], []
    a, pc, comparison = layout.initializer, layout.initializer, None
    entry_sp = None
    boundary, return_cut = None, None

    def stop(reason, at=None):
        raise atoms.remove._Boundary(pc, reason, at)

    def scalar(reg):
        value = words.observe(r[reg])
        if value['kind'] != 'constant':
            stop('scalar R' + str(reg) + ' observes opaque or pointer bits')
        return value['value']

    def address(reg):
        value = words.observe(r[reg])
        if value['kind'] != 'base-plus':
            stop('address R' + str(reg) + ' lacks intact common-base provenance')
        return value['coordinate']

    def physical(at, width, write=False, allocating=False):
        if not -(2**31) <= at <= 2**31 - width or not 0 <= arena_base + at <= 2**32 - width:
            stop('numeric common-base access or frame wraps', at)
        if at % 4:
            stop('unaligned word access or frame', at)
        if not allocating and any(at < hi and at + width > lo for lo, hi in retired):
            stop('access overlaps retired private bytes', at)
        if write and any(at < hi and at + width > lo for lo, hi in protected_spans):
            stop('actual write overlaps protected bytes', at)

    def load(at):
        physical(at, 4)
        value = tuple(m.get(at + i) for i in range(4))
        if any(v is None for v in value):
            stop('read has missing reaching byte origins', at)
        events.append(dict(site=pc, operation='read32', coordinate=at, bytes=value))
        return value

    def store(at, value):
        physical(at, 4, True)
        if len(set(m) | set(range(at, at + 4))) > 4096:
            stop('byte state exceeds4096 cells', at)
        m.update({at + i: v for i, v in enumerate(value)})
        events.append(dict(site=pc, operation='write32', coordinate=at, bytes=value))

    def push_frame(top):
        nonlocal retired
        low = top - 12
        physical(low, 12, True, True)
        if len(set(m) | set(range(low, top))) > 4096:
            stop('PUSH byte state exceeds4096 cells', low)
        live = []
        for lo, hi in retired:
            if top <= lo or low >= hi:
                live.append((lo, hi))
            else:
                if lo < low:
                    live.append((lo, low))
                if top < hi:
                    live.append((top, hi))
        retired = live
        events.append(dict(site=pc, operation='allocate-frame', coordinates=[low, top], initialization_granted=False))
        for i, value in enumerate((r[4], r[5], r[14])):
            store(low + 4*i, value)
        r[13] = words._pointer(low)

    def pop(selected):
        low = address(13)
        values = [load(low + 4*i) for i in range(len(selected))]
        for reg, value in zip(selected, values):
            r[reg] = value
        top = low + 4*len(selected)
        r[13] = words._pointer(top)
        retired.append((low, top))
        events.append(dict(site=pc, operation='retire-frame', coordinates=[low, top]))

    try:
        entry_sp = address(13)
        physical(entry_sp, 4, allocating=True)
        if r[14] != words._constant((call_site + 4) | 1):
            stop('entry LR differs from actual motion BL continuation')
        for _ in range(48):
            offset = pc - a
            if offset % 2 or not 0 <= offset < 82:
                stop('control outside complete initializer')
            trace.append(pc)
            op = int.from_bytes(layout.initializer_data[offset:offset + 2], 'little')
            nxt = pc + 2
            if op == 0xb530:
                push_frame(address(13))
            elif op == 0xbc30:
                pop((4, 5))
            elif op == 0xbc01:
                pop((0,))
            elif op == 0x4700:
                expected = (call_site + 4) | 1
                if r[0] != words._constant(expected):
                    stop('actual popped return word differs from motion BL continuation')
                return_cut = dict(site=pc, target=call_site + 4, register=0, return_word=r[0],
                                  SP=address(13), caller_executed=False)
                events.append(dict(site=pc, operation='bx-known-continuation', target=call_site + 4,
                                   executable_authority_proved=False))
                break
            elif op & 0xf800 == 0x9800:
                r[(op >> 8) & 7] = load(address(13) + 4*(op & 255))
            elif op & 0xf800 in (0x6000, 0x6800):
                at = address((op >> 3) & 7) + 4*((op >> 6) & 31)
                reg = op & 7
                if op & 0x0800:
                    r[reg] = load(at)
                else:
                    store(at, r[reg])
            elif op == 0x1c04:
                r[4] = r[0]
                comparison = None
            elif op & 0xfe00 == 0x1a00:
                r[op & 7] = words._constant((scalar((op >> 3) & 7) - scalar((op >> 6) & 7)) & 0xffffffff)
                comparison = None
            elif op & 0xf800 == 0x2800:
                value = scalar((op >> 8) & 7)
                if op & 255:
                    stop('comparison outside exact zero guards')
                comparison = value - 2**32 if value & 0x80000000 else value
            elif op & 0xf000 == 0xd000:
                kind = (op >> 8) & 15
                if comparison is None or kind not in (1, 10):
                    stop('branch lacks exact signed-zero comparison')
                take = comparison != 0 if kind == 1 else comparison >= 0
                if take:
                    disp = op & 255
                    if disp & 128:
                        disp -= 256
                    nxt = pc + 4 + 2*disp
            elif op & 0xffc0 == 0x4240:
                r[op & 7] = words._constant((-scalar((op >> 3) & 7)) & 0xffffffff)
                comparison = None
            elif op & 0xf800 == 0x2000:
                r[(op >> 8) & 7] = words._constant(op & 255)
                comparison = None
            elif op & 0xf800 == 0xe000:
                disp = op & 2047
                if disp & 1024:
                    disp -= 2048
                nxt = pc + 4 + 2*disp
            elif op & 0xf800 == 0x1000:
                value = scalar((op >> 3) & 7)
                if value & 0x80000000:
                    value -= 2**32
                r[op & 7] = words._constant((value >> (((op >> 6) & 31) or 32)) & 0xffffffff)
                comparison = None
            else:
                stop('instruction outside exact initializer decoder')
            pc = nxt
        else:
            stop('bounded acyclic initializer step limit exhausted')
    except atoms.remove._Boundary as error:
        boundary = error.report
    aliases = {}
    for reg, value in r.items():
        origin = words.observe(value)
        if origin['kind'] == 'base-plus' and any(lo <= origin['coordinate'] < hi for lo, hi in retired):
            aliases[str(reg)] = origin['coordinate']
    return dict(schema=SELECTOR, starts_at=a, call_site=call_site, entry_SP=entry_sp,
        reaches_motion_return=return_cut is not None, return_cutpoint=return_cut, boundary=boundary,
        registers=r, post_cells={str(k): v for k, v in sorted(m.items())},
        changed_cells={str(k): v for k, v in sorted(m.items()) if cells.get(k) != v},
        trace=trace, memory_events=events, retired_spans=retired, known_retired_alias_registers=aliases,
        complete_owner_pin=dict(address=a, bytes=82, sha256=hashlib.sha256(layout.initializer_data).hexdigest()),
        ordered_shared_state=True, fabricated_callee_effects=False, fabricated_saved_words=False,
        output_initialization_assumed=False, role_separation_assumed=False, ABI_preservation_assumed=False,
        actual_reaching_state_proved=False, Sqrt_effect_proved=False, physical_access_proved=False,
        actual_heap_or_SP_proved=False, actual_lifetime_proved=False, actual_code_execution_proved=False,
        actual_termination_proved=False, flags_proved=False, returns_to_root=False, full_CFG_closed=False,
        source_or_ELF_admission=False, native_admission=False,
        obligations=[dict(id=k, proved=False, text=v) for k, v in (
            ('entry', 'This explicit state must be the actual initializer entry at the selected motion BL. No post-Sqrt registers, memory, ABI survival or result is derived here.'),
            ('access', 'Every common-base access needs real live permitted memory, complete protected caller/code ranges and noninterference. Numeric pointer coordinates grant no physical access or extent.'),
            ('aliases', 'Record, incoming fifth word and private saved words may overlap. Consumers must use the resulting byte state and actual restored words, not presumed untouched registers.'),
            ('lifetime', 'Only the real PUSH reactivates its saved-word frame. Incoming retired bytes remain inaccessible; all ambient aliases and actual lifetimes require justification.'),
            ('continuation', 'The observed BX word identifies an unexecuted caller continuation. Executable authority, actual reaching, remaining caller effects, all paths and native admission stay open.'),
        )])
