"""Actual count12 scheduler entry and allocator bytes up to installed code.

Frozen complete owner identities are reused, not their count92 state relation.
All executed saves, fields, output slots and returns share one byte map. No
allocator ABI snapshot or post-Sqrt state is supplied. An optional authenticated
zero12 certificate composes its conditional effect, retaining every premise.
"""
from dataclasses import dataclass
import hashlib
import json

import scheduler_coordinate_common_state as coordinate
import scheduler_allocator_state as state
import scheduler_copy_state as words

SELECTOR = 'conditional-small-scheduler-entry-byte-state-v1'
CALLBACK = bytes.fromhex('70b5061c0d1c141c2988012938d0012902dc002908d033e08020400081420bd0013081421cd02be069688878a070486860600888208023e0f8f706fe000600281ed16268002a08d0a078002805d0011c101c321cf7f78afda060288801300ee02088002801d001382080a068f7f7a4fda060002804d12088002801d102202880002070bc02bc0847')


@dataclass(frozen=True)
class Layout:
    coordinate: coordinate.Layout
    scheduler: state.Layout
    callback: int
    callback_data: bytes
    zero_pointer_data: bytes


def _validate(layout):
    if type(layout) is not Layout or type(layout.scheduler) is not state.Layout:
        raise ValueError('complete coordinate and scheduler layouts required')
    cf = coordinate._validate(layout.coordinate)
    s = layout.scheduler
    data = state._identity(s.address, s.allocator, s.callback_thunk)
    if hashlib.sha256(data).hexdigest() != s.sha256:
        raise ValueError('complete scheduler identity changed')
    if cf['prior']['calls'][layout.coordinate.helper.helper+266] != s.address:
        raise ValueError('actual equality scheduler call identity differs')
    if type(layout.callback) is not int or layout.callback % 2 or not 0 <= layout.callback <= 2**32-136:
        raise ValueError('complete aligned136B callback required')
    if int.from_bytes(layout.coordinate.helper.helper_data[288:292], 'little') != layout.callback | 1:
        raise ValueError('actual helper callback literal differs')
    if type(layout.callback_data) is not bytes or len(layout.callback_data) != 136:
        raise ValueError('complete callback body required')
    expected = bytearray(CALLBACK)
    for offset in (56, 84, 108):
        target = coordinate.shapes._call(layout.callback_data, layout.callback, offset)
        if target is None:
            raise ValueError('callback actual nested call encoding differs')
        expected[offset:offset+4] = state.remove._bl(layout.callback+offset, target)
    if layout.callback_data != bytes(expected):
        raise ValueError('complete DFF04 callback shape differs')
    if type(layout.zero_pointer_data) is not bytes or len(layout.zero_pointer_data) != 4:
        raise ValueError('actual literal-point four-byte ROM contents required')
    w, a = s.allocator, s.allocator.allocator
    i, m = a.insertion, a.insertion.median
    owners = {
        s.address: data,
        w.address: state.wrapper._identity(w.address, a),
        a.address: state.split._identity(a.address, i, a.thunk, a.pointer_literal),
        i.address: state.split.insert.HEAD+state.remove._bl(i.address+22, i.search.address)+state.split.insert.MIDDLE+
                   state.remove._bl(i.address+138, m.median)+state.split.insert.TAIL,
        i.search.address: state.split.insert.search.SHAPE,
        m.removal: state.remove.REMOVE_HEAD+state.remove._bl(m.removal+124, m.median)+state.remove.REMOVE_TAIL,
        m.median: state.remove.MEDIAN,
        a.thunk: b'\x10\x47', s.callback_thunk: b'\x18\x47', layout.callback: layout.callback_data,
    }
    c = layout.coordinate
    spans = [(p, p+len(b)) for p, b in owners.items()] + [
        (c.transform, c.transform+72), (c.predicate, c.predicate+36), (c.motion, c.motion+256),
        (c.helper.helper, c.helper.helper+292), (c.helper.getter, c.helper.getter+12),
        (c.helper.identity, c.helper.identity+2), (c.helper.coordinates, c.helper.coordinates+40)]
    spans.sort()
    if len(owners) != 10 or any(x[1] > y[0] for x, y in zip(spans, spans[1:])):
        raise ValueError('complete scheduler/allocator/callback owners overlap')
    if any(lo < a.pointer_literal+4 and hi > a.pointer_literal for lo, hi in spans):
        raise ValueError('external zero pointer word overlaps executable owner')
    return owners


def bind(coordinate_layout, scheduler_layout, callback_data, callback_address,
         zero_pointer_data, *, selector):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit small scheduler selector required')
    result = Layout(coordinate_layout, scheduler_layout, callback_address, callback_data, zero_pointer_data)
    _validate(result)
    return result


def continue_from_076(layout, arena_base, report, *, selector, protected_spans=(), max_steps=1024,
                      zero12_receipt=None):
    """Consume one new076 equality report; never invoke the frozen producer."""
    _validate(layout)
    c, s = layout.coordinate, layout.scheduler.address
    if type(report) is not dict or report.get('schema') != coordinate.SELECTOR or report.get('starts_at') != c.transform or \
            report.get('conditional_returns') != dict(transform=True, coordinate=True, predicate=True, motion_early=True) or \
            report.get('reaches_helper_scheduler_call') is not True:
        raise ValueError('076 equality continuation report required; Sqrt path remains refused')
    cut = report.get('nested_call_cutpoint')
    r = report.get('registers')
    e = report.get('helper_entry_SP')
    if type(e) is not int or type(r) is not dict or set(r) != set(range(15)) or \
            type(cut) is not dict or cut.get('call_site') != c.helper.helper+266 or cut.get('target') != s or \
            cut.get('callee_executed') is not False or report.get('boundary', {}).get('site') != s or \
            cut.get('SP') != e-72 or r[13] != words._pointer(e-72) or cut.get('return_word') != r[14] or \
            cut.get('register_arguments') != {i:r[i] for i in range(4)}:
        raise ValueError('076 real scheduler entry/callsite/register context differs')
    return derive(layout, arena_base, {int(k):v for k,v in report['post_cells'].items()}, r,
        selector=selector, protected_spans=protected_spans,
        retired_spans=tuple(tuple(v) for v in report['retired_spans']), max_steps=max_steps,
        zero12_receipt=zero12_receipt)


def derive(layout, arena_base, cells, registers, *, selector, protected_spans=(), retired_spans=(), max_steps=1024,
           zero12_receipt=None):
    """New conditional exact entry state; no claim that real memory reaches it."""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit small scheduler selector required')
    if zero12_receipt is not None and type(zero12_receipt) is not bytes:
        raise ValueError('optional retained zero12 receipt must be exact bytes')
    owners = _validate(layout)
    if type(arena_base) is not int or arena_base % 4 or not 0 <= arena_base < 2**32 or \
            type(registers) is not dict or set(registers) != set(range(15)) or any(
                type(k) is not int or not words._word(v) for k,v in registers.items()) or \
            type(cells) is not dict or len(cells) > 4096 or any(type(k) is not int or
                not -(2**31) <= k < 2**31 or not state._cell(v) for k,v in cells.items()) or \
            type(max_steps) is not int or not 1 <= max_steps <= 1024:
        raise ValueError('bounded numeric base/register/byte state and step limit required')
    for spans in (protected_spans, retired_spans):
        if type(spans) is not tuple or len(spans) > 40 or any(type(s) is not tuple or len(s) != 2 or
                any(type(v) is not int for v in s) or not -(2**31) <= s[0] < s[1] <= 2**31 for s in spans):
            raise ValueError('bounded protection/lifetime intervals required')
    s, a, w = layout.scheduler.address, layout.scheduler.allocator.allocator, layout.scheduler.allocator.address
    r, memory, retired = dict(registers), dict(cells), list(retired_spans)
    pc, flags = s, None
    trace, events, stack, returns, certificates = [], [], [], [], []
    boundary = cut = None
    entry_sp = None
    # Only the actual pre-zero prefix is supported. Neither retained zero92
    # nor a fabricated40-byte effect can jump control into the copy/callback.
    executable = {s: owners[s][:52], w: owners[w], a.address: owners[a.address],
                  a.insertion.address: owners[a.insertion.address],
                  a.insertion.search.address: owners[a.insertion.search.address],
                  a.insertion.median.removal: owners[a.insertion.median.removal],
                  a.insertion.median.median: owners[a.insertion.median.median], a.thunk: owners[a.thunk]}
    starts = {}
    for owner, data in executable.items():
        pos, sites = 0, set()
        while pos < len(data):
            if owner == a.address and pos == 196:
                pos += 4
                continue
            sites.add(owner+pos)
            op = int.from_bytes(data[pos:pos+2], 'little')
            pos += 4 if op & 0xf800 == 0xf000 else 2
        starts[owner] = sites

    def stop(reason, at=None, **extra):
        error = state.remove._Boundary(pc, reason, at)
        error.report.update(extra)
        raise error

    def physical(at, width, write=False, allocating=False):
        if not -(2**31) <= at <= 2**31-width or not 0 <= arena_base+at <= 2**32-width:
            stop('numeric common-base access/frame wraps', at)
        if width in (2,4) and at % width:
            stop('unaligned byte-state access', at)
        if not allocating and any(at < hi and at+width > lo for lo,hi in retired):
            stop('access overlaps retired private bytes', at)
        if write and any(at < hi and at+width > lo for lo,hi in protected_spans):
            stop('actual write overlaps protected bytes', at)

    def address(reg):
        value = words.observe(r[reg])
        if value['kind'] != 'base-plus':
            stop('address R'+str(reg)+' lacks intact common-base provenance')
        return value['coordinate']

    def numeric(value, pointers=False):
        origin = words.observe(value)
        if origin['kind'] == 'constant':
            return origin['value']
        if pointers and origin['kind'] == 'base-plus':
            result = arena_base+origin['coordinate']
            if 0 <= result < 2**32:
                return result
        stop('scalar/control observation has opaque or unsupported pointer bits')

    def load(at, width):
        physical(at, width)
        value = tuple(memory.get(at+i) for i in range(width))
        if any(v is None for v in value):
            stop('read lacks reaching byte origins', at)
        if width < 4 and any(type(v) is not int for v in value):
            stop('scalar field observes opaque or pointer bytes', at)
        events.append(dict(site=pc, operation='read'+str(width*8), coordinate=at, bytes=value))
        return value if width == 4 else value+(0,)*(4-width)

    def store(at, value):
        physical(at, len(value), True)
        if len(value) < 4 and any(type(v) is not int for v in value):
            stop('narrow write contains unknown scalar bits', at)
        if len(set(memory) | set(range(at, at+len(value)))) > 4096:
            stop('byte state exceeds4096 cells', at)
        memory.update({at+i:v for i,v in enumerate(value)})
        events.append(dict(site=pc, operation='write'+str(len(value)*8), coordinate=at, bytes=value))

    def activate(lo, hi, forget=False):
        nonlocal retired
        physical(lo, hi-lo, allocating=True)
        if lo % 4 or hi % 4:
            stop('unaligned stack allocation', lo)
        if len(set(memory) | set(range(lo,hi))) > 4096:
            stop('frame byte state exceeds4096 cells', lo)
        live = []
        for x,y in retired:
            if hi <= x or lo >= y:
                live.append((x,y))
            else:
                if x < lo:live.append((x,lo))
                if hi < y:live.append((hi,y))
        retired = live
        if forget:
            names = {v[1] for v in [*memory.values(), *(v for word in r.values() for v in word)]
                     if type(v) is tuple and v[0] == 'opaque-byte'}
            name, n = 'small scheduler local', 0
            while name in names:
                n += 1
                name = 'small scheduler local:'+str(n)
            for at in range(lo,hi):memory[at] = ('opaque-byte',name,at-lo)
        events.append(dict(site=pc, operation='allocate-frame', coordinates=[lo,hi], initialization_granted=False))

    def retire(lo,hi):
        retired.append((lo,hi))
        events.append(dict(site=pc, operation='retire-frame', coordinates=[lo,hi]))

    def arithmetic(left, right, subtract=False):
        l, q = words.observe(left), words.observe(right)
        if l['kind'] == 'base-plus' and q['kind'] == 'base-plus' and subtract:
            return words._constant((l['coordinate']-q['coordinate']) & 0xffffffff)
        if not subtract and l['kind'] == 'constant' and q['kind'] == 'base-plus':
            left, right, l, q = right, left, q, l
        if l['kind'] == 'base-plus' and q['kind'] == 'constant':
            delta = q['value'] if q['value'] < 2**31 else q['value']-2**32
            value = l['coordinate'] + (-delta if subtract else delta)
            if not -(2**31) <= value < 2**31 or not 0 <= arena_base+value < 2**32:
                stop('pointer arithmetic wraps common-base coordinate')
            return words._pointer(value)
        return words._constant((numeric(left) + (-numeric(right) if subtract else numeric(right))) & 0xffffffff)

    def compare(left, right):
        x, y = numeric(left, True), numeric(right, True)
        result = (x-y) & 0xffffffff
        return bool(result & 0x80000000), result == 0, x >= y, bool((x^y) & (x^result) & 0x80000000)

    def compose_zero12(target):
        if zero12_receipt is None or r[1] != words._constant(12):
            return None
        if hashlib.sha256(zero12_receipt).hexdigest() != state.split.ZERO12_SHA256:
            stop('retained zero12 certificate bytes changed')
        rule = json.loads(zero12_receipt)
        if target != rule['entry'] | 1:
            stop('actual R2 target differs from retained zero12 entry')
        top, dest = address(13), address(0)
        physical(top-4,4,True,True)
        physical(dest,12,True)
        physical(dest+12,1)
        if dest < top and dest+12 > top-4:
            stop('zero12 destination overlaps its actual private return save',dest)
        if len(set(memory) | set(range(dest,dest+12)) | set(range(top-4,top))) > 4096:
            stop('zero12 composed state exceeds4096 cells',dest)
        if not stack or r[14] != words._constant(stack[-1][1] | 1):
            stop('zero12 LR differs from actual nested BL continuation')
        case = rule['alignment_cases'][(arena_base+dest) & 3]
        incoming_lr, event_start = r[14], len(events)
        activate(top-4,top)
        r[13] = words._pointer(top-4)
        store(top-4,incoming_lr)
        for kind, offset, width in case['writes']:
            if kind == 'destination':store(dest+offset,(0,)*width)
        restored_lr = load(top-4,4)
        if restored_lr != incoming_lr:
            stop('zero12 actual saved return was overwritten')
        r[0], r[1], r[2], r[13] = restored_lr, words._constant(0), words._pointer(dest+12), words._pointer(top)
        retire(top-4,top)
        for event in events[event_start:]:
            event.update(effect_origin='retained-zero12-certificate',site_kind='certificate-composition-boundary')
        frame = stack.pop()
        certificates.append(dict(receipt_sha256=state.split.ZERO12_SHA256,call_site=frame[1]-4,
            destination=dest,SP=top,count=12,certified_trace=case['trace'],
            unproved_premises=rule['unproved_premises'],actual_installed_identity_proved=False))
        returns.append(dict(owner=target & ~1,site=pc,target=frame[1],SP=top,entry_SP=frame[2],
                            conditional_retained_zero12_effect=True))
        return frame[1]

    try:
        entry_sp = address(13)
        if entry_sp % 4 or r[2] != words._constant(12) or r[1] != words._constant(layout.callback|1) or \
                r[3] != words._pointer(entry_sp+4) or \
                r[14] != words._constant((layout.coordinate.helper.helper+270)|1):
            stop('entry differs from actual count12 callback/descriptor/SP/LR interface')
        for _ in range(max_steps):
            owner = next((x for x,data in executable.items() if x <= pc < x+len(data)), None)
            if owner is None or pc not in starts[owner]:
                stop('control outside supported complete-owner instruction boundaries')
            data, off = owners[owner], pc-owner
            trace.append(pc)
            op, nxt = int.from_bytes(data[off:off+2],'little'), pc+2
            if op & 0xfe00 == 0xb400:
                selected = [i for i in range(8) if op & (1<<i)] + ([14] if op & 256 else [])
                top = address(13)
                lo = top-4*len(selected)
                physical(lo, top-lo, True, True)
                values = [r[i] for i in selected]
                activate(lo,top)
                for i,value in enumerate(values):store(lo+4*i,value)
                r[13] = words._pointer(lo)
            elif op & 0xff00 == 0xbc00:
                selected = [i for i in range(8) if op & (1<<i)]
                lo = address(13)
                values = [load(lo+4*i,4) for i in range(len(selected))]
                for i,value in zip(selected,values):r[i] = value
                r[13] = words._pointer(lo+4*len(selected))
                retire(lo,lo+4*len(selected))
            elif op & 0xff00 == 0xb000:
                lo = address(13)
                hi = lo + (-1 if op & 128 else 1)*4*(op & 127)
                if op & 128:activate(hi,lo,True)
                else:
                    physical(hi,1)
                    retire(lo,hi)
                r[13] = words._pointer(hi)
            elif op & 0xff00 == 0x4600:
                r[(op & 7)|((op>>4)&8)] = r[(op>>3)&15]
            elif op & 0xf800 == 0x2000:
                r[(op>>8)&7] = words._constant(op & 255)
                flags = None
            elif op & 0xf800 in (0x0000,0x0800,0x1000):
                value, shift, kind = numeric(r[(op>>3)&7]), (op>>6)&31, op & 0xf800
                if kind == 0:value <<= shift
                elif kind == 0x0800:value >>= shift or 32
                else:value = (value-2**32 if value & 0x80000000 else value) >> (shift or 32)
                r[op & 7] = words._constant(value & 0xffffffff)
                flags = None
            elif op & 0xf800 == 0x1800:
                right = words._constant((op>>6)&7) if op & 0x400 else r[(op>>6)&7]
                if op & 0x400 and not op & 0x200 and (op>>6)&7 == 0:
                    r[op & 7] = r[(op>>3)&7]
                else:r[op & 7] = arithmetic(r[(op>>3)&7],right,bool(op & 0x200))
                flags = None
            elif op & 0xf800 in (0x3000,0x3800):
                reg = (op>>8)&7
                r[reg] = arithmetic(r[reg],words._constant(op & 255),op & 0xf800 == 0x3800)
                flags = None
            elif op & 0xffc0 in (0x4000,0x4300):
                x,y = numeric(r[op & 7]),numeric(r[(op>>3)&7])
                r[op & 7] = words._constant(x & y if op & 0xffc0 == 0x4000 else x | y)
                flags = None
            elif op & 0xffc0 == 0x4240:
                r[op & 7] = words._constant((-numeric(r[(op>>3)&7])) & 0xffffffff)
                flags = None
            elif op & 0xf800 == 0x2800:
                flags = compare(r[(op>>8)&7],words._constant(op & 255))
            elif op & 0xffc0 == 0x4280:
                flags = compare(r[op & 7],r[(op>>3)&7])
            elif op & 0xf000 == 0xd000:
                if flags is None:stop('branch lacks an exact comparison')
                n,z,c,v = flags
                conditions = (z,not z,c,not c,n,not n,v,not v,c and not z,not c or z,n==v,n!=v,not z and n==v,z or n!=v)
                kind = (op>>8)&15
                if kind >= len(conditions):stop('unsupported conditional instruction')
                if conditions[kind]:
                    disp = op & 255
                    nxt = pc+4+2*(disp-256 if disp & 128 else disp)
            elif op & 0xf800 == 0xe000:
                disp = op & 2047
                nxt = pc+4+2*(disp-2048 if disp & 1024 else disp)
            elif op & 0xf800 == 0x4800:
                at = ((pc+4)&~3)+4*(op & 255)
                if (owner,at-owner) not in ((s,100),(a.address,196)):
                    stop('literal outside retained complete-owner pools')
                value = tuple(data[at-owner:at-owner+4])
                r[(op>>8)&7] = value
                events.append(dict(site=pc,operation='read-ROM32',address=at,bytes=value))
            elif op & 0xf800 == 0xa800:
                value = address(13)+4*(op & 255)
                physical(value,1)
                r[(op>>8)&7] = words._pointer(value)
            elif op & 0xf000 == 0x9000:
                at, reg = address(13)+4*(op & 255),(op>>8)&7
                if op & 0x800:r[reg] = load(at,4)
                else:store(at,r[reg])
            elif op & 0xf000 in (0x6000,0x7000,0x8000):
                group = op & 0xf000
                width = 4 if group == 0x6000 else 1 if group == 0x7000 else 2
                base,reg,disp = (op>>3)&7,op & 7,width*((op>>6)&31)
                if pc in (s+42,a.address+92):
                    if op != 0x6802 or r[base] != words._constant(a.pointer_literal):
                        stop('actual zero-pointer literal load identity changed')
                    r[reg] = tuple(layout.zero_pointer_data)
                    events.append(dict(site=pc,operation='read-ROM32',address=a.pointer_literal,bytes=r[reg]))
                elif op & 0x800:r[reg] = load(address(base)+disp,width)
                else:store(address(base)+disp,r[reg][:width])
            elif op & 0xf800 == 0xf000:
                target = coordinate.shapes._call(data,owner,off)
                r[14] = words._constant((pc+4)|1)
                events.append(dict(site=pc,operation='ordinary-call',target=target,SP=address(13),return_word=r[14]))
                if target not in executable:
                    cut = dict(call_site=pc,target=target,SP=address(13),return_word=r[14],register_arguments={i:r[i] for i in range(4)},callee_executed=False)
                    pc = target
                    stop('actual callee outside the closed shared-byte owner set',cutpoint='callee-entry')
                stack.append((target,pc+4,address(13)))
                nxt = target
            elif op & 0xff87 == 0x4700:
                reg = (op>>3)&15
                target = numeric(r[reg])
                if owner == a.thunk:
                    resumed = compose_zero12(target)
                    if resumed is not None:
                        flags = None
                        pc = resumed
                        continue
                    cut = dict(call_site=stack[-1][1]-4,thunk=owner,target_word=target,target=target & ~1,
                        SP=address(13),return_word=r[14],register_arguments={i:r[i] for i in range(4)},
                        callee_executed=False,installed_identity_proved=False)
                    stop('actual R2 installed-code effect remains unproved',cutpoint='BX R2',target_word=target)
                if not stack or stack[-1][0] != owner or target != stack[-1][1]|1:
                    stop('actual popped return word differs from nested BL continuation')
                frame = stack.pop()
                nxt = frame[1]
                returns.append(dict(owner=owner,site=pc,target=nxt,SP=address(13),entry_SP=frame[2]))
                events.append(dict(site=pc,operation='bx-known-continuation',target=nxt,executable_authority_proved=False))
            else:
                stop('instruction outside bounded shared-byte decoder')
            pc = nxt
        else:
            stop('explicit instruction bound exhausted; no termination claim')
    except state.remove._Boundary as error:
        boundary = error.report
    stale = {}
    for reg,value in r.items():
        value = words.observe(value)
        if value['kind'] == 'base-plus' and any(lo <= value['coordinate'] < hi for lo,hi in retired):
            stale[str(reg)] = value['coordinate']
    return dict(schema=SELECTOR, starts_at=s, entry_SP=entry_sp, boundary=boundary,nested_call_cutpoint=cut,
        reaches_unproved_installed_call=cut is not None and cut.get('thunk') == a.thunk,
        allocation_count=40 if s+30 in trace else None,
        registers=r,post_cells={str(k):v for k,v in sorted(memory.items())},
        changed_cells={str(k):v for k,v in sorted(memory.items()) if cells.get(k)!=v},
        changed_cells_include_explicit_forgetting=True,trace=trace,memory_events=events,actual_returns=returns,
        retained_zero12_compositions=certificates,
        retired_spans=retired,known_retired_alias_registers=stale,
        complete_owner_pins=[dict(address=a,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for a,b in sorted(owners.items())],
        fabricated_callee_effects=False,fabricated_saved_words=False,ABI_preservation_assumed=False,
        old_count92_effect_used=False,callback_executed=False,Sqrt_effect_proved=False,
        actual_reaching_state_proved=False,actual_heap_or_SP_proved=False,physical_access_proved=False,
        actual_lifetime_proved=False,actual_code_execution_proved=False,actual_termination_proved=False,
        full_CFG_closed=False,returns_to_root=False,source_or_ELF_admission=False,native_admission=False,
        obligations=[dict(id=k,proved=False,text=v) for k,v in (
            ('entry','The supplied076 equality registers and bytes must equal the actual scheduler entry; adapter shape checks do not establish actual reaching or root transport.'),
            ('memory','Every actual common-base byte access must be live and permitted, with complete caller/code protections, no wrap and no interference. Numeric coordinates are not allocation/access authority.'),
            ('saves','All allocator saves and output slots are materialized. Actual stores may alias them; later reloads and return guards observe their resulting words without ABI snapshots.'),
            ('installed','The actual four ROM bytes identify an R2 word, not installed executable code. Optional retained zero12 composition remains conditional on every listed certificate premise. No zero40 or zero92 effect is supplied.'),
            ('continuation','The scheduler copy, actual DFF04 phase0 callback, return/lifetime and remaining caller paths require new justified effects after the installed-code boundary.'),
        )])
