"""Conditional count40 image, scheduler copy and real callback byte relation.

The complete176B image is authenticated source data, never installation authority.
A single common-base byte state observes aliases across zero, saves, list fields,
descriptor transfers and callback. Only executed instructions supply effects.
"""
from dataclasses import dataclass
import hashlib

import scheduler_small_entry_state as small

state, words = small.state, small.words
SELECTOR = 'conditional-scheduler-zero40-common-byte-state-v1'
PHASE0_TRANSPORT = 'scheduler-phase0-opaque-payload-transport-v1'
IMAGE_SHA256 = 'ce26dd719323641c1c4cbfa501368306ce6e31e193dabce7e84c7067f7590130'
IMAGE_BASE = 0x03005e78


@dataclass(frozen=True)
class Layout:
    prior: small.Layout
    image: bytes
    image_base: int


def _validate(layout):
    if type(layout) is not Layout or type(layout.image) is not bytes or len(layout.image) != 176 or \
            hashlib.sha256(layout.image).hexdigest() != IMAGE_SHA256 or \
            type(layout.image_base) is not int or layout.image_base != IMAGE_BASE:
        raise ValueError('complete actual176B source image and installed destination required')
    owners = small._validate(layout.prior)
    if layout.prior.zero_pointer_data != (layout.image_base|1).to_bytes(4,'little'):
        raise ValueError('actual four-byte R2 literal does not identify image zero entry')
    if any(p < layout.image_base+176 and p+len(b) > layout.image_base for p,b in owners.items()):
        raise ValueError('installed image overlaps complete ROM owner')
    return owners


def bind(prior_layout, image, image_base, *, selector):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit zero40 common-byte selector required')
    result = Layout(prior_layout,image,image_base)
    _validate(result)
    return result


def _transport_selector(selector):
    if type(selector) is not str or selector != PHASE0_TRANSPORT:
        raise ValueError('opaque phase0 payloads require their explicit transport selector')


def _transport_record(layout, owners):
    cb = layout.prior.callback
    return dict(schema=PHASE0_TRANSPORT,
        complete_owner_pins=[dict(address=p,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
                             for p,b in sorted(owners.items())],
        callback_phase_condition=0, actual_phase_reaching_proved=False,
        conditional_callback_path=[cb+off for off in (
            *range(0,22,2), *range(40,56,2), *range(128,136,2))],
        ordered_payload_transfers=[dict(read_site=cb+42,write_site=cb+44,offset=2,width=1),
                                   dict(read_site=cb+46,write_site=cb+48,offset=4,width=4),
                                   dict(read_site=cb+50,write_site=cb+52,offset=0,width=2)],
        payload_values='unchanged byte origins; no scalar interpretation or initialization',
        branch_address_and_return_checks_unchanged=True,
        nested_pointer_nonescape_proved=False,
        actual_physical_access_proved=False, native_admission=False)


def phase0_transport_contract(layout, *, selector):
    """Bind the complete owners and their conditional phase0 transport sites.

    The phase must still be reached by actual execution. Payload bytes never
    become scalar or address facts, and this record supplies no call authority.
    """
    _transport_selector(selector)
    return _transport_record(layout, _validate(layout))


def continue_from_078(layout, arena_base, report, *, selector, protected_spans=(), max_steps=1024,
                      phase0_transport_policy=None):
    """Consume a supplied078 cutpoint; do not invoke its frozen producer.

    Report shape and identity checks are not authentication of actual reaching.
    The conditional caller must supply the genuine, unchanged prior byte state.
    """
    owners = _validate(layout)
    s,a = layout.prior.scheduler.address,layout.prior.scheduler.allocator.allocator
    if type(report) is not dict or report.get('schema') != small.SELECTOR or report.get('starts_at') != s or \
            report.get('allocation_count') != 40 or report.get('reaches_unproved_installed_call') is not True:
        raise ValueError('078 actual count40 cutpoint report required')
    r,e,cut = report.get('registers'),report.get('entry_SP'),report.get('nested_call_cutpoint')
    pins = [dict(address=p,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for p,b in sorted(owners.items())]
    if type(r) is not dict or set(r) != set(range(15)) or type(e) is not int or type(cut) is not dict or \
            report.get('complete_owner_pins') != pins or report.get('boundary',{}).get('site') != a.thunk or \
            cut.get('call_site') != s+48 or cut.get('thunk') != a.thunk or cut.get('target') != layout.image_base or \
            cut.get('target_word') != layout.image_base|1 or cut.get('callee_executed') is not False or \
            cut.get('SP') != e-56 or cut.get('return_word') != r[14] or \
            cut.get('register_arguments') != {i:r[i] for i in range(4)}:
        raise ValueError('078 original complete-owner/count40 interface differs')
    result = derive(layout,arena_base,{int(k):v for k,v in report['post_cells'].items()},r,e,
        selector=selector,protected_spans=protected_spans,
        retired_spans=tuple(tuple(v) for v in report['retired_spans']),max_steps=max_steps,
        phase0_transport_policy=phase0_transport_policy)
    result['inherited_078_obligations'] = report.get('obligations',[])
    result['inherited_zero12_compositions'] = report.get('retained_zero12_compositions',[])
    result['actual_078_reaching_authentication_proved'] = False
    return result


def derive(layout, arena_base, cells, registers, scheduler_entry_sp, *, selector,
           protected_spans=(), retired_spans=(), max_steps=1024, phase0_transport_policy=None):
    """Execute a new conditional count40 reaching state, stopping at exact gaps."""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit zero40 common-byte selector required')
    owners = _validate(layout)
    transport = None
    if phase0_transport_policy is not None:
        _transport_selector(phase0_transport_policy)
        transport = _transport_record(layout, owners)
    if type(arena_base) is not int or arena_base % 4 or not 0 <= arena_base < 2**32 or \
            type(scheduler_entry_sp) is not int or not -(2**31) <= scheduler_entry_sp < 2**31 or \
            type(registers) is not dict or set(registers) != set(range(15)) or any(
                type(k) is not int or not words._word(v) for k,v in registers.items()) or \
            type(cells) is not dict or len(cells) > 4096 or any(type(k) is not int or
                not -(2**31) <= k < 2**31 or not state._cell(v) for k,v in cells.items()) or \
            type(max_steps) is not int or not 1 <= max_steps <= 1024:
        raise ValueError('bounded exact base/register/cell/SP/step inputs required')
    for spans in (protected_spans,retired_spans):
        if type(spans) is not tuple or len(spans) > 40 or any(type(s) is not tuple or len(s) != 2 or
                any(type(v) is not int for v in s) or not -(2**31) <= s[0] < s[1] <= 2**31 for s in spans):
            raise ValueError('bounded explicit protection/lifetime intervals required')
    prior = layout.prior
    s, cb, z = prior.scheduler.address, prior.callback, layout.image_base
    thunk, cbthunk = prior.scheduler.allocator.allocator.thunk, prior.scheduler.callback_thunk
    r,memory,retired = dict(registers),dict(cells),list(retired_spans)
    e,pc,flags = scheduler_entry_sp,thunk,None
    boundary = cut = None
    trace,events,returns = [],[],[]
    payload_events = []
    zero_returned = callback_entered = callback_returned = scheduler_returned = False
    callback_phase = None
    cb_entry_sp = None
    expected_return = (prior.coordinate.helper.helper+270)|1
    executable = {thunk:owners[thunk],cbthunk:owners[cbthunk],z:layout.image[:50],s:owners[s],cb:owners[cb]}
    starts = {}
    for owner,data in executable.items():
        pos,sites = (52 if owner == s else 0),set()
        while pos < len(data):
            if owner == s and pos == 98:
                pos = 104
                continue
            sites.add(owner+pos)
            op = int.from_bytes(data[pos:pos+2],'little')
            pos += 4 if op & 0xf800 == 0xf000 else 2
        starts[owner] = sites
    immutable = [(p,p+len(b)) for p,b in owners.items()]+[(z,z+len(layout.image))]

    def stop(reason, at=None, **extra):
        error = state.remove._Boundary(pc,reason,at)
        error.report.update(extra)
        raise error

    def physical(at,width,write=False,allocating=False):
        if not -(2**31) <= at <= 2**31-width or not 0 <= arena_base+at <= 2**32-width:
            stop('numeric common-base access/frame wraps',at)
        if width in (2,4) and at % width:
            stop('unaligned byte-state access',at)
        if not allocating and any(at < hi and at+width > lo for lo,hi in retired):
            stop('access overlaps retired private bytes',at)
        if write and any(at < hi and at+width > lo for lo,hi in protected_spans):
            stop('actual write overlaps protected bytes',at)
        if write and any(arena_base+at < hi and arena_base+at+width > lo for lo,hi in immutable):
            stop('actual write overlaps assumed immutable executable bytes',at)

    def address(reg):
        value = words.observe(r[reg])
        if value['kind'] != 'base-plus':
            stop('address R'+str(reg)+' lacks intact common-base provenance')
        return value['coordinate']

    def numeric(word,pointers=False):
        value = words.observe(word)
        if value['kind'] == 'constant':return value['value']
        if pointers and value['kind'] == 'base-plus' and 0 <= arena_base+value['coordinate'] < 2**32:
            return arena_base+value['coordinate']
        stop('scalar/control observation has opaque or unsupported pointer bits')

    def load(at,width):
        physical(at,width)
        value = tuple(memory.get(at+i) for i in range(width))
        if any(v is None for v in value):stop('read lacks reaching byte origins',at)
        if width < 4 and any(type(v) is not int for v in value):
            if transport is None or (pc,width) not in ((cb+42,1),(cb+50,2)):
                stop('scalar field observes opaque or pointer bytes',at)
            payload_events.append(dict(site=pc,operation='read',coordinate=at,width=width,bytes=value))
        events.append(dict(site=pc,operation='read'+str(width*8),coordinate=at,bytes=value))
        return value+(0,)*(4-width)

    def store(at,value):
        physical(at,len(value),True)
        if len(value)<4 and any(type(v) is not int for v in value):
            if transport is None or (pc,len(value)) not in ((cb+44,1),(cb+52,2)):
                stop('narrow write contains unknown scalar bits',at)
            payload_events.append(dict(site=pc,operation='write',coordinate=at,width=len(value),bytes=value))
        if len(set(memory)|set(range(at,at+len(value)))) > 4096:
            stop('byte state exceeds4096 cells',at)
        memory.update({at+i:v for i,v in enumerate(value)})
        events.append(dict(site=pc,operation='write'+str(len(value)*8),coordinate=at,bytes=value))

    def activate(lo,hi):
        nonlocal retired
        physical(lo,hi-lo,allocating=True)
        if lo % 4 or hi % 4:stop('unaligned actual stack push',lo)
        live = []
        for x,y in retired:
            if hi <= x or lo >= y:live.append((x,y))
            else:
                if x < lo:live.append((x,lo))
                if hi < y:live.append((hi,y))
        retired = live
        events.append(dict(site=pc,operation='allocate-frame',coordinates=[lo,hi],initialization_granted=False))

    def retire(lo,hi):
        retired.append((lo,hi))
        events.append(dict(site=pc,operation='retire-frame',coordinates=[lo,hi]))

    def arithmetic(left,right,subtract=False):
        x,y = words.observe(left),words.observe(right)
        if x['kind'] == 'base-plus' and y['kind'] == 'constant':
            delta = y['value'] if y['value'] < 2**31 else y['value']-2**32
            at = x['coordinate']+(-delta if subtract else delta)
            if not -(2**31) <= at < 2**31 or not 0 <= arena_base+at < 2**32:
                stop('pointer arithmetic wraps common-base coordinate')
            return words._pointer(at)
        return words._constant((numeric(left)+(-numeric(right) if subtract else numeric(right))) & 0xffffffff)

    def compare(left,right):
        x,y = numeric(left,True),numeric(right,True)
        v = (x-y)&0xffffffff
        return bool(v&0x80000000),v==0,x>=y,bool((x^y)&(x^v)&0x80000000)

    try:
        if e%4 or r[13] != words._pointer(e-56) or r[14] != words._constant((s+52)|1) or \
                r[0] != r[7] or r[1] != words._constant(40) or r[4] != words._constant(40) or \
                r[2] != words._constant(z|1) or r[8] != words._constant(cb|1) or r[9] != words._pointer(e+4):
            stop('entry differs from real078 count40 register/frame/return interface')
        for _ in range(max_steps):
            owner = next((p for p,b in executable.items() if p<=pc<p+len(b)),None)
            if owner is None or pc not in starts[owner]:
                stop('control outside supported complete-owner instruction boundaries')
            data,off = executable[owner],pc-owner
            op,nxt = int.from_bytes(data[off:off+2],'little'),pc+2
            trace.append(pc)
            if op & 0xfe00 == 0xb400:
                selected = [i for i in range(8) if op & (1<<i)]+([14] if op&256 else [])
                top = address(13);lo = top-4*len(selected)
                values = [r[i] for i in selected]
                physical(lo,top-lo,True,True);activate(lo,top)
                for i,value in enumerate(values):store(lo+4*i,value)
                r[13] = words._pointer(lo)
            elif op & 0xff00 == 0xbc00:
                selected = [i for i in range(8) if op & (1<<i)];lo = address(13)
                values = [load(lo+4*i,4) for i in range(len(selected))]
                for i,value in zip(selected,values):r[i] = value
                r[13] = arithmetic(r[13],words._constant(4*len(selected)));retire(lo,lo+4*len(selected))
            elif op & 0xff00 == 0xb000:
                if op&128:stop('unexpected new local-frame allocation')
                lo = address(13);hi = lo+4*(op&127)
                physical(hi,1);retire(lo,hi);r[13] = words._pointer(hi)
            elif op & 0xff00 == 0x4600:
                r[(op&7)|((op>>4)&8)] = r[(op>>3)&15]
            elif op & 0xf800 == 0x2000:
                r[(op>>8)&7] = words._constant(op&255);flags = None
            elif op & 0xf800 == 0x0000:
                r[op&7] = words._constant((numeric(r[(op>>3)&7])<<((op>>6)&31))&0xffffffff);flags = None
            elif op & 0xf800 == 0x1800:
                right = words._constant((op>>6)&7) if op&0x400 else r[(op>>6)&7]
                if op&0x400 and not op&0x200 and (op>>6)&7 == 0:r[op&7] = r[(op>>3)&7]
                else:r[op&7] = arithmetic(r[(op>>3)&7],right,bool(op&0x200))
                flags = None
            elif op & 0xf800 in (0x3000,0x3800):
                rd = (op>>8)&7
                r[rd] = arithmetic(r[rd],words._constant(op&255),op&0xf800==0x3800);flags = None
            elif op & 0xffc0 == 0x4000:
                r[op&7] = words._constant(numeric(r[op&7],True)&numeric(r[(op>>3)&7],True));flags = None
            elif op & 0xf800 == 0x2800:flags = compare(r[(op>>8)&7],words._constant(op&255))
            elif op & 0xffc0 == 0x4280:flags = compare(r[op&7],r[(op>>3)&7])
            elif op & 0xf000 == 0xd000:
                if flags is None:stop('branch lacks exact preceding comparison')
                n,zf,c,v = flags
                conditions = (zf,not zf,c,not c,n,not n,v,not v,c and not zf,not c or zf,n==v,n!=v,not zf and n==v,zf or n!=v)
                kind = (op>>8)&15
                if kind>=len(conditions):stop('unsupported conditional instruction')
                if conditions[kind]:
                    d = op&255;nxt = pc+4+2*(d-256 if d&128 else d)
            elif op & 0xf800 == 0xe000:
                d = op&2047;nxt = pc+4+2*(d-2048 if d&1024 else d)
            elif op & 0xf000 in (0x6000,0x7000,0x8000):
                width = {0x6000:4,0x7000:1,0x8000:2}[op&0xf000]
                at,rd = address((op>>3)&7)+width*((op>>6)&31),op&7
                if op&0x800:
                    r[rd] = load(at,width)
                    if pc==cb+8:callback_phase = numeric(r[rd])
                else:store(at,r[rd][:width])
            elif op & 0xf000 == 0xc000:
                rn = (op>>8)&7;selected = [i for i in range(8) if op & (1<<i)]
                if not selected or rn in selected:stop('ambiguous multiple-transfer register list')
                at = address(rn)
                if op&0x800:
                    values = [load(at+4*i,4) for i in range(len(selected))]
                    for i,value in zip(selected,values):r[i] = value
                else:
                    values = [r[i] for i in selected]
                    for i,value in enumerate(values):store(at+4*i,value)
                r[rn] = arithmetic(r[rn],words._constant(4*len(selected)))
            elif op & 0xf800 == 0xf000:
                target = small.coordinate.shapes._call(data,owner,off)
                r[14] = words._constant((pc+4)|1)
                events.append(dict(site=pc,operation='ordinary-call',target=target,SP=address(13),return_word=r[14]))
                if pc!=s+180 or target!=cbthunk:
                    cut = dict(call_site=pc,target=target,SP=address(13),return_word=r[14],register_arguments={i:r[i] for i in range(4)},callee_executed=False)
                    pc = target;stop('actual callback nested helper effect outside079',cutpoint='callee-entry')
                nxt = target
            elif op & 0xff87 == 0x4700:
                target = numeric(r[(op>>3)&15])
                if owner==thunk:
                    if target != layout.image_base|1:stop('actual R2 target differs from bound zero image')
                    nxt = layout.image_base
                elif owner==cbthunk:
                    if target != cb|1:
                        cut = dict(call_site=s+180,thunk=owner,target_word=target,target=target&~1,SP=address(13),return_word=r[14],register_arguments={i:r[i] for i in range(4)},callee_executed=False)
                        stop('reloaded callback identity differs from bound DFF04',target_word=target)
                    callback_entered=True;cb_entry_sp=address(13);nxt=cb
                else:
                    expected = (s+52)|1 if owner==layout.image_base else (s+184)|1 if owner==cb else expected_return
                    top = e-56 if owner in (layout.image_base,cb) else e
                    if target!=expected:stop('actual reloaded return differs from known continuation',target_word=target)
                    if address(13)!=top:stop('actual return SP differs from calling frame')
                    returns.append(dict(owner=owner,site=pc,target=target&~1,SP=top))
                    events.append(dict(site=pc,operation='bx-known-continuation',target=target&~1,executable_authority_proved=False))
                    if owner==layout.image_base:zero_returned=True
                    elif owner==cb:callback_returned=True
                    else:
                        scheduler_returned=True;pc=target&~1;break
                    nxt = target&~1
            else:stop('instruction outside079 exact bounded decoder',encoding=op)
            pc = nxt
        else:stop('explicit instruction bound exhausted; no termination claim')
    except state.remove._Boundary as error:
        boundary = error.report
    stale = {}
    for reg,value in r.items():
        value=words.observe(value)
        if value['kind']=='base-plus' and any(lo<=value['coordinate']<hi for lo,hi in retired):
            stale[str(reg)]=value['coordinate']
    result = dict(schema=SELECTOR,starts_at=thunk,scheduler_entry_SP=e,final_PC=pc,boundary=boundary,nested_call_cutpoint=cut,
        conditional_returns=dict(zero40=zero_returned,callback=callback_returned,scheduler=scheduler_returned),
        callback_entered=callback_entered,callback_observed_phase=callback_phase,callback_entry_SP=cb_entry_sp,
        registers=r,post_cells={str(k):v for k,v in sorted(memory.items())},
        changed_cells={str(k):v for k,v in sorted(memory.items()) if cells.get(k)!=v},
        trace=trace,memory_events=events,actual_returns=returns,retired_spans=retired,known_retired_alias_registers=stale,
        complete_owner_pins=[dict(address=p,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for p,b in sorted(owners.items())],
        image_pin=dict(address=layout.image_base,bytes=176,sha256=IMAGE_SHA256),
        executed_image_bytes=50,allocation_count=40,descriptor_bytes=28,
        fabricated_callee_effects=False,fabricated_saved_words=False,ABI_preservation_assumed=False,
        old_count92_effect_used=False,actual_reaching_state_proved=False,actual_heap_or_SP_proved=False,
        physical_access_proved=False,actual_lifetime_proved=False,actual_installed_identity_proved=False,
        actual_code_execution_proved=False,actual_termination_proved=False,full_CFG_closed=False,
        Sqrt_effect_proved=False,post_Sqrt_executed=False,returns_to_root=False,source_or_ELF_admission=False,native_admission=False,
        obligations=[dict(id=k,proved=False,text=v) for k,v in (
            ('entry','The supplied078 count40 cutpoint registers, bytes, arena base and scheduler entrySP must be actual reaching state; interface checks are conditional only.'),
            ('image','The exact176B ROM source must really be installed at03005E78 and executable/unchanged for every fetch. A source hash and ROM pointer do not prove installation or instruction execution.'),
            ('memory','Every observed read/write/save/frame byte must be live ordinary little-endian memory with physical access permission, complete caller protection and no asynchronous interference. Numeric span checks do not grant these facts.'),
            ('alias','All participating addresses/bytes must use this one complete common-base alias model. No allocator separation or fresh heap initialization is assumed; writes to known code/protected bytes are refused.'),
            ('lifetime','Stack activation/retirement represents the conditional actual PUSH/POP/local-release order; physical lifetime and absence of untracked external stale aliases remain premises.'),
            ('continuation','Only recorded bounded paths/returns are closed. Unknown callbacks, nested D8B4C/D7ABC effects, Sqrt, subsequent E03F8/root execution, fullCFG and actual termination remain outside079.'),
        )])
    if transport is not None:
        result['phase0_payload_transport'] = transport
        result['opaque_payload_events'] = payload_events
    return result
