"""Track the incoming descriptor R3 only until the allocator overwrites it.

This is an observation-prefix prerequisite, not a callee effects or native
admission certificate. Unrelated memory origins, the scheduler's R9 alias,
fresh allocator aliases and every returning-call obligation remain open.
"""
import hashlib

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_CALL, CS_GRP_JUMP
from capstone.arm import ARM_REG_R0, ARM_REG_SP

import descriptor_frame_shape_prerequisite as frames
import scheduler_allocator_state as scheduler

SELECTOR = 'scheduler-allocator-descriptor-observation-prefix-v1'
R3 = ARM_REG_R0 + 3


def _wrapper_prefix(data, address, core):
    partition = dict(code_bytes=len(data), alignment_bytes=0,
                     literal_and_table_bytes=0, alignment=[], words=[])
    instructions, edges, calls = frames.decode_partition(data, address, partition)
    if len(instructions) != 26 or calls != {address+34: core} or \
            data[4:8] != bytes.fromhex('002901d1'):
        raise ValueError('complete wrapper and original nonzero-size branch required')
    pending, visited = [address], set()
    while pending:
        site = pending.pop()
        if site in visited:
            continue
        visited.add(site)
        item = instructions[site]
        if site in calls:
            continue
        read, written = map(set, item.regs_access())
        if R3 in read | written:
            raise ValueError('wrapper observes or changes the incoming descriptor R3')
        if not edges[site]:
            raise ValueError('nonzero wrapper returns before the allocator handoff')
        # Only this entry predicate follows from the nonzero-size premise.
        # Both rounding alternatives remain in the checked prefix graph.
        pending.extend((address+12,) if site == address+6 else edges[site])
    if address+34 not in visited:
        raise ValueError('nonzero wrapper has no allocator handoff')
    return dict(complete_instructions=len(instructions), sites=sorted(visited),
                handoff_site=address+34, target=core,
                excluded_original_zero_edge=[address+6, address+8],
                rounding_alternatives_checked=True)


def _core_prefix(data, address):
    """Decode every instruction before the first incoming-R3 overwrite."""
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    stack, sites = [], []
    for item in decoder.disasm(data[:64], address):
        sites.append(item.address)
        if item.size != 2 or CS_GRP_CALL in item.groups or CS_GRP_JUMP in item.groups:
            raise ValueError('control transfer precedes descriptor R3 overwrite')
        read, written = map(set, item.regs_access())
        if R3 in read:
            raise ValueError('incoming descriptor R3 is observed before overwrite')
        raw = int.from_bytes(item.bytes, 'little')
        if R3 in written:
            displacement = 4*(raw & 255)
            if raw & 0xf800 != 0xa800 or (raw >> 8) & 7 != 3 or \
                    displacement//4 >= len(stack) or stack[displacement//4] != 'local':
                raise ValueError('R3 overwrite is not a fresh allocated local SP slot')
            return dict(sites=sites, overwrite_site=item.address,
                        overwrite_encoding=bytes(item.bytes).hex(),
                        incoming_R3_read_sites=[], incoming_R3_spill_sites=[],
                        private_frame_bytes_at_overwrite=4*len(stack),
                        new_R3_origin='allocator-private SP plus immediate',
                        new_R3_SP_displacement=displacement,
                        new_R3_entry_SP_offset=displacement-4*len(stack),
                        new_R3_is_scalar=False, new_R3_still_has_alias_obligations=True)
        if raw & 0xfe00 == 0xb400:
            count = (raw & 255).bit_count() + bool(raw & 0x100)
            if not count:
                raise ValueError('empty allocator PUSH before overwrite')
            stack[:0] = ['saved']*count
        elif raw & 0xff80 == 0xb080:
            count = raw & 127
            if not count:
                raise ValueError('empty allocator allocation before overwrite')
            stack[:0] = ['local']*count
        elif ARM_REG_SP in written:
            raise ValueError('unsupported allocator frame change before overwrite')
    raise ValueError('bounded allocator prefix has no descriptor R3 overwrite')


def prove(layout, payload_size, *, selector):
    """Prove the tracked R3 prefix under an explicit uint32 R2 premise.

    Complete shapes bind every owner byte. The wrapper is checked under its
    derived nonzero input, including both rounding paths. No state interpreter,
    historical effects report or ABI preservation declaration supplies the kill.
    """
    if type(selector) is not str or selector != SELECTOR or type(layout) is not scheduler.Layout:
        raise ValueError('explicit descriptor-prefix selector and scheduler layout required')
    if type(payload_size) is not int or not 0 <= payload_size < 2**32:
        raise ValueError('exact unsigned32 incoming R2 premise required')
    wrapper, core = layout.allocator, layout.allocator.allocator
    scheduler_body = scheduler._identity(layout.address, wrapper, layout.callback_thunk)
    if hashlib.sha256(scheduler_body).hexdigest() != layout.sha256:
        raise ValueError('complete scheduler identity changed')
    wrapper_body = scheduler.wrapper._identity(wrapper.address, core)
    core_body = scheduler.split._identity(core.address, core.insertion, core.thunk, core.pointer_literal)
    count = (payload_size+28) & 65535
    if count == 0:
        raise ValueError('derived zero request retains the incoming descriptor R3 shortcut')
    first = _wrapper_prefix(wrapper_body, wrapper.address, core.address)
    last = _core_prefix(core_body, core.address)
    owners = {layout.address: scheduler_body, wrapper.address: wrapper_body, core.address: core_body}
    return dict(schema=SELECTOR,
        complete_owner_pins=[dict(address=p, bytes=len(b), sha256=hashlib.sha256(b).hexdigest())
                             for p, b in sorted(owners.items())],
        incoming_R2_condition=payload_size, derived_allocator_request_bytes=count,
        actual_incoming_R2_proved=False,
        scheduler_handoff=dict(site=layout.address+34, target=wrapper.address,
            descriptor_origins=['R3 incoming descriptor', 'R9 retained descriptor'],
            R9_preservation_proved=False),
        wrapper_prefix=first, allocator_prefix=last,
        tracked_incoming_R3_observed_or_stored_before_overwrite=False,
        tracked_incoming_R3_origin_removed_at_overwrite=True,
        all_other_origin_and_alias_obligations_unchanged=True,
        zero_request_shortcut_supported=False,
        whole_allocator_effects_proved=False, allocator_return_proved=False,
        physical_or_saved_memory_separation_proved=False,
        actual_pointer_nonescape_proved=False, native_admission=False,
        scope='only this incoming register origin before its first overwrite; no initial memory or unrelated register is classified as scalar or nonalias')
