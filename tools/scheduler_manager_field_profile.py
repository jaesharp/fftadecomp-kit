"""Explicit conditional scheduler entry through one manager-pointer field.

Only the actual chain ``ldr r0,[pc]; ldr r0,[r0]; ldr r0,[r0]`` is
authenticated. Readability, alignment and separation of its two storage words
remain premises; neither a named literal nor the load chain proves them.
"""
import hashlib
from pathlib import Path

import match
import scheduler_entry_profile as entry

SELECTOR = 'conditional-scheduler-indirect-manager-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR


def bind(data, address, ins, edges, calls):
    entry.require(len(calls) == 1 and set(calls.values()) == {entry.DIRECT},
                  'indirect manager contract requires one direct scheduler call')
    site = next(iter(calls))
    predecessors = {}
    for source, targets in edges.items():
        for target in targets:
            predecessors.setdefault(target, []).append(source)
    writes, seen, current = [], {site}, site
    while len(writes) < 3:
        before = predecessors.get(current, [])
        entry.require(len(before) == 1 and list(edges[before[0]]) == [current]
                      and before[0] not in seen and before[0] in ins,
                      'manager field requires a finite straight-line load chain')
        current = before[0]
        seen.add(current)
        instruction = ins[current]
        if match.ARM_REG_R0 in instruction.regs_access()[1]:
            writes.append(instruction)

    final, pointer, literal = writes

    def load(instruction, base):
        operands = instruction.operands
        return (instruction.mnemonic == 'ldr' and instruction.size == 2
                and len(operands) == 2 and operands[0].type == match.ARM_OP_REG
                and operands[0].reg == match.ARM_REG_R0
                and operands[1].type == match.ARM_OP_MEM
                and operands[1].mem.base == base and not operands[1].mem.index)

    entry.require(load(literal, match.ARM_REG_PC)
                  and all(load(i, match.ARM_REG_R0) and i.operands[1].mem.disp == 0
                          for i in (pointer, final)),
                  'manager field requires exactly two zero-offset word dereferences')
    offset = ((literal.address + 4) & ~3) + literal.operands[1].mem.disp - address
    entry.require(0 <= offset and offset % 4 == 0 and offset + 4 <= len(data),
                  'manager field literal is not a complete aligned owner word')
    return dict(address=entry.DIRECT, kind='direct-named-manager-field',
                descriptor_register=3, dependencies=(entry.DIRECT,),
                manager=dict(literal_offset=offset, load_site=literal.address,
                             pointer_load_site=pointer.address,
                             dereference_site=final.address,
                             dereference_count=2, field_offset=0))


def check_call(proof, address, aliases, stack, slots, *, site):
    return entry.check_call(proof, address, aliases, stack, slots, site=site)


def check_bindings(manifest, bindings):
    entry.check_bindings(manifest, bindings)


def manifest(proof):
    result = entry.manifest(proof)
    result['schema'] = SCHEMA
    result['entry_source_sha256'] = result['source_sha256']
    result['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    # Replace the single-load premise; retaining it would describe a different
    # manager value from the actual second dereference.
    result['assumptions'][-1] = (
        'The recorded typed named literal addresses a readable aligned word. '
        'The pointer actually read from that word addresses another readable aligned word '
        'at offset zero; both storage words are separate from every caller stack word. '
        'Their values are the values seen by the recorded ordered loads; no value, '
        'initialization, allocation or lifetime follows from the literal identity. '
        'The second loaded value is a valid scheduler manager separate from every caller '
        'stack word. The pinned func_08005954 reads its fifth argument from the caller '
        'outgoing word at SP (ldr r6,[sp,#0x38] at 0x08005966 after its 56-byte frame). '
        'That parent word holds no tracked local pointer; its initialization is not checked. '
        'No other caller private or saved word is read through SP.')
    result['manager_memory_access_proved'] = False
    return result
