"""Conditional byte relations for local copies with unproved source bytes.

Unknown bytes are symbolic machine contents, never initialized scalar facts or
bounded pointers. No callback, frame, allocation, or owner admission is made.
"""
from dataclasses import dataclass

import local_descriptor_copy_prerequisite as strict

SELECTOR = 'bounded-partial-local-descriptor-copy-prerequisite-v1'


@dataclass(frozen=True)
class Word:
    bytes: tuple

    def __post_init__(self):
        if type(self.bytes) is not tuple or len(self.bytes) != 4:
            raise ValueError('partial word requires exactly four immutable bytes')
        for atom in self.bytes:
            if type(atom) is not tuple or not atom:
                raise ValueError('partial word requires exact byte provenance')
            if atom[0] == 'constant':
                valid = len(atom) == 2 and type(atom[1]) is int and 0 <= atom[1] <= 255
            elif atom[0] == 'pointer':
                valid = len(atom) == 3 and type(atom[1]) is int and \
                    type(atom[2]) is int and 0 <= atom[2] <= 3
            elif atom[0] == 'unproved':
                valid = len(atom) == 3 and type(atom[1]) is str and \
                    0 < len(atom[1]) <= 128 and type(atom[2]) is int and 0 <= atom[2] <= 3
            else:
                valid = False
            if not valid:
                raise ValueError('invalid partial-word byte provenance')

    @classmethod
    def constant(cls, value):
        if type(value) is not int or not 0 <= value <= 0xffffffff:
            raise ValueError('constant word requires exact unsigned32 bits')
        return cls(tuple(('constant', (value >> (8*i)) & 255) for i in range(4)))

    @classmethod
    def pointer(cls, offset):
        if type(offset) is not int:
            raise ValueError('local pointer requires exact offset')
        return cls(tuple(('pointer', offset, i) for i in range(4)))

    @classmethod
    def unproved(cls, origin):
        return cls(tuple(('unproved', origin, i) for i in range(4)))

    def pointer_offset(self):
        if any(atom[0] == 'pointer' for atom in self.bytes):
            offset = self.bytes[0][1]
            if self.bytes != tuple(('pointer', offset, i) for i in range(4)):
                raise ValueError('partial pointer provenance cannot become a scalar or address')
            return offset
        return None

    def known_value(self):
        if all(atom[0] == 'constant' for atom in self.bytes):
            return sum(atom[1] << (8*i) for i, atom in enumerate(self.bytes))
        return None

    def known_byte_mask(self):
        return sum((atom[0] != 'unproved') << i for i, atom in enumerate(self.bytes))

    def read_scalar(self, offset, width, *, signed=False):
        """Interpret only a justified concrete scalar slice, never opaque bytes."""
        if type(offset) is not int or type(width) is not int or width not in (1, 2, 4) or \
                offset < 0 or offset % width or offset+width > 4 or type(signed) is not bool:
            raise ValueError('scalar observation requires an aligned in-word byte slice')
        selected = self.bytes[offset:offset+width]
        if any(atom[0] != 'constant' for atom in selected):
            raise ValueError('consumer observes unproved or pointer bytes as a scalar value')
        value = sum(atom[1] << (8*i) for i, atom in enumerate(selected))
        if signed and value & (1 << (8*width-1)):
            value -= 1 << (8*width)
        return value

    def require_pointer(self):
        """Numeric equality and opaque origins cannot supply pointer authority."""
        offset = self.pointer_offset()
        if offset is None:
            raise ValueError('consumer address requires complete local pointer provenance')
        return offset

    def guard_fact(self):
        """Erase only payloads for structural guards; never export this witness.

The strict transfer checks address provenance, bounds, opcodes and saved words.
It performs no payload-dependent branching or arithmetic except STRH merging,
whose result is discarded and rebuilt from byte provenance below. An unproved
payload's zero witness cannot pass an address guard: it is a constant, not a
pointer. It never enters the returned register or word facts.
"""
        offset = self.pointer_offset()
        if offset is not None:
            return ('pointer', offset)
        value = self.known_value()
        return ('constant', 0 if value is None else value)


def replay(code, registers, stack, words, *, protected=()):
    """Preserve each byte relation through the closed nonbranching copy subset."""
    if type(code) is not bytes or not code or len(code) % 2 or len(code) > 2*strict.MAX_INSTRUCTIONS:
        raise ValueError('partial copy requires bounded complete Thumb halfwords')
    if type(registers) is not dict or type(words) is not dict or \
            any(type(value) is not Word for value in (*registers.values(), *words.values())):
        raise ValueError('partial copy requires explicit immutable Word facts')
    if type(stack) not in (tuple, list) or not 0 < len(stack) <= strict.MAX_STACK_WORDS:
        raise ValueError('partial copy requires bounded live stack')
    regs = dict(registers)
    base = -4*len(stack)
    # These atoms assert no value or initialization. Each denotes the same
    # arbitrary initial byte until an actual instruction overwrites that byte.
    memory = {offset: Word.unproved(f'initial-word:{offset}')
              for offset in range(base, 0, 4)}
    memory.update(words)
    reads, writes = [], []
    for index in range(0, len(code), 2):
        instruction = code[index:index+2]
        op = int.from_bytes(instruction, 'little')
        guard = strict.replay(instruction,
            {reg: value.guard_fact() for reg, value in regs.items()}, stack,
            {offset: value.guard_fact() for offset, value in memory.items()}, protected=protected)
        if op & 0xff00 == 0x4600:
            src, dst = (op >> 3) & 15, (op & 7) | ((op >> 4) & 8)
            regs[dst] = regs[src]
        elif op & 0xf800 == 0x2000:
            regs[(op >> 8) & 7] = Word.constant(op & 255)
        elif op & 0xf000 == 0xc000:
            base_reg = (op >> 8) & 7
            transfer = [reg for reg in range(8) if op & (1 << reg)]
            if op & 0x0800:
                values = [memory[offset] for offset in guard['reads']]
                regs.update(zip(transfer, values))
            else:
                values = [regs[reg] for reg in transfer]
                memory.update(zip(guard['writes'], values))
            kind, offset = guard['registers'][base_reg]
            if kind != 'pointer':
                raise ValueError('multiple-transfer writeback lost local provenance')
            regs[base_reg] = Word.pointer(offset)
        elif op & 0xf800 in (0x6000, 0x6800):
            reg = op & 7
            if op & 0x0800:
                regs[reg] = memory[guard['reads'][0]]
            else:
                memory[guard['writes'][0]] = regs[reg]
        elif op & 0xf800 == 0x8000:
            reg, base_reg = op & 7, (op >> 3) & 7
            offset = regs[base_reg].pointer_offset()+2*((op >> 6) & 31)
            aligned = guard['writes'][0]
            previous, value = memory[aligned], regs[reg]
            if previous.pointer_offset() is not None or value.pointer_offset() is not None:
                raise ValueError('partial copy excludes partial pointer overwrite')
            first = offset-aligned
            result = list(previous.bytes)
            result[first:first+2] = value.bytes[:2]
            memory[aligned] = Word(tuple(result))
        else:
            raise ValueError('partial copy decoder differs from strict guard subset')
        reads.extend(guard['reads']); writes.extend(guard['writes'])
    return dict(registers=regs, words=memory, reads=reads, writes=writes,
                flags_known=False, input_state_authenticated=False,
                frame_replay_complete=False, native_admission=False, callback_effects=None)


class PartialWordCopyPrerequisite:
    def __init__(self, data, address, rom, mapping, index, *, selector):
        if selector != SELECTOR or type(selector) is not str:
            raise ValueError('partial copy requires its explicit prerequisite selector')
        self.structure = strict.LocalDescriptorCopyPrerequisite(data, address, rom, mapping, index,
                                                                selector=strict.SELECTOR)

    def check_segment(self, start, end, registers, stack, words, *, protected=()):
        record = self.structure.segment_structure(start, end)
        result = replay(bytes.fromhex(record['code_hex']), registers, stack, words, protected=protected)
        return dict(record, schema=SELECTOR, conditional_transfer=result)
