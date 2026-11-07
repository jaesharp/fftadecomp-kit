"""Bounded local-copy transfer lemma; never an owner or callback admission.

Every input fact must come from a complete caller replay. Numeric RAM constants
are not pointers. This module neither establishes its input state nor grants
allocation, lifetime, call preservation, callback identity, or callback effects.
"""
import hashlib

import owner_admission_profile as owner
import owner_graph_profile as graph
import owner_runtime_profile as operations

SELECTOR = 'bounded-local-descriptor-copy-prerequisite-v1'
MAX_INSTRUCTIONS = 32
MAX_STACK_WORDS = 256
LOCAL = (False, False, True)


def replay(code, registers, stack, words, *, protected=()):
    """Replay a straight-line Thumb segment over exact word facts, atomically.

Register keys use architectural numbers (0..15), not Capstone identifiers.
Pointers are offsets relative to the enclosing replay's entry SP. Stack rows
are in increasing address order, exactly as in BufferCallProof. Missing words
remain unproved and cannot be read; overlapping copies use sequential machine
semantics, without an invented disjointness premise.
"""
    if type(code) is not bytes or not code or len(code) % 2 or len(code) > 2*MAX_INSTRUCTIONS:
        raise ValueError('copy segment requires bounded complete Thumb halfwords')
    if type(stack) not in (tuple, list) or not 0 < len(stack) <= MAX_STACK_WORDS:
        raise ValueError('copy requires a bounded exact live stack')
    if any(type(row) not in (tuple, list) or len(row) != 3 or
           any(type(bit) is not bool for bit in row) for row in stack):
        raise ValueError('copy requires exact stack classifications')
    base = -4*len(stack)
    excluded = set()
    for offset in protected:
        if type(offset) is not int or offset % 4 or not base <= offset <= -4:
            raise ValueError('protected word outside live stack')
        excluded.add(offset)

    def fact(value):
        if type(value) is not tuple or len(value) != 2 or type(value[1]) is not int:
            raise ValueError('copy requires exact word provenance')
        kind, payload = value
        if kind == 'constant' and 0 <= payload <= 0xffffffff:
            return value
        if kind == 'pointer' and base <= payload <= 0:
            return value
        raise ValueError('copy excludes opaque or external word provenance')

    if type(registers) is not dict or type(words) is not dict:
        raise ValueError('copy requires exact register and word maps')
    regs = {}
    for reg, value in registers.items():
        if type(reg) is not int or not 0 <= reg < 16 or reg == 15:
            raise ValueError('invalid copy register fact')
        regs[reg] = fact(value)
    memory = {}
    for offset, value in words.items():
        if type(offset) is not int or offset % 4 or not base <= offset <= -4:
            raise ValueError('word fact outside live stack')
        memory[offset] = fact(value)
    if regs.get(13) != ('pointer', base):
        raise ValueError('copy SP must equal the exact live stack origin')

    def access(offset, width):
        if type(offset) is not int or offset % width or not base <= offset < offset+width <= 0:
            raise ValueError('copy access outside aligned live stack')
        for slot in range((offset-base)//4, (offset+width-1-base)//4+1):
            address = base+4*slot
            if tuple(stack[slot]) != LOCAL or address in excluded:
                raise ValueError('copy observes or overwrites saved/protected state')

    def pointer(reg):
        value = regs.get(reg)
        if value is None or value[0] != 'pointer':
            raise ValueError('copy address lacks concrete local pointer provenance')
        return value[1]

    def read(offset):
        access(offset, 4)
        if offset not in memory:
            raise ValueError('copy reads an unproved word')
        return memory[offset]

    def register(reg):
        if reg not in regs:
            raise ValueError('copy reads an unproved register')
        return regs[reg]

    reads, writes = [], []
    for index in range(0, len(code), 2):
        op = int.from_bytes(code[index:index+2], 'little')
        if op & 0xff00 == 0x4600:  # exact high-register MOV, including MOV low,SP
            src, dst = (op >> 3) & 15, (op & 7) | ((op >> 4) & 8)
            if src == 15 or dst in (13, 15):
                raise ValueError('copy excludes control and SP writes')
            regs[dst] = register(src)
        elif op & 0xf800 == 0x2000:  # MOVS low,#imm8
            regs[(op >> 8) & 7] = ('constant', op & 255)
        elif op & 0xf000 == 0xc000:  # Thumb LDMIA/STMIA, increasing register order
            base_reg = (op >> 8) & 7
            transfer = [reg for reg in range(8) if op & (1 << reg)]
            if not transfer or base_reg in transfer:
                raise ValueError('copy excludes empty or base-in-list multiple transfers')
            start = pointer(base_reg)
            offsets = [start+4*i for i in range(len(transfer))]
            for offset in offsets:
                access(offset, 4)
            if op & 0x0800:
                values = [read(offset) for offset in offsets]
                regs.update(zip(transfer, values))
                reads.extend(offsets)
            else:
                values = [register(reg) for reg in transfer]
                memory.update(zip(offsets, values))
                writes.extend(offsets)
            regs[base_reg] = ('pointer', start+4*len(transfer))
        elif op & 0xf800 in (0x6000, 0x6800):  # STR/LDR low,[low,#word]
            reg, base_reg = op & 7, (op >> 3) & 7
            offset = pointer(base_reg)+4*((op >> 6) & 31)
            access(offset, 4)
            if op & 0x0800:
                regs[reg] = read(offset)
                reads.append(offset)
            else:
                memory[offset] = register(reg)
                writes.append(offset)
        elif op & 0xf800 == 0x8000:  # STRH low,[low,#halfword]
            reg, base_reg = op & 7, (op >> 3) & 7
            offset = pointer(base_reg)+2*((op >> 6) & 31)
            access(offset, 2)
            aligned = offset & ~3
            previous, value = read(aligned), register(reg)
            if previous[0] != 'constant' or value[0] != 'constant':
                raise ValueError('copy excludes partial overwrite of pointer provenance')
            shift = (offset-aligned)*8
            memory[aligned] = ('constant', (previous[1] & ~(0xffff << shift)) |
                               ((value[1] & 0xffff) << shift))
            reads.append(aligned)
            writes.append(aligned)
        else:
            raise ValueError('instruction outside closed local-copy transfer subset')
    return dict(registers=regs, words=memory, reads=reads, writes=writes,
                flags_known=False, native_admission=False, callback_effects=None)


class LocalDescriptorCopyPrerequisite:
    """Authenticate a full owner before selecting a single-entry copy segment."""
    def __init__(self, data, address, rom, mapping, index, *, selector):
        if selector != SELECTOR or type(selector) is not str:
            raise ValueError('local copy requires its explicit prerequisite selector')
        if any(type(value) is not bytes for value in (data, rom, mapping, index)) or \
                type(address) is not int or not 2 <= len(data) <= 4096:
            raise ValueError('local copy requires bounded immutable complete inputs')
        owner.validate_span(data, address, rom, mapping, index)
        refined = owner.refine(data, address, mapping)
        if not refined['cfg_closed']:
            raise ValueError('local copy requires complete closed owner CFG')
        ins, edges, branches, calls, table = graph.graph(data, address, refined)
        if branches or table:
            raise ValueError('local copy excludes unselected local BL and table policies')
        partition = graph.partition(data, address, refined, ins, table)
        operations.verify_operations(ins, edges, address, branches, calls, refined)
        self.data, self.address, self.ins, self.edges = data, address, ins, edges
        self.record = dict(schema=SELECTOR, owner=[address, len(data), hashlib.sha256(data).hexdigest()],
                           partition=partition, mapping_sha256=hashlib.sha256(mapping).hexdigest(),
                           index_sha256=hashlib.sha256(index).hexdigest(), native_admission=False)

    def segment_structure(self, start, end):
        """Return only authenticated bytes and CFG facts, without input-state facts."""
        if any(type(value) is not int for value in (start, end)) or \
                not self.address <= start < end <= self.address+len(self.data) or \
                (end-start) % 2 or end-start > 2*MAX_INSTRUCTIONS:
            raise ValueError('copy segment is outside the bounded complete owner')
        sites = set(range(start, end, 2))
        for site in sites:
            if site not in self.ins or self.ins[site].size != 2 or set(self.edges[site]) != {site+2}:
                raise ValueError('copy segment is not uninterrupted Thumb fallthrough')
        for site, successors in self.edges.items():
            if site not in sites and any(target in sites-{start} for target in successors):
                raise ValueError('copy segment has an interior CFG entry')
        code = self.data[start-self.address:end-self.address]
        return dict(self.record, segment=[start, end], code_hex=code.hex(),
                    code_sha256=hashlib.sha256(code).hexdigest(),
                    input_state_authenticated=False, frame_replay_complete=False,
                    callback_effects=None)

    def check_segment(self, start, end, registers, stack, words, *, protected=()):
        structure = self.segment_structure(start, end)
        result = replay(bytes.fromhex(structure['code_hex']), registers, stack, words,
                        protected=protected)
        return dict(self.record, segment=[start, end], conditional_transfer=result,
                    input_state_authenticated=False, frame_replay_complete=False,
                    callback_effects=None)
