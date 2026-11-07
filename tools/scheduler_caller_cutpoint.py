"""Bounded machine-value derivation to one descriptor call cutpoint.

The retained complete partition is an external structural authority. Only
paths reaching the selected direct call are interpreted. This establishes no
whole-owner behavior, physical access, C initialization, callback, allocation,
ABI, escape or termination theorem. External pointers and reads are formal
origins with explicit access and separation premises.
"""
from dataclasses import dataclass
import hashlib

import descriptor_frame_shape_prerequisite as frames
from descriptor_partial_word_prerequisite import Word

SELECTOR = 'conditional-scheduler-caller-cutpoint-v1'
MAX_STEPS = 256
MAX_PATHS = 64
SAVED = (False, True, False)


@dataclass(frozen=True)
class Value:
    kind: str
    value: object
    offset: int = 0

    def word(self):
        if self.kind == 'constant':
            return Word.constant(self.value)
        if self.kind == 'local':
            return Word.pointer(self.value)
        if self.kind == 'external' and self.offset:
            return Word.unproved(f'external-address:{self.value}:{self.offset}')
        return Word.unproved(str(self.value))


def _plus(value, amount):
    if value.kind == 'constant':
        return Value('constant', (value.value+amount) & 0xffffffff)
    if value.kind == 'local':
        return Value('local', value.value+amount)
    if value.kind == 'external':
        return Value('external', value.value, value.offset+amount)
    if amount == 0:
        return value
    raise ValueError('unsupported symbolic arithmetic before descriptor call')


def _restrict(ranges, operation, constant):
    result = []
    for lo, hi in ranges:
        pieces = {'eq': [(constant, constant)], 'ne': [(lo, constant-1), (constant+1, hi)],
                  'gt': [(constant+1, hi)], 'le': [(lo, constant)]}[operation]
        for left, right in pieces:
            low, high = max(lo, left), min(hi, right)
            if low <= high:
                result.append((low, high))
    return tuple(result)


def _branch(domains, comparison, operation):
    if comparison is None:
        raise ValueError('branch requires a current modeled comparison')
    left, right = comparison
    if right.kind != 'constant':
        raise ValueError('comparison requires a concrete right operand')
    if operation in ('gt', 'le') and (right.value > 0x7fffffff or left.kind == 'constant' and left.value > 0x7fffffff):
        raise ValueError('signed comparison requires proven nonnegative operands')
    if left.kind == 'constant':
        yes = {'eq': left.value == right.value, 'ne': left.value != right.value,
               'gt': left.value > right.value, 'le': left.value <= right.value}[operation]
        return dict(domains) if yes else None
    if left.kind != 'read' or left.value not in domains:
        raise ValueError('branch requires a bounded unsigned external read')
    old = domains[left.value]
    # Signed BGT/LE is sound for these nonnegative halfword/byte origins.
    if operation in ('gt', 'le') and (any(hi > 0x7fffffff for _, hi in old) or right.value > 0x7fffffff):
        raise ValueError('signed comparison requires proven nonnegative operands')
    narrowed = _restrict(old, operation, right.value)
    if not narrowed:
        return None
    return dict(domains, **{left.value: narrowed})


def bind(data, address, partition, target, *, selector):
    if selector != SELECTOR or type(selector) is not str:
        raise ValueError('explicit scheduler caller selector required')
    if type(target) is not int or target % 2:
        raise ValueError('aligned direct Thumb target required')
    instructions, edges, calls = frames.decode_partition(data, address, partition)
    sites = [site for site, destination in calls.items() if destination == target]
    if len(sites) != 1:
        raise ValueError('exactly one selected call is required')
    goal = sites[0]
    ancestors = {goal}
    while True:
        expanded = ancestors | {site for site, following in edges.items() if set(following) & ancestors}
        if expanded == ancestors:
            break
        ancestors = expanded
    if address not in ancestors or any(site != goal and site in ancestors for site in calls):
        raise ValueError('cutpoint must be reachable without an earlier ordinary call')
    return dict(data=data, address=address, partition=partition, target=target,
                goal=goal, instructions=instructions, edges=edges, ancestors=ancestors)


def derive(layout, *, selector):
    if selector != SELECTOR or type(selector) is not str:
        raise ValueError('explicit scheduler caller selector required')
    data, address = layout['data'], layout['address']
    registers = {reg: Value('opaque', f'entry-r{reg}') for reg in (*range(13), 14)}
    registers[1] = Value('external', 'entry-r1')
    registers[2] = Value('external', 'entry-r2')
    pending = [(address, registers, 0, {}, {}, {}, None, (), (), 0)]
    results = []
    visits = 0
    while pending:
        if len(pending)+len(results) > MAX_PATHS:
            raise ValueError('bounded caller path budget exceeded')
        site, regs, sp, words, classes, domains, comparison, reads, trace, depth = pending.pop()
        if site not in layout['ancestors']:
            continue
        if depth >= MAX_STEPS:
            raise ValueError('bounded caller step budget exceeded; no termination theorem')
        visits += 1
        if site == layout['goal']:
            regs = dict(regs); regs[14] = Value('constant', (site+4) | 1)
            results.append(dict(registers=regs, SP=sp, words=words, classes=classes,
                                domains=domains, reads=reads, trace=trace))
            continue
        item = layout['instructions'][site]
        if item.size != 2:
            raise ValueError('unmodeled wide instruction before selected call')
        encoded = int.from_bytes(bytes(item.bytes), 'little')
        regs, words, classes, domains = dict(regs), dict(words), dict(classes), dict(domains)
        next_comparison = comparison
        if encoded & 0xfe00 == 0xb400:
            numbers = [i for i in range(8) if encoded & (1 << i)]
            if encoded & 0x100:
                numbers.append(14)
            if not numbers:
                raise ValueError('empty push')
            sp -= 4*len(numbers)
            for index, reg in enumerate(numbers):
                offset = sp+4*index
                if offset in words:
                    raise ValueError('overlapping pushed caller storage')
                words[offset] = regs[reg].word(); classes[offset] = SAVED
        elif encoded & 0xff80 == 0xb080:
            count = 4*(encoded & 127)
            if not count or sp-count < -1024:
                raise ValueError('bounded nonzero caller allocation required')
            for offset in range(sp-count, sp, 4):
                if offset in words:
                    raise ValueError('overlapping caller allocation')
                words[offset] = Word.unproved(f'caller-word:{offset}'); classes[offset] = frames.LOCAL
            sp -= count
        elif encoded & 0xf800 == 0x2000:
            regs[(encoded >> 8) & 7] = Value('constant', encoded & 255); next_comparison = None
        elif encoded & 0xfe00 == 0x1c00:
            regs[encoded & 7] = _plus(regs[(encoded >> 3) & 7], (encoded >> 6) & 7); next_comparison = None
        elif encoded & 0xf800 == 0x3000:
            reg = (encoded >> 8) & 7; regs[reg] = _plus(regs[reg], encoded & 255); next_comparison = None
        elif encoded & 0xf800 == 0:
            source, shift = regs[(encoded >> 3) & 7], (encoded >> 6) & 31
            if source.kind != 'constant':
                raise ValueError('shift requires concrete machine value')
            regs[encoded & 7] = Value('constant', (source.value << shift) & 0xffffffff); next_comparison = None
        elif encoded & 0xf800 == 0x4800:
            literal = ((site+4) & ~3)+4*(encoded & 255)
            matches = [w for w in layout['partition']['words'] if w['address'] == literal and site in w['load_sites']]
            if len(matches) != 1:
                raise ValueError('literal requires complete retained referenced word')
            regs[(encoded >> 8) & 7] = Value('constant', int.from_bytes(data[literal-address:literal-address+4], 'little'))
        elif encoded & 0xf800 in (0x6800, 0x7800, 0x8800):
            width = {0x6800: 4, 0x7800: 1, 0x8800: 2}[encoded & 0xf800]
            base = regs[(encoded >> 3) & 7]; offset = ((encoded >> 6) & 31)*width
            if base.kind != 'external':
                raise ValueError('external load needs an explicit external pointer origin')
            origin = f'read:{base.value}:{base.offset+offset}:{width}@{site:08X}'
            regs[encoded & 7] = Value('read', origin)
            domains[origin] = ((0, (1 << (8*width))-1),)
            reads += (dict(site=site, base=base.value, offset=base.offset+offset, width=width, origin=origin),)
        elif encoded & 0xf800 == 0xa800:
            offset = sp+4*(encoded & 255)
            if classes.get(offset) != frames.LOCAL:
                raise ValueError('SP alias must point into live caller locals')
            regs[(encoded >> 8) & 7] = Value('local', offset)
        elif encoded & 0xf800 == 0x8000:
            base = regs[(encoded >> 3) & 7]; value = regs[encoded & 7]
            if base.kind != 'local' or value.kind != 'constant':
                raise ValueError('local halfword store requires local provenance and concrete value')
            offset = base.value+2*((encoded >> 6) & 31); aligned = offset & ~3
            if classes.get(aligned) != frames.LOCAL:
                raise ValueError('halfword store overlaps protected or absent caller state')
            atoms = list(words[aligned].bytes)
            atoms[offset-aligned:offset-aligned+2] = value.word().bytes[:2]
            words[aligned] = Word(tuple(atoms))
        elif encoded & 0xf800 == 0x9000:
            offset = sp+4*(encoded & 255)
            if classes.get(offset) != frames.LOCAL:
                raise ValueError('word store overlaps protected or absent caller state')
            words[offset] = regs[(encoded >> 8) & 7].word()
        elif encoded & 0xffc0 == 0x4280:
            next_comparison = (regs[encoded & 7], regs[(encoded >> 3) & 7])
        elif encoded & 0xf800 == 0x2800:
            next_comparison = (regs[(encoded >> 8) & 7], Value('constant', encoded & 255))
        elif item.mnemonic in ('b', 'beq', 'bne', 'bgt', 'ble'):
            pass
        else:
            raise ValueError(f'unmodeled caller prefix instruction {item.mnemonic} at {site:08X}')
        trace += (site,)
        following = layout['edges'][site]
        for index, destination in enumerate(following):
            branch_domains = domains
            if len(following) == 2:
                operations = {'beq': ('eq', 'ne'), 'bne': ('ne', 'eq'), 'bgt': ('gt', 'le'), 'ble': ('le', 'gt')}
                if item.mnemonic not in operations:
                    raise ValueError('unmodeled caller branch condition')
                branch_domains = _branch(domains, comparison, operations[item.mnemonic][index])
            if branch_domains is not None:
                pending.append((destination, regs, sp, words, classes, branch_domains, next_comparison, reads, trace, depth+1))
    if not results:
        raise ValueError('no feasible path reaches selected descriptor call')
    return tuple(results)


def report(layout, states):
    def words(items):
        return {str(k): [list(atom) for atom in v.bytes] for k, v in sorted(items.items())}
    return dict(schema=SELECTOR, body=dict(address=layout['address'], bytes=len(layout['data']), sha256=hashlib.sha256(layout['data']).hexdigest()),
        call=dict(site=layout['goal'], target=layout['target']),
        states=[dict(SP=x['SP'], caller_stack=[list(x['classes'][p]) for p in range(x['SP'], 0, 4)],
                     caller_words=words(x['words']), entry_registers=words({r: v.word() for r, v in x['registers'].items()}),
                     protected=[p for p, c in sorted(x['classes'].items()) if c == (False, True, False)],
                     read_domains={key: list(value) for key, value in x['domains'].items()}, reads=list(x['reads']), trace=list(x['trace'])) for x in states],
        conditional_call_reaching_value_relation=True,
        premises=['retained complete structural partition is authentic and current',
                  'entry R1/R2 denote live correctly aligned external objects for each listed access',
                  'caller stack is aligned, nonwrapping, accessible and separate from those external objects',
                  'external reads observe the listed formal values without intervening effects'],
        caller_memory_physical_permission=False, source_C_initialization=False,
        whole_owner_admission=False, scheduler_prefix_closed=False, callback_effects_closed=False,
        nonescape_proved=False, unconditional_termination=False, source_or_ELF_admission=False, native_admission=False)
