"""Conditional scheduler descriptor calls through two other pinned entries.

`func_08121B8C` forwards the same R2 descriptor and parent to
`func_08005954` with the manager loaded from its pool state. A direct
`func_08005954` call passes the descriptor in R3, the parent in the caller's
outgoing stack word and a manager word loaded from a typed named data literal.
Entry identity, frame bounds and manager provenance are checked; the scheduler
and callback effects remain the explicit premises of the descriptor profile.
"""
import hashlib
from pathlib import Path

import match

SELECTOR = 'conditional-scheduler-entry-descriptor-calls-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
POOL, DIRECT = 0x08121B8C, 0x08005954
# Closed entry table. func_08005B6C keeps its own selectors and contract.
ENTRIES = {
    POOL: dict(kind='pool-manager-wrapper', descriptor_register=2,
               dependencies=(POOL, DIRECT)),
    DIRECT: dict(kind='direct-named-manager', descriptor_register=3,
                 dependencies=(DIRECT,)),
}
DESCRIPTOR_BYTES = 28


def require(condition, message):
    if not condition:
        raise ValueError(message)


def manager_word(data, address, ins, edges, site):
    """Return the literal offset of `ldr r0,[pc,#k]; ldr r0,[r0]` reaching site."""
    r0 = match.ARM_REG_R0
    predecessors = {}
    for source, targets in edges.items():
        for target in targets:
            predecessors.setdefault(target, []).append(source)
    writes, current = [], site
    while len(writes) < 2:
        before = predecessors.get(current, [])
        require(len(before) == 1 and list(edges[before[0]]) == [current] and before[0] != site,
                'direct scheduler manager requires one straight-line named data load')
        current = before[0]
        if r0 in ins[current].regs_access()[1]:
            writes.append(ins[current])
    deref, literal = writes

    def load(instruction, base):
        operands = instruction.operands
        return (instruction.mnemonic == 'ldr' and instruction.size == 2 and len(operands) == 2
                and operands[0].type == match.ARM_OP_REG and operands[0].reg == r0
                and operands[1].type == match.ARM_OP_MEM and operands[1].mem.base == base
                and not operands[1].mem.index)
    require(load(deref, r0) and deref.operands[1].mem.disp == 0 and load(literal, match.ARM_REG_PC),
            'direct scheduler manager requires one straight-line named data load')
    offset = ((literal.address + 4) & ~3) + literal.operands[1].mem.disp - address
    require(0 <= offset and offset + 4 <= len(data) and offset % 4 == 0,
            'direct scheduler manager literal is not a complete aligned owner word')
    return dict(literal_offset=offset, load_site=literal.address, dereference_site=deref.address)


def bind(data, address, ins, edges, calls):
    require(len(calls) == 1 and set(calls.values()) <= set(ENTRIES),
            'scheduler entry contract requires one actual pinned entry call')
    (site, target), = calls.items()
    entry = dict(address=target, **ENTRIES[target])
    if target == DIRECT:
        entry['manager'] = manager_word(data, address, ins, edges, site)
    return entry


def check_call(proof, address, aliases, stack, slots, *, site):
    entry = proof.scheduler_entry
    register = match.ARM_REG_R0 + entry['descriptor_register']
    require(address == entry['address'] and
            {reg for reg in aliases if reg in match.CALLER_CLOBBERED} == {register} and not slots,
            'scheduler entry contract excludes additional register or pointer-word aliases')
    offset = aliases[register]
    # func_08005954 copies the descriptor with LDM, which ignores address bits [1:0].
    require(offset % 4 == 0, 'scheduler entry descriptor must be word-aligned')
    observation = dict(site=site, target=address, scheduler_entry=entry['kind'],
                       local_offset=offset, bytes=DESCRIPTOR_BYTES,
                       aliases=sorted(aliases.items()), pointer_words=[])
    if address == DIRECT:
        # The fifth argument is the caller's outgoing word at SP; it must be a
        # private word that holds no tracked local pointer and the descriptor
        # must lie wholly above it.
        base = -4*len(stack)
        require(offset >= base + 4,
                'direct scheduler descriptor overlaps the outgoing argument word')
        proof.access(base, 4, stack)
        observation['outgoing_argument_word'] = base
    for byte in range(offset, offset + DESCRIPTOR_BYTES):
        proof.access(byte, 1, stack)
    require(site not in proof.observations or proof.observations[site] == observation,
            'local-buffer contract differs across incoming paths')
    proof.observations[site] = observation
    return {}


def check_bindings(manifest, bindings):
    """Bind a direct entry's manager literal to a typed named data relocation."""
    entry = manifest['entry']
    if entry['address'] != DIRECT:
        return
    offset = entry['manager']['literal_offset']
    rows = [row for row in bindings['data'] if row[0] == offset]
    require(len(rows) == 1 and rows[0][2] == 0,
            'direct scheduler manager literal requires one typed named data relocation')


def manifest(proof):
    require(set(proof.observations) == set(proof.calls),
            'every conditional local-buffer call must be observed')
    entry = proof.scheduler_entry
    return dict(schema=SCHEMA, runtime_dependencies=proof.runtime_dependencies,
        environment=proof.environment, entry=entry,
        observations=[proof.observations[s] for s in sorted(proof.observations)],
        assumptions=[
            'Actual calls return with compatible ARM ABI, exact SP and protected saved/caller words preserved.',
            'No local pointer is retained for later use or returned through caller-clobbered registers.',
            'Scheduler allocator/zero/list prefix and callback obey frame noninterference; the 28-byte '
            'descriptor is readable as representation bytes, its copied pointer values remain conditional, '
            'and the returned allocation is separate from all caller stack words. Both the copied R1 '
            'descriptor and ambient original R9 pointer are exposed to the callback; copying does not prove nonescape.',
            'Every recorded preserved-register alias is also exposed; the callback must not access other '
            'private or saved caller bytes through it.',
            'The parent argument is NULL or a valid scheduler node that addresses no caller stack word: '
            'func_08005954 writes through it (str r7,[r6,#0x10] at 0x080059BC) and walks its +8 chain, '
            'storing into the last node (0x080059A6-0x080059B0). Its value is not checked.',
            ('The pinned func_08121B8C body forwards R0-R3 unchanged as callback, u16 size, descriptor and '
             'parent to the pinned func_08005954 body, with the manager loaded from the word addressed by its '
             'pool state data_020159CC; that pool word is a valid scheduler manager separate from every caller '
             'stack word. Its own outgoing word is in its frame, not the caller frame.'
             if entry['address'] == POOL else
             'The manager in R0 is the word loaded from the recorded typed named data literal; that word is a '
             'valid scheduler manager separate from every caller stack word. The pinned func_08005954 body reads '
             'its fifth argument from the caller outgoing word at SP (ROM inspection: ldr r6,[sp,#0x38] at '
             '0x08005966 after its 56-byte frame) as the parent value; that word holds no tracked local pointer '
             'and its initialization is not checked. No other caller private or saved word is read through SP.')],
        actual_callback_effects_proved=False, nonescape_proved=False, termination_proved=False,
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
