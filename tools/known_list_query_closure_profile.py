"""Exact list queries with initialized byte/word callback effects.

The complete machine relation is conditional on live external objects and
compatible returning ABI/frame noninterference. It grants no C type, physical
access, iterator bound, or unconditional termination theorem.
"""
import hashlib
from pathlib import Path

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from addressed_signed_runtime_profile import toolchain_fingerprint, runtime_fingerprint
from software_double_profile import indices, span_record

SELECTOR = 'conditional-known-list-query-closure-v1'
SCHEMA = 'elf-symbol-thumb-conditional-known-list-query-closure-v1'
CONTROL_FLOW = ('complete initialized list query and known callback byte effects; '
                'compatible returning ABI, C binding and external memory/frame '
                'noninterference conditional; termination unproved')
ROM_BASE = 0x08000000
ROM_SHA256 = '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
ROOTS = {
    0x08022044: ('byte', 14, 0x08022194,
        '00b581b0012269460a70806804496a46a5f034fe6846007801b002bc0847000095210208'),
    0x08099560: ('search', 13, 0x0809AB5C,
        '00b583b0009100210291006903496a462ef0a6fb029803b002bc08475dab0908'),
}
DEPENDENCIES = {
    0x08022194: (18, '10b50c1ca5f0ecfc021c1168802000030140002903d1d06a002800d02170012010bc02bc0847'),
    0x0809AB5C: (15, '10b50c1c2df008f8021c11682068814201d0012001e0a260002010bc02bc0847'),
    0x080C7CC0: (16, '70b50e1c151c446800e0a468002c05d0201c291c7af0c2fa0028f6d170bc01bc0047'),
    0x080C7B74: (2, '00687047'),
    0x0814225C: (1, '3047'),
}


def sha(raw): return hashlib.sha256(raw).hexdigest()


def require(ok, message):
    if not ok: raise ValueError(message)


def environment_fingerprint():
    return dict(toolchain=toolchain_fingerprint(), runtime=runtime_fingerprint(),
        sources={p.name: sha(p.read_bytes()) for p in sorted(Path(__file__).parent.glob('*.py'))})


def constant(value): return ('constant', value & 0xffffffff)


def callback_effects(body, address, kind):
    """Interpret every forward path, retaining initialized-byte observations."""
    require(kind in ('byte', 'search') and type(body) is bytes and type(address) is int and address >= ROM_BASE and address % 2 == 0,
            'explicit bounded list callback kind required')
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB); decoder.detail = True
    instructions = {i.address: i for i in decoder.disasm(body, address)}
    require(0 < len(body) <= 128 and sum(i.size for i in instructions.values()) == len(body),
            'complete code-only bounded callback required')
    registers = [('ordinary',)] * 15
    registers[0], registers[1], registers[14] = ('node',), ('query',), ('return',)
    for n in range(4, 12): registers[n] = ('entry', n)
    pending = [(address, registers, [], [], None, [], [])]
    reached, paths = set(), []
    states = 0
    while pending:
        site, regs, stack, facts, compared, reads, writes = pending.pop()
        states += 1; require(states <= 256 and site in instructions, 'bounded callback CFG escaped')
        reached.add(site); item = instructions[site]; code = int.from_bytes(item.bytes[:2], 'little')
        def value(token):
            for left, right, equal in reversed(facts):
                if equal and left == token and right[0] == 'constant': return right
                if equal and right == token and left[0] == 'constant': return left
            return token
        def scalar(token):
            require(token[0] not in ('query', 'node', 'object', 'entry', 'return'),
                    'scalar operation observes tracked pointer or saved origin')
        if item.mnemonic == 'bl':
            require(item.size == 4 and item.operands[0].imm == 0x080C7B74 and
                    regs[0] == ('node',) and regs[4] == ('query',),
                    'callback call must be exact getter with protected query')
            regs[0] = ('object',)
            # Exact getter is LDR R0,[R0]; BX LR. All other data
            # registers retain their origins, including the incoming R1 alias.
            regs[14] = ('ordinary-return', site)
            reads = reads + [(site, 'node', 0, 4)]
        elif code & 0xfe00 in (0xb400, 0xbc00):
            push = code & 0xfe00 == 0xb400
            numbers = [n for n in range(8) if code & 1 << n]
            if code & 0x100: numbers.append(14 if push else 15)
            require(numbers and 15 not in numbers, 'explicit saved BX return required')
            if push:
                require(not stack and numbers == [4, 14] and
                        [regs[n] for n in numbers] == [('entry', 4), ('return',)],
                        'callback must protect original R4/LR')
                stack = [regs[n] for n in numbers]
            else:
                require(len(numbers) <= len(stack), 'callback pop leaves protected frame')
                for n, token in zip(numbers, stack): regs[n] = token
                stack = stack[len(numbers):]
        elif code & 0xff87 == 0x4700:
            source = (code >> 3) & 15
            require(source < 15 and regs[source] == ('return',) and not stack and
                    all(regs[n] == ('entry', n) for n in range(4, 12)) and
                    value(regs[0]) in (constant(0), constant(1)), 'callback return/frame differs')
            require(all(token != ('query',) for token in regs), 'query alias escapes callback')
            paths.append(dict(return_value=value(regs[0])[1], conditions=facts,
                              reads=reads, writes=writes)); continue
        elif code & 0xf800 == 0x1800:
            destination, left, right = code & 7, (code >> 3) & 7, (code >> 6) & 7
            require(code & 0x400 and not code & 0x200 and right == 0,
                    'only exact alias-preserving ADD immediate zero supported')
            regs[destination] = regs[left]
        elif code & 0xf800 == 0x2000:
            regs[(code >> 8) & 7] = constant(code & 255)
        elif code & 0xf800 == 0:
            destination, source, amount = code & 7, (code >> 3) & 7, (code >> 6) & 31
            token = value(regs[source]); scalar(token)
            require(token[0] == 'constant', 'exact constant shift required')
            regs[destination] = constant(token[1] << amount)
        elif code & 0xffc0 == 0x4000:
            destination, source = code & 7, (code >> 3) & 7
            left, right = value(regs[destination]), value(regs[source]); scalar(left); scalar(right)
            regs[destination] = constant(left[1] & right[1]) if left[0] == right[0] == 'constant' else ('and', left, right)
        elif code & 0xe000 == 0x6000:
            width = 1 if code & 0x1000 else 4
            register, base = code & 7, (code >> 3) & 7
            offset = width * ((code >> 6) & 31); origin = regs[base]
            if code & 0x800:
                if origin == ('query',):
                    require(kind == 'search' and (offset, width) == (0, 4),
                            'query read touches uninitialized or unsupported bytes')
                    regs[register] = ('query-key',)
                else:
                    require(origin == ('object',) and width == 4 and offset in (0, 44),
                            'unproved callback external read origin or width')
                    regs[register] = ('object-word', offset)
                reads = reads + [(site, origin[0], offset, width)]
            else:
                token = value(regs[register])
                require(origin == ('query',) and
                        ((kind == 'byte' and (offset, width, token) == (0, 1, constant(0))) or
                         (kind == 'search' and (offset, width, token) == (8, 4, ('object',)))),
                        'callback write is not the exact permitted initialized query effect')
                writes = writes + [(site, offset, width, token)]
        elif code & 0xf800 == 0x2800:
            compared = (value(regs[(code >> 8) & 7]), constant(code & 255))
        elif code & 0xffc0 == 0x4280:
            compared = (value(regs[code & 7]), value(regs[(code >> 3) & 7]))
        elif code & 0xf000 == 0xd000:
            condition = (code >> 8) & 15
            require(condition in (0, 1) and compared is not None, 'exact equality predicate required')
            left, right = compared
            for target, equal in ((item.operands[0].imm, condition == 0), (site+2, condition != 0)):
                require(target in instructions and target > site, 'callback branch must be forward and internal')
                if left[0] == right[0] == 'constant' and (left == right) != equal: continue
                pending.append((target, list(regs), list(stack), facts+[(left, right, equal)],
                                compared, list(reads), list(writes)))
            continue
        elif code & 0xf800 == 0xe000:
            target = item.operands[0].imm
            require(target in instructions and target > site, 'callback branch must be forward and internal')
            pending.append((target, regs, stack, facts, compared, reads, writes)); continue
        else:
            raise ValueError('unsupported known-list callback instruction')
        following = site+item.size
        require(following in instructions, 'callback falls outside complete code')
        pending.append((following, regs, stack, facts, compared, reads, writes))
    require(reached == set(instructions) and len(paths) == (3 if kind == 'byte' else 2),
            'complete known callback path inventory differs')
    require(all(row['return_value'] == 1 for row in paths) if kind == 'byte' else
            sorted((row['return_value'], bool(row['writes'])) for row in paths) == [(0, True), (1, False)],
            'known callback return/effect relation differs')
    return dict(address=address, instructions=len(instructions), paths=paths,
                frame_bytes=8, protected_registers=[4, 14], getter=0x080C7B74,
                query_alias_returned=False, all_paths_interpreted=True)


def prove(data, address, rom, mapping, index, *, selector):
    require(selector == SELECTOR and type(address) is int and address in ROOTS and
            all(type(raw) is bytes for raw in (data, rom, mapping, index)),
            'explicit known-list query selector and immutable complete inputs required')
    require(len(rom) == 16*1024*1024 and sha(rom) == ROM_SHA256, 'approved complete ROM differs')
    kind, count, callback, encoded = ROOTS[address]
    require(data == bytes.fromhex(encoded), 'exact complete list query root differs')
    entries, rows = indices(mapping, index); identities = []
    needed = {address: (count, encoded), **{start: DEPENDENCIES[start] for start in
              (callback, 0x080C7CC0, 0x080C7B74, 0x0814225C)}}
    for start, (expected_count, code) in needed.items():
        body = bytes.fromhex(code); end = start+len(body)
        row = span_record(start, end, entries, rows, rom)
        require(row['mode'] == 'thumb' and row['instrs'] == expected_count and
                rom[start-ROM_BASE:end-ROM_BASE] == body, 'exact complete query dependency/count differs')
        identities.append(dict(address=start, end=end, instructions=expected_count, body_sha256=sha(body)))
    require(rom[0x14225e:0x142260] == bytes.fromhex('c046') and not any(
            int(row['rom'], 16) < 0x08142260 and int(row['end'], 16) > 0x0814225e for row in entries) and not any(
            int(row[0], 16) < 0x08142260 and int(row[1], 16) > 0x0814225e for row in rows),
            'R6 thunk padding must remain separate and unowned')
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    refinement = owner.refine(data, address, mapping)
    ins, edges, branches, calls, words = graph.graph(data, address, refinement)
    partition = graph.partition(data, address, refinement, ins, words)
    require(not branches and not words and len(ins) == count and calls == {address+16: 0x080C7CC0},
            'complete query CFG/call relation differs')
    effects = callback_effects(bytes.fromhex(DEPENDENCIES[callback][1]), callback, kind)
    query = (dict(bytes=4, initialized=[dict(offset=0, width=1, value=1)],
                  opaque_unread_offsets=[1, 2, 3], result=dict(offset=0, width=1, values=[0, 1]))
             if kind == 'byte' else
             dict(bytes=12, initialized=[dict(offset=0, width=4, entry_register=1),
                                        dict(offset=8, width=4, value=0)],
                  opaque_unread_offsets=[4, 5, 6, 7], result=dict(offset=8, width=4,
                      values=['null', 'object word from a reached node whose object key equals query key'])))
    conditions = [
        'Every reached owner/context/node/object load has its exact aligned, live, initialized, readable external extent and valid provenance; numeric addresses grant no permission.',
        'External node and object values cannot carry private query, protected frame or saved return provenance; reached external storage and continuation code do not overlap those frames.',
        'All direct and indirect calls have compatible returning ABI, private frame validity, balanced stack, preserved callee-saved registers and required noninterference.',
        'The immutable known callback identity is preserved in iterator R6; iterator R5 preserves the same live root query. The callback modifies only its recorded query field and protected private frame.',
        'Actual C declarations, nominal object/function compatibility, layout, pointer representations, effective types, object lifetime, initialized scalar reads and conversions satisfy their source-language obligations.',
        'The root continuation does not observe any outward expired R2 query alias. No callback count or list acyclicity bound, whole-program nonescape, physical permission or termination is proved.',
    ]
    return dict(schema=SCHEMA, instructions=count, partition=partition,
        calls=[[16, 'func_080C7CC0']], runtime_calls=[],
        query=query, callback_effects=effects, current_dependency_identities=identities,
        iterator=dict(address=0x080C7CC0, instructions=16, protected_frame_bytes=16,
            invariant='R6 exact known callback; R5 same root query; current node in R4 is null or external. Every callback preserves initialized query reads and writes only its permitted field.',
            initial_load=dict(base='context', offset=4, width=4),
            next_load=dict(base='each reached current node after returning callback', offset=8, width=4),
            calls_via_R6=True, no_iteration_bound=True, termination_proved=False),
        frame=dict(root_protected_bytes=4, root_local_bytes=query['bytes'],
                   iterator_protected_bytes=16, callback_protected_bytes=8,
                   all_complete_return_paths_balance=True,
                   private_callback_allocation_bytes=0),
        outward_expired_aliases=[dict(register=2, origin='root query on empty-list path',
            accessible_after_return=False, observed_by_root_continuation=False)],
        explicit_conditions=conditions,
        source_sha256={p.name: sha(p.read_bytes()) for p in sorted(Path(__file__).parent.glob('*.py'))},
        mapping_sha256=sha(mapping), index_sha256=sha(index),
        old_effect_or_owner_producer_executions=0, conditional_known_callback_effects=True,
        source_or_ELF_admission=False, native_admission=False,
        physical_memory_permission=False, actual_C_function_compatibility_proved=False,
        unconditional_termination=False)
