"""Conditional known-query effects and exact initialized-query transport.

Fresh effect interpretation, not replay of an owner/native producer. Published
reports are independently authenticated structural premises. Ordinary callees
are not declared pure: their returning ABI and memory noninterference remain
explicit conditions. No actual physical permission or termination is proved.
"""
from dataclasses import dataclass
import hashlib
import json
import re
import struct

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

SELECTOR = 'conditional-known-query-callback-effects-v1'
ROM_BASE = 0x08000000
SCALAR = ('ordinary',)
QUERY = ('query', 0)
FLAG = ('incoming-flag',)
RETURN = ('entry-return',)
MAX_STATES = 8192


def sha(data): return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok: raise ValueError(message)


def const(n): return ('constant', n & 0xffffffff)


def published(raw, pin):
    require(type(raw) is bytes and type(pin) is dict and pin.get('bytes') == len(raw) and
            pin.get('sha256') == sha(raw), 'independent published report pin differs')
    text = raw.decode()
    evidence = re.findall(r'^\* owner runtime evidence: `([^\n]+)`$', text, re.M)
    compiled = re.findall(r'^\* compiled : `([0-9a-f]+)`$', text, re.M)
    rom = re.findall(r'^\* ROM bytes: `([0-9a-f]+)` \((\d+) bytes\)$', text, re.M)
    require(len(evidence) == len(compiled) == len(rom) == 1, 'complete published evidence required')
    result = json.loads(evidence[0]); body = bytes.fromhex(compiled[0])
    require(compiled[0] == rom[0][0] and len(body) == int(rom[0][1]) == result['bytes'],
            'published whole FUNC bytes differ')
    return result, body


def decoded(body, address):
    require(type(body) is bytes and type(address) is int and address % 2 == 0 and
            0 < len(body) <= 4096 and len(body) % 2 == 0, 'bounded immutable Thumb body required')
    cs = Cs(CS_ARCH_ARM, CS_MODE_THUMB); cs.detail = True
    ins = {item.address: item for item in cs.disasm(body, address)}
    require(sum(item.size for item in ins.values()) == len(body) and address in ins,
            'complete code-only body did not decode')
    edges, calls = {}, {}
    for site, item in ins.items():
        code = int.from_bytes(item.bytes[:2], 'little')
        if item.mnemonic == 'bl':
            target = item.operands[0].imm
            require(item.size == 4 and not address <= target < address+len(body), 'ordinary call must leave owner')
            calls[site] = target; targets = [site+4]
        elif code & 0xff87 == 0x4700:
            targets = []
        elif code & 0xf800 == 0xe000:
            targets = [item.operands[0].imm]
        elif code & 0xf000 == 0xd000 and (code >> 8) & 15 < 14:
            targets = [item.operands[0].imm, site+2]
        else:
            require(item.size == 2, 'unsupported wide callback instruction')
            targets = [site+2]
        require(all(target in ins and target > site for target in targets),
                'callback CFG must be complete and forward acyclic')
        edges[site] = tuple(targets)
    return ins, edges, calls


@dataclass
class State:
    registers: list
    stack: list
    flag: tuple = FLAG

    def clone(self): return State(list(self.registers), list(self.stack), self.flag)
    def key(self): return tuple(self.registers), tuple(self.stack), self.flag
    def value(self, register):
        return ('local', -4*len(self.stack)) if register == 13 else self.registers[register]


def effects(body, address, *, selector):
    """Track formal R1, exact scalar local slots, protected saves and all paths."""
    require(selector == SELECTOR, 'explicit query-effect selector required')
    ins, edges, calls = decoded(body, address)
    regs = [SCALAR]*15
    regs[1] = QUERY
    for n in range(4, 12): regs[n] = ('entry', n)
    regs[14] = RETURN
    pending = [(address, State(regs, []))]; seen = set(); reached = set()
    reads, writes, local_reads, local_writes, ordinary, returns, call_rows = set(), set(), set(), set(), set(), set(), set()
    allocated, protected = set(), set()
    returned_aliases = set()
    maximum = 0

    def scalar(value):
        require(value[0] in ('ordinary', 'constant'), 'scalar operation observes a tracked pointer or saved origin')

    def add(value, amount):
        if amount == 0: return value
        if value[0] in ('query', 'local'): return (value[0], value[1]+amount)
        scalar(value)
        return const(value[1]+amount) if value[0] == 'constant' else SCALAR

    while pending:
        site, state = pending.pop()
        key = (site, state.key())
        if key in seen: continue
        seen.add(key); require(len(seen) <= MAX_STATES, 'query-effect state budget exceeded')
        reached.add(site); item = ins[site]; code = int.from_bytes(item.bytes[:2], 'little')
        v, r = state.value, state.registers
        terminal = False

        def memory(load, register, base, displacement, width):
            origin = v(base)
            if origin[0] in ('query', 'local'):
                offset = origin[1] + displacement
                if origin[0] == 'query':
                    if load:
                        require(offset == 0 and width == 4, 'query read must be the initialized record word')
                        reads.add((site, offset, width)); r[register] = SCALAR
                    else:
                        require(offset == 4 and width == 4 and v(register) == const(1),
                                'query write must be the exact flag word constant one')
                        writes.add((site, offset, width, 1)); state.flag = const(1)
                else:
                    position = (offset + 4*len(state.stack))//4
                    require(width == 4 and offset % 4 == 0 and
                            0 <= position < len(state.stack) and state.stack[position][0] == 'local',
                            'local access escapes allocation or touches protected saves')
                    if load:
                        value = state.stack[position][1]
                        require(value is not None, 'local rectangle read precedes its own initialization')
                        r[register] = value; local_reads.add((site, offset, width))
                    else:
                        scalar(v(register)); state.stack[position] = ('local', v(register))
                        local_writes.add((site, offset, width))
            else:
                scalar(origin)
                ordinary.add((site, 'read' if load else 'write', base, displacement, width))
                if load: r[register] = SCALAR
                else: scalar(v(register))

        if item.mnemonic == 'bl':
            require(all(v(n)[0] not in ('query', 'local', 'entry', 'entry-return') for n in range(4)),
                    'tracked query/private/saved alias reaches ordinary call argument')
            call_rows.add((site, calls[site], tuple(v(n) for n in range(4)), state.flag))
            # Explicit conditional ABI/memory summary, never arbitrary purity.
            for n in (0, 1, 2, 3, 12): r[n] = SCALAR
            r[14] = ('ordinary-return', site)
        elif code & 0xfe00 in (0xb400, 0xbc00):
            push = code & 0xfe00 == 0xb400
            numbers = [n for n in range(8) if code & 1 << n]
            if code & 0x100: numbers.append(14 if push else 15)
            require(numbers and 15 not in numbers, 'explicit saved-register BX return required')
            if push:
                require(all(v(n)[0] in ('entry', 'entry-return') for n in numbers),
                        'push must protect original entry origins')
                state.stack[:0] = [('saved', v(n)) for n in numbers]
                protected.update(range(-4*len(state.stack), -4*len(state.stack)+4*len(numbers), 4))
            else:
                require(len(numbers) <= len(state.stack) and
                        all(slot[0] == 'saved' for slot in state.stack[:len(numbers)]),
                        'pop reaches uninitialized/local storage')
                for n, slot in zip(numbers, state.stack): r[n] = slot[1]
                del state.stack[:len(numbers)]
        elif code & 0xff00 == 0xb000:
            count = code & 127
            require(count > 0, 'empty callback stack adjustment')
            if code & 0x80:
                state.stack[:0] = [('local', None)]*count
                allocated.update(range(-4*len(state.stack), -4*len(state.stack)+4*count, 4))
            else:
                require(count <= len(state.stack) and all(slot[0] == 'local' for slot in state.stack[:count]),
                        'deallocation overlaps protected saves')
                del state.stack[:count]
        elif code & 0xff87 == 0x4700:
            source = (code >> 3) & 15
            require(source < 15 and v(source) == RETURN and not state.stack and
                    all(r[n] == ('entry', n) for n in range(4, 12)) and r[0] == const(1),
                    'callback must restore its frame and return constant one')
            for n in (0, 1, 2, 3, 12):
                require(r[n][0] != 'query', 'query alias escapes callback return')
                if r[n][0] == 'local':
                    require(n == 2 and r[n][1] in allocated,
                            'unsupported private alias escapes callback return')
                    # This is an expired origin, not an accessible object or an
                    # ABI-clobbered scalar. The outer transport must retain it.
                    returned_aliases.add((site, n, r[n][1]))
            returns.add((site, state.flag)); terminal = True
        elif code & 0xfc00 == 0x4400:
            operation = (code >> 8) & 3
            destination, source = (code & 7) + ((code >> 4) & 8), (code >> 3) & 15
            require(operation == 2 and destination < 13 and source < 14, 'unsupported high-register/control operation')
            r[destination] = v(source)
        elif code & 0xf800 == 0xa800:
            position = code & 255
            require(position < len(state.stack) and state.stack[position][0] == 'local',
                    'materialized local address touches protected saves or leaves allocation')
            r[(code >> 8) & 7] = ('local', -4*len(state.stack) + 4*position)
        elif code & 0xf800 == 0x2000:
            r[(code >> 8) & 7] = const(code & 255)
        elif code & 0xf800 in (0x9000, 0x9800):
            memory(bool(code & 0x800), (code >> 8) & 7, 13, 4*(code & 255), 4)
        elif code & 0xe000 == 0x6000:
            width = 1 if code & 0x1000 else 4
            memory(bool(code & 0x800), code & 7, (code >> 3) & 7, width*((code >> 6) & 31), width)
        elif code & 0xf000 == 0x8000:
            memory(bool(code & 0x800), code & 7, (code >> 3) & 7, 2*((code >> 6) & 31), 2)
        elif code & 0xf200 == 0x5200:
            operation = (code >> 10) & 3; index = (code >> 6) & 7
            require(v(index)[0] == 'constant', 'indexed access requires exact scalar offset')
            width = 1 if operation == 1 else 2
            memory(operation != 0, code & 7, (code >> 3) & 7, v(index)[1], width)
        elif code & 0xf800 == 0x1800:
            destination, left, right = code & 7, (code >> 3) & 7, (code >> 6) & 7
            subtract = bool(code & 0x200)
            other = const(right) if code & 0x400 else v(right)
            if other[0] == 'constant': r[destination] = add(v(left), -other[1] if subtract else other[1])
            else:
                scalar(v(left)); scalar(other); r[destination] = SCALAR
        elif code & 0xf800 in (0x3000, 0x3800):
            destination = (code >> 8) & 7
            r[destination] = add(v(destination), -(code & 255) if code & 0x800 else code & 255)
        elif code & 0xe000 == 0 and code & 0x1800 != 0x1800:
            destination, source = code & 7, (code >> 3) & 7
            scalar(v(source)); r[destination] = SCALAR
        elif code & 0xfc00 == 0x4000:
            op, destination, source = (code >> 6) & 15, code & 7, (code >> 3) & 7
            require(op in (0, 9, 10), 'unsupported callback scalar operation')
            scalar(v(source))
            if op != 9: scalar(v(destination))
            if op != 10: r[destination] = SCALAR
        elif code & 0xf800 == 0x2800:
            scalar(v((code >> 8) & 7))
        elif code & 0xf800 == 0xe000 or code & 0xf000 == 0xd000 and (code >> 8) & 15 < 14:
            pass
        else:
            raise ValueError(f'unsupported query-effect instruction at {site:08X}: {item.mnemonic}')
        maximum = max(maximum, 4*len(state.stack)); require(maximum <= 256, 'private callback frame budget exceeded')
        if not terminal:
            require(edges[site], 'fallthrough callback path has no return')
            for target in edges[site]: pending.append((target, state.clone()))
    require(reached == set(ins) and returns and writes and reads and local_reads and local_writes,
            'complete callback query and private-frame effect coverage required')
    require(all(flag in (FLAG, const(1)) for _, flag in returns), 'callback query flag relation differs')
    return dict(schema=SELECTOR, address=address, end=address+len(body), body_sha256=sha(body),
        instructions=len(ins), state_count=len(seen), query_reads=sorted(reads), query_writes=sorted(writes),
        local_reads=sorted(local_reads), local_writes=sorted(local_writes), maximum_frame_bytes=maximum,
        allocated_local_word_offsets=sorted(allocated), protected_saved_word_offsets=sorted(protected),
        external_accesses=sorted(ordinary), calls=[[site, target] for site, target in sorted(calls.items())],
        ordinary_call_observations=[[site, target, list(args), list(flag)] for site, target, args, flag in sorted(call_rows)],
        returns=[[site, list(flag)] for site, flag in sorted(returns)],
        returned_private_aliases=[dict(site=site, register=n, entry_SP_offset=offset, lifetime='expired-at-return')
                                  for site,n,offset in sorted(returned_aliases)],
        relation='query.record unchanged; query.flag is its incoming word or1; returning R0 is1; exact R4-R11/SP/entry-return restored under the listed ordinary-call premises',
        tracked_query_or_private_alias_passed_to_ordinary_callees=False,
        explicit_conditions=[
            'Each ordinary call returns to its continuation, preserves R4-R11/SP, and neither reads nor writes the query object, active private/local/saved/incoming frames, or code through any argument, ambient state or hidden alias. No such memory effect is inferred from absence of a tracked argument alias.',
            'Every external callback access has valid aligned live initialized readable/writable storage as appropriate, and its effective bytes do not overlap the query object, active private frames, saved returns or code.',
            'The query is an aligned live initialized two-word object. Its designated record read and flag stores are permitted; its record value supplies no private-frame/saved-return provenance.',
            'Private stack allocation, protected saves and incoming frames are valid, live, nonwrapping and noninterfering; asynchronous mutation, exceptions and faults are not inferred away.'],
        ordinary_callee_purity_proved=False, physical_memory_permission=False,
        source_or_ELF_admission=False, termination_proved=False)


def span(address, size, count, rom, mapping, index):
    entries = [row for row in mapping if int(row['rom'], 16) == address]
    lines = [row for row in index if int(row[0], 16) == address]
    require(len(entries) == len(lines) == 1 and entries[0]['mode'] == 'thumb' and
            int(entries[0]['end'], 16) == address+size and entries[0]['instrs'] == count and
            int(lines[0][1], 16) == address+size and int(lines[0][2]) == size and int(lines[0][3]) == count and
            ROM_BASE <= address < address+size <= ROM_BASE+len(rom), 'current exact indexed span/count required')
    require(not any(row is not entries[0] and int(row['rom'], 16) < address+size and int(row['end'], 16) > address for row in mapping) and
            not any(row is not lines[0] and int(row[0], 16) < address+size and int(row[1], 16) > address for row in index),
            'current indexed owner overlaps another entry')
    return rom[address-ROM_BASE:address-ROM_BASE+size]


def target(raw, site):
    code = list(Cs(CS_ARCH_ARM, CS_MODE_THUMB).disasm(raw, site))
    require(len(code) == 1 and code[0].mnemonic == 'bl' and code[0].size == 4, 'exact direct Thumb BL required')
    # Avoid parsing disassembler text: decode the architectural signed offset.
    first, second = struct.unpack('<HH', raw)
    offset = ((first & 2047) << 12) | ((second & 2047) << 1)
    if offset & 0x400000: offset -= 0x800000
    return site+4+offset


def prove(body, address, rom, mapping, index, *, callback_report, transport_report, trusted_pins, selector):
    require(selector == SELECTOR and all(type(v) is bytes for v in (body, rom, mapping, index)),
            'explicit query closure and immutable inputs required')
    cb, callback_body = published(callback_report, trusted_pins['callback'])
    tr, transport_body = published(transport_report, trusted_pins['transport'])
    require(cb['manifest']['profile'] == 'elf-symbol-thumb-acyclic-stack-alias-v1' and
            tr['manifest']['profile'] == 'elf-symbol-thumb-conditional-two-word-callback-closure-v1' and
            cb['rom_sha256'] == tr['rom_sha256'] == sha(rom), 'published structural context differs')
    entries = json.loads(mapping); rows = [line.split() for line in index.decode().splitlines() if line.strip() and not line.lstrip().startswith('#')]
    require(body == span(address, 44, 18, rom, entries, rows), 'complete original query root differs')
    require(body[:22] == bytes.fromhex('00b582b0021c00290cd00091002001900349101c6a46') and
            body[26:32] == bytes.fromhex('019803e00000') and body[36:] == bytes.fromhex('002002b002bc0847'),
            'root must be the complete conditional initialized two-word query')
    callback = struct.unpack_from('<I', body, 32)[0]
    require(callback == cb['address'] | 1 and target(body[22:26], address+22) == tr['address'],
            'root callback literal/direct wrapper target differs')
    require(callback_body == span(cb['address'], len(callback_body), cb['instructions'], rom, entries, rows) and
            transport_body == span(tr['address'], 28, 11, rom, entries, rows), 'published callback/wrapper bytes differ')
    closure = tr['manifest']['proof']['callback_closure']
    worker, adapter = closure['iterator'], closure['adapter']; getter = adapter['getter']
    dependencies = []
    for proof in (worker, adapter, getter):
        size = proof['end']-proof['address']; count = proof.get('instructions', proof.get('frame', {}).get('instructions'))
        data = span(proof['address'], size, count, rom, entries, rows)
        require(sha(data) == proof['body_sha256'], 'frozen transport dependency body differs')
        dependencies.append((proof['address'], data))
    wi, ad, leaf = [data for _, data in dependencies]
    require(transport_body[:14] == bytes.fromhex('00b582b000920191006903496a46') and
            transport_body[18:24] == bytes.fromhex('02b001bc0047') and
            target(transport_body[14:18], tr['address']+14) == worker['address'] and
            struct.unpack_from('<I', transport_body, 24)[0] == adapter['address'] | 1,
            'wrapper query-token transport differs')
    require(wi[:20] == bytes.fromhex('70b50e1c151c446800e0a468002c05d0201c291c') and
            wi[24:] == bytes.fromhex('0028f6d170bc01bc0047') and
            target(wi[20:24], worker['address']+20) == worker['thunk'][1], 'iterator query-token transport differs')
    require(ad[:4] == bytes.fromhex('10b50c1c') and ad[8:12] == bytes.fromhex('21686268') and
            ad[16:] == bytes.fromhex('10bc02bc0847') and leaf == bytes.fromhex('00687047') and
            target(ad[4:8], adapter['address']+4) == getter['address'] and
            target(ad[12:16], adapter['address']+12) == adapter['callback']['thunk'],
            'adapter/getter must transport query only to the known callback R1')
    for canonical, opcode in ((worker['thunk'], bytes.fromhex('3047')), (adapter['callback']['canonical'], bytes.fromhex('1047'))):
        _, lo, hi, digest = canonical
        require(hi == lo+4 and span(lo, 2, 1, rom, entries, rows) == opcode and
                sha(rom[lo-ROM_BASE:hi-ROM_BASE]) == digest and
                not any(int(row['rom'],16) < hi and int(row['end'],16) > lo+2 for row in entries),
                'canonical thunk and separately indexed padding differ')
    observed = effects(callback_body, cb['address'], selector=SELECTOR)
    require(observed['maximum_frame_bytes'] == 48 and
            observed['allocated_local_word_offsets'] == list(range(-48, -16, 4)) and
            observed['protected_saved_word_offsets'] == [-16, -12, -8, -4],
            'query closure requires the exact32-byte rectangle and16-byte save frame')
    declared = [[cb['address']+offset, int(name[5:], 16)] for offset, name in cb['manifest']['bindings']['calls']]
    require(observed['instructions'] == cb['instructions'] and observed['calls'] == declared,
            'published callback graph/bindings differ from new formal effects')
    return dict(schema=SELECTOR, address=address, end=address+44, instructions=18,
        body_sha256=sha(body), ROM_sha256=sha(rom), mapping_sha256=sha(mapping), index_sha256=sha(index),
        callback_effects=observed, frozen_authorities=trusted_pins,
        transport_lift='Exact wrapper/iterator/adapter/getter/thunk bytes transport the outer query token into callback R1 without dereferencing it. This establishes the known-private-query instance; the old unknown-scalar/no-private-provenance restriction is not silently imported or asserted satisfied.',
        frame_layout_relative_to_root_entry_SP=dict(query=[-12,-4], root_save=[-4,0],
            wrapper_descriptor=[-24,-16], wrapper_save=[-16,-12], iterator_saves=[-40,-24],
            adapter_saves=[-48,-40], callback_local=[-48-observed['maximum_frame_bytes'],-64], callback_saves=[-64,-48]),
        query_initialization=dict(record='root entry R1', flag=0, call_argument='R2 is root entrySP-12'),
        query_effect='For every finite number of completed callbacks, record is unchanged and flag is0or1. A reached flag store sets1; once1 it remains1 under the explicit external-effect conditions.',
        stale_alias_transport=dict(callback_returns=observed['returned_private_aliases'],
            null_record_R2=dict(register=2,origin='root-entry-R0',caller_origin_preserved=True),
            no_callback_R2=dict(register=2, root_entry_SP_offset=-24, origin='expired-wrapper-descriptor'),
            callback_R2=[dict(register=2,root_entry_SP_offset=row['entry_SP_offset']-48,
                origin='expired-callback-local')for row in observed['returned_private_aliases']],
            nonobservation='Exact iterator tail and wrapper/root continuations do not read R2. On a later iteration the getter reads onlyR0, then the adapter replaces R2 with the authenticated callback code pointer before the thunk. Expired R2 origins are retained at outer return and are not memory permissions.',
            outward_aliases_erased=False, caller_use_after_outer_return_proved=False),
        root_return_origins=dict(R0='zero on null record; query.flag on a returning nonnull path',
            R1='original root entry LR', R2='case split retained in stale_alias_transport',
            R3_R12='entry origins on the null/no-callback paths; ordinary callback-clobbered values otherwise'),
        return_effect='Null record returns0 without calling wrapper; a returning nonnull path returns the initialized query flag. Every returning known callback yields1. No iteration count or unconditional return is asserted.',
        explicit_conditions=observed['explicit_conditions']+[
            'Every reached owner/list/node/getter load in the authenticated transport is valid, aligned, live and initialized, and does not overlap any active frame, the query or code. No list extent, acyclicity or iterator termination is assumed.',
            'All nested frames occupy the stated disjoint nonwrapping stack intervals and have valid lifetime/access permissions. The designated query reads and writes are the only permitted observations of the outer query through its transported alias.',
            'Ordinary callback calls and external accesses preserve the wrapper descriptor, iterator/adapter state, all saved returns and the query record/flag except for the two designated callback flag stores; ambient aliases provide no exemption.',
            'Concrete C object layout, compatible function types, calling convention and source/ELF binding remain separate admission obligations.'],
        old_owner_or_transport_producer_executions=0, ordinary_callee_purity_proved=False,
        physical_memory_permission=False, iteration_bound_assumed=False, termination_proved=False,
        source_or_ELF_admission=False, native_admission=False)
