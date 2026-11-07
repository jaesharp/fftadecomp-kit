"""Closed Thumb bitvector relation for a conditional halfword add/clamp slice.

This component proves a relation on two distinct symbolic local halfwords.
Owner coverage, entry bindings and physical memory are separate composition
premises. It neither grants memory permissions nor admits original C or ELF.
"""
import hashlib
import json

import match

SELECTOR = 'conditional-thumb-halfword-add-clamp-bitvector-v1'
CHANNEL, ADJUSTMENT = ('channel16',), ('adjustment16',)
MAX_PATH_STEPS, MAX_PATHS = 64, 16
MASK = 0xffffffff


def const(value):
    return ('constant', value & MASK)


def add32(left, right):
    if left[0] == right[0] == 'constant':
        return const(left[1]+right[1])
    return ('add32', *sorted((left, right), key=repr))


def low16(value):
    if value[0] == 'constant':
        return const(value[1] & 65535)
    if value[0] in ('channel16', 'adjustment16', 'add16', 'low16'):
        return value
    if value[0] == 'sext16':
        return value[1]
    if value[0] == 'add32':
        return ('add16', *sorted((low16(value[1]), low16(value[2])), key=repr))
    return ('low16', value)


def sext16(value):
    value = low16(value)
    if value[0] == 'constant':
        return const(value[1] if value[1] < 32768 else value[1]-65536)
    return ('sext16', value)


def shift(value, amount, arithmetic=False):
    if not amount:
        return value
    if arithmetic and amount == 16 and value[0] == 'lsl32' and value[2] == 16:
        return sext16(value[1])
    return ('asr32' if arithmetic else 'lsl32', value, amount)


def evaluate(expression, channel, adjustment):
    """Concrete bitvector semantics, used by focused finite checks."""
    op = expression[0]
    if op == 'constant':
        return expression[1]
    if op == 'channel16':
        return channel & 65535
    if op == 'adjustment16':
        return adjustment & 65535
    if op in ('add32', 'add16'):
        return (evaluate(expression[1], channel, adjustment)+evaluate(expression[2], channel, adjustment)) & (MASK if op == 'add32' else 65535)
    value = evaluate(expression[1], channel, adjustment)
    if op == 'low16':
        return value & 65535
    if op == 'sext16':
        value &= 65535
        return (value if value < 32768 else value-65536) & MASK
    if op == 'lsl32':
        return (value << expression[2]) & MASK
    if op == 'asr32':
        return ((value if value < (1 << 31) else value-(1 << 32)) >> expression[2]) & MASK
    raise ValueError('unsupported bitvector expression')


def predicate(relation, left, right):
    if relation in ('eq', 'ne') and right == 0 and left[0] == 'sext16':
        left = left[1]
    return relation, left, right


def predicate_value(guard, channel, adjustment):
    relation, expression, right = guard
    left = evaluate(expression, channel, adjustment)
    if relation.startswith('s'):
        left = left if left < (1 << 31) else left-(1 << 32)
    return {'eq': left == right, 'ne': left != right, 'slt': left < right,
            'sge': left >= right, 'sle': left <= right, 'sgt': left > right}[relation]


def expected_cases():
    total = low16(add32(CHANNEL, ADJUSTMENT)); signed = sext16(total)
    nonzero = predicate('ne', ADJUSTMENT, 0)
    return {
        (frozenset((predicate('eq', ADJUSTMENT, 0),)), CHANNEL),
        (frozenset((nonzero, predicate('slt', signed, 0))), const(0)),
        (frozenset((nonzero, predicate('sge', signed, 0), predicate('sle', signed, 31))), total),
        (frozenset((nonzero, predicate('sge', signed, 0), predicate('sgt', signed, 31))), const(31)),
    }


def region(data, address, entry, exit_site, bindings, allowed_sites, *, selector, manifest=None):
    if selector != SELECTOR or type(selector) is not str or type(data) is not bytes:
        raise ValueError('halfword arithmetic requires explicit typed selector/body')
    if type(bindings) is not dict or type(allowed_sites) not in (set, frozenset) or not allowed_sites:
        raise ValueError('halfword arithmetic needs explicit owner boundaries and entry bindings')
    if any(type(site) is not int or site & 1 or not address <= site < address+len(data) for site in allowed_sites):
        raise ValueError('halfword arithmetic allowed site leaves exact owner')
    if entry not in allowed_sites or exit_site not in allowed_sites or entry == exit_site:
        raise ValueError('halfword arithmetic entry/exit not distinct owner instructions')
    registers = {}
    for register, binding in bindings.items():
        if type(register) is not int or not 0 <= register <= 12:
            raise ValueError('halfword arithmetic binding changes control register')
        if type(binding) is int:
            registers[register] = const(binding)
        elif binding == 'channel_pointer':
            registers[register] = ('pointer', 'channel')
        elif binding == 'adjustment_pointer':
            registers[register] = ('pointer', 'adjustment')
        elif binding == 'channel_value':
            registers[register] = CHANNEL
        else:
            raise ValueError('unsupported halfword arithmetic entry binding')
    if not {('pointer', 'channel'), ('pointer', 'adjustment')} <= set(registers.values()):
        raise ValueError('both distinct local halfword pointer bindings are required')
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB); decoder.detail = True
    pending = [(entry, registers, {'channel': CHANNEL, 'adjustment': ADJUSTMENT}, None, (), (), ())]
    paths, reached = [], set()
    while pending:
        site, regs, memory, comparison, guards, trace, effects = pending.pop()
        if site == exit_site:
            paths.append({'guards': guards, 'channel': memory['channel'], 'trace': trace, 'effects': effects})
            if len(paths) > MAX_PATHS:
                raise ValueError('halfword arithmetic path budget exceeded')
            continue
        if site in trace or len(trace) >= MAX_PATH_STEPS:
            raise ValueError('halfword arithmetic region contains a cycle or exceeds step bound')
        if site not in allowed_sites:
            raise ValueError('halfword arithmetic branch leaves retained owner instruction set')
        decoded = list(decoder.disasm(data[site-address:site-address+4], site, count=1))
        if len(decoded) != 1 or decoded[0].size != 2:
            raise ValueError('halfword arithmetic instruction is not exact Thumb16')
        item = decoded[0]; raw = int.from_bytes(item.bytes, 'little')
        regs, memory = dict(regs), dict(memory)
        trace = trace+(site,); reached.add(site)

        def value(register):
            if register not in regs:
                raise ValueError('halfword arithmetic reads an unbound entry register')
            return regs[register]

        def scalar_value(register):
            result = value(register)
            if result[0] == 'pointer':
                raise ValueError('halfword arithmetic interprets pointer as scalar')
            return result

        def local(base, displacement=0):
            pointer = value(base)
            if pointer[0] != 'pointer' or displacement:
                raise ValueError('halfword arithmetic access leaves its two local cells')
            return pointer[1]

        target = site+2
        if raw & 0xf000 == 0xd000:
            condition = (raw >> 8) & 15
            if condition not in (0, 10, 13) or comparison is None:
                raise ValueError('halfword arithmetic branch lacks exact CMP flags or supported signed condition')
            yes, no = {0: ('eq', 'ne'), 10: ('sge', 'slt'), 13: ('sle', 'sgt')}[condition]
            delta = raw & 255; delta = delta if delta < 128 else delta-256
            branch = site+4+2*delta
            for destination, relation in ((branch, yes), (target, no)):
                pending.append((destination, regs, memory, comparison,
                    guards+(predicate(relation, *comparison),), trace, effects))
            continue
        if raw & 0xf800 == 0xe000:
            delta = raw & 2047; delta = delta if delta < 1024 else delta-2048
            target = site+4+2*delta
        elif raw & 0xf800 == 0x2800:
            comparison = (scalar_value((raw >> 8) & 7), raw & 255)
        elif raw & 0xf800 == 0x2000:
            regs[(raw >> 8) & 7] = const(raw & 255); comparison = None
        elif raw & 0xff00 == 0x4600:
            destination, source = (raw & 7)+((raw >> 4) & 8), (raw >> 3) & 15
            if destination > 12 or source > 12:
                raise ValueError('halfword arithmetic MOV changes control state')
            regs[destination] = value(source)
        elif raw & 0xfe00 == 0x1800:
            regs[raw & 7] = add32(scalar_value((raw >> 3) & 7), scalar_value((raw >> 6) & 7))
            comparison = None
        elif raw & 0xf800 in (0x0000, 0x1000):
            arithmetic = raw & 0xf800 == 0x1000
            amount = (raw >> 6) & 31
            regs[raw & 7] = shift(scalar_value((raw >> 3) & 7), amount or (32 if arithmetic else 0), arithmetic)
            comparison = None
        elif raw & 0xf800 in (0x8000, 0x8800):
            cell = local((raw >> 3) & 7, ((raw >> 6) & 31)*2)
            if raw & 0xf800 == 0x8800:
                regs[raw & 7] = memory[cell]
                effects += (('read-u16', site, cell),)
            else:
                if cell != 'channel':
                    raise ValueError('halfword arithmetic overwrites adjustment or another object')
                memory[cell] = low16(scalar_value(raw & 7))
                effects += (('write-u16', site, cell, memory[cell]),)
        elif raw & 0xfe00 == 0x5e00:
            if scalar_value((raw >> 6) & 7) != const(0):
                raise ValueError('halfword signed load lacks exact zero index')
            cell = local((raw >> 3) & 7)
            regs[raw & 7] = sext16(memory[cell]); effects += (('read-s16', site, cell),)
        else:
            raise ValueError('unsupported halfword arithmetic instruction: '+item.mnemonic)
        pending.append((target, regs, memory, comparison, guards, trace, effects))
    observed = {(frozenset(path['guards']), path['channel']) for path in paths}
    if len(paths) != 4 or observed != expected_cases():
        raise ValueError('actual halfword paths differ from wrapped signed add/clamp relation')
    result = {'schema': SELECTOR, 'owner_address': address, 'owner_end': address+len(data),
        'body_sha256': hashlib.sha256(data).hexdigest(), 'entry': entry, 'exit': exit_site,
        'entry_bindings': sorted(bindings.items()), 'reached_sites': sorted(reached), 'paths': paths,
        'relation': 'd==0 ? c : (s16((c+d)&65535)<0 ? 0 : min(s16((c+d)&65535),31))',
        'input_bit_widths': {'channel': 16, 'adjustment': 16},
        'signed_sum_narrowing_precedes_clamp': True,
        'zero_adjustment_preserves_unrestricted_channel': True,
        'memory_premises': 'Two distinct initialized aligned local halfwords; authenticated entry pointers/value/constant bindings; no interfering memory effects during the slice.',
        'C_compatibility': {'channel_domains_from_caller_required': [[0,31],[0,255]],
            'promoted_sum_bounds_for_channel_u8': [-32768,33022],
            'promoted_signed32_overflow': False,
            'required_target_conversion': 'Out-of-range int to signed16 conversion keeps low16 bits and interprets bit15 as sign. This implementation-defined conversion is an explicit target condition, not a portable C theorem.',
            'source_parsed_or_admitted': False},
        'physical_memory_permission': False, 'whole_owner_numeric_equivalence': False,
        'source_or_ELF_admission': False, 'native_admission': False}
    if manifest is not None and json.dumps(manifest, sort_keys=True) != json.dumps(result, sort_keys=True):
        raise ValueError('halfword arithmetic manifest differs from fresh result')
    return result


def certificate_digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def authenticate_entry_pointer_uses(data, address, paths, bindings, pointer_access_sites):
    """A later location fact cannot justify earlier reads/copies of a pointer.

    Callers reusing paths must independently authenticate their exhaustive
    arithmetic certificate and exact body. compose supplies fresh paths itself.
    No pointer is read or overwritten before its selected witnessed access;
    paths that skip that access must not use the pointer anywhere in the slice.
    """
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB); decoder.detail = True
    witnessed = []
    for register,binding in bindings.items():
        if binding not in ('channel_pointer','adjustment_pointer'):
            continue
        access = pointer_access_sites.get(register); seen = False
        for path in paths:
            for site in path['trace']:
                if site == access:
                    seen = True; break
                decoded = list(decoder.disasm(data[site-address:site-address+4],site,count=1))
                if len(decoded)!=1 or decoded[0].size!=2:
                    raise ValueError('halfword pointer-use trace leaves exact Thumb16 body')
                read,written = decoded[0].regs_access()
                if match.ARM_REG_R0+register in set(read)|set(written):
                    raise ValueError('halfword entry pointer is read or changed before its witnessed access')
        if not seen:
            raise ValueError('halfword pointer witness is outside arithmetic paths')
        witnessed.append({'register':register,'first_access':access,'earlier_reads_or_writes':False})
    return witnessed


def compose(data, address, entry, exit_site, bindings, pointer_access_sites, preloaded_stores,
            frame_certificate, numeric_certificate, *, selector, reuse_authority):
    """Authenticate logical entry bindings against independently proved facts.

    A unique straight predecessor chain from a zero-extending load and local
    store establishes a preloaded register/local relation. Constant bindings
    must be singleton values in the retained numerical certificate. Local role
    alternatives come from the retained complete initialized-frame proof.
    """
    if type(reuse_authority) is not dict or reuse_authority.get('independently_established_frozen_certificates') is not True:
        raise ValueError('halfword composition requires independent certificate authority')
    for name, certificate in (('frame', frame_certificate), ('numeric', numeric_certificate)):
        if reuse_authority.get(name+'_sha256') != certificate_digest(certificate):
            raise ValueError('halfword reused certificate digest differs')
        if certificate['address'] != address or certificate['end'] != address+len(data) or certificate['body_sha256'] != hashlib.sha256(data).hexdigest():
            raise ValueError('halfword reused certificate belongs to another exact owner')
    if frame_certificate['ROM_sha256'] != numeric_certificate['ROM_sha256'] or frame_certificate['partition'] != numeric_certificate['partition']:
        raise ValueError('halfword reused ROM or complete partition differs')
    continuation = frame_certificate['continuation']
    if continuation.get('local_reads_have_definite_prior_machine_byte_writes') is not True:
        raise ValueError('halfword composition lacks definite initialized local reads')
    sites = set(continuation['continuation_sites'])
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB); decoder.detail = True
    instructions, predecessors = {}, {site:set() for site in sites}
    for site in sites:
        items = list(decoder.disasm(data[site-address:site-address+4], site, count=1))
        if len(items) != 1 or items[0].size != 2:
            raise ValueError('halfword retained continuation is not Thumb16')
        item = items[0]; instructions[site] = item
        if item.mnemonic == 'bx':
            targets = ()
        elif item.id == match.ARM_INS_B:
            targets = (item.operands[0].imm,) if item.mnemonic == 'b' else (item.operands[0].imm, site+2)
        elif item.mnemonic == 'bl':
            raise ValueError('halfword seed graph has an uncomposed call')
        else:
            targets = (site+2,)
        for target in targets:
            if target not in sites:
                raise ValueError('halfword retained seed graph is not closed')
            predecessors[target].add(site)
    numeric = {row['site']:row['ranges'] for row in numeric_certificate['fixed_point_states']}
    if entry not in numeric:
        raise ValueError('halfword entry has no numerical certificate')
    records = continuation['records']
    role_offsets = {}
    for register, binding in bindings.items():
        if type(binding) is int:
            if not 0 <= binding <= MASK or numeric[entry][register] != [binding, binding]:
                raise ValueError('halfword constant binding is not an authenticated singleton')
        elif binding in ('channel_pointer','adjustment_pointer'):
            site = pointer_access_sites.get(register)
            if site not in instructions:
                raise ValueError('halfword pointer binding lacks actual local access')
            raw = int.from_bytes(instructions[site].bytes, 'little')
            if raw & 0xf800 not in (0x8000,0x8800) or (raw >> 3)&7 != register or (raw >> 6)&31:
                raise ValueError('halfword pointer binding differs from actual zero-offset local access')
            kind = 'local-write' if raw & 0xf800 == 0x8000 else 'local-read'
            offsets = {row[2] for row in records if row[0] == kind and row[1] == site and row[3] == 2}
            if not offsets:
                raise ValueError('halfword pointer binding lacks retained halfword locations')
            role_offsets.setdefault(binding,set()).update(offsets)
        elif binding != 'channel_value':
            raise ValueError('unsupported halfword composition binding')
    if set(role_offsets) != {'channel_pointer','adjustment_pointer'} or any(
            left < right+2 and right < left+2 for left in role_offsets['channel_pointer'] for right in role_offsets['adjustment_pointer']):
        raise ValueError('halfword channel and adjustment local alternatives overlap')
    preload_evidence = []
    for register,binding in bindings.items():
        if binding != 'channel_value':
            continue
        store = preloaded_stores.get(register)
        if store not in instructions:
            raise ValueError('halfword preloaded value has no actual preceding store')
        raw = int.from_bytes(instructions[store].bytes, 'little'); base = (raw >> 3)&7
        if raw & 0xf800 != 0x8000 or raw & 7 != register or (raw >> 6)&31 or bindings.get(base) != 'channel_pointer':
            raise ValueError('halfword preload store does not bind the channel register')
        offsets = {row[2] for row in records if row[0]=='local-write' and row[1]==store and row[3]==2}
        if not offsets or offsets != role_offsets['channel_pointer']:
            raise ValueError('halfword preload writes different local alternatives')
        load = store-2
        if load not in instructions or predecessors[store] != {load}:
            raise ValueError('halfword preload store can bypass its zero-extending load')
        raw_load = int.from_bytes(instructions[load].bytes, 'little')
        if raw_load & 0xf800 not in (0x7800,0x8800) or raw_load & 7 != register:
            raise ValueError('halfword preload register lacks a zero-extending load')
        previous = store
        for site in range(store+2,entry+1,2):
            if site not in instructions or predecessors[site] != {previous}:
                raise ValueError('halfword preload entry has an alternative predecessor')
            if site == entry:
                break
            item = instructions[site]
            if item.id == match.ARM_INS_B or item.mnemonic in ('bl','bx') or item.mnemonic.startswith(('str','stm','push')):
                raise ValueError('halfword preload chain changes control or memory')
            _,written = item.regs_access()
            if match.ARM_REG_R0+register in written or match.ARM_REG_R0+base in written:
                raise ValueError('halfword preload chain changes value or local pointer')
            previous = site
        if store >= entry:
            raise ValueError('halfword preload store does not precede slice entry')
        preload_evidence.append({'register':register,'load':load,'store':store,'entry':entry,
            'load_width':1 if raw_load&0xf800==0x7800 else 2,'offsets':sorted(offsets),
            'unique_predecessors_and_unchanged_value':True})
    proof = region(data,address,entry,exit_site,bindings,sites,selector=selector)
    first_uses = authenticate_entry_pointer_uses(data,address,proof['paths'],bindings,pointer_access_sites)
    proof['authenticated_entry_evidence'] = {
        'local_role_offsets':{key:sorted(value) for key,value in role_offsets.items()},
        'preloaded_registers':preload_evidence,
        'constants':[(register,value) for register,value in bindings.items() if type(value) is int],
        'pointer_first_uses':first_uses,
        'reuse_authority':reuse_authority,
        'required_unproved_conditions':frame_certificate['required_unproved_conditions'],
        'old_producer_executions':0}
    return proof
