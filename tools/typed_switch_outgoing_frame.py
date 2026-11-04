"""Explicit two-object switch with six ordinary outgoing words, never a local buffer."""

SELECTOR = 'typed-outgoing-six-words-v1'
SCHEMA = 'elf-symbol-thumb-switch-typed-outgoing-frame-v1'
SUMMARY = 'one typed two-object Thumb switch with six initialized outgoing words; ordinary conditional call ABI'
FRAME_BYTES = 24


def selector_for_report(report):
    """Recover only this report family; callers must replay full fresh evidence."""
    import json
    from match_evidence import switch_manifest
    lines = report.splitlines()
    if not any('switch-typed-outgoing-frame' in line or SELECTOR in line or
               line.lstrip().startswith('* switches:') and SUMMARY in line or
               line.lstrip().startswith('* switch manifest') and 'frame_policy' in line
               for line in lines):
        return None
    if [line for line in lines if line.lstrip().startswith('* verification')] != \
            [f'* verification: `{SCHEMA}`'] or \
            [line for line in lines if line.lstrip().startswith('* switches')] != \
            [f'* switches: {SUMMARY}']:
        raise ValueError('mixed or malformed typed outgoing switch selection')
    manifests = [line for line in lines if line.lstrip().startswith('* switch manifest')]
    prefix = '* switch manifest: `'
    if len(manifests) != 1 or not manifests[0].startswith(prefix) or not manifests[0].endswith('`'):
        raise ValueError('missing or malformed typed outgoing switch manifest')
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError('duplicate typed outgoing switch manifest key')
            result[key] = value
        return result
    encoded = manifests[0][len(prefix):-1]
    try:
        manifest = json.loads(encoded, object_pairs_hook=unique)
    except (ValueError, TypeError, RecursionError) as error:
        raise ValueError('malformed typed outgoing switch manifest') from error
    if type(manifest) is not dict or switch_manifest(manifest) != encoded or \
            manifest.get('frame_policy') != SELECTOR:
        raise ValueError('missing or malformed typed outgoing switch policy')
    forbidden = ('* switch constants', '* scalar frame', '* function address',
                 '* function-address', '* function buffer', '* buffer', '* signed',
                 '* unsigned', '* addressed signed', '* owner runtime',
                 '* private float', '* software double', '* inert', '* empty')
    if any(line.lstrip().lower().startswith(forbidden) for line in lines):
        raise ValueError('mixed typed outgoing switch profiles')
    return SELECTOR


def fingerprint(address, data, manifest):
    import hashlib
    from match_evidence import switch_manifest
    proof = hashlib.sha256()
    for payload in (SCHEMA.encode('ascii'), address.to_bytes(4, 'little'),
                    data, switch_manifest(manifest).encode('ascii')):
        proof.update(len(payload).to_bytes(8, 'little'))
        proof.update(payload)
    return proof.hexdigest()


def check_context(selector, thumb, calls, relocations, objects, incompatible):
    if type(selector) is not str or selector != SELECTOR or thumb is not True or \
            type(calls) is not dict or not 1 <= len(calls) <= 5 or \
            type(relocations) is not dict or not relocations or \
            type(objects) is not dict or len(objects) != 2 or \
            any(value is not None and value is not False for value in incompatible):
        raise ValueError('typed outgoing switch requires its isolated explicit ordinary Thumb policy')
    literal = min(relocations)
    if sorted(objects) != [literal - 8, literal - 4]:
        raise ValueError('typed outgoing switch requires exactly two adjacent interposed object words')


def verify_frame(instructions, edges, address, calls):
    """Prove outgoing-slot ownership, initialization, and lifetime on every reached path.

    The existing verifier supplies complete CFG, saved-return restoration, balanced
    frames, typed literal ownership, and ordinary direct-call ABI checks. No local
    address may be materialized. Outgoing values need not survive a call and are
    never read by the caller; no callee memory-effect theorem follows.
    """
    from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_SP
    from match import thumb_stack_adjustment
    allocations, releases = [], []
    for site, item in instructions.items():
        adjustment = thumb_stack_adjustment(item)
        if adjustment:
            if adjustment == -FRAME_BYTES // 4:
                allocations.append(site)
            elif adjustment == FRAME_BYTES // 4:
                releases.append(site)
            else:
                raise ValueError('typed outgoing switch requires one exact 24-byte fixed allocation')
        elif item.mnemonic.startswith(('ldm', 'stm')) or any(
                operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP
                for operand in item.operands) and item.mnemonic not in ('push', 'pop'):
            raise ValueError('typed outgoing switch excludes stack-address materialization and block transfers')
    if len(allocations) != 1 or len(releases) != 1:
        raise ValueError('typed outgoing switch requires one allocation and one common release')
    allocation, release = allocations[0], releases[0]
    pending = [(address, 0, 0)]
    seen = set()
    while pending:
        site, phase, initialized = pending.pop()
        state = (site, phase, initialized)
        if state in seen:
            continue
        seen.add(state)
        item = instructions[site]
        if site == allocation:
            if phase != 0:
                raise ValueError('typed outgoing allocation is repeated or out of lifetime')
            phase = 1
        elif site == release:
            if phase != 1:
                raise ValueError('typed outgoing release is outside its allocation')
            phase, initialized = 2, 0
        for operand in item.operands:
            if operand.type != ARM_OP_MEM or operand.mem.base != ARM_REG_SP:
                continue
            if phase != 1 or item.mnemonic != 'str' or item.size != 2 or \
                    operand.mem.index or operand.mem.disp not in range(0, FRAME_BYTES, 4):
                raise ValueError('typed outgoing access must write an owned aligned outgoing word')
            initialized |= 1 << (operand.mem.disp // 4)
        if site in calls and (phase != 1 or initialized != 63):
            raise ValueError('all six outgoing words must be initialized on every path before a call')
        successors = edges[site]
        if not successors and phase != 2:
            raise ValueError('typed outgoing normal return must follow frame release')
        # A saved-register push/pop inside the live outgoing region would shift
        # its slots. Existing balanced-frame checks alone do not prohibit that.
        if phase == 1 and item.mnemonic in ('push', 'pop'):
            raise ValueError('typed outgoing slots cannot move inside their live frame')
        pending.extend((target, phase, initialized) for target in successors)
