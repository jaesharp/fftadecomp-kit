"""Unobserved saved entry aliases across exact conditional ordinary ABI calls."""
import hashlib

import match
import local_long_branch_profile as frame

PRESERVED = frozenset(range(match.ARM_REG_R0+4,match.ARM_REG_R0+12))
MAX_STATES = 4096
MAX_SAVED_WORDS = 64


def prove(data,ins,edges,calls,partition,address,watched,arguments):
    written=set().union(*(set(item.regs_access()[1]) for item in ins.values()))
    relaxed=set(watched)&PRESERVED&written
    if not relaxed:
        return tuple(watched),None
    if relaxed&set(arguments):
        raise ValueError('callee restoration cannot hide an explicit pointer argument')
    pending=[(address,frozenset(relaxed),())]
    seen=set()
    while pending:
        site,opaque,saved=pending.pop()
        state=site,opaque,saved
        if state in seen:continue
        seen.add(state)
        if len(seen)>MAX_STATES:
            raise ValueError('callee alias restoration state budget exceeded')
        item=ins[site]
        read,changed=map(set,item.regs_access())
        registers=tuple(op.reg for op in item.operands if op.type==match.ARM_OP_REG)
        following_saved=saved
        if item.mnemonic=='push':
            following=opaque
            following_saved=tuple(reg in opaque for reg in registers)+saved
            if len(following_saved)>MAX_SAVED_WORDS:
                raise ValueError('callee alias private save-word budget exceeded')
        elif item.mnemonic=='pop':
            if len(saved)<len(registers):
                raise ValueError('callee alias pop exceeds its private saved words')
            following=(opaque-set(registers))|{reg for reg,taint in zip(registers,saved) if taint}
            following_saved=saved[len(registers):]
        elif site in calls:
            if opaque:
                raise ValueError('callee call observes an unoverwritten opaque entry alias')
            following=opaque
        else:
            if match.ARM_REG_SP in read or match.ARM_REG_SP in changed:
                raise ValueError('callee alias saves permit only private PUSH/POP stack access')
            if read&opaque:
                raise ValueError('callee observes an opaque live entry alias')
            following=opaque-changed
        pending.extend((target,frozenset(following),following_saved) for target in edges[site])
    certificate=frame.prove_frame(ins,edges,address,{},calls,
        call_preservation={site:PRESERVED for site in calls})
    record=dict(address=address,body_sha256=hashlib.sha256(data).hexdigest(),
        partition=partition,frame=certificate,
        registers=sorted(reg-match.ARM_REG_R0 for reg in relaxed),
        unobserved_entry_states=len(seen),calls=sorted(calls.items()),
        conditional_ABI='Existing compatible returning ordinary ABI preserves R4-R11. '
            'Every relaxed entry alias is overwritten before every call, private saves '
            'are inaccessible except PUSH/POP, and actual nested effects and frames '
            'must independently complete. No numeric or arbitrary-memory theorem.')
    return tuple(sorted(set(watched)-relaxed)),record
