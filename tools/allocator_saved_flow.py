"""Conditional saved-origin restoration across a closed Thumb helper graph.

No ABI summary is assumed. Actual PUSH/MOV/POP origins and every CFG edge are
checked. All memory access, saved-word preservation, normal-return, installed
zero identity and noninterference conditions remain external. This component
does not interpret unknown return registers as scalars or erase alias risk.
"""
from dataclasses import dataclass
import hashlib

from capstone.arm import ARM_OP_MEM, ARM_REG_R0, ARM_REG_SP, ARM_REG_LR, ARM_REG_PC
import descriptor_frame_shape_prerequisite as frame

SELECTOR='conditional-allocator-saved-origin-flow-v1'
UNKNOWN=('unknown-including-pointer-or-expired-alias',)


def number(reg):
    if ARM_REG_R0 <= reg <= ARM_REG_R0+12: return reg-ARM_REG_R0
    return {ARM_REG_SP:13,ARM_REG_LR:14,ARM_REG_PC:15}.get(reg)


@dataclass(frozen=True)
class Body:
    address: int
    data: bytes
    partition: dict
    count: int

    def decode(self):
        if type(self.address) is not int or self.address % 2 or type(self.data) is not bytes or \
                not 0 <= self.address < self.address+len(self.data) <= 0x100000000 or \
                type(self.count) is not int or self.count <= 0:
            raise ValueError('complete immutable Thumb body and exact count required')
        ins,edges,calls=frame.decode_partition(self.data,self.address,self.partition)
        if len(ins)!=self.count: raise ValueError('complete helper instruction count differs')
        return ins,edges,calls


@dataclass(frozen=True)
class Flow:
    address: int
    preserved: tuple
    private_peak: int
    nested_peak: int
    returns: tuple
    calls: tuple
    accesses: tuple
    body_pin: tuple

    def report(self):
        return dict(address=self.address,preserved_registers=list(self.preserved),
            private_frame_bytes=self.private_peak,including_nested_private_bytes=self.nested_peak,
            return_sites=list(self.returns),calls=list(self.calls),memory_sites=list(self.accesses),
            body=self.body_pin,normal_return_target='saved incoming ThumbLR',
            conditional_saved_origin_relation=True,physical_memory_permission=False,
            memory_effect_values_closed=False,termination_proved=False,
            unproved_premises=[
                'Every listed read/write completes with actual permissions and valid alignment',
                'Protected saved words retain their entry origins until the corresponding POP',
                'Ordinary calls return normally through their derived entry-LR continuation',
                'The BX-R2 endpoint has the separate installed zero count/identity/effect contract',
                'No asynchronous or external alias write changes tracked saved/local words'],
            unknown_outputs_keep_all_pointer_and_expired_alias_possibilities=True)


def _join(old,new):
    ro,so=old;rn,sn=new
    if len(so)!=len(sn) or any(a[0]!=b[0] for a,b in zip(so,sn)):
        raise ValueError('helper CFG join changes exact private frame shape')
    return (tuple(a if a==b else UNKNOWN for a,b in zip(ro,rn)),
            tuple((a[0],a[1] if a[1]==b[1] else UNKNOWN) for a,b in zip(so,sn)))


def prove_program(bodies, entry, zero_thunk, *, selector):
    """All helper paths, with one separately justified BX-R2 zero endpoint.

The thunk's register conclusion is conditional on the exact installed zero
relation. Its target, count and destination at each call are NOT proved here.
Each external memory instruction and concrete stack operation is exposed.
"""
    if selector!=SELECTOR or type(selector) is not str or type(bodies) is not tuple or \
            not 1<=len(bodies)<=32 or any(type(b) is not Body for b in bodies) or \
            type(entry) is not int or type(zero_thunk) is not int:
        raise ValueError('explicit selector and bounded complete helper graph required')
    owners={b.address:b for b in bodies}
    if len(owners)!=len(bodies) or entry not in owners or zero_thunk not in owners:
        raise ValueError('helper graph entry, thunk or unique ownership missing')
    spans=sorted((b.address,b.address+len(b.data)) for b in bodies)
    if any(a[1]>b[0] for a,b in zip(spans,spans[1:])):
        raise ValueError('overlapping complete helper bodies')
    decoded={a:b.decode() for a,b in owners.items()}
    thunk=owners[zero_thunk]
    if thunk.data!=bytes.fromhex('1047') or thunk.count!=1:
        raise ValueError('conditional zero endpoint must be complete BX R2')
    summaries={zero_thunk:Flow(zero_thunk,tuple(range(3,13))+(14,),0,4,(zero_thunk,),(),(),
        (zero_thunk,2,hashlib.sha256(thunk.data).hexdigest()))}
    active=set()

    def visit(address):
        if address in summaries:return summaries[address]
        if address in active:raise ValueError('recursive helper call graph is outside bounded relation')
        if address not in owners:raise ValueError('ordinary helper target lacks complete bound body')
        active.add(address);body=owners[address];ins,edges,calls=decoded[address]
        nested={target:visit(target) for target in set(calls.values())}
        initial=tuple(('entry-register',i) for i in range(15))
        states={address:(initial,())};pending=[address];return_rows={};accesses={};call_rows={}
        peak=nested_peak=0;steps=0
        while pending:
            site=pending.pop();regs,stack=states[site];regs=list(regs);stack=list(stack)
            item=ins[site];raw=int.from_bytes(item.bytes,'little');steps+=1
            if steps>512*len(ins):raise ValueError('saved-origin dataflow did not converge within bound')
            if site in calls:
                target=calls[site];summary=nested[target]
                nested_peak=max(nested_peak,4*len(stack)+summary.nested_peak)
                call_rows[site]=dict(site=site,target=target,SP=-4*len(stack),
                    preserved_registers=list(summary.preserved),memory_effects_closed=False,
                    zero_destination_count_and_identity_proved=False if target==zero_thunk else None)
                regs=[v if i in summary.preserved or i==13 else UNKNOWN for i,v in enumerate(regs)]
                # Nested output pointers may name any allocated local word.
                # No callee purity or nonescape contract is available here.
                stack=[(kind,UNKNOWN if kind=='local' else value) for kind,value in stack]
                # Returned LR is not a caller-save or callee-save assumption.
                regs[14]=('BL-continuation',site+4) if 14 in summary.preserved else UNKNOWN
            elif item.size!=2:
                raise ValueError('helper instruction outside closed Thumb subset')
            elif raw&0xfe00==0xb400:
                selected=[i for i in range(8) if raw>>i&1]+([14] if raw&0x100 else [])
                if not selected:raise ValueError('empty helper PUSH')
                stack=[('saved',regs[i]) for i in selected]+stack
                accesses[site]=dict(site=site,operation='PUSH',SP_after=-4*len(stack),
                    saved_registers=selected,bytes=4*len(selected))
            elif raw&0xfe00==0xbc00:
                selected=[i for i in range(8) if raw>>i&1]
                if raw&0x100 or not selected or len(stack)<len(selected) or any(
                        row[0]!='saved' for row in stack[:len(selected)]):
                    raise ValueError('helper POP consumes locals/caller words or writes PC')
                for i,row in zip(selected,stack):regs[i]=row[1]
                accesses[site]=dict(site=site,operation='POP',SP_before=-4*len(stack),
                    registers=selected,bytes=4*len(selected))
                stack=stack[len(selected):]
            elif raw&0xff00==0xb000:
                n=raw&127
                if not n:raise ValueError('zero helper frame adjustment')
                if raw&128:stack=[('local',UNKNOWN)]*n+stack
                else:
                    if n>len(stack) or any(row[0]!='local' for row in stack[:n]):
                        raise ValueError('helper deallocation consumes saved/caller words')
                    stack=stack[n:]
            elif raw&0xff00==0x4600:
                src=(raw>>3)&15;dst=(raw&7)|((raw>>4)&8)
                if src==15 or dst in (13,15):raise ValueError('helper control/SP MOV is not supported')
                regs[dst]=('local-SP',-4*len(stack)) if src==13 else regs[src]
            elif raw&0xffc0==0x1c00:
                regs[raw&7]=regs[(raw>>3)&7]
            elif raw&0xf000==0x9000:
                slot=raw&255;reg=(raw>>8)&7
                if slot>=len(stack) or stack[slot][0]!='local':
                    raise ValueError('helper direct SP access crosses its local allocation')
                if raw&0x800:regs[reg]=stack[slot][1]
                else:stack[slot]=('local',regs[reg])
                accesses[site]=dict(site=site,operation='LDR' if raw&0x800 else 'STR',
                    base='SP',offset=4*slot,SP=-4*len(stack),width=4)
            elif raw&0xff87==0x4700:
                source=(raw>>3)&15
                if source==15 or stack or regs[source]!=initial[14]:
                    raise ValueError('helper return does not restore its exact saved entry LR/SP')
                return_rows[site]=tuple(regs)
            else:
                allowed=(raw&0xf800 in (0x0000,0x0800,0x1000,0x1800,0x2000,0x2800,
                    0x3000,0x3800,0x4800,0x6000,0x6800,0x7000,0x7800,0x8000,0x8800,0xa800,0xe000)
                    or raw&0xffc0 in (0x4000,0x4040,0x4240,0x4280,0x4300)
                    or raw&0xf000==0xd000 and ((raw>>8)&15)<14)
                if not allowed:raise ValueError('helper instruction outside closed saved-origin subset')
                for reg in item.regs_access()[1]:
                    n=number(reg)
                    if n is not None:
                        if n==13:raise ValueError('unmodeled helper SP write')
                        if n!=15:regs[n]=UNKNOWN
                memory=[op.mem for op in item.operands if op.type==ARM_OP_MEM]
                if memory:
                    if len(memory)!=1:raise ValueError('ambiguous helper memory operand')
                    m=memory[0];width=1 if item.mnemonic.endswith('b') else 2 if item.mnemonic.endswith('h') else 4
                    accesses[site]=dict(site=site,operation=item.mnemonic,base_register=number(m.base),
                        index_register=number(m.index),offset=m.disp,width=width,
                        permission=False,alias_and_value_effects_closed=False)
                    if item.mnemonic.startswith('str'):
                        stack=[(kind,UNKNOWN if kind=='local' else value) for kind,value in stack]
            if len(stack)>256:raise ValueError('helper private frame exceeds bound')
            peak=max(peak,4*len(stack));nested_peak=max(nested_peak,peak)
            regs[13]=initial[13] if not stack else ('local-SP',-4*len(stack))
            following=(tuple(regs),tuple(stack))
            for target in edges[site]:
                value=following if target not in states else _join(states[target],following)
                if states.get(target)!=value:states[target]=value;pending.append(target)
        if set(states)!=set(ins) or not return_rows:raise ValueError('helper complete CFG has unreachable code/no return')
        preserved=tuple(i for i in range(15) if all(r[i]==initial[i] for r in return_rows.values()))
        out=Flow(address,preserved,peak,nested_peak,tuple(sorted(return_rows)),
            tuple(call_rows[k] for k in sorted(call_rows)),tuple(accesses[k] for k in sorted(accesses)),
            (address,len(body.data),hashlib.sha256(body.data).hexdigest()))
        summaries[address]=out;active.remove(address);return out

    visit(entry)
    if set(summaries)!=set(owners):raise ValueError('unused helper owner supplied outside actual call closure')
    return tuple(summaries[a] for a in sorted(summaries))
