"""Conditional ranking proofs for closed Thumb loops with narrowed counters.

The outer form carries counter+1 in a separate register while the body may
reuse the counter for address arithmetic. Only freshly proved inner loops are
summarized. Memory validity and completion of each instruction remain premises.
"""
import hashlib
import json

import match

SELECTOR = 'conditional-narrowed-nested-counter-loop-v1'


def digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


class Graph:
    def __init__(self,data,address,sites):
        self.instructions={};self.edges={};self.predecessors={site:set() for site in sites}
        decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
        for site in sites:
            if type(site) is not int or site&1 or not address<=site<address+len(data):
                raise ValueError('loop site leaves exact owner')
            items=list(decoder.disasm(data[site-address:site-address+4],site,count=1))
            if len(items)!=1 or items[0].size!=2:
                raise ValueError('loop continuation must be exact Thumb16')
            item=items[0];self.instructions[site]=item
            if item.mnemonic=='bx':targets=()
            elif item.id==match.ARM_INS_B:
                targets=(item.operands[0].imm,) if item.mnemonic=='b' else (item.operands[0].imm,site+2)
            elif item.mnemonic=='bl':raise ValueError('loop continuation has an uncomposed call')
            else:targets=(site+2,)
            if any(target not in sites for target in targets):
                raise ValueError('loop continuation is not a closed retained CFG')
            self.edges[site]=targets
            for target in targets:self.predecessors[target].add(site)

    def raw(self,site):
        if site not in self.instructions:raise ValueError('loop instruction is absent')
        return int.from_bytes(self.instructions[site].bytes,'little')

    def writes(self,sites,registers):
        forbidden={match.ARM_REG_R0+register for register in registers}
        return [(site,sorted(forbidden&set(self.instructions[site].regs_access()[1])))
                for site in sites if forbidden&set(self.instructions[site].regs_access()[1])]

    def straight(self,start,stop):
        path=[];site=start
        while site!=stop:
            if site in path or site not in self.edges or len(self.edges[site])!=1:
                raise ValueError('loop entry/capture path is not finite straight control')
            path.append(site);target=self.edges[site][0]
            if target!=stop and self.predecessors[target]!={site}:
                raise ValueError('loop straight path has an alternative predecessor')
            site=target
        return path

    def sequence(self,start,count):
        sites=[start+2*i for i in range(count)]
        for previous,current in zip(sites,sites[1:]):
            self.raw(previous);self.raw(current)
            if self.edges[previous]!=(current,) or self.predecessors[current]!={previous}:
                raise ValueError('loop update sequence can be bypassed')
        return sites

    def closed_body(self,start,stop,macros=(),blocked=()):
        summaries={row['header']:row for row in macros}
        interiors={site for row in macros for site in row['nodes'] if site!=row['header']}
        visiting=set();done=set();all_nodes=set();blocked=set(blocked)
        def visit(site):
            if site==stop:return
            if site in blocked or site in interiors:
                raise ValueError('loop body reenters prefix or summarized loop interior')
            if site in visiting:raise ValueError('loop body has an unsummarized cycle')
            if site in done:return
            if site not in self.edges:raise ValueError('loop body leaves retained CFG')
            visiting.add(site)
            if site in summaries:
                all_nodes.update(summaries[site]['nodes']);targets=(summaries[site]['exit'],)
            else:
                all_nodes.add(site);targets=self.edges[site]
                if not targets:raise ValueError('loop body exits before its update')
            for target in targets:visit(target)
            visiting.remove(site);done.add(site)
        visit(start)
        return all_nodes

    def external_entries(self,nodes,entry_edge):
        for site in nodes:
            for previous in self.predecessors[site]:
                if previous not in nodes and (previous,site)!=entry_edge:
                    raise ValueError('loop has an unguarded external entry')


def add_one(graph,site,counter):
    raw=graph.raw(site)
    if raw&0xfe00!=0x1c00 or (raw>>6)&7!=1 or (raw>>3)&7!=counter or raw&7==counter:
        raise ValueError('loop successor is not an exact counter+1 temporary')
    return raw&7


def high_move(graph,site,destination=None,source=None):
    raw=graph.raw(site);dst=(raw&7)+((raw>>4)&8);src=(raw>>3)&15
    if raw&0xff00!=0x4600 or dst>12 or src>12 or destination is not None and dst!=destination or source is not None and src!=source:
        raise ValueError('loop carried successor MOV differs')
    return dst,src


def narrow_tail(graph,start,counter,header,*,ceiling=None,limit_register=None,carry=None):
    sites=graph.sequence(start,5)
    if carry is None:temporary=add_one(graph,start,counter)
    else:temporary=high_move(graph,start,source=carry)[0]
    left=graph.raw(start+2);right=graph.raw(start+4)
    if left&0xf800!=0 or (left>>6)&31!=16 or (left>>3)&7!=temporary:
        raise ValueError('loop successor lacks exact left16 narrowing')
    if right&0xf800!=0x0800 or (right>>6)&31!=16 or (right>>3)&7!=left&7 or right&7!=counter:
        raise ValueError('loop successor lacks exact unsigned right16 narrowing')
    compare=graph.instructions[start+6]
    if ceiling is not None:
        raw=graph.raw(start+6)
        if raw&0xf800!=0x2800 or (raw>>8)&7!=counter or raw&255!=ceiling:
            raise ValueError('loop compares a different immediate ceiling')
    else:check_compare(compare,counter,limit_register)
    if graph.raw(start+8)&0xff00!=0xd900 or graph.edges[start+8]!=(header,start+10):
        raise ValueError('loop backedge is not the exact unsigned inclusive guard')
    return sites,start+10


def check_compare(item,left,right):
    if item.mnemonic!='cmp' or len(item.operands)!=2 or any(op.type!=match.ARM_OP_REG for op in item.operands) or \
            tuple(op.reg for op in item.operands)!=(match.ARM_REG_R0+left,match.ARM_REG_R0+right):
        raise ValueError('loop bound comparison has different registers')


def inner_loop(graph,spec):
    header,init,tail,counter,ceiling=(spec[key] for key in ('header','init','tail','counter','ceiling'))
    if type(ceiling) is not int or not 0<=ceiling<65535:
        raise ValueError('inner loop ceiling does not prevent16bit wrap')
    raw=graph.raw(init)
    if raw&0xf800!=0x2000 or (raw>>8)&7!=counter or raw&255:
        raise ValueError('inner loop lacks exact zero initialization')
    entry_path=graph.straight(init,header)
    if not entry_path or graph.predecessors[header]-{tail+8}!={entry_path[-1]}:
        raise ValueError('inner loop entry can bypass zero initialization')
    if graph.writes(entry_path[1:],(counter,)):
        raise ValueError('inner loop counter changes after zero initialization')
    body=graph.closed_body(header,tail,blocked=entry_path)
    if graph.writes(body,(counter,)):
        raise ValueError('inner loop body changes its induction counter')
    update,exit_site=narrow_tail(graph,tail,counter,header,ceiling=ceiling)
    nodes=body|set(update)
    graph.external_entries(nodes,(entry_path[-1],header))
    return {'kind':'zero-initialized-u16-inclusive-counter','header':header,'exit':exit_site,
        'nodes':sorted(nodes),'counter':counter,'ceiling':ceiling,'entry_path':entry_path,
        'tail':update,'iterations':ceiling+1,'rank':'ceiling-counter+1 before each iteration',
        'increment_wrap_impossible':True,'all_body_paths_reach_update':True,
        'instruction_completion_is_a_condition':True}


def outer_loop(graph,spec,numeric,inner_proofs):
    header,counter,bound,carry,capture,tail,guard=(spec[key] for key in (
        'header','counter','limit_register','carry','capture','tail','guard'))
    if len({counter,bound,carry})!=3 or any(type(r) is not int or not 0<=r<=12 for r in (counter,bound,carry)):
        raise ValueError('outer loop induction/limit/carry roles overlap')
    if header not in numeric:raise ValueError('outer loop lacks retained header ranges')
    low,high=numeric[header][counter];limit_low,limit_high=numeric[header][bound]
    if not 0<=low<=high<65535 or not 0<=limit_low<=limit_high<65535:
        raise ValueError('outer loop retained bounds do not prevent16bit wrap')
    graph.sequence(guard,2);check_compare(graph.instructions[guard],counter,bound)
    raw=graph.raw(guard+2)
    if raw&0xff00==0xd900:selected,other=graph.edges[guard+2]
    elif raw&0xff00==0xd800:other,selected=graph.edges[guard+2]
    else:raise ValueError('outer loop entry guard is not unsigned <= or inverted >')
    if selected==other:raise ValueError('outer entry comparison does not guard the body')
    entry_path=graph.straight(selected,header)
    if entry_path and graph.predecessors[entry_path[0]]!={guard+2}:
        raise ValueError('outer loop entry path bypasses its comparison')
    if graph.writes(entry_path,(counter,bound)):
        raise ValueError('outer loop entry path changes compared values')
    prefix=graph.straight(header,capture)
    if graph.writes(prefix,(counter,bound)):
        raise ValueError('outer loop overwrites its index before successor capture')
    graph.sequence(capture,2)
    temporary=add_one(graph,capture,counter)
    high_move(graph,capture+2,destination=carry,source=temporary)
    if graph.writes((capture,capture+2),(bound,)):
        raise ValueError('outer successor capture overwrites invariant limit')
    capture_nodes=prefix+[capture,capture+2]
    body=graph.closed_body(capture+4,tail,inner_proofs,blocked=capture_nodes)
    if graph.writes(body,(carry,bound)):
        raise ValueError('outer loop body clobbers carried successor or invariant limit')
    update,exit_site=narrow_tail(graph,tail,counter,header,limit_register=bound,carry=carry)
    if graph.writes(update,(carry,bound)):
        raise ValueError('outer loop update clobbers carry or invariant limit')
    nodes=set(capture_nodes)|body|set(update)
    entry_previous=entry_path[-1] if entry_path else guard+2
    graph.external_entries(nodes,(entry_previous,header))
    return {'kind':'carried-successor-u16-inclusive-counter','header':header,'exit':exit_site,
        'nodes':sorted(nodes),'counter':counter,'limit_register':bound,'carry_register':carry,
        'counter_range_at_header':[low,high],'limit_range_at_header':[limit_low,limit_high],
        'entry_guard':guard,'entry_path':entry_path,'successor_capture':[capture,capture+2],
        'tail':update,'maximum_iterations':limit_high+1,
        'rank':'limit-counter+1 at guarded header; exact captured successor is counter+1',
        'increment_wrap_impossible':True,'carried_successor_and_limit_preserved':True,
        'all_body_paths_reach_update':True,
        'summarized_inner_headers':[row['header'] for row in inner_proofs if row['header'] in body],
        'instruction_completion_is_a_condition':True}


def verify(data,address,frame_certificate,numeric_certificate,inner_specs,outer_specs,*,selector,reuse_authority):
    if selector!=SELECTOR or type(data) is not bytes or type(selector) is not str:
        raise ValueError('loop prerequisite requires explicit immutable input/selector')
    if type(reuse_authority) is not dict or reuse_authority.get('independently_established_frozen_certificates') is not True:
        raise ValueError('loop prerequisite needs independent retained proof authority')
    for name,certificate in (('frame',frame_certificate),('numeric',numeric_certificate)):
        if reuse_authority.get(name+'_sha256')!=digest(certificate) or certificate['address']!=address or \
                certificate['end']!=address+len(data) or certificate['body_sha256']!=hashlib.sha256(data).hexdigest():
            raise ValueError('loop retained certificate differs from exact owner')
    if frame_certificate['ROM_sha256']!=numeric_certificate['ROM_sha256'] or frame_certificate['partition']!=numeric_certificate['partition']:
        raise ValueError('loop retained ROM/partition differs')
    graph=Graph(data,address,set(frame_certificate['continuation']['continuation_sites']))
    numeric={row['site']:row['ranges'] for row in numeric_certificate['fixed_point_states']}
    inners=[inner_loop(graph,spec) for spec in inner_specs]
    if any(set(left['nodes'])&set(right['nodes']) for i,left in enumerate(inners) for right in inners[i+1:]):
        raise ValueError('inner loop summaries overlap')
    outers=[outer_loop(graph,spec,numeric,inners) for spec in outer_specs]
    return {'schema':SELECTOR,'address':address,'end':address+len(data),
        'body_sha256':hashlib.sha256(data).hexdigest(),'ROM_sha256':frame_certificate['ROM_sha256'],
        'inner_loops':inners,'outer_loops':outers,'reuse_authority':reuse_authority,
        'claim':'Conditional finite loop control only: every entered body reaches its update, unsigned guards bound a strictly decreasing rank, and narrowed successor does not wrap. Outer counter reuse is permitted only after its exact successor is captured and preserved.',
        'required_unproved_conditions':frame_certificate['required_unproved_conditions']+[
            'Every reached instruction and memory access completes according to the established CPU semantics; no external control transfer, mutation of code/registers, exception or nontermination is inferred away.'],
        'unconditional_termination':False,'whole_owner_numeric_equivalence':False,
        'source_or_ELF_admission':False,'physical_memory_permission':False,
        'old_producer_executions':0}
