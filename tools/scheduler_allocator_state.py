"""Conditional scheduler prefix on one allocator/list/descriptor byte arena.

No list is invented by naming its nodes. Actual ordered pointer reads must
resolve from this new state, after allocator and zero effects. Opaque bytes
remain opaque; saved/frame aliases and unknown pointer representations refuse.
The relation stops BEFORE descriptor copy or callback execution.
"""
from dataclasses import dataclass
import hashlib
import json

import allocator_wrapper_relation as wrapper
import allocator_split_relation as split
import allocator_remove_relation as remove

SELECTOR='conditional-scheduler-allocator-list-state-v1'
MAX_LINKS=128
ZERO92_SHA256='cee672a0c6580d8e53ee28f4c9ec61ae7a4b18eb2b237f8b6d9fe61b3b376046'
ZERO112_SHA256='0b1975920e093915955367a11337798791b506defa1b044127acd746f8bb93b7'
HEAD=bytes.fromhex('f0b5 4f46 4646 c0b4 87b0 051c 8846 141c 9946 0e9e 2404 e020 4003 2418 240c 2868 211c')
POST=bytes.fromhex('071c 0e48 0268 381c 211c')
LINK1=bytes.fromhex('''
4346 3b60 a889 f882 002e 18d0 3069 0028 10d0 011c 8868 3a1c 1832 0028
03d0 8968 8868 0028 fbd1 081c 8760 7860 05e0 0000
''')
LINK2=bytes.fromhex('''
3761 3a1c 1832 fe60 13e0 6868 0028 03d1 6f60 3a1c 1832 0ce0 011c 8868
3a1c 1832 0028 03d0 8968 8868 0028 fbd1 081c 8760 7860 6946 4846 38c8
38c1 38c8 38c1 0068 0860 6946 0020 0880 3b68 381c
''')
TAIL=bytes.fromhex('8020 4000 b882 381c 07b0 18bc 9846 a146 f0bc 02bc 0847')


@dataclass(frozen=True)
class Layout:
    address: int
    sha256: str
    allocator: wrapper.Layout
    callback_thunk: int


def _encoded(address,allocator,callback_thunk):
    core=allocator.allocator
    return (HEAD+remove._bl(address+34,allocator.address)+POST+remove._bl(address+48,core.thunk)+
            LINK1+core.pointer_literal.to_bytes(4,'little')+LINK2+
            remove._bl(address+180,callback_thunk)+TAIL)


def _identity(address,allocator,callback_thunk):
    if type(allocator) is not wrapper.Layout:
        raise ValueError('retained complete allocator wrapper required')
    if allocator.sha256!=hashlib.sha256(wrapper._identity(allocator.address,allocator.allocator)).hexdigest():
        raise ValueError('retained wrapper identity changed')
    if type(address) is not int or address%4 or not 0<=address<=2**32-206 or \
            type(callback_thunk) is not int or callback_thunk%2 or not 0<=callback_thunk<=2**32-2:
        raise ValueError('complete aligned scheduler and callback-thunk owners required')
    a=allocator.allocator;i=a.insertion;m=i.median
    spans=sorted([(address,address+206),(allocator.address,allocator.address+54),(a.address,a.address+266),
                  (i.address,i.address+150),(i.search.address,i.search.address+174),
                  (m.removal,m.removal+134),(m.median,m.median+102),(a.thunk,a.thunk+2),(callback_thunk,callback_thunk+2)])
    if any(x[1]>y[0] for x,y in zip(spans,spans[1:])):
        raise ValueError('complete scheduler/helper owners overlap')
    return _encoded(address,allocator,callback_thunk)


def bind(data,address,instruction_count,allocator_layout,callback_thunk,callback_thunk_bytes,*,selector):
    expected=_identity(address,allocator_layout,callback_thunk)
    if type(selector) is not str or selector!=SELECTOR or type(data) is not bytes or data!=expected or \
            type(instruction_count) is not int or instruction_count!=97 or \
            type(callback_thunk_bytes) is not bytes or callback_thunk_bytes!=b'\x18\x47':
        raise ValueError('complete206B/97-instruction scheduler with exact pool/padding/calls required')
    return Layout(address,hashlib.sha256(data).hexdigest(),allocator_layout,callback_thunk)


def _cell(v):
    return split.insert._cell(v) or (type(v) is tuple and len(v)==3 and v[0]=='opaque-byte' and
        type(v[1]) is str and 0<len(v[1])<=64 and type(v[2]) is int and 0<=v[2]<2**31)


class _Arena(split._Arena):
    def check_field(self,at,width,site,operation):
        if not -(2**31)<=at<=2**31-width or width in (2,4) and at%width:
            raise remove._Boundary(site,'field coordinate is unaligned or outside bounded nonwrapping arena',at)
        self.field_guard(at,width,site)
        self.guard(at,width,site,operation)

    def pointer(self,at,site,role,*,incoming=False,helper_output=False):
        if at%4 or not -(2**31)<=at<=2**31-4:
            raise remove._Boundary(site,'pointer word access is unaligned or outside bounded arena',at)
        if not incoming and not helper_output:self.check_field(at,4,site,'pointer field read')
        # The incoming stack argument is read once before any heap effects.
        # Helper output slots are the exact ordinary stack words in their
        # frozen contracts. Neither path makes a numeric nonzero word a pointer.
        values=[self.cells.get(at+i) for i in range(4)]
        if all(type(v)is int and v==0 for v in values):value=None
        elif all(type(v)is tuple and len(v)==3 and v[0]=='base-plus-byte' and v[2]==i for i,v in enumerate(values)) and \
                all(v[1]==values[0][1] for v in values):value=values[0][1]
        else:raise remove._Boundary(site,'pointer word lacks intact base-relative provenance or exact null',at)
        self.events.append(dict(site=site,operation='read32',coordinate=at,value=0 if value is None else ['base-plus',value],role=role))
        return value

    def pointer_store(self,at,value,site,role,*,helper_output=False):
        if not helper_output:self.check_field(at,4,site,'pointer field write')
        self.store_pointer(at,value,site,role)

    def half(self,at,site,role):
        self.check_field(at,2,site,'halfword field read')
        values=[self.cells.get(at+i) for i in range(2)]
        if any(type(v)is not int or not 0<=v<256 for v in values):
            raise remove._Boundary(site,'halfword has missing or opaque reaching bits',at)
        value=values[0]|values[1]<<8
        self.events.append(dict(site=site,operation='read16',coordinate=at,value=value,role=role))
        return value

    def half_store(self,at,value,site,role):
        self.check_field(at,2,site,'halfword field write')
        self.cells[at]=value&255;self.cells[at+1]=(value>>8)&255
        self.changed.update((at,at+1))
        self.events.append(dict(site=site,operation='write16',coordinate=at,value=value&65535,role=role))

    def callback_store(self,at,value,site):
        self.check_field(at,4,site,'callback word write')
        values=[(value>>(8*i))&255 for i in range(4)] if type(value)is int else [('opaque-byte',value[1],i) for i in range(4)]
        for i,v in enumerate(values):self.cells[at+i]=v;self.changed.add(at+i)
        self.events.append(dict(site=site,operation='write32-origin',coordinate=at,value=value,role='incoming callback word'))


def _replay(memory,report):
    for e in report['memory_events']:
        op=e['operation']
        if op=='write32':
            memory.pointer_store(e['coordinate'],None if e['value']==0 else e['value'][1],e['site'],e['role'],helper_output=True)
        elif op=='read32':
            got=memory.pointer(e['coordinate'],e['site'],e['role'],helper_output=True)
            if (0 if got is None else ['base-plus',got])!=e['value']:
                raise ValueError('retained helper pointer observation differs from composed state')
        elif op=='read8':
            if memory.read(e['coordinate'],e['site'],e['role'])!=e['value']:
                raise ValueError('retained helper byte observation differs from composed state')
        elif op=='write8':memory.write(e['coordinate'],e['value'],e['site'],e['role'])
        elif op=='zero-write':
            at=e['coordinate'];width=e['width']
            memory.check_field(at,width,e['site'],'nested zero write')
            for i in range(width):memory.cells[at+i]=0;memory.changed.add(at+i)
            memory.events.append(e)
        else:memory.events.append(e)


def _zero92(memory,receipt,target,count,destination,sp,site):
    if type(receipt)is not bytes or hashlib.sha256(receipt).hexdigest()!=ZERO92_SHA256:
        raise remove._Boundary(site,'retained first count92 zero certificate absent or changed')
    rule=json.loads(receipt)
    if count!=rule['count']:
        raise remove._Boundary(site,'actual scheduler count differs from retained count92 effect')
    if type(target)is not int or target!=(rule['entry']|1):
        raise remove._Boundary(site,'direct zero R2 word lacks retained installed Thumb identity')
    memory.check_field(destination,count,site,'direct zero destination')
    memory.guard(sp-4,4,site,'direct zero private save')
    memory.events.append(dict(site=site,operation='conditional-installed-zero92',target=target,
        destination=destination,count=count,receipt_sha256=ZERO92_SHA256,private_save=[sp-4,sp],
        alignment_case=0,installed_identity_proved=False,physical_permission_proved=False))
    for region,offset,width in rule['alignment_cases'][0]['writes']:
        if region!='destination':continue
        for i in range(width):memory.cells[destination+offset+i]=0;memory.changed.add(destination+offset+i)
        memory.events.append(dict(site=site,operation='zero-write',coordinate=destination+offset,width=width,value=0,
                                  origin='retained direct count92 effect'))


def _zero112(memory,receipt,target,count,destination,sp,site):
    if type(receipt)is not bytes or hashlib.sha256(receipt).hexdigest()!=ZERO112_SHA256:
        raise remove._Boundary(site,'retained first count112 zero certificate absent or changed')
    rule=json.loads(receipt)
    if count!=rule['count']:
        raise remove._Boundary(site,'actual scheduler count differs from retained count112 effect')
    if type(target)is not int or target!=(rule['entry']|1):
        raise remove._Boundary(site,'direct zero R2 word lacks retained installed Thumb identity')
    memory.check_field(destination,count,site,'direct zero destination')
    memory.guard(sp-4,4,site,'direct zero private save')
    memory.events.append(dict(site=site,operation='conditional-installed-zero112',target=target,
        destination=destination,count=count,receipt_sha256=ZERO112_SHA256,private_save=[sp-4,sp],
        alignment_case=0,installed_identity_proved=False,physical_permission_proved=False))
    for region,offset,width in rule['alignment_cases'][0]['writes']:
        if region!='destination':continue
        for i in range(width):memory.cells[destination+offset+i]=0;memory.changed.add(destination+offset+i)
        memory.events.append(dict(site=site,operation='zero-write',coordinate=destination+offset,width=width,value=0,
                                  origin='retained direct count112 effect'))


def derive(layout,size_word,cells,scheduler_offset,descriptor_offset,callback_word,entry_sp,*,selector,
           zero12_receipt=None,zero92_receipt=None,observed_zero_target=None,protected_spans=(),
           max_links=MAX_LINKS,max_search_transitions=256,max_median_links=256,zero112_receipt=None):
    """Derive only the conditional pre-copy state. All addresses share one base."""
    if type(selector)is not str or selector!=SELECTOR or type(layout)is not Layout:
        raise ValueError('explicit scheduler-state selector and retained layout required')
    if layout.sha256!=hashlib.sha256(_identity(layout.address,layout.allocator,layout.callback_thunk)).hexdigest():
        raise ValueError('scheduler identity changed')
    callback_ok=(type(callback_word)is int and 0<=callback_word<2**32 or
        type(callback_word)is tuple and len(callback_word)==2 and callback_word[0]=='word-origin' and
        type(callback_word[1])is str and 0<len(callback_word[1])<=64)
    if type(size_word)is not int or not 0<=size_word<2**32 or not callback_ok or \
            type(cells)is not dict or len(cells)>4096 or any(type(k)is not int or not -(2**31)<=k<2**31 or not _cell(v) for k,v in cells.items()) or \
            any(type(v)is not int or v%4 or not -(2**31)+132<=v<=2**31-128 for v in (scheduler_offset,descriptor_offset,entry_sp)) or \
            type(protected_spans)is not tuple or len(protected_spans)>27 or any(type(p)is not tuple or len(p)!=2 or
                any(type(v)is not int for v in p) or not -(2**31)<=p[0]<p[1]<=2**31 for p in protected_spans) or \
            type(max_links)is not int or not 1<=max_links<=MAX_LINKS or \
            type(max_search_transitions)is not int or not 1<=max_search_transitions<=256 or \
            type(max_median_links)is not int or not 0<=max_median_links<=256:
        raise ValueError('bounded exact byte/origin state, aligned coordinates and retained limits required')
    c=layout.address;sp=entry_sp-56;save=(entry_sp-28,entry_sp)
    memory=_Arena(cells,protected_spans,(entry_sp-132,entry_sp))
    count=((size_word&65535)+28)&65535
    boundary=None;allocation=None;parent=None;phase=None;ar=None;visited=[]
    try:
        memory.guard(save[0],28,c,'scheduler saved-register writes')
        memory.events.extend([
            dict(site=c,operation='save-entry-registers',registers=[4,5,6,7,14],coordinates=[entry_sp-20,entry_sp]),
            dict(site=c+6,operation='save-entry-R8-R9',coordinates=list(save[:1])+[entry_sp-20]),
            dict(site=c+8,operation='allocate-descriptor-local',coordinates=[sp,sp+28],initialization_granted=False)])
        parent=memory.pointer(entry_sp,c+18,'incoming parent stack word',incoming=True)
        memory.protected.extend([save,(entry_sp,entry_sp+4)])
        heap=memory.pointer(scheduler_offset,c+30,'scheduler incoming heap word')
        if heap!=0:
            raise remove._Boundary(c+30,'scheduler heap pointer is null or differs from chosen symbolic heap base',scheduler_offset)
        memory.events.append(dict(site=c+34,operation='ordinary-call',target=layout.allocator.address,SP=sp,
                                  inputs=dict(R0=['base-plus',0],R1=count)))
        lo,hi=memory.envelope
        projected={k:v for k,v in memory.cells.items() if split.insert._cell(v) and not lo<=k<hi}
        ar=wrapper.derive(layout.allocator,count,projected,sp,selector=wrapper.SELECTOR,
            zero12_receipt=zero12_receipt,observed_zero_target=observed_zero_target,
            protected_spans=tuple(memory.protected),max_search_transitions=max_search_transitions,max_median_links=max_median_links)
        _replay(memory,ar)
        if not ar['returns_under_witness']:
            raise remove._Boundary(c+34,'allocator does not return under the composed witness: '+ar['boundary']['reason'])
        allocation=None if ar['result_pointer']==0 else ar['result_pointer'][1]
        memory.events.append(dict(site=c+40,operation='literal-address',pool=c+100,value=layout.allocator.allocator.pointer_literal))
        memory.events.append(dict(site=c+42,operation='conditional-ROM-pointer-read',address=layout.allocator.allocator.pointer_literal,
                                  value=observed_zero_target,origin_proved=False))
        if allocation is None:
            raise remove._Boundary(c+48,'actual zero destination is null; no writable null span is admitted')
        if zero112_receipt is None:
            _zero92(memory,zero92_receipt,observed_zero_target,count,allocation,sp,c+48)
        else:
            _zero112(memory,zero112_receipt,observed_zero_target,count,allocation,sp,c+48)
        memory.callback_store(allocation,callback_word,c+54)
        phase=memory.half(scheduler_offset+12,c+56,'scheduler phase after allocator/zero/callback writes')
        memory.half_store(allocation+22,phase,c+58,'allocation phase')
        is_parent=parent is not None
        owner=parent if is_parent else scheduler_offset
        head_at=owner+(16 if is_parent else 4)
        head=memory.pointer(head_at,c+(64 if is_parent else 114),'post-effect list head')
        if head is None:
            memory.pointer_store(head_at,allocation,c+(104 if is_parent else 120),'empty-list head assignment')
        else:
            node=head;visited.append(node)
            nxt=memory.pointer(node+8,c+(72 if is_parent else 130),'initial next test')
            while nxt is not None:
                if len(visited)>=max_links:
                    raise remove._Boundary(c+(82 if is_parent else 140),'explicit list link bound exhausted',node+8)
                node=memory.pointer(node+8,c+(82 if is_parent else 140),'loop advance reload')
                if node is None:
                    raise remove._Boundary(c+(84 if is_parent else 142),'advance reload unexpectedly null; ordinary stable memory required')
                if node in visited:
                    raise remove._Boundary(c+(84 if is_parent else 142),'stable-memory list cycle; no tail store or termination granted',node)
                visited.append(node)
                nxt=memory.pointer(node+8,c+(84 if is_parent else 142),'loop next test')
            memory.pointer_store(node+8,allocation,c+(92 if is_parent else 150),'tail next assignment')
            memory.pointer_store(allocation+4,node,c+(94 if is_parent else 152),'allocation previous assignment')
        if is_parent:memory.pointer_store(allocation+12,parent,c+110,'allocation parent assignment')
    except remove._Boundary as error:boundary=error.report
    except ValueError as error:boundary=dict(site=c+34,reason='retained bounded allocator input refusal: '+str(error),coordinate=None)
    # PUSH effects preserve register origins conditionally, but this arena does
    # not materialize every saved byte. A later copy must never consume stale
    # pre-entry cells from that envelope as its source witness.
    frame_low,frame_high=memory.envelope
    source_overlaps_frame=descriptor_offset<frame_high and descriptor_offset+28>frame_low
    descriptor_bytes=[('opaque-byte','unmodeled private-frame byte',descriptor_offset+i-frame_low)
                      if frame_low<=descriptor_offset+i<frame_high else memory.cells.get(descriptor_offset+i)
                      for i in range(28)]
    return dict(schema=SELECTOR,reaches_copy_cutpoint=boundary is None,boundary=boundary,
        count=count,parent=parent,allocation=allocation,phase_after_effects=phase,visited_nodes=visited,
        allocator_relation=ar,memory_events=memory.events,
        changed_cells={str(k):memory.cells[k] for k in sorted(memory.changed)},
        descriptor_snapshot=descriptor_bytes,descriptor_intersects_unmodeled_frame=source_overlaps_frame,
        descriptor_frame_transport_authorized=False if source_overlaps_frame else None,
        callback_slot_snapshot=None if allocation is None else [memory.cells.get(allocation+i) for i in range(4)],
        conditional_cutpoint_registers=None if boundary else dict(R2=['base-plus',allocation+24],R4=count,
            R5=['base-plus',scheduler_offset],R6=0 if parent is None else ['base-plus',parent],
            R7=['base-plus',allocation],R8=callback_word,R9=['base-plus',descriptor_offset],SP=sp),
        frame=dict(entry_SP_coordinate=entry_sp,copy_SP=sp,own_private_bytes=56,maximum_private_bytes=132,
                   incoming_parent_word=[entry_sp,entry_sp+4],heap_field_exclusion=list(memory.envelope)),
        actual_heap_or_input_proved=False,actual_byte_origins_proved=False,actual_phase_zero_proved=False,
        installed_identity_proved=False,physical_access_proved=False,allocation_extent_proved=False,
        actual_frame_noninterference_proved=False,source_initialization_proved=False,actual_termination_proved=False,
        callback_effects_closed=False,full_scheduler_proved=False,source_or_native_admission=False,
        obligations=[dict(id=k,proved=False,text=t) for k,t in [
            ('actual-entry', 'All indexed code and supplied R0/R1/R2/R3/entrySP/stack-parent words and byte origins equal actual reaching state; scheduler heap word matches the chosen symbolic arena.'),
            ('physical-memory', 'The common heap base is word aligned; every coordinate and pointer operation is valid, nonwrapping ordinary memory with required access and object lifetime. No role or literal point grants extent.'),
            ('frame-and-source', 'All actual caller/source/saved/code protections are complete and live. The checked132-byte envelope and incoming-word protection express numeric conditions, not actual separation facts.'),
            ('retained-allocator', 'Every frozen allocator/search/remove/insert/wrapper condition applies to this new byte state; unknown origins are not promoted to scalar or pointer bits.'),
            ('installed-zero', 'Retained zero12 and the selected direct zero92 or zero112 installed-image, target, private-save, destination, return and no-interference conditions hold when used.'),
            ('stable-list', 'Only listed writes occur; synchronous ordinary reads have no asynchronous/device interference. Cycles and budget exhaustion remain refusals, not termination evidence.'),
            ('copy-and-callback', 'This ends before descriptor copy. The reported post-effect source/callback bytes must feed the retained copy and actual callback contracts; original initialization/identity cannot be reused after an alias overwrite.')]])
