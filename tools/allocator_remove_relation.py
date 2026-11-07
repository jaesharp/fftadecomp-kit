"""Conditional free-list removal and count-controlled median byte effects.

All heap fields share one symbolic coordinate arena. Writes are applied before
later reads; no linked-list validity, allocation extent or disjointness is
assumed. Physical stack/code preservation remains an explicit condition.
"""
from dataclasses import dataclass
import hashlib

SELECTOR='conditional-allocator-remove-median-fields-v1'
MAX_CELLS=4096
MAX_LINK_READS=256
MEDIAN=bytes.fromhex('''
10b5 041c 2178 6078 0002 0843 0028 02d0 8000 2018 00e0 0020 021c 002a
02d1 a270 e270 1de0 2179 6079 0002 0843 4308 0ae0 917a d07a 0002 0843
0028 02d0 8000 2018 00e0 0020 021c 013b 002b f1dc 002a 03d0 101b 8003
000c 00e0 0020 a070 000a e070 10bc 01bc 0047
''')
REMOVE_HEAD=bytes.fromhex('''
70b5 041c 0b1c 197a 587a 0002 0843 0028 02d0 8000 2018 00e0 0020 051c
987a d97a 0a02 0243 061c 002a 02d0 9000 2018 00e0 0020 021c 002d 05d0
0802 3043 a872 000a e872 04e0 0802 3043 2070 000a 6070 002a 06d0 197a
587a 0002 0843 1072 000a 5072 0020 9872 d872 1872 5872 2179 6079 0002
0843 0138 2071 000a 6071 201c
''')
REMOVE_TAIL=bytes.fromhex('70bc 01bc 0047')


def _bl(site,target):
    displacement=target-site-4
    if displacement%2 or not -(2**22)<=displacement<2**22:
        raise ValueError('direct Thumb call displacement outside encoding')
    return (0xf000|((displacement>>12)&2047)).to_bytes(2,'little')+(0xf800|((displacement>>1)&2047)).to_bytes(2,'little')


@dataclass(frozen=True)
class Layout:
    removal: int
    median: int
    removal_sha256: str
    median_sha256: str


def bind(removal_bytes,removal_address,median_bytes,median_address,counts,*,selector):
    if type(selector) is not str or selector!=SELECTOR or type(counts) is not tuple or \
            len(counts)!=2 or any(type(n) is not int for n in counts) or counts!=(66,51) or \
            type(removal_bytes) is not bytes or type(median_bytes) is not bytes or \
            any(type(a) is not int or a%2 or not 0<=a for a in (removal_address,median_address)) or \
            removal_address+134>2**32 or median_address+102>2**32 or \
            max(removal_address,median_address)<min(removal_address+134,median_address+102):
        raise ValueError('complete nonoverlapping134/102-byte owners and exact66/51 counts required')
    if median_bytes!=MEDIAN or removal_bytes!=REMOVE_HEAD+_bl(removal_address+124,median_address)+REMOVE_TAIL:
        raise ValueError('closed removal/median shape or exact direct call target differs')
    return Layout(removal_address,median_address,hashlib.sha256(removal_bytes).hexdigest(),hashlib.sha256(median_bytes).hexdigest())


class _Boundary(Exception):
    def __init__(self,site,reason,coordinate=None,remaining=None):
        self.report=dict(site=site,reason=reason,coordinate=coordinate,remaining_link_reads=remaining)


class _Memory:
    def __init__(self,cells):
        self.cells=dict(cells);self.events=[];self.changed=set()

    def read(self,offset,site,role):
        if offset not in self.cells:
            raise _Boundary(site,'field byte lacks justified reaching bits',offset)
        value=self.cells[offset]
        self.events.append(dict(site=site,operation='read8',coordinate=offset,value=value,role=role))
        return value

    def write(self,offset,value,site,role):
        self.cells[offset]=value&255;self.changed.add(offset)
        self.events.append(dict(site=site,operation='write8',coordinate=offset,value=value&255,role=role))

    def word(self,offset,sites,role):
        return self.read(offset,sites[0],role)|(self.read(offset+1,sites[1],role)<<8)

    def putword(self,offset,value,sites,role):
        self.write(offset,value,sites[0],role);self.write(offset+1,value>>8,sites[1],role)


def _validate(layout,cells,budget,selector):
    if type(selector) is not str or selector!=SELECTOR or type(layout) is not Layout or \
            type(cells) is not dict or len(cells)>MAX_CELLS or \
            any(type(k) is not int or not 0<=k<=0x40010 or type(v) is not int or not 0<=v<=255 for k,v in cells.items()) or \
            type(budget) is not int or not 0<=budget<=MAX_LINK_READS:
        raise ValueError('bounded concrete-byte witness and explicit link budget required')
    if any(type(a) is not int or a%2 or not 0<=a<2**32 for a in (layout.removal,layout.median)):
        raise ValueError('layout identity invalid')
    # Reconstruct identity without invoking old or actual proof producers.
    expected=REMOVE_HEAD+_bl(layout.removal+124,layout.median)+REMOVE_TAIL
    if layout.removal+len(expected)>2**32 or layout.median+len(MEDIAN)>2**32 or \
            max(layout.removal,layout.median)<min(layout.removal+len(expected),layout.median+len(MEDIAN)) or \
            layout.removal_sha256!=hashlib.sha256(expected).hexdigest() or layout.median_sha256!=hashlib.sha256(MEDIAN).hexdigest():
        raise ValueError('layout identity invalid')


def _node(index):
    return None if index==0 else 4*index


def _median(memory,base,budget,stack_offset):
    memory.events.append(dict(site=base,operation='save-entry-registers',registers=[4,14],stack_span=[stack_offset-8,stack_offset]))
    head=memory.word(0,(base+4,base+6),'heap head index')
    cursor=_node(head);count=None;steps=0;remaining=0
    if cursor is None:
        memory.putword(2,0,(base+30,base+32),'empty median index')
    else:
        count=memory.word(4,(base+36,base+38),'heap element count')
        # The machine decrements BEFORE BGT. Count0/1 starts at0 and becomes
        # signed-1; count2/3 starts at1 and becomes0. Neither follows a link.
        remaining=max((count>>1)-1,0)
        while remaining:
            if steps>=budget:
                raise _Boundary(base+48,'explicit link-read budget exhausted',remaining=remaining)
            if cursor is None:
                raise _Boundary(base+48,'premature null cursor would read absolute0xA/0xB without heap provenance',remaining=remaining)
            index=memory.word(cursor+10,(base+48,base+50),'median next index')
            cursor=_node(index);steps+=1;remaining-=1
        median_index=0 if cursor is None else (((cursor<<14)&0xffffffff)>>16)
        memory.putword(2,median_index,(base+90,base+94),'derived median index')
    memory.events.extend([
        dict(site=base+96,operation='restore-entry-register',register=4,stack_span=[stack_offset-8,stack_offset-4]),
        dict(site=base+98,operation='restore-entry-LR-into-R0',stack_span=[stack_offset-4,stack_offset]),
        dict(site=base+100,operation='return-saved-entry-LR')])
    return dict(head_index=head,element_count=count,required_link_reads=0 if count is None else max((count>>1)-1,0),
                completed_link_reads=steps,median_offset=cursor,final_counter_u32=None if count is None else (0xffffffff if count<2 else 0),
                numeric_termination_argument='finite unsigned16 count with signed predecrement; each actual read still must complete')


def _report(layout,memory,entry,summary,boundary):
    return dict(schema=SELECTOR,entry=entry,body_pins=dict(removal=layout.removal_sha256,median=layout.median_sha256),
        status='conditional returned byte relation' if boundary is None else 'retained conditional boundary',
        returns_under_witness=boundary is None,summary=summary,boundary=boundary,
        memory_events=memory.events,modified_coordinates=sorted(memory.changed),
        changed_bytes={str(k):memory.cells[k] for k in sorted(memory.changed)},
        modified_coordinates_scope='heap coordinate arena; listed private PUSH events also write saved stack words',
        actual_entry_heap_proved=False,physical_access_proved=False,allocation_or_object_extent_proved=False,
        actual_frame_noninterference_proved=False,actual_termination_proved=False,source_or_native_admission=False,
        list_sortedness_or_distinct_nodes_assumed=False,
        obligations=[
            dict(id='entry-binding',proved=False,text='Complete current indexed owners, exact call target, incoming heap/block pointers and every supplied byte must equal the actual reaching state.'),
            dict(id='physical-byte-access',proved=False,text='All base-plus offsets and byte reads/writes are valid, nonwrapping synchronous ordinary RAM accesses. Relative field values grant no physical extent or allocation.'),
            dict(id='frame-and-control',proved=False,text='Aligned live private saves retain their entry origins, incoming ThumbLR is valid, and all actual heap/code/ambient aliases preserve protected caller/source words. Removal16 plus nested median8 requires24bytes, not fresh memory permission.'),
            dict(id='code-and-interference',proved=False,text='Executing code and read bytes remain stable except for the explicitly ordered writes. No asynchronous/device interference or hidden callee effects are assumed.'),
            dict(id='actual-path',proved=False,text='A returned relation is conditional on this exact byte witness and successful reads. Budget exhaustion, missing bytes and premature-null dereference remain boundaries; count arithmetic alone supplies no physical termination theorem.')])


def derive_median(layout,cells,*,selector,max_link_reads=MAX_LINK_READS):
    _validate(layout,cells,max_link_reads,selector);memory=_Memory(cells);summary=None;boundary=None
    try:summary=_median(memory,layout.median,max_link_reads,0)
    except _Boundary as e:boundary=e.report
    return _report(layout,memory,'median',summary,boundary)


def derive_removal(layout,cells,block_offset,*,selector,max_link_reads=MAX_LINK_READS):
    _validate(layout,cells,max_link_reads,selector)
    if type(block_offset) is not int or block_offset%4 or not 4<=block_offset<=65535*4:
        raise ValueError('explicit nonzero unsigned16-indexed block coordinate required')
    memory=_Memory(cells);c=layout.removal;summary={};boundary=None
    try:
        memory.events.append(dict(site=c,operation='save-entry-registers',registers=[4,5,6,14],stack_span=[-16,0]))
        prev_index=memory.word(block_offset+8,(c+6,c+8),'block previous index')
        next_index=memory.word(block_offset+10,(c+28,c+30),'block next index')
        previous=_node(prev_index);following=_node(next_index)
        if previous is None:
            memory.putword(0,next_index,(c+72,c+76),'replace heap head')
        else:
            memory.putword(previous+10,next_index,(c+60,c+64),'previous next link')
        if following is not None:
            # Real reload AFTER the previous/header writes, preserving aliases.
            reread=memory.word(block_offset+8,(c+82,c+84),'reload block previous index')
            memory.putword(following+8,reread,(c+90,c+94),'next previous link')
        for offset,site in [(10,98),(11,100),(8,102),(9,104)]:
            memory.write(block_offset+offset,0,c+site,'clear removed block links')
        old_count=memory.word(4,(c+106,c+108),'heap count before decrement')
        new_count=(old_count-1)&65535
        memory.putword(4,new_count,(c+116,c+120),'heap count decrement modulo16')
        summary.update(block_offset=block_offset,previous_offset=previous,next_offset=following,
                       count_before=old_count,count_after=new_count,underflow=old_count==0)
        memory.events.append(dict(site=c+124,operation='ordinary-call',target=layout.median,SP=-16))
        summary['median']=_median(memory,layout.median,max_link_reads,-16)
        memory.events.extend([
            dict(site=c+128,operation='restore-entry-registers',registers=[4,5,6],stack_span=[-16,-4]),
            dict(site=c+130,operation='restore-entry-LR-into-R0',stack_span=[-4,0]),
            dict(site=c+132,operation='return-saved-entry-LR')])
    except _Boundary as e:boundary=e.report
    return _report(layout,memory,'removal',summary,boundary)
