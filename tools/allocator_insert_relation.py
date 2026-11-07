"""Conditional insertion with real stack-output reloads and byte effects.

Frozen search/median components are applied to the new composed state. Numeric
coordinates are formal witnesses, never actual heap/SP permission. Pointer
output words retain representation tokens; alias-corrupted words are refused.
"""
from dataclasses import dataclass
import hashlib

import allocator_search_relation as search
import allocator_remove_relation as median

SELECTOR='conditional-allocator-insert-output-alias-v1'
HEAD=bytes.fromhex('30b5 82b0 041c 0d1c a879 e979 0902 0143 01ab 201c 6a46')
MIDDLE=bytes.fromhex('''
002d 03d0 281b 8003 000c 00e0 0020 0004 020c 0099 0029 03d0 8a72 000e c872
02e0 2270 000e 6070 0199 0029 02d0 0a72 100a 4872 0098 0028 03d0 001b
8003 000c 00e0 0020 2872 000a 6872 0198 0028 03d0 001b 8003 000c 00e0
0020 a872 000a e872 2179 6079 0002 0843 0130 2071 000a 6071 201c
''')
TAIL=bytes.fromhex('02b0 30bc 01bc 0047')


@dataclass(frozen=True)
class Layout:
    address: int
    sha256: str
    search: search.Layout
    median: median.Layout


def _validate_dependencies(s,m):
    if type(s) is not search.Layout or type(m) is not median.Layout or \
            type(s.address) is not int or s.address%2 or not 0<=s.address<=2**32-174 or \
            s.sha256!=hashlib.sha256(search.SHAPE).hexdigest():
        raise ValueError('frozen complete search layout identity required')
    median._validate(m,{},0,median.SELECTOR)


def bind(data,address,instruction_count,search_layout,median_layout,*,selector):
    _validate_dependencies(search_layout,median_layout)
    if type(selector) is not str or selector!=SELECTOR or type(data) is not bytes or \
            type(address) is not int or address%2 or not 0<=address<=2**32-150 or \
            type(instruction_count) is not int or instruction_count!=73:
        raise ValueError('complete150-byte/73-instruction insertion owner required')
    spans=sorted([(address,address+150),(search_layout.address,search_layout.address+174),
                  (median_layout.median,median_layout.median+102)])
    if any(a[1]>b[0] for a,b in zip(spans,spans[1:])):
        raise ValueError('insertion/search/median owners overlap')
    expected=HEAD+median._bl(address+22,search_layout.address)+MIDDLE+median._bl(address+138,median_layout.median)+TAIL
    if data!=expected:raise ValueError('closed insertion shape or exact call targets differ')
    return Layout(address,hashlib.sha256(data).hexdigest(),search_layout,median_layout)


def _cell(value):
    return type(value) is int and 0<=value<=255 or type(value) is tuple and len(value)==3 and \
        value[0]=='base-plus-byte' and type(value[1]) is int and -(2**31)<=value[1]<2**31 and \
        type(value[2]) is int and 0<=value[2]<4


class _Memory(median._Memory):
    def __init__(self,cells,protected):
        super().__init__(cells);self.protected=list(protected)

    def guard(self,offset,width,site,action):
        if any(offset<hi and offset+width>lo for lo,hi in self.protected):
            raise median._Boundary(site,action+' intersects protected saved/caller bytes',offset)

    def read(self,offset,site,role):
        self.guard(offset,1,site,'field read')
        value=self.cells.get(offset)
        if type(value) is not int or not 0<=value<=255:
            raise median._Boundary(site,'field has missing/opaque byte bits',offset)
        return super().read(offset,site,role)

    def write(self,offset,value,site,role):
        self.guard(offset,1,site,'byte write')
        super().write(offset,value,site,role)

    def store_pointer(self,offset,pointer,site,role):
        self.guard(offset,4,site,'pointer-word write')
        values=[0]*4 if pointer is None else [('base-plus-byte',pointer,i) for i in range(4)]
        for i,value in enumerate(values):self.cells[offset+i]=value;self.changed.add(offset+i)
        self.events.append(dict(site=site,operation='write32',coordinate=offset,
            value=0 if pointer is None else ['base-plus',pointer],role=role))

    def load_pointer(self,offset,site,role):
        self.guard(offset,4,site,'pointer-word read')
        values=[self.cells.get(offset+i) for i in range(4)]
        if all(type(v) is int and v==0 for v in values):pointer=None
        elif all(type(v) is tuple and len(v)==3 and v[0]=='base-plus-byte' and v[2]==i for i,v in enumerate(values)) and \
                all(v[1]==values[0][1] for v in values):pointer=values[0][1]
        else:
            raise median._Boundary(site,'output word lacks intact pointer representation or exact null; alias effects retained',offset)
        self.events.append(dict(site=site,operation='read32',coordinate=offset,
            value=0 if pointer is None else ['base-plus',pointer],role=role))
        return pointer


def derive(layout,cells,block_offset,entry_sp,*,selector,protected_spans=(),
           max_search_transitions=search.MAX_TRANSITIONS,max_median_links=median.MAX_LINK_READS):
    """Full insertion relation under explicit relative heap/SP byte witnesses."""
    if type(selector) is not str or selector!=SELECTOR or type(layout) is not Layout:
        raise ValueError('explicit insertion selector and frozen layout required')
    _validate_dependencies(layout.search,layout.median)
    if type(layout.address) is not int or layout.address%2 or not 0<=layout.address<=2**32-150:
        raise ValueError('insertion identity changed')
    expected=HEAD+median._bl(layout.address+22,layout.search.address)+MIDDLE+median._bl(layout.address+138,layout.median.median)+TAIL
    spans=sorted([(layout.address,layout.address+150),(layout.search.address,layout.search.address+174),
                  (layout.median.median,layout.median.median+102)])
    if any(a[1]>b[0] for a,b in zip(spans,spans[1:])) or \
            layout.sha256!=hashlib.sha256(expected).hexdigest():raise ValueError('insertion identity changed')
    if type(cells) is not dict or len(cells)>4096 or any(type(k) is not int or not -(2**31)<=k<2**31 or not _cell(v) for k,v in cells.items()) or \
            type(block_offset) is not int or block_offset%4 or not 0<=block_offset<=2**31-12 or \
            type(entry_sp) is not int or entry_sp%4 or not -(2**31)+40<=entry_sp<=2**31-4 or \
            type(protected_spans) is not tuple or len(protected_spans)>32 or any(type(p) is not tuple or len(p)!=2 or
                any(type(v) is not int for v in p) or not -(2**31)<=p[0]<p[1]<=2**31 for p in protected_spans) or \
            type(max_search_transitions) is not int or not 1<=max_search_transitions<=search.MAX_TRANSITIONS or \
            type(max_median_links) is not int or not 0<=max_median_links<=median.MAX_LINK_READS:
        raise ValueError('bounded byte/token state, aligned block/SP and explicit protection required')
    c=layout.address;sp=entry_sp-20
    private_save=(entry_sp-12,entry_sp)
    memory=_Memory(cells,protected_spans+(private_save,))
    summary={};boundary=None;search_report=None;median_report=None
    memory.events.extend([
        dict(site=c,operation='save-entry-registers',registers=[4,5,14],stack_span=[-12,0]),
        dict(site=c+2,operation='allocate-output-locals',coordinates=[sp,sp+8],initialization_granted=False)])
    try:
        size=memory.word(block_offset+6,(c+8,c+10),'inserted block size')
        summary['request_u16']=size
        memory.events.append(dict(site=c+22,operation='ordinary-call',target=layout.search.address,
            inputs=dict(R0='heap base',R1=size,R2=['base-plus',sp],R3=['base-plus',sp+4]),SP=sp))
        nested_save=(sp-20,sp)
        memory.protected.append(nested_save)
        # Projection keeps only justified numeric field bytes. Opaque cells
        # remain in outer memory; observing one in search is a real boundary.
        known={k:v for k,v in memory.cells.items() if type(v) is int and
               not any(lo<=k<hi for lo,hi in memory.protected)}
        try:
            search_report=search.derive(layout.search,size,known,sp,sp+4,selector=search.SELECTOR,
                                        max_transitions=max_search_transitions)
        except ValueError as error:
            # Search always makes these two stores before its first heap read.
            memory.events.append(dict(site=layout.search.address,operation='save-entry-registers',
                registers=[4,5,6,7,14],stack_span=[-20,0],frame_origin_coordinate=sp))
            memory.store_pointer(sp+4,None,layout.search.address+14,'initial selected zero')
            memory.store_pointer(sp,None,layout.search.address+16,'initial predecessor zero')
            raise median._Boundary(c+22,'nested search witness refused: '+str(error)) from error
        for event in search_report['memory_events']:
            if event['operation']=='write32':
                value=event['value'];pointer=None if value==0 else value[1]
                memory.store_pointer(event['coordinate'],pointer,event['site'],event['role'])
            elif event['operation']=='read8':
                observed=memory.read(event['coordinate'],event['site'],event['role'])
                if observed!=event['value']:raise ValueError('search event replay differs from composed state')
            else:
                # Retained search frame is relative to insertion local SP.
                memory.events.append(dict(event,frame_origin_coordinate=sp))
        if not search_report['returns_under_witness']:
            raise median._Boundary(c+22,'nested search does not return under witness: '+search_report['status'])
        memory.protected.remove(nested_save)
        index=(((block_offset<<14)&0xffffffff)>>16)&65535
        previous=memory.load_pointer(sp,c+44,'first predecessor output reload')
        if previous is None:memory.putword(0,index,(c+58,c+62),'new heap head')
        else:memory.putword(previous+10,index,(c+50,c+54),'predecessor next link')
        following=memory.load_pointer(sp+4,c+64,'first successor output reload')
        if following is not None:memory.putword(following+8,index,(c+70,c+74),'successor previous link')
        previous_again=memory.load_pointer(sp,c+76,'second predecessor output reload')
        prev_index=0 if previous_again is None else (((previous_again<<14)&0xffffffff)>>16)
        memory.putword(block_offset+8,prev_index,(c+92,c+96),'inserted previous link')
        following_again=memory.load_pointer(sp+4,c+98,'second successor output reload')
        next_index=0 if following_again is None else (((following_again<<14)&0xffffffff)>>16)
        memory.putword(block_offset+10,next_index,(c+114,c+118),'inserted next link')
        old_count=memory.word(4,(c+120,c+122),'heap count before increment')
        new_count=(old_count+1)&65535
        memory.putword(4,new_count,(c+130,c+134),'heap count increment modulo16')
        summary.update(inserted_index=index,predecessor=previous_again,successor=following_again,
                       count_before=old_count,count_after=new_count,overflow=old_count==65535)
        memory.events.append(dict(site=c+138,operation='ordinary-call',target=layout.median.median,SP=sp))
        median_save=(sp-8,sp);memory.protected.append(median_save)
        median_report=median._median(memory,layout.median.median,max_median_links,-20)
        memory.protected.remove(median_save)
        memory.events.extend([
            dict(site=c+142,operation='deallocate-output-locals',coordinates=[sp,sp+8],aliases_expire=True),
            dict(site=c+144,operation='restore-entry-registers',registers=[4,5],stack_span=[-12,-4]),
            dict(site=c+146,operation='restore-entry-LR-into-R0',stack_span=[-4,0]),
            dict(site=c+148,operation='return-saved-entry-LR')])
    except median._Boundary as error:boundary=error.report
    return dict(schema=SELECTOR,status='conditional returned insertion relation' if boundary is None else 'retained conditional insertion boundary',
        returns_under_witness=boundary is None,boundary=boundary,summary=summary,
        search_relation=search_report,median_relation=median_report,memory_events=memory.events,
        changed_cells={str(k):memory.cells[k] for k in sorted(memory.changed)},
        output_local_coordinates=[sp,sp+8],output_local_lifetime='expired on return; no future-use or nonescape claim',
        numeric_frame=dict(entry_SP_coordinate=entry_sp,insertion_private_bytes=20,including_search_private_bytes=40,
                           including_median_private_bytes=28,provided_protected_spans=protected_spans),
        physical_access_proved=False,actual_entry_heap_SP_or_alias_proved=False,allocation_extent_proved=False,
        actual_frame_noninterference_proved=False,actual_termination_proved=False,nonescape_proved=False,source_or_native_admission=False,
        obligations=[
            dict(id='actual-binding',proved=False,text='All complete indexed bodies, retained dependency identities and supplied heap/block/SP values equal actual reaching state.'),
            dict(id='physical-memory',proved=False,text='Every base-plus coordinate is aligned as needed, live, valid, nonwrapping ordinary RAM with actual read/write permissions. No byte or role name provides allocation extent.'),
            dict(id='saved-control-and-source',proved=False,text='All actual protected caller/source/saved regions, beyond the supplied numeric ranges, survive writes; incoming ThumbLR is valid and executing code stays unchanged.'),
            dict(id='entry-byte-origins',proved=False,text='All integer and pointer-representation tokens have independently justified reaching origins. Unknown bits are never promoted to initialized scalars or pointers.'),
            dict(id='stable-memory-and-helper-effects',proved=False,text='Only ordered listed writes occur, with no interrupt/device/external interference. Retained search and median conditional contracts apply to these new states.'),
            dict(id='lifetime-and-return-aliases',proved=False,text='Output locals die at deallocation; ambient aliases, unknown scratch results and stored pointer tokens retain future-use and nonescape obligations.')])
