"""Exact conditional byte-count wrapper around the frozen allocator relation.

R0 is an incoming heap pointer. This body contains no global-pointer load.
Rounding and index truncation retain machine wrap; no requested object extent
or successful allocation follows from returning a selected-block-plus12 token.
"""
from dataclasses import dataclass
import hashlib

import allocator_split_relation as split
import allocator_remove_relation as remove

SELECTOR='conditional-allocator-byte-count-return-v1'
HEAD=bytes.fromhex('00b5 021c 0029 01d1 0020 12e0 0320 0840 0028 03d0 0420 4042 0840 011d 8903 090c 101c')
TAIL=bytes.fromhex('0021 0028 01d0 011c 0c31 081c 02bc 0847')


@dataclass(frozen=True)
class Layout:
    address: int
    sha256: str
    allocator: split.Layout


def _identity(address,allocator):
    if type(allocator) is not split.Layout:
        raise ValueError('retained complete split layout required')
    raw=split._identity(allocator.address,allocator.insertion,allocator.thunk,allocator.pointer_literal)
    if allocator.sha256!=hashlib.sha256(raw).hexdigest():
        raise ValueError('split layout identity changed')
    if type(address) is not int or address%2 or not 0<=address<=2**32-54:
        raise ValueError('complete aligned wrapper owner required')
    entries=[(allocator.address,266),(allocator.insertion.address,150),(allocator.insertion.search.address,174),
             (allocator.insertion.median.removal,134),(allocator.insertion.median.median,102),(allocator.thunk,2)]
    if any(max(address,a)<min(address+54,a+n) for a,n in entries):
        raise ValueError('wrapper and retained helper owners overlap')
    return HEAD+remove._bl(address+34,allocator.address)+TAIL


def bind(data,address,instruction_count,allocator_layout,*,selector):
    expected=_identity(address,allocator_layout)
    if type(selector) is not str or selector!=SELECTOR or type(data) is not bytes or data!=expected or \
            type(instruction_count) is not int or instruction_count!=26:
        raise ValueError('complete54-byte/26-instruction byte-count wrapper required')
    return Layout(address,hashlib.sha256(data).hexdigest(),allocator_layout)


def arithmetic(size_word):
    """Actual uint32 rounding, uint16 unit extraction and original-zero branch."""
    if type(size_word) is not int or not 0<=size_word<=0xffffffff:
        raise ValueError('exact unsigned32 size word required')
    rounded=size_word if size_word%4==0 else ((size_word&0xfffffffc)+4)&0xffffffff
    return dict(input_u32=size_word,original_zero_shortcut=size_word==0,
                rounded_u32=rounded,rounding_overflow=size_word>0xfffffffc,
                allocator_units_u16=((rounded<<14)&0xffffffff)>>16,
                full_requested_extent_preserved=False)


def derive(layout,size_word,cells,entry_sp,*,selector,zero12_receipt=None,observed_zero_target=None,
           protected_spans=(),max_search_transitions=256,max_median_links=256):
    if type(selector) is not str or selector!=SELECTOR or type(layout) is not Layout:
        raise ValueError('explicit wrapper selector and retained layout required')
    if layout.sha256!=hashlib.sha256(_identity(layout.address,layout.allocator)).hexdigest():
        raise ValueError('wrapper identity changed')
    numbers=arithmetic(size_word)
    if type(cells) is not dict or len(cells)>4096 or any(type(k) is not int or not -(2**31)<=k<2**31 or not split.insert._cell(v) for k,v in cells.items()) or \
            type(entry_sp) is not int or entry_sp%4 or not -(2**31)+76<=entry_sp<=2**31-4 or \
            type(protected_spans) is not tuple or len(protected_spans)>29 or any(type(p) is not tuple or len(p)!=2 or
                any(type(x) is not int for x in p) or not -(2**31)<=p[0]<p[1]<=2**31 for p in protected_spans) or \
            type(max_search_transitions) is not int or not 1<=max_search_transitions<=256 or \
            type(max_median_links) is not int or not 0<=max_median_links<=256:
        raise ValueError('bounded cells, aligned relative SP and retained helper limits required')
    c=layout.address;save=(entry_sp-4,entry_sp);events=[];boundary=None;core=None;returned=0
    if any(save[0]<hi and save[1]>lo for lo,hi in protected_spans):
        boundary=dict(site=c,coordinate=save[0],reason='wrapper saved LR overlaps provided caller/source protection')
    else:
        events.append(dict(site=c,operation='save-entry-LR',coordinates=list(save)))
        if not numbers['original_zero_shortcut']:
            events.append(dict(site=c+34,operation='ordinary-call',target=layout.allocator.address,
                inputs=dict(R0='incoming heap base',R1=numbers['allocator_units_u16']),SP=entry_sp-4))
            core=split.derive(layout.allocator,numbers['allocator_units_u16'],cells,entry_sp-4,selector=split.SELECTOR,
                zero12_receipt=zero12_receipt,observed_zero_target=observed_zero_target,
                protected_spans=protected_spans+(save,),max_search_transitions=max_search_transitions,max_median_links=max_median_links)
            events.extend(core['memory_events'])
            if not core['returns_under_witness']:
                boundary=dict(site=c+34,coordinate=None,reason='allocator continuation refused',nested=core['boundary'])
            elif core['result_pointer']!=0:
                returned=['base-plus',core['result_pointer'][1]+12]
                events.append(dict(site=c+46,operation='return-pointer-add',base=core['result_pointer'],bytes=12,result=returned,
                    nonwrapping_and_extent_proved=False))
        if boundary is None:
            events.extend([dict(site=c+50,operation='restore-entry-LR-into-R1',coordinates=list(save)),
                           dict(site=c+52,operation='return-saved-entry-LR')])
    return dict(schema=SELECTOR,returns_under_witness=boundary is None,boundary=boundary,
        arithmetic=numbers,result_pointer=returned if boundary is None else None,
        allocator_relation=core,memory_events=events,changed_cells={} if core is None else core['changed_cells'],
        frame=dict(entry_SP_coordinate=entry_sp,own_private_bytes=4,maximum_private_bytes=76,
                   nested_entry_SP=entry_sp-4,protected_saved_LR=list(save)),
        conditional_preserved_registers=list(range(4,13)) if boundary is None else None,
        SP_restored_under_conditions=boundary is None,incoming_heap_source='R0; no memory/global pointer read in this wrapper',
        actual_input_or_heap_proved=False,actual_size_proved=False,actual_heap_bytes_proved=False,
        allocation_extent_proved=False,actual_frame_noninterference_proved=False,
        physical_access_proved=False,installed_identity_proved=False,actual_termination_proved=False,
        source_or_native_admission=False,
        obligations=[dict(id=k,proved=False,text=t) for k,t in [
            ('entry', 'Actual complete bodies, incoming R0 heap, R1 size and relative SP equal this conditional reaching state.'),
            ('saved-return', 'Aligned live wrapper4-byte save and all nested frames are accessible; incoming ThumbLR is valid and all saves survive protected caller/source/heap aliases.'),
            ('allocator', 'Every frozen allocator physical, byte-origin, code, zero-image, noninterference and lifetime condition applies to the new state.'),
            ('return-plus12', 'For nonnull returns, heap+selected+12 is a valid nonwrapping pointer with independently established object extent/lifetime. Rounded or truncated unit counts alone provide no such extent.'),
            ('future-use', 'Returned and ambient aliases retain future access and nonescape obligations; no extra field initialization or numeric heap identity is introduced.')]])
