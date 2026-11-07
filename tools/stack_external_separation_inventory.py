"""Exact conditional numerical separation, without selecting a runtime stack."""
import hashlib
import json
from pathlib import Path

SELECTOR = 'stack-external-numerical-separation-inventory-v1'
SPACE = 1 << 32


def integer(value):
    return type(value) is int


def derive(frame_offsets, excluded_spans, *, selector, alignment=4, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('stack separation requires its explicit inventory selector')
    if type(frame_offsets) not in (tuple, list) or len(frame_offsets) != 2 or \
            not all(integer(v) for v in frame_offsets):
        raise ValueError('frame requires exact signed integer endpoints')
    lower, upper = frame_offsets
    if not -SPACE < lower <= 0 <= upper < SPACE or lower >= upper or \
            not integer(alignment) or alignment < 1 or alignment > 16 or alignment & (alignment-1):
        raise ValueError('frame or alignment leaves the finite address domain')
    if type(excluded_spans) not in (tuple, list) or not excluded_spans:
        raise ValueError('stack separation requires explicit numerical excluded spans')
    spans = []
    for row in excluded_spans:
        if type(row) not in (tuple, list) or len(row) != 3 or type(row[0]) is not str or \
                not row[0] or not all(integer(v) for v in row[1:]) or not 0 <= row[1] < row[2] <= SPACE:
            raise ValueError('excluded span requires a label and complete nonwrapping endpoints')
        spans.append(list(row))
    spans.sort()
    if len({row[0] for row in spans}) != len(spans):
        raise ValueError('excluded span labels must be unique')
    first, last = (max(0, -lower)+alignment-1)//alignment, min(SPACE-1, SPACE-upper)//alignment
    forbidden, derivations = [], []
    for name, start, end in spans:
        # [SP+lower,SP+upper) intersects [start,end) exactly when
        # start-upper < SP < end-lower. Convert the open bounds to
        # inclusive integer bounds before restricting to aligned addresses.
        a, b = start-upper+1, end-lower-1
        left, right = max(first, (a+alignment-1)//alignment), min(last, b//alignment)
        derivations.append(dict(label=name, excluded_span=[start,end],
            forbidden_entry_SP_inclusive=[a,b],
            clipped_aligned_quotients_inclusive=[left,right] if left <= right else []))
        if left <= right:
            forbidden.append([left,right])
    merged = []
    for left, right in sorted(forbidden):
        if merged and left <= merged[-1][1]+1:
            merged[-1][1] = max(merged[-1][1], right)
        else:
            merged.append([left,right])
    allowed, cursor = [], first
    for left, right in merged:
        if cursor < left:
            allowed.append([cursor,left-1])
        cursor = right+1
    if cursor <= last:
        allowed.append([cursor,last])
    result = dict(schema=SELECTOR, inventory_only=True, frame_offsets=list(frame_offsets),
        excluded_spans=spans, alignment=alignment, address_bits=32,
        nonwrapping_aligned_entry_SP_quotients_inclusive=[first,last],
        forbidden_aligned_entry_SP_quotients_inclusive=merged,
        admissible_aligned_entry_SP_quotients_inclusive=allowed,
        admissible_entry_SP_count=sum(b-a+1 for a,b in allowed), derivations=derivations,
        condition='Entry SP is an alignment multiple whose quotient lies in one of the admissible closed intervals; the memory model uses these numerical addresses without aliases or asynchronous mutation.',
        conclusion='Under that explicit membership condition the complete translated frame envelope does not wrap and is numerically disjoint from every listed excluded interval.',
        actual_entry_SP_established=False, physical_memory_permission=False,
        object_extent_or_lifetime_established=False, initialized_contents_established=False,
        asynchronous_noninterference_established=False, source_or_ELF_admission=False,
        producer_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    if manifest is not None and json.dumps(manifest,sort_keys=True) != json.dumps(result,sort_keys=True):
        raise ValueError('stack separation inventory manifest differs')
    return result
