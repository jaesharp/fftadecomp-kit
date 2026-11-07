"""Conditional scheduler size/zero/list relation up to its descriptor copy.

The allocator register/frame projection is derived from its complete call
closure. Its field values, allocation success/extent, permissions and separation
remain explicit. A finite list witness is a premise, never invented heap data.
No original producer or old image inventory is replayed by this adapter.
"""
from dataclasses import dataclass
import hashlib
import json

import allocator_saved_flow as saved
import scheduler_descriptor_lifetime as tail
import installed_zero_effects as zero

SELECTOR='conditional-scheduler-prefix-zero-list-v1'
MAX_CHAIN=128
POST_ALLOC=bytes.fromhex('071c 0e48 0268 381c 211c')
LINK_BEFORE_POOL=bytes.fromhex('4346 3b60 a889 f882 002e 18d0 3069 0028 10d0 '
    '011c 8868 3a1c 1832 0028 03d0 8968 8868 0028 fbd1 081c 8760 7860 05e0 0000')
LINK_AFTER_POOL=bytes.fromhex('3761 3a1c 1832 fe60 13e0 6868 0028 03d1 6f60 '
    '3a1c 1832 0ce0 011c 8868 3a1c 1832 0028 03d0 8968 8868 0028 fbd1 081c 8760 7860')
ALLOC_HEAD=bytes.fromhex('00b5 021c 0029 01d1 0020 12e0 0320 0840 0028 03d0 '
    '0420 4042 0840 011d 8903 090c 101c')
ALLOC_TAIL=bytes.fromhex('0021 0028 01d0 011c 0c31 081c 02bc 0847')


@dataclass(frozen=True)
class BoundPrefix:
    root: int
    allocator: int
    zero_thunk: int
    zero_pointer_word: int
    flows: tuple
    root_pin: tuple
    nested_zero_sites: tuple


@dataclass(frozen=True)
class ZeroRule:
    count: int
    image_sha: str
    destination: int
    entry: int
    retained_pin: str
    cases_json: str

    def report(self):
        return dict(count=self.count,image_sha256=self.image_sha,destination=self.destination,
            entry=self.entry,retained_structural_authority=self.retained_pin,
            alignment_cases=json.loads(self.cases_json),preserved_registers=list(range(3,13))+[14],
            R0='incoming ThumbLR',R1=0,R2='destination+count',SP_restored=True,
            destination_reads=[],zero_write_span=[0,self.count],private_save_span=[-4,0],
            unproved_premises=[
                'Installed code equals the retained source image throughout execution',
                'Incoming ThumbLR is a valid continuation and SP is word-aligned',
                'Destination[0,count) is ordinary writable little-endian RAM without faults',
                'Stack[-4,0) is ordinary readable/writable private memory outside protected caller state',
                'Destination, private save and executing image are physically disjoint and do not wrap',
                'No asynchronous writer, interrupt or alias interferes with code or saved return'],
            installed_identity_proved=False,allocator_or_memory_permissions_proved=False,
            actual_caller_count_proved=False,source_or_native_admission=False)


def specialize_zero(payload,destination,entry,retained_receipt,retained_sha,count,*,selector):
    """New count execution through the retained byte-transfer core, no census.

The pinned prior receipt supplies only unchanged source-image structure. Its
old count/effect trace is not reused as the new count theorem. All four actual
destination alignments are independently interpreted for this specialization.
"""
    if type(selector) is not str or selector!=SELECTOR or type(payload) is not bytes or \
            type(retained_receipt) is not bytes or type(retained_sha) is not str or \
            hashlib.sha256(retained_receipt).hexdigest()!=retained_sha:
        raise ValueError('explicit selector and exact retained image authority required')
    if type(count) is not int or not 0<=count<=zero.MAX_COUNT or \
            any(type(v) is not int for v in (destination,entry)) or destination%2 or entry%2 or \
            not 0<=destination<=entry<destination+len(payload)<=0x100000000:
        raise ValueError('bounded count and nonwrapping aligned source-image placement required')
    try:
        old=json.loads(retained_receipt)['effect_evidence']
        if old['schema']!=zero.SELECTOR or old['image_sha256']!=hashlib.sha256(payload).hexdigest() or \
                old['destination']!=destination or old['entry']!=entry or not old['inventory']['instructions']:
            raise ValueError('retained complete image identity or structure differs')
    except (KeyError,TypeError,json.JSONDecodeError) as error:
        raise ValueError('malformed retained image structural authority') from error
    if count==old['count']:
        raise ValueError('unchanged successful zero count must reuse its retained receipt')
    cases=[zero._case(payload,destination,entry,count,alignment) for alignment in range(4)]
    return ZeroRule(count,hashlib.sha256(payload).hexdigest(),destination,entry,retained_sha,
                    json.dumps(cases,sort_keys=True))


def bind_prefix(root,helpers,allocator,zero_thunk,*,selector):
    if type(selector) is not str or selector!=SELECTOR or type(root) is not saved.Body or \
            type(helpers) is not tuple:
        raise ValueError('explicit scheduler prefix selector and complete owners required')
    ins,edges,calls=root.decode();data=root.data;c=root.address
    if c%4 or len(data)!=206 or data[:34]!=tail.CALLEE_HEAD or data[38:48]!=POST_ALLOC or \
            data[52:100]!=LINK_BEFORE_POOL or data[104:154]!=LINK_AFTER_POOL or \
            data[154:180]!=tail.COPY+tail.CALL_SETUP or data[184:]!=tail.CALLEE_RETURN or \
            set(calls)!={c+34,c+48,c+180} or calls[c+34]!=allocator or calls[c+48]!=zero_thunk:
        raise ValueError('complete scheduler prefix/frame/list/continuation shape differs')
    words=root.partition.get('words',())
    if len(words)!=1 or words[0]['address']!=c+100 or words[0].get('load_sites')!=[c+40] or \
            root.partition.get('alignment')!=[[c+98,c+100]]:
        raise ValueError('scheduler zero-pointer literal partition differs')
    root_pointer_word=words[0]['value']
    # The fixed branch encodings above are relocatable and determine all four
    # list paths. The decoder independently checks exact complete boundaries.
    reached=set();pending=[c]
    while pending:
        site=pending.pop()
        if site in reached:continue
        reached.add(site);pending.extend(edges[site])
    if reached!=set(ins):raise ValueError('scheduler complete CFG contains unreachable instructions')
    bodies={b.address:b for b in helpers}
    if allocator not in bodies:raise ValueError('allocator wrapper complete body absent')
    a=bodies[allocator];ai,ae,ac=a.decode()
    if len(a.data)!=54 or a.data[:34]!=ALLOC_HEAD or a.data[38:]!=ALLOC_TAIL or \
            len(ai)!=26 or set(ac)!={allocator+34}:
        raise ValueError('allocator rounding/null/plus12 wrapper shape differs')
    flows=saved.prove_program(helpers,allocator,zero_thunk,selector=saved.SELECTOR)
    af=next(f for f in flows if f.address==allocator)
    if not set(range(4,13))<=set(af.preserved):
        raise ValueError('complete allocator closure does not restore R4 through R12')
    zero_sites=[]
    for b in helpers:
        bi,be,bc=b.decode()
        predecessors={site:set() for site in bi}
        for source,targets in be.items():
            for target in targets:predecessors[target].add(source)
        for site,target in bc.items():
            if target!=zero_thunk:continue
            sites=list(range(site-8,site,2))
            if any(s not in bi or bi[s].size!=2 for s in sites) or any(
                    predecessors[s]!={s-2} for s in sites[1:]+[site]):
                raise ValueError('nested zero setup has an interior bypass or incomplete instructions')
            raw=[int.from_bytes(bi[s].bytes,'little') for s in sites]
            if raw[0]&0xff00!=0x4800 or raw[1]!=0x6802 or raw[2]&0xffc7!=0x1c00 or \
                    raw[3]&0xff00!=0x2100 or (raw[2]>>3)&7 in (0,2):
                raise ValueError('nested zero target/destination/immediate-count setup differs')
            literal=((sites[0]+4)&~3)+4*(raw[0]&255)
            words=[w for w in b.partition['words'] if w['address']==literal and sites[0] in w.get('load_sites',())]
            if len(words)!=1:raise ValueError('nested zero ROM pointer literal is not complete and bound')
            zero_sites.append(dict(site=site,count=raw[3]&255,destination_register=(raw[2]>>3)&7,
                ROM_pointer_word=words[0]['value'],destination_provenance_proved=False,
                loaded_target_equals_installed_entry_proved=False))
    return BoundPrefix(c,allocator,zero_thunk,root_pointer_word,flows,
                        (c,len(data),hashlib.sha256(data).hexdigest()),tuple(zero_sites))


def allocation_arithmetic(size_word):
    if type(size_word) is not int or not 0<=size_word<=0xffffffff:
        raise ValueError('size requires exact unsigned32 bits')
    count=((size_word&65535)+28)&65535
    rounded=(count+3)&~3
    return dict(incoming_u32=size_word,wrapper_u16=size_word&65535,scheduler_count=count,
        allocator_rounded_bytes=rounded,allocator_units=((rounded<<14)&0xffffffff)>>16,
        zero_count=count,allocation_success_proved=False,object_extent_proved=False)


def relate_prefix(binding,zero_rule,size_word,*,wrapper_entry_sp,parent_present,chain,
                  allocation_case='nonzero-block',nested_zero_rules=(),selector):
    """Parametric finite-list relation with every real access still conditional.

Chain names are symbolic pointer variables, not numeric addresses or objects.
The witness asserts exactly the stable next-link reads listed below. It cannot
establish the actual heap list, allocation, readability, separation or lifetime.
"""
    if type(selector) is not str or selector!=SELECTOR or type(binding) is not BoundPrefix or \
            type(zero_rule) is not ZeroRule or type(wrapper_entry_sp) is not int or \
            wrapper_entry_sp%4 or not -1024<=wrapper_entry_sp<=-28 or type(parent_present) is not bool or \
            type(chain) is not tuple or len(chain)>MAX_CHAIN or any(type(n) is not str or
                not n or len(n)>64 for n in chain) or len(set(chain))!=len(chain):
        raise ValueError('bounded explicit prefix state and consistent finite chain witness required')
    arithmetic=allocation_arithmetic(size_word);count=arithmetic['scheduler_count']
    if zero_rule.count!=count:raise ValueError('zero specialization does not cover actual scheduler count')
    if type(nested_zero_rules) is not tuple or any(type(r) is not ZeroRule for r in nested_zero_rules):
        raise ValueError('each nested zero count needs an explicit immutable specialization')
    nested={r.count:r for r in nested_zero_rules}
    expected={r['count'] for r in binding.nested_zero_sites}
    if len(nested)!=len(nested_zero_rules) or set(nested)!=expected or any(
            (r.image_sha,r.destination,r.entry)!=(zero_rule.image_sha,zero_rule.destination,zero_rule.entry)
            for r in nested_zero_rules):
        raise ValueError('nested allocator zero counts/image differ from bound sites')
    if allocation_case not in ('null','nonzero-block'):
        raise ValueError('allocator outcome case must be explicit')
    sp=wrapper_entry_sp-80;c=binding.root
    allocator_flow=next(f for f in binding.flows if f.address==binding.allocator)
    if min(sp-allocator_flow.nested_peak,sp-4)<-1024:
        raise ValueError('combined live frame exceeds retained256-word bound')
    events=[dict(site=c,operation='save-words',address=['stack',wrapper_entry_sp-44],bytes=20,
                 values=['callee-entry R4','callee-entry R5','callee-entry R6','callee-entry R7','callee-entry LR']),
        dict(site=c+6,operation='save-words',address=['stack',wrapper_entry_sp-52],bytes=8,
             values=['callee-entry R8','callee-entry R9']),
        dict(site=c+8,operation='allocate-local',address=['stack',sp],bytes=28,initial_bytes='unproved'),
        dict(site=c+18,operation='read32',address=['stack',sp+56],value='incoming parent word'),
        dict(site=c+30,operation='read32',address=['scheduler',0],value='heap pointer'),
        dict(site=c+34,operation='call',target=binding.allocator,
             inputs={'R0':'heap pointer','R1':count},outcome=allocation_case,
             memory_effects_closed=False),
        dict(site=c+40,operation='read32',address=['ROM-literal',c+100],value=binding.zero_pointer_word),
        dict(site=c+42,operation='read32',address=['ROM-pointer-word',binding.zero_pointer_word],
             value=zero_rule.entry|1,required_value_equality=True)]
    common=dict(schema=SELECTOR,root=binding.root_pin,copy_cutpoint=c+154,arithmetic=arithmetic,
        helper_flows=[f.report() for f in binding.flows],zero_specialization=zero_rule.report(),
        nested_zero_sites=list(binding.nested_zero_sites),
        nested_zero_specializations=[r.report() for r in nested_zero_rules],
        frame=dict(wrapper_entry_SP=wrapper_entry_sp,copy_cutpoint_SP=sp,
                   allocator_deepest_SP=sp-allocator_flow.nested_peak,
                   direct_zero_private_save=[sp-4,sp],physical_permissions=False),
        finite_chain_witness=list(chain),parent_present=parent_present,
        branch_preconditions=[dict(expression='incoming parent '+('!=0' if parent_present else '==0'),proved=False),
            dict(expression='every named chain node is nonzero and all listed next-link equalities hold',proved=False)],
        actual_heap_shape_proved=False,allocator_field_values_closed=False,
        installed_identity_proved=False,actual_memory_or_allocation_proved=False,
        source_initialization_proved=False,callback_effects_closed=False,
        unconditional_termination=False,source_or_native_admission=False)
    if allocation_case=='null':
        return dict(common,status='conditional null-result boundary',events=events,
            boundary=dict(site=c+48,reason='zero destination is null; no writable-span permission follows'),
            reaches_copy_cutpoint=False)
    events.extend([
        dict(site=c+48,operation='conditional-installed-zero',target=binding.zero_thunk,
             destination='allocation',count=count,private_stack=[sp-4,sp],
             exact_writes_by_alignment=json.loads(zero_rule.cases_json)),
        dict(site=c+54,operation='write32',address=['allocation',0],value='incoming callback word'),
        dict(site=c+56,operation='read16',address=['scheduler',12],value='scheduler phase halfword'),
        dict(site=c+58,operation='write16',address=['allocation',22],value='scheduler phase halfword')])
    parent='parent' if parent_present else 'scheduler';head_offset=16 if parent_present else 4
    events.append(dict(site=c+(64 if parent_present else 114),operation='read32',
        address=[parent,head_offset],value=['node',chain[0]] if chain else 0))
    if not chain:
        events.append(dict(site=c+(104 if parent_present else 120),operation='write32',
            address=[parent,head_offset],value='allocation'))
    else:
        for i,node in enumerate(chain):
            events.append(dict(site=c+((72 if i==0 else 84) if parent_present else (130 if i==0 else 142)),
                operation='read32',address=['node',node,8],value=['node',chain[i+1]] if i+1<len(chain) else 0,
                role='initial next test' if i==0 else 'loop next test'))
            if i+1<len(chain):
                # The machine reloads the previous link to advance R1, then
                # reads the next node. Both reads matter under alias/interference.
                events.append(dict(site=c+(82 if parent_present else 140),operation='read32',
                    address=['node',node,8],value=['node',chain[i+1]],role='loop advance reload'))
        events.extend([
            dict(site=c+(92 if parent_present else 150),operation='write32',address=['node',chain[-1],8],value='allocation'),
            dict(site=c+(94 if parent_present else 152),operation='write32',address=['allocation',4],value=['node',chain[-1]])])
    if parent_present:
        events.append(dict(site=c+110,operation='write32',address=['allocation',12],value='parent'))
    conditions=[
        dict(id='actual-input-context',proved=False,scope='complete indexed bodies and retained source/image authorities are trusted and freshly bound to current ROM/maps/runtime; actual caller reaches this prefix'),
        dict(id='physical-frame',proved=False,scope='every listed private/caller/saved span is live, aligned, nonwrapping and permitted; saved stack contents and source descriptor survive all actual external writes'),
        dict(id='allocator-field-and-list-effects',proved=False,scope='every complete helper memory site has the exact address/value/alias effect under its branch; no purity or output extent follows from saved-register restoration'),
        dict(id='allocator-result',proved=False,scope='actual selected block plus12 is the allocation result; its required92/count-byte extent is ordinary writable storage with valid provenance, not a literal RAM premise'),
        dict(id='installed-zero',proved=False,scope='both direct scheduler zero and any nested allocator zero use the actual source image at the loaded target, correct destination/count and return continuation; code/private save/destination are nonwrapping and noninterfering'),
        dict(id='finite-list-witness',proved=False,scope='the explicit parent null/nonzero branch and all ordered head/next-link reads equal the supplied finite witness, including nonzero nodes and loop reloads; zero tail and ordinary instruction completion are actual, not inferred from a budget'),
        dict(id='external-alias-effects',proved=False,scope='all listed zero/header/link writes have real permissions and do not alter protected/source/code state or invalidate later read equalities; symbolic role names grant no physical separation'),
        dict(id='callback-boundary',proved=False,scope='062 copy/return remains a separate retained relation; source R9 and later copy R1 aliases remain exposed to actual callback and may escape')]
    return dict(common,status='conditional finite prefix relation',events=events,obligations=conditions,
        conditional_cutpoint_registers={'R2':'allocation+24','R4':count,'R5':'scheduler','R6':'incoming parent',
            'R7':'allocation','R8':'incoming callback word','R9':'original caller descriptor','SP':sp},
        allocator_preservation_derived_from_actual_saves=list(allocator_flow.preserved),
        ambient_aliases_retained=['R9 original descriptor','R8 callback word','all unknown ordinary output origins'],
        reaches_copy_cutpoint=True,actual_cutpoint_reached=False,full_prefix_memory_effects_closed=False)
