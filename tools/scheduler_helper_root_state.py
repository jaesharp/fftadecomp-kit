"""Conditional phase-zero root transport and actual post079 helper/root return.

Every store and POP observes one ordered common-byte state. Complete owner
identity supplies instruction facts only, never actual reaching or execution.
"""
from dataclasses import dataclass
import hashlib

import scheduler_zero40_state as zero
import scheduler_helper_common_state as helper

words,atoms = zero.words,zero.state
SELECTOR = 'conditional-helper-root-common-byte-continuation-v1'
ROOT = bytes.fromhex('70b589b0061c0d1c141c2b8880204000834226d0834204dc002b0bd0012b1dd05ce0034883422fd00130834248d055e001010000e88aa0706d68256105220006002800d00022044900930196281c0023e2f77afc606141e098d73908d5f7d2fe3ce06069e2f762fd6061002836d12069e31c00960521002200f096f9a06000282ad02888013028e0e078002826d0022802d18120400020e002a99e2088820120c882206903900548402102aa331c08f705f8e060288801300fe00000515f0e08a06800f0a3f9a060002807d1e068e2f7cdfce060002801d102202880002009b070bc02bc0847')
CALLS = (80,92,100,120,174,194,206)


@dataclass(frozen=True)
class Layout:
    prior: zero.Layout
    root: int
    root_data: bytes


def _validate(layout):
    if type(layout) is not Layout or type(layout.root) is not int or layout.root%4 or \
            not 0<=layout.root<=2**32-230 or type(layout.root_data) is not bytes or len(layout.root_data)!=230:
        raise ValueError('complete aligned230B root and prior079 layout required')
    owners=zero._validate(layout.prior)
    c=layout.prior.prior.coordinate;h=c.helper
    known=dict(owners)
    known.update({h.helper:h.helper_data,h.getter:h.getter_data,h.identity:h.identity_data,h.coordinates:h.coordinates_data,
                  c.transform:c.transform_data,c.predicate:c.predicate_data,c.motion:c.motion_data,
                  layout.prior.image_base:layout.prior.image})
    if any(layout.root<p+len(b) and layout.root+230>p for p,b in known.items()):
        raise ValueError('complete root overlaps retained owner/image')
    expected=bytearray(ROOT);calls={}
    for off in CALLS:
        target=helper.shapes._call(layout.root_data,layout.root,off)
        if target is None or target%2 or not 0<=target<2**32:
            raise ValueError('root requires actual complete Thumb call identities')
        calls[off]=target;expected[off:off+4]=atoms.remove._bl(layout.root+off,target)
    if calls[80]!=h.helper:raise ValueError('root case0 call does not identify retained helper')
    # Nonselected calls remain bound identities, not admitted effects.
    for off in (88,188):expected[off:off+4]=layout.root_data[off:off+4]
    if not int.from_bytes(layout.root_data[188:192],'little')&1 or layout.root_data!=bytes(expected):
        raise ValueError('complete230B root shape/literals differ')
    known[layout.root]=layout.root_data
    return known


def bind(prior_layout,root_data,root_address,*,selector):
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit080 selector required')
    result=Layout(prior_layout,root_address,root_data);_validate(result);return result


def derive_entry(layout,arena_base,cells,registers,*,selector,protected_spans=(),retired_spans=(),max_steps=256):
    """New actual phase0 entry transport; other phases stop at exact targets."""
    return _execute(layout,arena_base,cells,registers,selector=selector,stage='entry',
        root_entry_sp=None,root_return_word=None,protected_spans=protected_spans,retired_spans=retired_spans,max_steps=max_steps)


def derive_continuation(layout,arena_base,cells,registers,root_entry_sp,root_return_word,*,selector,
                        protected_spans=(),retired_spans=(),max_steps=256):
    """Conditional079 continuation with explicit enclosing entry SP/LR premises."""
    return _execute(layout,arena_base,cells,registers,selector=selector,stage='return',
        root_entry_sp=root_entry_sp,root_return_word=root_return_word,protected_spans=protected_spans,
        retired_spans=retired_spans,max_steps=max_steps)


def continue_from_079(layout,arena_base,report,root_entry_sp,root_return_word,*,selector,protected_spans=(),max_steps=256):
    _validate(layout)
    h=layout.prior.prior.coordinate.helper.helper
    owners=zero._validate(layout.prior)
    pins=[dict(address=p,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for p,b in sorted(owners.items())]
    if type(report) is not dict or report.get('schema')!=zero.SELECTOR or report.get('boundary') is not None or \
            report.get('conditional_returns')!=dict(zero40=True,callback=True,scheduler=True) or \
            report.get('final_PC')!=h+270 or report.get('complete_owner_pins')!=pins or \
            report.get('image_pin')!=dict(address=layout.prior.image_base,bytes=176,sha256=zero.IMAGE_SHA256) or \
            type(root_entry_sp) is not int or report.get('scheduler_entry_SP')!=root_entry_sp-124:
        raise ValueError('079 successful exact helper continuation/owner/frame report required')
    result=derive_continuation(layout,arena_base,{int(k):v for k,v in report['post_cells'].items()},report['registers'],
        root_entry_sp,root_return_word,selector=selector,protected_spans=protected_spans,
        retired_spans=tuple(tuple(v) for v in report['retired_spans']),max_steps=max_steps)
    result['inherited_079_obligations']=report.get('obligations',[])
    result['inherited_078_obligations']=report.get('inherited_078_obligations',[])
    result['inherited_zero12_compositions']=report.get('inherited_zero12_compositions',[])
    result['actual_079_reaching_authentication_proved']=False
    return result


def _execute(layout,arena_base,cells,registers,*,selector,stage,root_entry_sp,root_return_word,
             protected_spans,retired_spans,max_steps):
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit080 selector required')
    owners=_validate(layout)
    if type(arena_base) is not int or arena_base%4 or not 0<=arena_base<2**32 or \
            type(registers) is not dict or set(registers)!=set(range(15)) or any(
                type(k) is not int or not words._word(v) for k,v in registers.items()) or \
            type(cells) is not dict or len(cells)>4096 or any(type(k) is not int or not -(2**31)<=k<2**31 or
                not atoms._cell(v) for k,v in cells.items()) or type(max_steps) is not int or not 1<=max_steps<=256:
        raise ValueError('bounded numeric base/register/byte/step inputs required')
    if stage=='return' and (type(root_entry_sp) is not int or not -(2**31)<=root_entry_sp<2**31 or not words._word(root_return_word)):
        raise ValueError('explicit root entrySP and complete incoming return word required')
    for spans in (protected_spans,retired_spans):
        if type(spans) is not tuple or len(spans)>80 or any(type(s) is not tuple or len(s)!=2 or
            any(type(v) is not int for v in s) or not -(2**31)<=s[0]<s[1]<=2**31 for s in spans):
            raise ValueError('bounded protection/lifetime intervals required')
    root,h=layout.root,layout.prior.prior.coordinate.helper.helper
    r,m,retired=dict(registers),dict(cells),list(retired_spans)
    pc=root if stage=='entry' else h+270
    start=pc;flags=None;boundary=cut=None
    trace,events,returns=[],[],[]
    entry_sp,expected_return=root_entry_sp,root_return_word
    reached_helper=returned_helper=returned_root=False
    phase=mode=None
    sites=set(range(root,root+48,2))|set(range(root+52,root+82,2)) if stage=='entry' else \
          {h+270,h+272,h+274,h+276,root+84,root+86,root+220,root+222,root+224,root+226,root+228}

    def stop(reason,at=None,**extra):
        error=atoms.remove._Boundary(pc,reason,at);error.report.update(extra);raise error
    def physical(at,width,write=False,allocating=False):
        if not -(2**31)<=at<=2**31-width or not 0<=arena_base+at<=2**32-width:
            stop('numeric common-base access/frame wraps',at)
        if width in (2,4) and at%width:stop('unaligned byte-state access',at)
        if not allocating and any(at<hi and at+width>lo for lo,hi in retired):stop('access overlaps retired private bytes',at)
        if write and any(at<hi and at+width>lo for lo,hi in protected_spans):stop('actual write overlaps protected bytes',at)
        if write and any(arena_base+at<p+len(b) and arena_base+at+width>p for p,b in owners.items()):
            stop('actual write overlaps assumed immutable owner/image',at)
    def address(word):
        value=words.observe(word)
        if value['kind']!='base-plus':stop('address lacks intact common-base provenance')
        return value['coordinate']
    def numeric(word):
        value=words.observe(word)
        if value['kind']!='constant':stop('scalar/control observation has opaque or pointer bits')
        return value['value']
    def load(at,width):
        physical(at,width);value=tuple(m.get(at+i) for i in range(width))
        if any(v is None for v in value):stop('read lacks reaching byte origins',at)
        if width<4 and any(type(v) is not int for v in value):stop('scalar field observes opaque or pointer bytes',at)
        events.append(dict(site=pc,operation='read'+str(width*8),coordinate=at,bytes=value))
        return value+(0,)*(4-width)
    def store(at,value):
        physical(at,len(value),True)
        if len(value)<4 and any(type(v) is not int for v in value):stop('narrow write has unknown scalar bits',at)
        if len(set(m)|set(range(at,at+len(value))))>4096:stop('byte state exceeds4096 cells',at)
        m.update({at+i:v for i,v in enumerate(value)})
        events.append(dict(site=pc,operation='write'+str(len(value)*8),coordinate=at,bytes=value))
    def activate(lo,hi,forget=False):
        nonlocal retired
        physical(lo,hi-lo,allocating=True)
        if lo%4 or hi%4:stop('unaligned actual private frame',lo)
        new=[]
        for a,b in retired:
            if hi<=a or lo>=b:new.append((a,b))
            else:
                if a<lo:new.append((a,lo))
                if hi<b:new.append((hi,b))
        retired=new
        if forget:
            if len(set(m)|set(range(lo,hi)))>4096:stop('local byte state exceeds4096 cells',lo)
            names={v[1] for v in [*m.values(),*(v for w in r.values() for v in w)] if type(v) is tuple and v[0]=='opaque-byte'}
            name='080 root local';n=0
            while name in names:n+=1;name='080 root local:'+str(n)
            for at in range(lo,hi):m[at]=('opaque-byte',name,at-lo)
        events.append(dict(site=pc,operation='allocate-frame',coordinates=[lo,hi],initialization_granted=False))
    def retire(lo,hi):
        retired.append((lo,hi));events.append(dict(site=pc,operation='retire-frame',coordinates=[lo,hi]))
    def add(word,n):
        value=words.observe(word)
        if value['kind']=='base-plus':
            at=value['coordinate']+n
            if not -(2**31)<=at<2**31 or not 0<=arena_base+at<2**32:stop('pointer arithmetic wraps common-base coordinate')
            return words._pointer(at)
        return words._constant((numeric(word)+n)&0xffffffff)
    def compare(left,right):
        a,b=numeric(left),numeric(right);v=(a-b)&0xffffffff
        return bool(v&0x80000000),v==0,a>=b,bool((a^b)&(a^v)&0x80000000)
    try:
        if stage=='entry':entry_sp=address(r[13]);expected_return=r[14]
        if entry_sp%4:stop('unaligned enclosing root entrySP')
        physical(entry_sp,1)
        if stage=='return' and (r[13]!=words._pointer(entry_sp-124) or r[1]!=words._constant((h+270)|1)):
            stop('post079 SP/return word differs from actual helper/root frame relation')
        for _ in range(max_steps):
            if pc not in sites:
                stop('control outside selected phase0 entry/return path',cutpoint='unmodeled-root-path')
            owner=root if root<=pc<root+230 else h
            data=owners[owner];off=pc-owner;op=int.from_bytes(data[off:off+2],'little');nxt=pc+2;trace.append(pc)
            if op&0xfe00==0xb400:
                selected=[i for i in range(8) if op&(1<<i)]+([14] if op&256 else [])
                top=address(r[13]);lo=top-4*len(selected);values=[r[i] for i in selected]
                physical(lo,top-lo,True,True);activate(lo,top)
                for i,value in enumerate(values):store(lo+4*i,value)
                r[13]=words._pointer(lo)
            elif op&0xff00==0xbc00:
                selected=[i for i in range(8) if op&(1<<i)];lo=address(r[13])
                values=[load(lo+4*i,4) for i in range(len(selected))]
                for i,value in zip(selected,values):r[i]=value
                r[13]=add(r[13],4*len(selected));retire(lo,lo+4*len(selected))
            elif op&0xff00==0xb000:
                lo=address(r[13]);delta=(-1 if op&128 else 1)*4*(op&127);new=add(r[13],delta);hi=address(new)
                if delta<0:activate(hi,lo,True)
                else:retire(lo,hi)
                r[13]=new
            elif op&0xf800==0x2000:r[(op>>8)&7]=words._constant(op&255);flags=None
            elif op&0xf800==0x0000:
                r[op&7]=words._constant((numeric(r[(op>>3)&7])<<((op>>6)&31))&0xffffffff);flags=None
            elif op&0xfe00==0x1c00:
                delta=(op>>6)&7
                r[op&7]=r[(op>>3)&7] if delta==0 else add(r[(op>>3)&7],delta);flags=None
            elif op&0xf800==0x3000:
                rd=(op>>8)&7;r[rd]=add(r[rd],op&255);flags=None
            elif op&0xf800==0x2800:flags=compare(r[(op>>8)&7],words._constant(op&255))
            elif op&0xffc0==0x4280:flags=compare(r[op&7],r[(op>>3)&7])
            elif op&0xf000==0xd000:
                if flags is None:stop('branch lacks exact preceding comparison')
                n,z,c,v=flags;k=(op>>8)&15
                cond=(z,not z,c,not c,n,not n,v,not v,c and not z,not c or z,n==v,n!=v,not z and n==v,z or n!=v)
                if k>=len(cond):stop('unsupported conditional instruction')
                if cond[k]:
                    d=op&255;nxt=pc+4+2*(d-256 if d&128 else d)
            elif op&0xf800==0xe000:
                d=op&2047;nxt=pc+4+2*(d-2048 if d&1024 else d)
            elif op&0xf800==0x4800:
                at=((pc+4)&~3)+4*(op&255)
                if at not in (root+48,root+88):stop('literal outside bound selected root pools')
                r[(op>>8)&7]=tuple(data[at-owner:at-owner+4]);events.append(dict(site=pc,operation='read-ROM32',address=at,bytes=r[(op>>8)&7]))
            elif op&0xf000==0x9000:
                at=address(r[13])+4*(op&255);reg=(op>>8)&7
                if op&0x800:r[reg]=load(at,4)
                else:store(at,r[reg])
            elif op&0xf000 in (0x6000,0x7000,0x8000):
                width={0x6000:4,0x7000:1,0x8000:2}[op&0xf000];at=address(r[(op>>3)&7])+width*((op>>6)&31);rd=op&7
                if op&0x800:
                    r[rd]=load(at,width)
                    if pc==root+10:phase=numeric(r[rd])
                else:store(at,r[rd][:width])
            elif op&0xf800==0xf000:
                if pc!=root+80:stop('call outside selected root helper edge')
                mode=numeric(r[2]);r[14]=words._constant((root+84)|1)
                cut=dict(call_site=pc,target=h,SP=address(r[13]),return_word=r[14],register_arguments={i:r[i] for i in range(4)},callee_executed=False)
                events.append(dict(site=pc,operation='ordinary-call',target=h,SP=address(r[13]),return_word=r[14]))
                reached_helper=True;pc=h;break
            elif op&0xff87==0x4700:
                target=r[(op>>3)&15];word=numeric(target)
                if owner==h:
                    if word!=(root+84)|1:stop('actual helper saved return differs from root case0 continuation',target_word=word)
                    if r[13]!=words._pointer(entry_sp-52):stop('actual helper return SP differs from live root frame')
                    returned_helper=True;nxt=root+84
                else:
                    if target!=expected_return:stop('actual root saved return differs from incoming LR',target_word=word)
                    if not word&1:stop('root return does not establish a Thumb continuation',target_word=word)
                    if r[13]!=words._pointer(entry_sp):stop('actual root return SP differs from entry')
                    returned_root=True;nxt=word&~1
                returns.append(dict(owner=owner,site=pc,target=nxt,SP=address(r[13])))
                events.append(dict(site=pc,operation='bx-known-continuation',target=nxt,executable_authority_proved=False))
                if returned_root:pc=nxt;break
            else:stop('instruction outside080 selected exact decoder',encoding=op)
            pc=nxt
        else:stop('explicit instruction bound exhausted; no termination claim')
    except atoms.remove._Boundary as error:boundary=error.report
    stale={}
    for reg,word in r.items():
        value=words.observe(word)
        if value['kind']=='base-plus' and any(lo<=value['coordinate']<hi for lo,hi in retired):stale[str(reg)]=value['coordinate']
    return dict(schema=SELECTOR,stage=stage,starts_at=start,final_PC=pc,boundary=boundary,nested_call_cutpoint=cut,
        reaches_helper_entry=reached_helper,conditional_returns=dict(helper=returned_helper,root=returned_root),
        root_entry_SP=entry_sp,root_entry_LR=expected_return,observed_root_phase=phase,helper_mode=mode,
        registers=r,post_cells={str(k):v for k,v in sorted(m.items())},changed_cells={str(k):v for k,v in sorted(m.items()) if cells.get(k)!=v},
        changed_cells_include_explicit_forgetting=True,trace=trace,memory_events=events,actual_returns=returns,
        retired_spans=retired,known_retired_alias_registers=stale,
        complete_owner_pins=[dict(address=p,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for p,b in sorted(owners.items())],
        fabricated_callee_effects=False,fabricated_saved_words=False,ABI_preservation_assumed=False,
        actual_reaching_state_proved=False,physical_access_proved=False,actual_heap_or_SP_proved=False,
        actual_lifetime_proved=False,actual_installed_identity_proved=False,actual_code_execution_proved=False,
        actual_termination_proved=False,whole_owner_CFG_closed=False,Sqrt_effect_proved=False,
        actual_root_return_executed=False,source_or_ELF_admission=False,native_admission=False,
        obligations=[dict(id=k,proved=False,text=v) for k,v in (
          ('reaching','Supplied root entry or post079 state, numeric base and enclosing entrySP/LR must be actual reaching origins. Shape/coordinate guards do not establish that witness.'),
          ('access','Every ordered save, field access and POP needs live ordinary little-endian physical permission, complete caller/code protections and no asynchronous interference.'),
          ('alias','All addresses must use the same complete common-base alias model. No heap/payload/frame role separation or callee-saved ABI snapshot is assumed.'),
          ('lifetime','Retired bytes and surviving stale aliases remain tracked; physical allocation/lifetime and untracked escapes are not proved.'),
          ('control','The exact code must be executable/unchanged, inherited installed-image premises must hold, and the observed final Thumb return must have control authority. Conditional return is not actual execution.'),
          ('scope','Only root phase0 through the supported helper path and exact tail is closed. Other phases, unknown nested callees, Sqrt, fullCFG, actual termination and native admission remain open.'),
        )])


def compose(layout,arena_base,cells,registers,*,selector,protected_spans=(),zero12_receipt=None):
    """One NEW conditional root state through retained kernels, without replay.

    Every predecessor receives the actual preceding poststate. No entry snapshots
    supply returning registers, saved words, initialization or helper outcomes.
    """
    _validate(layout)
    reports={};current=None;stage='root-entry'
    entry=derive_entry(layout,arena_base,cells,registers,selector=selector,protected_spans=protected_spans)
    reports[stage]=current=entry
    if entry['reaches_helper_entry']:
        p=layout.prior.prior
        stage='helper075';current=helper.derive(p.coordinate.helper,arena_base,
            {int(k):v for k,v in current['post_cells'].items()},current['registers'],selector=helper.SELECTOR,
            protected_spans=protected_spans,retired_spans=tuple(tuple(v) for v in current['retired_spans']))
        reports[stage]=current
        cut=current.get('nested_call_cutpoint')
        if cut is not None and cut.get('target')==p.coordinate.transform:
            stage='coordinate076';current=zero.small.coordinate.continue_from_075(p.coordinate,arena_base,current,
                selector=zero.small.coordinate.SELECTOR,protected_spans=protected_spans)
            reports[stage]=current
            if current.get('reaches_helper_scheduler_call'):
                stage='scheduler078';current=zero.small.continue_from_076(p,arena_base,current,selector=zero.small.SELECTOR,
                    protected_spans=protected_spans,zero12_receipt=zero12_receipt)
                reports[stage]=current
                cut=current.get('nested_call_cutpoint')
                if cut is not None and cut.get('call_site')==p.scheduler.address+48 and cut.get('thunk')==p.scheduler.allocator.allocator.thunk:
                    stage='zero079';current=zero.continue_from_078(layout.prior,arena_base,current,selector=zero.SELECTOR,protected_spans=protected_spans)
                    reports[stage]=current
                    if current.get('conditional_returns')==dict(zero40=True,callback=True,scheduler=True):
                        stage='return080';current=continue_from_079(layout,arena_base,current,entry['root_entry_SP'],entry['root_entry_LR'],
                            selector=SELECTOR,protected_spans=protected_spans)
                        reports[stage]=current
    return dict(schema=SELECTOR+'-composition',stage=stage,stages=reports,boundary=current['boundary'],
        conditional_root_return=current.get('conditional_returns',{}).get('root',False),
        root_entry_SP=entry['root_entry_SP'],root_entry_LR=entry['root_entry_LR'],registers=current['registers'],
        post_cells=current['post_cells'],retired_spans=current['retired_spans'],
        known_retired_alias_registers=current.get('known_retired_alias_registers',{}),
        all_component_conditions_retained=True,actual_reaching_state_proved=False,actual_root_return_executed=False,
        physical_access_proved=False,actual_installed_identity_proved=False,actual_termination_proved=False,
        whole_owner_CFG_closed=False,Sqrt_effect_proved=False,native_admission=False)
