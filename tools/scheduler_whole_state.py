"""Conditional scheduler chain from one entry byte state and register vector.

Entry stores, allocator/list effects, copy, callback and returns are composed
in order. Existing bounded kernels keep their guards. Unmodeled allocator
private bytes are forgotten, never resurrected as old initialized memory.
This is not a physical-memory witness or source/native admission policy.
"""
from dataclasses import dataclass
import hashlib

import scheduler_entry_state as entry
import scheduler_copy_state as copy
import scheduler_allocator_state as state
import scheduler_callback_entry_state as prefix
import scheduler_callback_state as callback
import scheduler_return_state as returns

SELECTOR='conditional-scheduler-whole-common-byte-state-v1'


@dataclass(frozen=True)
class Layout:
    outer: returns.Layout
    effect: callback.Layout
    thunk_data: bytes


def _validate(layout):
    if type(layout) is not Layout or layout.thunk_data!=b'\x18\x47' or type(layout.thunk_data) is not bytes:
        raise ValueError('retained layouts and complete Thumb BX R3 thunk required')
    returns._validate(layout.outer);callback._validate(layout.effect)
    c=layout.outer.callee;a=c.allocator.allocator;i=a.insertion;m=i.median
    spans=[(layout.outer.wrapper,60),(c.address,206),(c.allocator.address,54),(a.address,266),
           (i.address,150),(i.search.address,174),(m.removal,134),(m.median,102),
           (a.thunk,2),(c.callback_thunk,2)]
    for start,size in [(layout.effect.callback,658),(layout.effect.helper,292)]:
        if any(start<address+length and start+size>address for address,length in spans):
            raise ValueError('callback/helper overlaps retained scheduler code owner')


def bind(outer_layout,effect_layout,thunk_data,*,selector):
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit whole-state selector required')
    layout=Layout(outer_layout,effect_layout,thunk_data);_validate(layout)
    return layout


def _spans(spans):
    result=[]
    for lo,hi in sorted(spans):
        if result and lo<=result[-1][1]:result[-1]=(result[-1][0],max(hi,result[-1][1]))
        else:result.append((lo,hi))
    return tuple(result)


def derive(layout,arena_base,cells,registers,*,selector,zero12_receipt=None,
           zero92_receipt=None,observed_zero_target=None,protected_spans=(),
           max_links=128,max_search_transitions=256,max_median_links=256):
    """Compose each kernel once on a NEW state; no fabricated saved words.

The retained zero target/receipts remain conditional installed-code premises.
Complete physical mapping, access, interference and caller protections remain
obligations. An input-adapter refusal is at scheduler+20, before that kernel;
its blocked-use site is reported separately, not claimed reached.
"""
    if type(selector) is not str or selector!=SELECTOR:raise ValueError('explicit whole-state selector required')
    _validate(layout)
    if type(protected_spans) is not tuple or len(protected_spans)>24 or any(type(p) is not tuple or len(p)!=2 or
            any(type(n) is not int for n in p) or not -(2**31)<=p[0]<p[1]<=2**31 for p in protected_spans):
        raise ValueError('bounded explicit protection intervals required')
    protected_spans=_spans(protected_spans)
    outer=layout.outer;c=outer.callee.address;effects=layout.effect
    memory=dict(cells);working=None;stages={};writes=set();retired=[];forgotten=[];reactivations=[]
    boundary=None;stage='entry';reached=False;allocation=None;wrapper_sp=None

    def merge(changed):
        for key,value in changed.items():
            at=int(key);memory[at]=value;writes.add(at)

    def fail(site,reason,at=None,**extra):
        error=state.remove._Boundary(site,reason,at)
        error.report.update(extra);raise error

    def consume(report,key,success):
        stages[key]=report
        if not report[success]:
            error=state.remove._Boundary(report['boundary']['site'],report['boundary']['reason'],report['boundary'].get('coordinate'))
            error.report.update(report['boundary']);raise error

    def argument(word,kind,role,use):
        observation=copy.observe(word)
        if observation['kind']!=kind:
            fail(c+20,role+' cannot enter the retained kernel without '+kind+' origins',blocked_use_site=use)
        return observation['coordinate' if kind=='base-plus' else 'value']

    def activate(low,high,site):
        nonlocal retired
        remaining=[]
        for lo,hi in retired:
            if high<=lo or low>=hi:remaining.append((lo,hi))
            else:
                if lo<low:remaining.append((lo,low))
                if high<hi:remaining.append((high,hi))
        retired=remaining
        reactivations.append(dict(site=site,span=[low,high],old_initialization_granted=False))

    try:
        first=entry.derive(outer,arena_base,cells,registers,selector=entry.SELECTOR,protected_spans=protected_spans)
        working=first['registers'];merge(first['changed_cells']);wrapper_sp=first['wrapper_entry_SP']
        consume(first,'entry','reaches_scheduler_count_prefix')
        stage='count-argument-adapter'
        scheduler=argument(working[5],'base-plus','post-save scheduler R5',c+30)
        descriptor=argument(working[9],'base-plus','descriptor R9',c+156)
        size=argument(working[4],'constant','narrowed size R4',c+20)
        original_callback=copy.observe(working[8])
        if original_callback['kind']=='constant':callback_word=original_callback['value']
        elif all(type(v) is tuple and v[0]=='opaque-byte' and v[2]==n for n,v in enumerate(working[8])) and \
                all(v[1]==working[8][0][1] for v in working[8]):callback_word=('word-origin',working[8][0][1])
        else:fail(c+20,'callback word cannot be transported by retained069 representation',blocked_use_site=c+54)
        scheduler_sp=first['scheduler_entry_SP']
        if working[13]!=copy._pointer(scheduler_sp-56):fail(c+20,'entry transport SP differs from retained kernel origin')
        stage='allocator-copy'
        try:
            transported=copy.derive(outer.callee,size,memory,scheduler,descriptor,callback_word,scheduler_sp,
                {r:working[r] for r in (10,11,12)},selector=copy.SELECTOR,zero12_receipt=zero12_receipt,
                zero92_receipt=zero92_receipt,observed_zero_target=observed_zero_target,
                protected_spans=protected_spans,max_links=max_links,
                max_search_transitions=max_search_transitions,max_median_links=max_median_links)
        except ValueError as error:
            fail(c+20,'retained kernel input refusal: '+str(error))
        stages['allocator-copy']=transported
        merge(transported['prefix']['changed_cells']);merge(transported['changed_cells'])
        allocation=transported['prefix']['allocation'];working=transported['callback_registers']
        consume(transported,'allocator-copy','reaches_callback_thunk')
        # The allocator's exact heap/output effects are retained, but its
        # private save byte origins are not materialized by that kernel.
        # Forget the entire retired region rather than expose pre-entry bytes.
        low,high=scheduler_sp-132,scheduler_sp-56
        names={v[1] for v in [*memory.values(),*(v for w in working.values() for v in w)]
               if type(v) is tuple and v[0]=='opaque-byte'}
        name='unmodeled retired allocator';n=0
        while name in names:n+=1;name='unmodeled retired allocator:'+str(n)
        for at in range(low,high):memory[at]=('opaque-byte',name,at-low)
        forgotten.append((low,high));retired.append((low,high))
        stage='callback-thunk'
        if working[3]!=copy._constant(effects.callback|1):
            fail(outer.callee.callback_thunk,'actual reloaded R3 does not identify the bound Thumb callback')
        stages['callback-thunk']=dict(site=outer.callee.callback_thunk,bytes=layout.thunk_data.hex(),
            target=effects.callback|1,registers_changed=False,actual_executable_identity_proved=False)
        stage='callback-entry'
        if len(memory)>4096:fail(effects.callback,'bounded next-stage byte state exceeds4096 cells')
        pb=prefix.Binding(effects.callback,effects.callback_data,hashlib.sha256(effects.callback_data).hexdigest())
        entered=prefix.derive(pb,memory,working,selector=prefix.SELECTOR,protected_spans=protected_spans)
        working=entered['registers'];merge(entered['changed_cells'])
        if entered['entry_SP'] is not None and working[13]==copy._pointer(entered['entry_SP']-36):
            activate(entered['entry_SP']-36,entered['entry_SP'],effects.callback+2)
        consume(entered,'callback-entry','reaches_phase_comparison')
        stage='callback-suffix'
        if len(memory)>4096:fail(effects.callback+12,'bounded next-stage byte state exceeds4096 cells')
        if not -(2**31)+108<=entered['entry_SP']<=2**31-40:
            fail(effects.callback+12,'callback/helper frame exceeds retained coordinate bounds')
        acted=callback.derive(effects,working,memory,entry_sp=entered['entry_SP'],
            selector=callback.SELECTOR,protected_spans=protected_spans)
        working=acted['registers'];writes.update(int(k) for k in acted['changed_cells'])
        memory={int(k):v for k,v in acted['post_cells'].items()}
        if effects.helper+2 in acted['trace']:
            activate(entered['entry_SP']-56,entered['entry_SP']-36,effects.helper)
        for event in acted['memory_events']:
            if event['operation']=='allocate-frame':activate(*event['coordinates'],event['site'])
            elif event['operation']=='retire-frame':retired.append(tuple(event['coordinates']))
        consume(acted,'callback-suffix','returns_to_input_continuation_under_conditions')
        stage='return-consumer'
        if acted['observed_return_word']!=copy._constant((c+184)|1):
            fail(effects.callback+656,'actual callback BX word does not name the scheduler continuation')
        if copy.observe(registers[1])['kind']!='constant':
            fail(c+184,'retained071 requires complete original size bits; discarded opaque high bits remain unsupported')
        if len(memory)>4096:fail(c+184,'bounded next-stage byte state exceeds4096 cells')
        end=returns.derive(outer,arena_base,wrapper_sp,allocation,
            {r:registers[r] for r in list(range(13))+[14]},working,memory,selector=returns.SELECTOR,
            protected_spans=_spans(protected_spans+tuple(retired)))
        working=end['registers'];merge(end['changed_cells']);retired.extend(end['retired_spans'])
        consume(end,'return-consumer','reaches_outer_return_thunk');reached=True
    except state.remove._Boundary as error:boundary=error.report
    stale={}
    if working is not None:
        for r,value in working.items():
            observation=copy.observe(value)
            if observation['kind']=='base-plus' and any(lo<=observation['coordinate']<hi for lo,hi in retired):
                stale[str(r)]=observation['coordinate']
    return dict(schema=SELECTOR,boundary=boundary,stage=stage,reaches_outer_return_thunk=reached,
        stages=stages,registers=working,post_cells={str(k):v for k,v in sorted(memory.items())},
        changed_cells={str(k):memory[k] for k in sorted(writes)},
        unmodeled_retired_allocator_spans=forgotten,retired_spans=list(_spans(retired)),
        frame_reactivations=reactivations,
        known_retired_alias_registers=stale,wrapper_entry_SP=wrapper_sp,allocation_coordinate=allocation,
        outer_return_word=stages.get('return-consumer',{}).get('outer_return_word'),
        materialized_entry_saves=stages.get('entry',{}).get('all_saves_materialized',False),
        fabricated_saved_words=False,role_separation_assumed=False,ABI_preservation_assumed=False,
        actual_reaching_state_proved=False,actual_heap_or_SP_proved=False,physical_access_proved=False,
        source_initialization_proved=False,actual_termination_proved=False,nonescape_proved=False,
        full_scheduler_proved=False,all_paths_closed=False,actual_outer_return_executed=False,
        native_admission=False,obligations=[dict(id=k,proved=False,text=t) for k,t in [
            ('entry','The single supplied initial byte state and complete register vector equal actual live wrapper entry state.'),
            ('physical','All common-base pointer arithmetic and accesses in every component are physically nonwrapping, live, aligned and permitted; complete caller/source/code protections and interference exclusion hold.'),
            ('retained-kernels','All retained allocator, installed zero12/92, copy, callback and return conditions apply. Their success flags are conditional, not actual allocation, code installation or execution witnesses.'),
            ('literal-zero-target','The supplied observed zero target is the actual stable word read from the retained ROM point at both real call sites, and the retained installed image/return/private-save conditions hold.'),
            ('lifetime','Retired private bytes stay dead despite retained or unknown aliases. Reused callback frames grant no old initialization. Every later access and possible escape requires its own lifetime justification.'),
            ('control','The complete code owners and thunk remain installed and executable; the final observed outer return word has valid control authority. Unhandled branches and failed guards are not admitted.')]])
