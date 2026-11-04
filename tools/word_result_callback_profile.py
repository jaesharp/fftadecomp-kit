"""Explicit R7 callback/local-output/normal-word-result composition.

Conditional ordinary ARM ABI only. This selector establishes no physical
memory, termination, arithmetic or nominal C function-type theorem.
"""
import hashlib
import importlib
import json
from pathlib import Path

import match
import owner_graph_profile as graph
import function_thunk_profile as thunk
import protected_descriptor_word_profile as descriptor
import descriptor_output_alias_profile as frame
import callback_local_two_output_frame as local
import word_result_return_scratch as terminal
import static_callback_target_preservation_profile as r7

SELECTOR = 'static-callback-local-output-word-return-r7-v1'
SCHEMA = 'elf-symbol-thumb-static-callback-local-output-word-return-r7-v1'
CONTROL_FLOW = 'complete Thumb owner with R7-authenticated two-local-output callbacks and consumer-bound normal word returns'
MAX_DEPENDENCIES = 14


def sha(data):
    return hashlib.sha256(data).hexdigest()


class _R7Boundary(terminal.ConsumerBoundary):
    def call_target(self, policy):
        # Complete canonical thunk bytes and owner are authenticated again at
        # the actual call, before any callback return can project scratch.
        thunk.dependencies(['_call_via_r7'], self.inputs[0])
        return r7.THUNK


def _continuation(data, address, refinement, call_site):
    """Full root return coverage without requiring the ignored walker R0 use."""
    ins, edges, branches, calls, words = graph.graph(data, address, refinement)
    if branches or words or call_site not in calls:
        raise ValueError('word-result root requires one complete ordinary consumer call')
    graph.partition(data, address, refinement, ins, words)
    returns = {int(site, 16) for site in refinement['returns']}
    start = call_site + ins[call_site].size
    todo, paths, safe = [start], {}, set()
    while todo:
        site = todo.pop()
        if site in paths:
            continue
        item = ins[site]
        read, write = map(set, item.regs_access())
        if match.ARM_REG_R2 in read or match.CS_GRP_CALL in item.groups or match.CS_GRP_INT in item.groups:
            raise ValueError('outer word-result continuation observes or forwards R2')
        if site in returns or match.ARM_REG_R2 in write and item.cc in (match.ARM_CC_AL,match.ARM_CC_INVALID):
            paths[site] = ()
            safe.add(site)
        else:
            paths[site] = edges[site]
            todo.extend(edges[site])
    while True:
        added = {site for site, targets in paths.items() if site not in safe and targets
                 and all(target in safe for target in targets)}
        if not added:
            break
        safe.update(added)
    if start not in safe:
        raise ValueError('outer word-result continuation has an unclosed live cycle')
    return sorted(paths)


class WordResultCallbackProof(r7.StaticCallbackTargetPreservationProof,
                              local.CallbackLocalTwoOutputProof):
    """Distinct policy; old R7 descriptor-word rejection stays unchanged."""
    dependency_budget = MAX_DEPENDENCIES

    def __init__(self, rom, mapping, index, objects, *, root, bindings):
        import owner_admission_profile as owner
        inputs = (rom,mapping,index,objects)
        spans = frame.DescriptorOutputAliasProof(*inputs)
        data = spans.span(root)
        refinement = owner.refine(data,root,mapping)
        ins, _, branches, calls, words = graph.graph(data,root,refinement)
        if branches or words or len(calls) != 1 or type(bindings) is not dict or \
                set(bindings) != {'calls','data','functions','switches'} or bindings['data'] or bindings['switches'] or \
                len(bindings['functions']) != 1:
            raise ValueError('word-result callback root requires one bound call and one typed callback literal')
        root_site, consumer = next(iter(calls.items()))
        offset, name = bindings['functions'][0]
        if type(offset) is not int or offset % 4 or not 0 <= offset <= len(data)-4:
            raise ValueError('callback literal lacks an exact aligned owner word')
        value = int.from_bytes(data[offset:offset+4],'little')
        if type(name) is not str or name != f'func_{value & ~1:08X}' or value % 2 != 1:
            raise ValueError('callback literal lacks its exact typed Thumb target')
        callback = match.function_address_target(name,json.loads(mapping),root,len(data),len(rom))
        callback_data = spans.span(callback)
        callback_refinement = owner.refine(callback_data,callback,mapping)
        _, _, cb_branches, cb_calls, cb_words = graph.graph(callback_data,callback,callback_refinement)
        if cb_branches or cb_words or len(cb_calls) != 1:
            raise ValueError('local-output callback requires one actual complete helper call')
        helper_site, helper = next(iter(cb_calls.items()))
        consumer_data = spans.span(consumer)
        consumer_refinement = owner.refine(consumer_data,consumer,mapping)
        _, _, consumer_branches, consumer_calls, consumer_words = graph.graph(consumer_data,consumer,consumer_refinement)
        if consumer_branches or consumer_words or len(consumer_calls) != 1 or \
                next(iter(consumer_calls.values())) != r7.THUNK:
            raise ValueError('consumer requires one genuine canonical R7 callback site')
        consumer_site = next(iter(consumer_calls))
        local_policy = dict(schema=local.SCHEMA,callback=callback,helper=helper,
            call_site=helper_site,local_bytes=8,callback_sha256=sha(callback_data),
            helper_sha256=sha(spans.span(helper)))
        local_policy.update({name+'_sha256':sha(value) for name,value in
                            zip(('rom','mapping','index','objects'),inputs)})
        # These compiled typed bindings are re-derived from original ELF by the
        # enclosing owner path. They are not a source declaration attestation.
        source = terminal.canonical({'root':root,'root_body_sha256':sha(data),'bindings':bindings}).encode()
        boundary_policy = {key:value for key,value in local_policy.items() if key.endswith('_sha256')}
        boundary_policy.update(schema=terminal.SCHEMA,abi=terminal.ABI,consumer=consumer,
            call_site=consumer_site,callback=callback,helper=helper,
            consumer_sha256=sha(consumer_data),source_sha256=sha(source))
        self.boundary = _R7Boundary(*inputs,source,policy=boundary_policy)
        self.outer_sites = _continuation(data,root,refinement,root_site)
        local.CallbackLocalTwoOutputProof.__init__(self,*inputs,policy=local_policy)
        self.root, self.consumer, self.consumer_site = root,consumer,consumer_site
        self.root_site, self.root_bindings = root_site, terminal.canonical(bindings)
        self._completed, self._preservations = {},{}
        self._callback_active = False
        self.projections = []

    def inspect(self,address,data):
        if address == self.consumer:
            return frame.DescriptorOutputAliasProof.inspect(self,address,data)
        return local.CallbackLocalTwoOutputProof.inspect(self,address,data)

    def _helper_instructions(self):
        data = local.CallbackLocalTwoOutputProof._helper_instructions(self)
        self.records[self.helper] = dict(address=self.helper,end=self.helper+len(data),
            bytes=len(data),body_sha256=sha(data),**self.identities,
            structure={'kind':'exact-ordered-two-local-output-helper-v1'})
        return data

    word_context = descriptor.ProtectedDescriptorWordProof.word_context

    def check_arguments(self,address,arguments,stack,incoming,protected,*,constants=None,site=None,**context):
        if address == r7.THUNK:
            if site != self.consumer_site or context.get('root_frame') != self.root_site or \
                    (constants or {}).get(r7.REGISTER) != self.callback | 1:
                raise ValueError(f'R7 callback lacks its exact consumer/target context: site={site}, root={context.get("root_frame")}, R7={(constants or {}).get(r7.REGISTER)}, expected={(self.consumer_site,self.root_site,self.callback | 1)}')
            self.boundary.validate()
            canonical = thunk.dependencies(['_call_via_r7'],self.rom)[0]
            thunk_data = self.span(address)
            if len(thunk_data) != 2:
                raise ValueError('R7 callback thunk requires exact canonical owner')
            # The complete277 callback and exact helper effects must replay in
            # this context, watching R7 throughout. No E68 identity reuse.
            watched = tuple(sorted(set(context.get('watched',())) | {r7.REGISTER}))
            if set(arguments) != {match.ARM_REG_R1} or incoming or context.get('frame_base') != -4*len(stack):
                raise ValueError(f'callback context mismatch: arguments={arguments}, incoming={incoming}, frame_base={context.get("frame_base")}, stack_words={len(stack)}')
            self._callback_active = True
            try:
                aliases = local.CallbackLocalTwoOutputProof.check_arguments(self,self.callback,
                    arguments,stack,incoming,protected,constants=constants,site=site,
                    **dict(context,watched=watched))
            finally:
                self._callback_active = False
            result = r7._CallbackResult(aliases)
            result.words = aliases.words
            receipt = dict(site=site,thunk=address,register=r7.REGISTER,
                value=self.callback | 1,target=self.callback,watched=list(watched),
                precondition='no reached instruction writes watched R7 in callback or inspected dependencies',
                returning='conditional normal return only')
            self._completed[id(result)] = (result,receipt)
            self.dependencies[address] = thunk_data
            self.records[address] = {'address':address,'end':address+2,'bytes':2,
                'body_sha256':sha(thunk_data),**self.identities,
                'structure':{'kind':'existing-canonical-call-via-register-v1','canonical_dependency':canonical}}
            key = terminal.canonical(receipt)
            self.callbacks[key] = dict(receipt,arguments=[list(pair)for pair in sorted(arguments.items())])
            return result
        if address == self.helper:
            return local.CallbackLocalTwoOutputProof.check_arguments(self,address,arguments,stack,incoming,
                protected,constants=constants,site=site,**context)
        if address == self.callback:
            raise ValueError('callback effects require authenticated canonical R7 dispatch')
        if address != self.consumer or site != self.root_site or self._callback_active:
            raise ValueError('word-result callback excludes other inspected call owners')
        return descriptor.ProtectedDescriptorWordProof.check_arguments(self,address,arguments,stack,
            incoming,protected,constants=constants,site=site,**context)

    def normal_return_aliases(self,address,site,aliases):
        if address != self.callback or not self._callback_active or self._context is None:
            return aliases
        self.boundary.validate()
        if match.ARM_REG_R0 in aliases:
            raise ValueError('normal R0 word result carries a callback-local alias')
        if match.ARM_REG_R2 not in aliases:
            return aliases
        expected = self._context[0]-16
        if aliases[match.ARM_REG_R2] != expected or any(reg != match.ARM_REG_R2 and value == expected
                                                     for reg,value in aliases.items()):
            raise ValueError('R2 local-output projection has copied or unexpected alias')
        result = dict(aliases);del result[match.ARM_REG_R2]
        self.projections.append(dict(site=site,register=2,offset=expected,boundary=self.boundary.seal))
        return result

    def effect_manifest(self):
        local_effects = local.CallbackLocalTwoOutputProof.manifest(self)
        preservation = self.preservation_observations()
        if not preservation or not self.projections or not self.callbacks:
            raise ValueError('word-result callback lacks completed preservation/effect/projection replay')
        return dict(schema=SCHEMA,abi=terminal.ABI,normal_result='R0 word only, unknown value',
            consumer=self.boundary.validate(),outer_checked_sites=self.outer_sites,
            local_effects=local_effects,projections=self.projections,
            r7_preservation=dict(policy=r7.policy_manifest(),observations=preservation),
            producer_sha256={name:sha(Path(importlib.import_module(name).__file__).read_bytes())for name in
                ('word_result_callback_profile','word_result_return_scratch','callback_local_two_output_frame')},
            claims_excluded=['physical memory','termination','C nominal function-type equivalence'])
