"""Explicit source/ELF bridge to the closed three-call mutable-local inventory.

Roles are reconstructed from live frame aliases and authenticated complete callees,
never supplied by source declarations, an address list or an external policy file.
All ordinary calls remain conditional returning ARM ABI boundaries. This policy
proves no arithmetic equivalence, physical readability, nonaliasing or termination.
"""
import copy
import importlib
from pathlib import Path

import consumer_scratch_alias_profile as consumer
import readonly_leaf_overwrite_profile as leaf
import incoming_scratch_overwrite_profile as ordinary
import three_call_composition_profile as combined
import mutable_stack_index_inventory as inventory

SELECTOR = 'mutable-four-local-index-three-call-native-v1'
SCHEMA = 'elf-symbol-thumb-mutable-four-local-index-three-call-v1'
CONTROL_FLOW = 'complete mutable-local Thumb owner; three original ELF-bound scratch contracts under conditional returning ordinary ARM ABI'
CONTRACT = ('Original ELF call symbols and offsets bind complete caller/callee scratch proofs; '
    'local pointer, initializedness and saved-frame facts retained. Every ordinary call is '
    'conditional on returning and preserving ARM r4-r11/SP. No transitive memory effects, '
    'physical readability, nonaliasing, arithmetic/C equivalence or termination theorem.')


def environment_fingerprint():
    import entry_recursive_ordinary_call_profile as entry
    result = entry.environment_fingerprint()
    for name in ('match', 'owner_admission_profile', 'local_long_branch_profile',
                 'mutable_stack_index_profile', 'mutable_stack_index_inventory',
                 'three_call_composition_profile', 'consumer_scratch_alias_profile',
                 'readonly_leaf_overwrite_profile', 'incoming_scratch_overwrite_profile',
                 'ignored_leaf_alias_profile', __name__):
        path = Path(importlib.import_module(name).__file__)
        result['producers'][path.name] = consumer.ignored.sha(path.read_bytes())
    return result


class NativeRoleProof:
    """Closed role discovery through the real frame's allocated live alias states."""
    def __init__(self, rom, mapping, index, objects, caller, size, calls, bindings):
        self.consumer = consumer.ConsumerScratchAliasProof(rom,mapping,index,objects,caller,size,calls)
        self.leaf = leaf.ReadonlyLeafOverwriteProof(rom,mapping,index,objects,caller,size,calls)
        self.body = self.consumer.body
        self.caller, self.size, self.calls = caller, size, dict(calls)
        self.bindings = copy.deepcopy(bindings)
        self.original = copy.deepcopy(bindings)
        self.roles, self.ordinary, self.observations = {}, None, {}
        self.sources = environment_fingerprint()

    def fresh(self):
        self.consumer.fresh(); self.leaf.fresh()
        if self.consumer.identity() != self.leaf.identity() or self.calls != self.consumer.calls or \
                (self.caller,self.size) != (self.consumer.caller,self.consumer.size) or \
                self.original != self.bindings or self.sources != environment_fingerprint():
            raise ValueError('native role inputs, sources, bindings or producers changed')

    def bind_frame(self, instructions, edges, address, branches, calls):
        self.fresh()
        for proof in (self.consumer,self.leaf):
            proof.bind_frame(instructions,edges,address,branches,calls)

    def _role(self, site, target, aliases):
        import match
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        selected = set(aliases) & set(match.CALLER_CLOBBERED)
        if selected == {match.ARM_REG_R1}:
            return 'leaf_overwrite'
        if selected != {match.ARM_REG_R2}:
            raise ValueError('native roles require the exact supported live scratch-alias shape')
        rows = owner.validate_span(self.body,self.caller,self.consumer.rom,
                                   self.consumer.mapping,self.consumer.index)
        target_rows = [r for r in rows if int(r['rom'],16) == target]
        if len(target_rows) != 1:
            raise ValueError('native role callee requires a unique original owner')
        data = self.consumer.rom[target-match.ROM_BASE:int(target_rows[0]['end'],16)-match.ROM_BASE]
        if not 0 < len(data) <= ordinary.MAX_BYTES:
            raise ValueError('native role callee exceeds the bounded complete-owner budget')
        # This split grants no proof by itself. The chosen complete callee policy
        # below must independently authenticate every reached instruction/return.
        _,_,_,calls,_ = graph.graph(data,target,owner.refine(data,target,self.consumer.mapping))
        return 'ordinary_overwrite' if calls else 'consumer_scratch'

    def check_call(self, site, target, aliases, stack, pointer_slots, initialized):
        self.fresh()
        if self.calls.get(site) != target or [site-self.caller,f'func_{target:08X}'] not in self.bindings['calls']:
            raise ValueError('native scratch role lacks its exact original ELF BL binding')
        role = self._role(site,target,aliases)
        pair = [site,target]
        if role in self.roles and self.roles[role] != pair or any(
                key != role and value[0] == site for key,value in self.roles.items()):
            raise ValueError('native bridge requires exactly three disjoint original scratch roles')
        before = copy.deepcopy((aliases,stack,pointer_slots,initialized))
        if role == 'ordinary_overwrite':
            if self.ordinary is None:
                p = self.consumer
                self.ordinary = ordinary.IncomingScratchOverwriteProof(p.rom,p.mapping,p.index,p.objects,
                    self.caller,self.size,self.calls,{site:target},policy=ordinary.SELECTOR)
                self.ordinary.bind_caller(p.instructions,p.edges,self.caller,self.calls)
            self.ordinary.check_call(site,target,aliases,stack,pointer_slots,initialized)
        else:
            (self.leaf if role == 'leaf_overwrite' else self.consumer).check_call(site,target,aliases,pointer_slots)
        if before != (aliases,stack,pointer_slots,initialized):
            raise ValueError('native scratch role changed caller-local state')
        self.roles[role] = pair
        key = consumer.text([role,site,repr(before)])
        self.observations[key] = {'role':role,'offset':site-self.caller,'symbol':f'func_{target:08X}',
            'state_sha256':consumer.ignored.sha(repr(before).encode()),'local_state_unchanged':True}

    def manifest(self):
        self.fresh()
        if set(self.roles) != combined.ROLES:
            raise ValueError('native bridge requires all three independently proven actual roles')
        return {'sites':copy.deepcopy(self.roles),'canonical_original_ELF_offsets_required':True,
            'observations':[self.observations[key] for key in sorted(self.observations)],
            'contract':CONTRACT}


def verify_owner(data,address,rom,mapping,index,objects,manifest,bindings):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    import mutable_stack_index_profile as finite
    owner.validate_span(data,address,rom,mapping,index)
    refinement = owner.refine(data,address,mapping)
    ins,edges,branches,calls,words = graph.graph(data,address,refinement)
    expected = {'calls':[[site-address,name] for site,name in sorted(
        inventory.bind_calls(calls,mapping,address,len(data),len(rom)).items())],
        'data':[],'functions':[],'switches':[]}
    if branches or words or type(bindings) is not dict or bindings != expected:
        raise ValueError('native bridge requires exact canonical original ELF call offsets and no other binding roles')
    roles = NativeRoleProof(rom,mapping,index,objects,address,len(data),calls,bindings)
    frame.prove_frame(ins,edges,address,branches,calls,stack_aliases=True,
        mutable_stack_index_policy=finite.THREE_CALL_SELECTOR,consumer_scratch_proof=roles,
        native_three_call_policy=SELECTOR)
    discovered = roles.manifest()
    # Unchanged298 remains authoritative for every finite local/access/alias
    # guard and for all three complete contracts after authenticated discovery.
    checked,instructions = inventory.verify(data,address,rom,mapping,index,calls,
        {site:f'func_{target:08X}' for site,target in calls.items()},
        selector=inventory.THREE_CALL_SELECTOR,objects=objects,scratch_sites=discovered['sites'])
    observed = {'profile':SCHEMA,'selector':SELECTOR,'bindings':copy.deepcopy(bindings),
        'roles':discovered,'inventory':checked,'environment':environment_fingerprint(),
        'contract':CONTRACT,'arithmetic_or_memory_safety_theorem':False}
    if manifest is not None and owner.text(manifest) != owner.text(observed):
        raise ValueError('native bridge manifest differs from fresh source-bound replay')
    return observed,instructions
