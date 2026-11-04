"""Explicit inventory-only dispatch of three authenticated scratch contracts.

Every selected call has its own complete callee policy. No register is dropped
by name or by an ordinary ABI summary alone. Caller-local memory facts remain
owned by the mutable frame and unchanged by this composition.
"""
import copy
import hashlib
import json
from pathlib import Path

import consumer_scratch_alias_profile as consumer
import readonly_leaf_overwrite_profile as leaf
import incoming_scratch_overwrite_profile as ordinary

SELECTOR = 'mutable-four-local-word-three-call-v1'
SCHEMA = 'thumb-mutable-three-call-composition-v1'
ROLES = frozenset(('consumer_scratch', 'leaf_overwrite', 'ordinary_overwrite'))


def sha(value):
    return hashlib.sha256(value).hexdigest()


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


class ThreeCallCompositionProof:
    """Closed policies and disjoint original sites, bound to one whole caller."""
    def __init__(self, rom, mapping, index, objects, caller, size, calls, sites, *, policy):
        if type(policy) is not str or policy != SELECTOR:
            raise ValueError('three-call composition requires its explicit inventory policy')
        if type(sites) is not dict or set(sites) != ROLES or any(
                type(pair) not in (tuple, list) or len(pair) != 2 or
                any(type(value) is not int for value in pair) or
                calls.get(pair[0]) != pair[1] for pair in sites.values()) or \
                len({pair[0] for pair in sites.values()}) != 3:
            raise ValueError('three-call roles require three disjoint exact original BL bindings')
        self.sites = {role: list(pair) for role, pair in sites.items()}
        self.calls, self.caller, self.size = dict(calls), caller, size
        self.rom, self.mapping, self.index, self.objects = rom, mapping, index, objects
        self.proofs = {
            'consumer_scratch': consumer.ConsumerScratchAliasProof(
                rom, mapping, index, objects, caller, size, calls),
            'leaf_overwrite': leaf.ReadonlyLeafOverwriteProof(
                rom, mapping, index, objects, caller, size, calls),
            'ordinary_overwrite': ordinary.IncomingScratchOverwriteProof(
                rom, mapping, index, objects, caller, size, calls,
                {sites['ordinary_overwrite'][0]: sites['ordinary_overwrite'][1]},
                policy=ordinary.SELECTOR)}
        self.body = self.proofs['consumer_scratch'].body
        self.binding = self.identity()
        self.source_identity = self.source_pins()
        self.seen, self.observations = set(), {}

    def identity(self):
        return {'caller': self.caller, 'size': self.size,
            'calls': sorted(self.calls.items()), 'sites': copy.deepcopy(self.sites),
            **{name + '_sha256': sha(getattr(self, name))
               for name in ('rom', 'mapping', 'index', 'objects')}}

    def source_pins(self):
        import local_long_branch_profile as frame
        import mutable_stack_index_profile as finite
        import local_alias_slot_profile as slots
        modules = (consumer, leaf, ordinary, frame, finite, slots)
        return self.proofs['leaf_overwrite'].source_pins() | {
            Path(module.__file__).name: sha(Path(module.__file__).read_bytes())
            for module in modules} | {Path(__file__).name: sha(Path(__file__).read_bytes())}

    def fresh(self):
        if self.identity() != self.binding or self.source_pins() != self.source_identity:
            raise ValueError('three-call source, inputs or selected bindings changed')
        for role in ('consumer_scratch', 'leaf_overwrite'):
            proof = self.proofs[role]
            proof.fresh()
            if proof.identity() != self.proofs['consumer_scratch'].identity():
                raise ValueError('three-call leaf input identities changed')
        proof = self.proofs['ordinary_overwrite']
        if proof._identities() != proof.identities or proof.calls != self.calls or \
                (proof.caller, proof.size) != (self.caller, self.size) or \
                proof.sites != {self.sites['ordinary_overwrite'][0]: self.sites['ordinary_overwrite'][1]} or \
                any(getattr(proof, name) != getattr(self, name)
                    for name in ('rom', 'mapping', 'index', 'objects')) or \
                consumer.signature(proof.instructions, proof.edges) != self.proofs['consumer_scratch'].cfg:
            raise ValueError('three-call ordinary source or input bindings changed')

    def bind_frame(self, instructions, edges, address, branches, calls):
        self.fresh()
        for role in ('consumer_scratch', 'leaf_overwrite'):
            self.proofs[role].bind_frame(instructions, edges, address, branches, calls)
        self.proofs['ordinary_overwrite'].bind_caller(instructions, edges, address, calls)

    def check_call(self, site, target, aliases, stack, pointer_slots, initialized):
        self.fresh()
        selected = [role for role, pair in self.sites.items() if pair == [site, target]]
        if len(selected) != 1:
            raise ValueError('three-call composition refuses unselected alias calls')
        role = selected[0]
        # Mutable frame validates live allocated aliases before reaching this
        # dispatcher. Each original proof independently validates its contract.
        state = copy.deepcopy((aliases, stack, pointer_slots, initialized))
        proof = self.proofs[role]
        if role == 'ordinary_overwrite':
            proof.check_call(site, target, aliases, stack, pointer_slots, initialized)
        else:
            proof.check_call(site, target, aliases, pointer_slots)
        if state != (aliases, stack, pointer_slots, initialized):
            raise ValueError('three-call proof changed local alias, pointer-slot or initialized state')
        self.seen.add(role)
        key = text([role, site, sorted(initialized),
                    [[offset, sorted(values)] for offset, values in sorted(pointer_slots.items())]])
        self.observations[key] = {'role': role, 'site': site, 'target': target,
            'state_sha256': sha(repr(state).encode()), 'caller_local_state_unchanged': True}

    def manifest(self):
        self.fresh()
        if self.seen != ROLES:
            raise ValueError('three-call inventory requires all three actual certified call roles')
        return {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
            'source_or_ELF_admission': False, 'selected_sites': copy.deepcopy(self.sites),
            'caller_body_sha256': sha(self.body),
            'caller_CFG_sha256': sha(text(self.proofs['consumer_scratch'].cfg).encode()),
            'input_identity': self.binding, 'producer_source_sha256': self.source_identity,
            'contracts': {role: self.proofs[role].manifest() for role in sorted(ROLES)},
            'observations': [self.observations[key] for key in sorted(self.observations)],
            'ordinary_returning_ABI_conditional': True,
            'numeric_readability_effect_or_termination_theorem': False}
