"""Explicit resident two-local-output frame with conditional R0 word return.

This is a source/ELF-bound admission policy, not a claim about arbitrary
callers, physical memory, termination or nominal C function-type identity.
"""
import hashlib
import json
from pathlib import Path

import match
import owner_graph_profile as graph
import callback_local_two_output_frame as local
import descriptor_output_alias_profile as frame
import protected_descriptor_word_profile as descriptor
import word_result_return_scratch as terminal

SELECTOR = 'standalone-local-output-word-return-v1'
SCHEMA = 'elf-symbol-thumb-standalone-local-output-word-return-v1'
CONTROL_FLOW = 'complete resident two-word output frame; explicit normal R0-word ABI and exact expired R2 scratch projection'
MAX_BYTES = 64


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def _closed_returns(instructions, edges, returns, call_site, address):
    """Every finite root path executes the one helper before normal return."""
    completed = set()

    def visit(site, called, active):
        state = (site, called)
        if state in completed:
            return
        if site in active:
            raise ValueError('resident output frame excludes unclosed cycles')
        called |= site == call_site
        if site in returns:
            if not called:
                raise ValueError('resident return bypasses the actual output helper')
        else:
            if not edges[site]:
                raise ValueError('resident path lacks an authenticated normal return')
            for target in edges[site]:
                visit(target, called, active | {site})
        completed.add(state)

    visit(address, False, set())
    return sorted(returns)


class ResidentWordProof(local.CallbackLocalTwoOutputProof):
    """Reuse277 effect and restoring-frame engines from a real empty entry SP."""

    def __init__(self, rom, mapping, index, objects, *, root, bindings, source_fingerprint):
        import owner_admission_profile as owner
        if type(source_fingerprint) is not str or len(source_fingerprint) != 64 or \
                any(value not in '0123456789abcdef' for value in source_fingerprint):
            raise ValueError('resident word return requires current source/header fingerprint')
        spans = frame.DescriptorOutputAliasProof(rom, mapping, index, objects)
        data = spans.span(root)
        if not 0 < len(data) <= MAX_BYTES:
            raise ValueError('resident output owner exceeds the closed byte budget')
        refinement = owner.refine(data, root, mapping)
        instructions, edges, branches, calls, words = graph.graph(data, root, refinement)
        partition = graph.partition(data, root, refinement, instructions, words)
        if branches or words or partition['words'] or len(calls) != 1:
            raise ValueError('resident output requires one direct helper and no pools/switches/local calls')
        call_site, helper = next(iter(calls.items()))
        if type(bindings) is not dict or set(bindings) != {'calls','data','functions','switches'} or \
                bindings != dict(calls=[[call_site-root,f'func_{helper:08X}']],
                                 data=[],functions=[],switches=[]):
            raise ValueError('resident output requires its one original typed helper binding')
        spans.target(helper)
        returns = {int(site, 16) for site in refinement['returns']}
        if not returns:
            raise ValueError('resident output requires a complete normal return')
        self.return_sites = _closed_returns(instructions, edges, returns, call_site, root)
        policy = dict(schema=local.SCHEMA, callback=root, helper=helper,
            call_site=call_site, local_bytes=8, callback_sha256=sha(data),
            helper_sha256=sha(spans.span(helper)))
        inputs = (rom,mapping,index,objects)
        policy.update({name+'_sha256':sha(value) for name,value in
                       zip(('rom','mapping','index','objects'), inputs)})
        super().__init__(*inputs, policy=policy)
        self.source_fingerprint = source_fingerprint
        self.bindings = json.loads(json.dumps(bindings))
        self._resident_active = False
        self.projections = []

    def resident_effect_replay(self, address):
        return self._resident_active and address == self.callback

    word_context = descriptor.ProtectedDescriptorWordProof.word_context

    def _helper_instructions(self):
        data = super()._helper_instructions()
        self.records[self.helper] = dict(address=self.helper,end=self.helper+len(data),
            bytes=len(data),body_sha256=sha(data),**self.identities,
            structure={'kind':'exact-ordered-two-local-output-helper-v1'})
        return data

    def normal_return_aliases(self, address, site, aliases):
        if not self._resident_active or self._context != (0,0,None) or \
                address != self.callback or site not in self.return_sites:
            raise ValueError('resident projection lacks its exact active normal-return boundary')
        if match.ARM_REG_R0 in aliases:
            raise ValueError('resident R0 word result carries a local stack address')
        r2 = match.ARM_REG_R2
        if r2 not in aliases:
            return aliases
        if aliases[r2] != -16 or any(register != r2 and value == -16
                                     for register,value in aliases.items()):
            raise ValueError('resident scratch is not the unique second-output R2 alias')
        result = dict(aliases)
        del result[r2]
        self.projections.append(dict(site=site,register='R2',expired_local_offset=-16,
                                     abi=terminal.ABI,R0_projected=False))
        return result

    def replay(self):
        if self._resident_active or self._context is not None:
            raise ValueError('resident entry cannot be nested or recursively replayed')
        self._resident_active = True
        # No invented caller frame or pointer argument is introduced. The R1
        # incoming external context remains an ordinary unknown pointer value.
        self._context = (0,0,None)
        try:
            result = match.BufferCallProof.check_arguments(self,self.callback,
                {},[],{},frozenset(),constants={},words={},frame_base=0,
                root_frame=self.callback,watched=())
            if result:
                raise ValueError('resident normal return retains a local alias')
            self.completed = True
        finally:
            self._context = None
            self._resident_active = False
        if not self.projections or not self.effect_rows or not self.output_reads:
            raise ValueError('resident word policy lacks actual local helper/read/projection effects')

    def effect_manifest(self):
        effects = super().manifest()
        return dict(schema=SCHEMA,abi=terminal.ABI,
            normal_result='R0 single word; numeric result unknown',
            source_sha256=self.source_fingerprint,bindings=self.bindings,
            entry={'stack':[],'local_aliases':[],'incoming_stack_arguments':[]},
            return_sites=self.return_sites,projections=self.projections,
            local_effects=effects,
            producer_sha256={name:sha((Path(match.__file__).parent/name).read_bytes()) for name in
                ('standalone_local_output_word_profile.py','callback_local_two_output_frame.py',
                 'word_result_return_scratch.py')},
            claims_excluded=['physical memory','termination','nominal C function-type equivalence',
                             'arbitrary caller physical register overwrites'])


def prove(data,address,rom,mapping,index,objects,*,bindings,source_fingerprint):
    import owner_admission_profile as owner
    proof = ResidentWordProof(rom,mapping,index,objects,root=address,
        bindings=bindings,source_fingerprint=source_fingerprint)
    if data != proof.span(address):
        raise ValueError('resident compiled body differs from its complete mapped owner')
    proof.replay()
    refinement = owner.refine(data,address,mapping)
    instructions,_,_,calls,words = graph.graph(data,address,refinement)
    return dict(schema=SCHEMA,instructions=len(instructions),
        calls=[[site-address,f'func_{target:08X}'] for site,target in sorted(calls.items())],
        runtime_calls=[],partition=graph.partition(data,address,refinement,instructions,words),
        standalone_word_return=proof.effect_manifest())
