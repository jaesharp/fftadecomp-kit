"""Explicit R6 constants through replayed ordinary frames and leaf R7 callbacks.

No ABI declaration grants preservation. Each ordinary call restores its entry
frame under certificates for all nested calls, and independently replays the
existing alias/effect checks. Callback certificates require complete no-call
owners leaving every callee-saved register unwritten. Normal return and the
existing ordinary memory/ABI boundary remain conditional.
"""
import hashlib
import importlib
import json
from pathlib import Path

import match
import owner_graph_profile as graph
import local_long_branch_profile as frame
import static_callback_target_preservation_profile as r7

SELECTOR = 'static-callback-restoring-r6-v1'
SCHEMA = 'elf-symbol-thumb-static-callback-restoring-r6-v1'
CONTROL_FLOW = 'complete ordinary frames with authenticated R6 restoration and bounded leaf R7 callbacks'
MAX_DEPENDENCIES = r7.MAX_DEPENDENCIES
REGISTER = match.ARM_REG_R0 + 6
PRESERVED = frozenset(range(match.ARM_REG_R0 + 4, match.ARM_REG_R0 + 12))
REPLAY_GUARD = match.ARM_REG_R0 + 11


def policy_manifest():
    modules = ('static_callback_r6_frame_profile', 'static_callback_target_preservation_profile',
               'static_callback_buffer_profile', 'named_data_buffer_profile',
               'local_long_branch_profile', 'owner_graph_profile', 'owner_admission_profile',
               'function_thunk_profile', 'analyze', 'inert_spin_profile', 'match')
    return dict(schema='thumb-static-callback-restoring-r6-policy-v1', selector=SELECTOR,
        register=6, callbacks='exact canonical R7, complete leaf, R4-R11 and SP unwritten',
        ordinary_calls='complete existing restoring frame with exact completed nested call certificates',
        replay='fresh existing buffer alias/effect replay; R11 unwritten guard',
        attestation='same proof instance, result identity and aliases, site, target and incoming R6; once',
        returning='conditional compatible normal return only', descriptor_words=False,
        source_sha256={name+'.py': hashlib.sha256(Path(importlib.import_module(name).__file__).read_bytes()).hexdigest()
                       for name in modules})


class _Result(dict):
    pass


class R6FrameCallbackProof(r7.StaticCallbackTargetPreservationProof):
    def __init__(self, rom, mapping, index, objects, *, policy):
        if policy != SELECTOR:
            raise ValueError('R6 restoration requires its exact explicit policy')
        super().__init__(rom, mapping, index, objects, policy=r7.SELECTOR)
        self._frames = []
        self._structure_only = False
        self._restorations = {}
        self._ordinary_completed = {}
        self._leaf_completed = {}

    def inspect(self, address, data):
        # The inherited preliminary instruction check has no entry constants.
        # Keep its existing checks, then replay effects with the real context in
        # check_arguments. Only the new unconditional-call hook is suspended.
        previous = self._structure_only
        self._structure_only = True
        try:
            return super().inspect(address, data)
        finally:
            self._structure_only = previous

    def _graph(self, address):
        import owner_admission_profile as owner
        data = self.span(address)
        refinement = owner.refine(data, address, self.mapping)
        ins, edges, branches, calls, words = graph.graph(data, address, refinement)
        if branches or words:
            raise ValueError('R6 restoration excludes local long branches and switches')
        partition = graph.partition(data, address, refinement, ins, words)
        return data, ins, edges, calls, partition

    def _leaf(self, value):
        if type(value) is not int or value % 2 != 1:
            raise ValueError('R7 callback requires an exact odd Thumb target')
        address = match.function_address_target(f'func_{value & ~1:08X}', self.entries,
                                               r7.THUNK, 2, len(self.rom))
        data, ins, edges, calls, partition = self._graph(address)
        if calls:
            raise ValueError('R6 restoration requires a complete no-call callback')
        for instruction in ins.values():
            _, written = instruction.regs_access()
            if set(written) & (PRESERVED | {match.ARM_REG_SP}):
                raise ValueError('callback writes a required unwritten register or SP')
        certificate = frame.prove_frame(ins, edges, address, {}, {}, call_preservation={})
        return dict(address=address, body_sha256=hashlib.sha256(data).hexdigest(),
                    partition=partition, frame=certificate)

    def check_arguments(self, address, arguments, stack, incoming, protected, *,
                        constants=None, site=None, **context):
        if type(site) is not int or context.get('words'):
            raise ValueError('R6 restoration requires exact sites without descriptor words')
        facts = dict(constants or {})
        context = dict(words={}, frame_base=context.get('frame_base'),
                       root_frame=context.get('root_frame'), **{key: value for key, value in context.items()
                       if key not in ('words', 'frame_base', 'root_frame')})
        if address == r7.THUNK:
            if not self._frames:
                raise ValueError('R6 callback certificate requires an active ordinary caller')
            certificate = self._leaf(facts.get(r7.REGISTER))
            watched = tuple(sorted(set(context.get('watched', ())) | PRESERVED))
            result = super().check_arguments(address, arguments, stack, incoming, protected,
                constants=facts, site=site, **dict(context, watched=watched))
            self._leaf_completed[id(result)] = (result, tuple(sorted(result.items())),
                                                site, certificate)
            return result
        # The extra unwritten watch forces complete effect replay even for a
        # no-buffer call; it does not infer callee-saved restoration itself.
        watched = tuple(sorted(set(context.get('watched', ())) | {REPLAY_GUARD}))
        active = dict(address=address, calls={})
        self._frames.append(active)
        try:
            aliases = super().check_arguments(address, arguments, stack, incoming, protected,
                constants=facts, site=site, **dict(context, watched=watched))
            data, ins, edges, calls, partition = self._graph(address)
            if calls != {call_site: row['target'] for call_site, row in active['calls'].items()}:
                raise ValueError('ordinary frame has an unbound or incomplete nested call certificate')
            # Every nested site has independently completed its effects and a
            # frame or no-write callback proof. No arbitrary preserved set enters.
            certificate = frame.prove_frame(ins, edges, address, {}, calls,
                call_preservation={call_site: PRESERVED for call_site in calls})
            receipt = dict(site=site, target=address, value=facts.get(REGISTER),
                body_sha256=hashlib.sha256(data).hexdigest(), partition=partition,
                frame=certificate, calls=[dict(site=key, **active['calls'][key])
                                         for key in sorted(active['calls'])])
            result = _Result(aliases)
            self._ordinary_completed[id(result)] = (result, tuple(sorted(result.items())), receipt)
            return result
        finally:
            self._frames.pop()

    def finish_call_constants(self, constants, result, *, site=None, target=None):
        if self._structure_only:
            return super().finish_call_constants(constants, result, site=site, target=target)
        incoming = dict(constants)
        ordinary = self._ordinary_completed.pop(id(result), None)
        leaf = self._leaf_completed.pop(id(result), None)
        super().finish_call_constants(constants, result, site=site, target=target)
        if leaf is not None:
            original, aliases, call_site, certificate = leaf
            if original is not result or aliases != tuple(sorted(result.items())) or \
                    site != call_site or target != r7.THUNK or not self._frames:
                raise ValueError('callback frame certificate differs from completed call')
            self._record_call(site, target, certificate)
        elif ordinary is not None:
            original, aliases, receipt = ordinary
            if original is not result or aliases != tuple(sorted(result.items())) or \
                    receipt['site'] != site or receipt['target'] != target or \
                    incoming.get(REGISTER) != receipt['value']:
                raise ValueError('R6 frame attestation differs from completed call')
            value = receipt['value']
            if value is not None:
                # Only actual mapped Thumb callback identities are retained.
                if type(value) is not int or value % 2 != 1:
                    raise ValueError('preserved R6 is not a typed Thumb callback identity')
                match.function_address_target(f'func_{value & ~1:08X}', self.entries,
                                              target, len(self.span(target)), len(self.rom))
                constants[REGISTER] = value
            key = json.dumps(receipt, sort_keys=True, separators=(',', ':'))
            self._restorations[key] = receipt
            if self._frames:
                self._record_call(site, target, receipt)
        elif self._frames:
            raise ValueError('nested call lacks its exact completed preservation certificate')

    def _record_call(self, site, target, certificate):
        row = dict(target=target, certificate=certificate)
        calls = self._frames[-1]['calls']
        if site in calls and calls[site] != row:
            raise ValueError('nested call preservation context changed within one ordinary replay')
        calls[site] = row

    def restoration_observations(self):
        return [self._restorations[key] for key in sorted(self._restorations)]


def requires_replay(proof):
    # Closed native type hook. Existing defaults and arbitrary subclasses do
    # not acquire the all-ordinary-call replay or constant-restoration policy.
    return type(proof) is R6FrameCallbackProof and not proof._structure_only
