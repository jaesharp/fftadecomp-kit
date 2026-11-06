"""Direct halfword outputs through R3 and an initialized outgoing pointer word."""
import hashlib
from pathlib import Path

import match
import named_data_buffer_profile as named
import formal_entry_word_halfword_effects as effects
import nested_formal_output_buffer_profile as nested

SELECTOR = 'bounded-buffer-direct-halfword-output-v1'
SCHEMA = 'elf-symbol-thumb-bounded-buffer-direct-halfword-output-v1'
CONTROL_FLOW = 'complete Thumb owner with bounded direct halfword outputs and exact return entry aliases'
MAX_DEPENDENCIES = nested.MAX_DEPENDENCIES
LEAF = nested.LEAF


class DirectOutputBufferProof(nested.NestedOutputBufferProof):
    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self._root = None
        self._root_scratch = set()

    def bind_root(self, address, data):
        if self._root is not None or self.span(address) != data:
            raise ValueError('direct output root requires its exact unique complete body')
        import owner_admission_profile as owner
        refinement = owner.refine(data, address, self.mapping)
        instructions, edges, branches, calls, words = nested.graph.graph(data, address, refinement)
        if branches or words:
            raise ValueError('direct output root excludes local BL and word switches')
        self._root = (address, data, frozenset(site for site in edges if not edges[site]))

    def _prove(self):
        if self._native is not None:
            return self._native
        raw, instructions, edges, calls, partition = self._body(LEAF)
        if calls or len(instructions) != 51 or any(
                match.ARM_REG_R12 in item.regs_access()[1] for item in instructions.values()):
            raise ValueError('direct outputs require the complete call-free leaf with unwritten R12')
        proof = effects.prove_origins(instructions, edges, LEAF[0], raw, partition,
                                     self.objects, effects.named_policy())
        if [row[1:] for row in proof['formal_writes']] != [
                [['formal', 3], 0, 2], [['incoming', 0], 0, 2]] or \
                proof['return_entry_origins'] != [[3, 8]]:
            raise ValueError('direct output leaf effects or return origins differ')
        record = dict(address=LEAF[0], end=LEAF[0] + len(raw), bytes=len(raw),
            body_sha256=hashlib.sha256(raw).hexdigest(), structure=dict(
                kind=effects.SCHEMA, instructions=len(instructions),
                partition=partition, effects=proof), **self.identities)
        self.dependencies[LEAF[0]] = raw
        self.records[LEAF[0]] = record
        self._native = dict(leaf=record, unwritten_registers=[12],
            producer_sha256={Path(module.__file__).name:
                hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                for module in (effects, nested, __import__(__name__))})
        return self._native

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if address != LEAF[0]:
            return named.DiscardedReturnScratchProof.check_call(self, address, aliases, stack, slots,
                                     constants=constants, site=site, words=words)
        proof = self._prove()
        r0 = match.ARM_REG_R0
        call_sp = -4 * len(stack)
        if type(site) is not int or site % 2 or words or \
                any(register in aliases for register in (r0, r0+1, r0+2, match.ARM_REG_LR)) or \
                r0+3 not in aliases or type(slots) is not dict or set(slots) != {call_sp}:
            raise ValueError('direct output caller requires local R3 and one initialized outgoing pointer word0')
        self.access(call_sp, 4, stack)
        writes = [[aliases[r0+3], 2], [slots[call_sp], 2]]
        for offset, width in writes:
            self.access(offset, width, stack)
            if offset < call_sp + 4 and offset + width > call_sp:
                raise ValueError('direct outputs cannot overwrite their live outgoing pointer word')
        result = {}
        origins = proof['leaf']['structure']['effects']['return_entry_origins'] + [[12, 12]]
        for destination, source in origins:
            if r0 + source in aliases:
                offset = aliases[r0 + source]
                self.validate_pointer_value(offset, stack)
                result[r0 + destination] = offset
        self._calls.append(dict(site=site, target=address, call_entry_SP_offset=call_sp,
            outgoing_pointer_word=[call_sp, slots[call_sp]],
            writes_entry_SP_offsets=writes,
            return_aliases=[[n-r0, offset] for n, offset in sorted(result.items())],
            helper_frames='fresh saved/local words below actual callSP; outputs in live caller locals',
            physical_nonalias_claim=False))
        return result

    def direct_manifest(self):
        if not self._calls or self._native is None:
            raise ValueError('direct output profile requires an actual bounded caller composition')
        import local_long_branch_profile as frame
        root = None if self._root is None else dict(address=self._root[0],
            body_sha256=hashlib.sha256(self._root[1]).hexdigest(),
            schema=frame.DISCARDED_SCRATCH_SCHEMA, registers=[2, 3],
            contract=frame.DISCARDED_SCRATCH_CONTRACT,
            observations=[list(row) for row in sorted(self._root_scratch)],
            limits='Only exact root normal returns; R0/R1 and nested returns retain escape checks')
        return dict(schema=SCHEMA, native_helpers=self._native, calls=self._calls,
                    root_return_scratch=root, named_read_policy=effects.named_policy(),
                    physical_nonalias_claim=False)


def root_return_aliases(proof, data, address, site, aliases):
    """Apply the existing explicit R2/R3 ABI boundary only at this bound root."""
    if type(proof) is not DirectOutputBufferProof:
        return aliases
    if proof._root is None or proof.active:
        raise ValueError('direct output scratch requires its bound inactive root')
    root, body, returns = proof._root
    if address != root or data != body or site not in returns:
        raise ValueError('direct output scratch differs from its exact normal root return')
    scratch = {match.ARM_REG_R0+2, match.ARM_REG_R0+3}
    proof._root_scratch.update((site, register-match.ARM_REG_R0, offset)
        for register, offset in aliases.items() if register in scratch)
    return {register:offset for register,offset in aliases.items() if register not in scratch}
