"""Explicit inventory composition of existing ignored-leaf overwrite evidence.

The existing complete-leaf per-register overwrite proof remains authoritative.
The exact286 decoder allows only read-only scalar LDRSH in addition to that
closed leaf subset. Caller-local pointer slots and byte initializedness are
retained by the existing mutable frame, not supplied as absent to another API.
No caller-continuation projection or address/register-name whitelist is used.
"""
from pathlib import Path

import ignored_leaf_alias_profile as ignored
from consumer_scratch_alias_profile import ConsumerScratchAliasProof, text

SELECTOR = 'mutable-four-local-word-alias-slot-halfword-scalar-slot-leaf-overwrite-v1'
SCHEMA = 'thumb-readonly-ignored-leaf-overwrite-slots-v1'


class ReadonlyLeafOverwriteProof(ConsumerScratchAliasProof):
    """Authenticate one whole caller and reuse the old leaf overwrite policy."""

    def source_pins(self):
        return super().source_pins() | {Path(__file__).name: ignored.sha(Path(__file__).read_bytes())}

    def check_call(self, site, target, aliases, pointer_slots):
        import match
        import mutable_stack_index_profile as finite
        self.fresh()
        if self.calls.get(site) != target:
            raise ValueError('readonly overwrite requires an exact original caller BL binding')
        registers = sorted(set(aliases) & set(match.CALLER_CLOBBERED))
        if not registers:
            raise ValueError('readonly overwrite requires an actual incoming scratch alias')
        for register in registers:
            finite.offsets(aliases[register])
        slots = [[offset, [list(value) for value in sorted(values)]]
                 for offset, values in sorted(pointer_slots.items())]
        # This is the existing overwrite walk, extracted without changing its
        # checks. The closed inherited decoder cannot write caller-local bytes.
        # No empty pointer-slot state is invented or passed to an existing API.
        ignored.IgnoredLeafAliasProof.prove_incoming_overwrite(self, site, target, aliases)
        if slots != [[offset, [list(value) for value in sorted(values)]]
                     for offset, values in sorted(pointer_slots.items())]:
            raise ValueError('readonly overwrite proof changed possible local pointer taint')
        key = (site, text({str(r): sorted(values) for r, values in aliases.items()}), text(slots))
        self.checked[key] = {'callsite': site, 'target': target,
            'registers': [self.instructions[site].reg_name(register) for register in registers],
            'callee': self.dependencies[target],
            'overwrite_policy': ignored.LEAF_SCHEMA,
            'all_incoming_aliases_overwritten_before_read_on_every_callee_return': True,
            'caller_local_memory_writes': False, 'preserved_pointer_slots': slots,
            'caller_continuation_projection': False}
        return {}

    def manifest(self):
        observed = super().manifest()
        observed.update(schema=SCHEMA, selector=SELECTOR,
            contract='existing complete read-only leaf overwrite-before-use policy; retain every caller-local pointer slot and byte fact')
        return observed
