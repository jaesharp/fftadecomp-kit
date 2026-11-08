"""Explicit conditional native admission for the closed local halfword matrix.

Compiler identity transport and the complete common-byte relation remain
separate checks. No RAM value, valid index, physical access or later permission
for the expired R3 stack pointer is inferred by this adapter.
"""
import hashlib
from pathlib import Path

import local_shadow_halfword_matrix as matrix
import local_shadow_matrix_elf_binding as binding

SELECTOR = 'local-shadow-halfword-matrix-v1'
SCHEMA = 'elf-symbol-thumb-local-shadow-halfword-matrix-v1'
CONTROL_FLOW = ('complete sixteen-byte local matrix initialization and actual word copy; '
    'conditional row below four and column below two, explicit RAM/frame access and '
    'separation, expired R3 frame pointer retained')


def original_bindings(image, address, rom, mapping, index, objects):
    plan = binding.image_binding_plan(image, address, rom, mapping, index, objects)
    targets = {name: (point if kind == 1 else point & ~1, kind == 1)
               for name, (point, kind) in plan['targets'].items()}
    return plan['bindings'], targets


def prove(data, address, rom, mapping, index, objects, *, bindings, source_fingerprint):
    matrix.require(type(source_fingerprint) is str and len(source_fingerprint) == 64 and
        all(c in '0123456789abcdef' for c in source_fingerprint), 'current source fingerprint required')
    effect = matrix.prove(data, address, rom, mapping, index, objects)
    expected = dict(calls=[[66, 'memcpy']], data=[[92, effect['shadow_identity'], 0]],
                    functions=[], switches=[])
    matrix.require(type(bindings) is dict and bindings == expected,
                   'exact genuine compiler memcpy and canonical data bindings required')
    effect.update(source_sha256=source_fingerprint, producer_sha256={
        Path(module.__file__).name: hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
        for module in (matrix, binding)},
        adapter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        original_ELF_and_source='fresh compiler original, strict typed zero-addend link and complete bytes are independently required by the native harness')
    return dict(schema=SCHEMA, instructions=45, calls=expected['calls'], runtime_calls=[],
                partition=effect['partition'], helper_partition=effect['helper_partition'],
                local_shadow_halfword_matrix=effect)
