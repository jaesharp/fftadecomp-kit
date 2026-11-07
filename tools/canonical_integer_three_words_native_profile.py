"""Original ELF bridge with three conditional read-only incoming ABI words.

The existing entry-word inventory supplies every runtime, CFG and frame check.
Readability of three incoming words remains an explicit unknown-value premise.
"""
import copy
import hashlib
from pathlib import Path

import canonical_integer_native_profile as scalar_native
import canonical_integer_entry_words_inventory as inventory

SELECTOR = 'canonical-integer-three-words-source-v1'
SCHEMA = 'elf-symbol-thumb-canonical-integer-three-words-source-v1'
CONTROL_FLOW = ('complete original ELF-bound canonical integer calls and restoring scalar '
                'frame with three conditional read-only incoming ABI words')


def environment_fingerprint():
    result = scalar_native.environment_fingerprint()
    result['three_words_producers'] = {
        Path(module.__file__).name: hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
        for module in (inventory, inventory.entry)}
    result['three_words_producers'][Path(__file__).name] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def verify_original(original, linked, address, rom, mapping, index, bindings, manifest=None):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    if type(address) is not int or any(type(value) is not bytes
            for value in (original, linked, rom, mapping, index)):
        raise ValueError('three-word integer bridge requires immutable original inputs')
    before = environment_fingerprint()
    image = match.elf_image(original)
    actual, targets = owner.original_bindings(image, address, rom, mapping, b'{}',
                                             selector=scalar_native.SELECTOR, index=index)
    if type(bindings) is not dict or bindings != actual or any(
            actual[role] for role in ('data', 'functions', 'switches')):
        raise ValueError('three-word integer bindings differ from original call-only ELF roles')
    if any(symbol['size'] for symbol in image['symbols']
           if symbol['name'] in targets and not symbol['section']):
        raise ValueError('three-word integer calls require zero-sized original undefined functions')
    data = scalar_native.linked_bytes(image, match.elf_image(linked), address, actual, targets)
    _, _, _, calls, _ = graph.graph(data, address, owner.refine(data, address, mapping))
    expected = {address+at: name for at, name in actual['calls']}
    if expected != inventory.bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('three-word integer actual CFG differs from original compiler identities')
    checked, instructions = inventory.verify(data, address, rom, mapping, index, calls, expected,
        selector=inventory.SELECTOR,
        entry_stack_policy={'schema': inventory.entry.SCHEMA, 'words': [0, 1, 2]})
    if before != environment_fingerprint():
        raise ValueError('three-word integer producers, runtime or toolchain changed')
    result = dict(profile=SCHEMA, selector=SELECTOR, bindings=copy.deepcopy(actual),
        prerequisite=checked, environment=before,
        original_ET_REL_sha256=hashlib.sha256(original).hexdigest(),
        linked_ELF_sha256=hashlib.sha256(linked).hexdigest(),
        contract='Three readable aligned incoming ABI words are explicit premises with unknown '
        'contents; every declared word requires an actual reached read. No incoming stores, '
        'SP addresses, local aliases or extra words are permitted. Genuine compiler identities '
        'and all original ELF bytes are authenticated. Existing canonical runtime closure '
        'includes real zero-hook paths. Ordinary callees remain conditional returning ABI '
        'boundaries. No numeric result, arithmetic C-equivalence, caller allocation, physical '
        'memory separation, memory safety, escape or termination theorem is inferred.')
    if manifest is not None and owner.text(manifest) != owner.text(result):
        raise ValueError('three-word integer source manifest differs from fresh original replay')
    return result, len(instructions)
