"""Original ELF bridge for canonical integer calls and two incoming ABI words.

The existing inventory supplies all structural runtime and frame checks. Its
explicit readable incoming-word contract remains conditional; named object
points grant no memory contents, bounds, accessibility or physical separation.
"""
import copy
import hashlib
import json
from pathlib import Path
import struct

import canonical_integer_native_profile as scalar_native
import canonical_integer_entry_words_inventory as inventory

SELECTOR = 'canonical-integer-two-words-data-source-v1'
SCHEMA = 'elf-symbol-thumb-canonical-integer-two-words-data-source-v1'
CONTROL_FLOW = 'complete original ELF-bound integer calls, named object points and restoring scalar frame with two conditional read-only incoming ABI words'


def environment_fingerprint():
    result = scalar_native.environment_fingerprint()
    result['two_words_producers'] = {Path(module.__file__).name:
        hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
        for module in (inventory, inventory.entry)}
    result['two_words_producers'][Path(__file__).name] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def verify_original(original, linked, address, rom, mapping, index, bindings, manifest=None, *, objects):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    if type(address) is not int or any(type(value) is not bytes
            for value in (original, linked, rom, mapping, index, objects)):
        raise ValueError('two-word integer bridge requires immutable original inputs')
    before = environment_fingerprint()
    image, output = match.elf_image(original), match.elf_image(linked)
    actual, targets = owner.original_bindings(image, address, rom, mapping, objects,
                                               selector=SELECTOR, index=index)
    if type(bindings) is not dict or bindings != actual or any(actual[role] for role in ('functions', 'switches')):
        raise ValueError('two-word integer bindings differ from original call/object roles')
    if any(symbol['size'] for symbol in image['symbols'] if symbol['name'] in targets and not symbol['section']):
        raise ValueError('two-word integer original undefined symbols require zero size')
    match.allocated_text_only(output)
    name = f'func_{address:08X}'
    root, offset = match.function_record(output, name, address, True)
    source, _ = match.function_record(image, name, address, True)
    if output['type'] != 2 or output['relocations'] or offset or root['size'] != source['size'] or \
            len(output['text']) != len(image['text']) or any(
                symbol['name'] and not symbol['section'] for symbol in output['symbols']):
        raise ValueError('two-word integer typed link changes complete owner or leaves undefined symbols')
    for key, (value, is_object) in targets.items():
        found = [symbol for symbol in output['symbols'] if symbol['name'] == key]
        if len(found) != 1 or found[0]['section'] != 0xfff1 or found[0]['bind'] != 1 or \
                found[0]['size'] or found[0]['type'] != (1 if is_object else 2) or \
                found[0]['value'] != (value if is_object else value | 1):
            raise ValueError('two-word integer link requires exact unique typed absolute definitions')
    if any(symbol['name'] not in set(targets) | {name} and symbol['type'] in (1, 2) and symbol['section']
           for symbol in output['symbols']):
        raise ValueError('two-word integer link adds an unowned function or object')
    expected = bytearray(image['text'])
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    for site, key in actual['calls']:
        item = next(decoder.disasm(output['text'][site:site+4], address+site), None)
        if item is None or item.id != match.ARM_INS_BL or item.size != 4 or item.operands[0].imm != targets[key][0]:
            raise ValueError('two-word integer linked call differs from original identity')
        expected[site:site+4] = output['text'][site:site+4]
    for site, key, addend in actual['data']:
        if addend:
            raise ValueError('two-word integer named objects require zero addends')
        struct.pack_into('<I', expected, site, targets[key][0])
    if bytes(expected) != output['text']:
        raise ValueError('two-word integer link changes bytes outside original relocation roles')
    data = output['text'][:root['size']]
    refinement = owner.refine(data, address, mapping)
    ins, _, _, calls, words = graph.graph(data, address, refinement)
    partition = graph.partition(data, address, refinement, ins, words)
    for site, key, _ in actual['data']:
        value = targets[key][0]
        word = next((row for row in partition['words'] if row['address'] == address+site), None)
        if word is None or (address+site) % 4 or not word['load_sites'] or word['switch_word'] or \
                word['value'] != value or not 0x02000000 <= value < 0x09000000 or any(
                    (value & ~1) == int(row['rom'], 16) for row in json.loads(mapping)):
            raise ValueError('two-word integer objects require actual referenced non-code point literals')
    expected_calls = {address+site: key for site, key in actual['calls']}
    if expected_calls != inventory.bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('two-word integer CFG differs from original compiler call identities')
    checked, instructions = inventory.verify(data, address, rom, mapping, index, calls, expected_calls,
        selector=inventory.SELECTOR, entry_stack_policy={'schema': inventory.entry.SCHEMA, 'words': list(range(2))})
    if before != environment_fingerprint():
        raise ValueError('two-word integer producers, runtime or toolchain changed')
    result = dict(profile=SCHEMA, selector=SELECTOR, bindings=copy.deepcopy(actual), prerequisite=checked,
        environment=before, original_ET_REL_sha256=hashlib.sha256(original).hexdigest(),
        linked_ELF_sha256=hashlib.sha256(linked).hexdigest(), objects_sha256=hashlib.sha256(objects).hexdigest(),
        contract='Two incoming readable aligned ABI words are explicit premises with unknown contents; '
        'all two need actual reached reads. Canonical runtime structural closure includes real zero hooks. '
        'Named object points grant no memory permissions, bounds or initialized values. Ordinary calls '
        'remain returning ABI boundaries. No numeric result, arithmetic C-equivalence, physical memory '
        'separation, memory safety, alias escape or termination theorem is inferred.')
    if manifest is not None and owner.text(manifest) != owner.text(result):
        raise ValueError('two-word integer source manifest differs from fresh original replay')
    return result, len(instructions)
