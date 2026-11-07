"""Transport a frozen conditional closure to freshly compiled typed ELF.

The native caller must separately establish that the live original object was
produced from the supplied source with the fixed compiler. This pure byte API
retains that obligation and grants no physical permission or unconditional C
admission. Nonallocated debug/file metadata can differ; allocated code, sized
Thumb ownership, every original relocation and typed linked binding cannot.
"""
import json
import re
import struct
from pathlib import Path

import match
import palette_certificate_authority as authority
import palette_native_closure as closure
import software_double_profile as spans

SELECTOR = 'conditional-palette-original-transport-v1'
SCHEMA = 'elf-symbol-thumb-conditional-palette-original-transport-v1'


def image(raw, address, size, kind):
    result = match.elf_image(raw)
    match.allocated_text_only(result)
    symbol, offset = match.function_record(result, f'func_{address:08X}', address, True)
    closure.require(result['type'] == kind and offset == 0 and symbol['bind'] == 1 and
                    symbol['size'] == size == len(result['text']) and
                    (kind != 2 or symbol['value'] == address | 1),
                    'complete original/linked sized Thumb ownership differs')
    closure.require(not any(re.fullmatch(r'\$a(?:\..*)?', row['name']) or
                    row['type'] in (1, 2) and row['section'] not in (0, 0xfff1) and row is not symbol
                    for row in result['symbols']), 'foreign allocated symbol or ARM mapping')
    return result


def relocations(value, size):
    records, occupied = [], set()
    for number in value['relocations']:
        section = value['sections'][number]
        closure.require(section[1] == 9 and section[7] == value['text_index'] and
                        section[9] == 8 and section[5] % 8 == 0,
                        'canonical text REL table required')
        symbols = value['symbol_tables'].get(section[6]); raw = value['section_data'][number]
        closure.require(symbols is not None and len(raw) == section[5], 'REL symbols or extent differ')
        for position in range(0, len(raw), 8):
            site, info = struct.unpack_from('<II', raw, position); kind, index = info & 255, info >> 8
            closure.require(index < len(symbols) and kind in (2, 10) and site % 2 == 0 and
                            site + 4 <= size and not occupied.intersection(range(site, site+4)),
                            'invalid or overlapping original relocation')
            occupied.update(range(site, site+4)); symbol = symbols[index]
            closure.require(symbol == closure.unique_symbol(value, symbol['name']) and
                            symbol['section'] == 0 and symbol['bind'] == 1 and
                            symbol['value'] == symbol['size'] == 0 and
                            symbol['type'] in ((0, 2) if kind == 10 else (0, 1)),
                            'genuine unique zero-valued original symbol required')
            records.append((site, kind, symbol['name'], symbol['type']))
    names = {row[2] for row in records}
    closure.require(not any(row['name'] and row['section'] == 0 and row['name'] not in names
                            for row in value['symbols']), 'extra unresolved original symbol')
    closure.require(not any(row['type'] in (1, 2) and row['section'] == 0xfff1
                            for row in value['symbols']), 'extra original absolute typed symbol')
    return sorted(records)


def verify_original(original, linked, address, rom, mapping, index, objects, source,
                    bundle, *, selector, manifest=None):
    closure.require(type(selector) is str and selector == SELECTOR and type(address) is int and
                    all(type(raw) is bytes for raw in (original, linked, rom, mapping, index, objects, source, bundle)),
                    'explicit palette transport selector and immutable inputs required')
    artifacts = authority.decode(bundle)
    prior = json.loads(artifacts['closure'], object_pairs_hook=closure.unique)
    before = closure.environment_fingerprint()
    closure.require(prior['address'] == address and prior['source_sha256'] == closure.sha(source) and
                    prior['ROM_sha256'] == closure.sha(rom) and
                    prior['conditional_full_owner_closure'] is True and
                    all(prior[key] is False for key in ('native_admission', 'source_or_ELF_admission',
                                                       'physical_memory_permission', 'unconditional_termination')),
                    'frozen conditional source/owner/ROM premise differs')
    closure.require(before['toolchain'][0][1] == prior['environment']['toolchain'][0][1],
                    'fixed compiler differs from authenticated source lineage')
    size = prior['end'] - address
    old = image(artifacts['original'], address, size, 1)
    old_linked = image(artifacts['linked'], address, size, 2)
    live = image(original, address, size, 1); live_linked = image(linked, address, size, 2)
    closure.require(old['text'] == live['text'] and relocations(old, size) == relocations(live, size),
                    'fresh compiler text or every original relocation differs')
    body = rom[address-match.ROM_BASE:address-match.ROM_BASE+size]
    closure.require(live_linked['text'] == old_linked['text'] == body and not live_linked['relocations'] and
                    not old_linked['relocations'] and closure.sha(body) == prior['body_sha256'],
                    'complete linked body or resolved ELF differs')
    data = match.parse_data_symbols(objects)
    expected = {}
    for site, name in prior['bindings']['calls']:
        symbol = closure.unique_symbol(old_linked, name)
        expected[name] = (symbol['value'], 2)
    for site, name, addend in prior['bindings']['data']:
        closure.require(addend == 0 and name in data and list(data.values()).count(data[name]) == 1,
                        'current canonical named data binding differs')
        expected[name] = (data[name], 1)
    closure.require(not prior['bindings']['functions'] and not prior['bindings']['switches'],
                    'unsupported palette binding role')
    for value in (old_linked, live_linked):
        for name, (point, kind) in expected.items():
            symbol = closure.unique_symbol(value, name)
            closure.require(symbol['section'] == 0xfff1 and symbol['bind'] == 1 and
                            symbol['type'] == kind and symbol['value'] == point and symbol['size'] == 0,
                            'typed linked dependency identity differs')
        closure.require(not any(row['name'] and row['section'] == 0 or
                        row['type'] in (1, 2) and row['section'] == 0xfff1 and row['name'] not in expected
                        for row in value['symbols']), 'foreign linked dependency identity')
    entries, rows = spans.indices(mapping, index)
    for start, end, count in ((address, address+size, prior['instructions']),
                               tuple(prior['dependency_context']['helper'][:3])):
        closure.require(spans.span_record(start, end, entries, rows, rom)['instrs'] == count,
                        'current complete dependency owner/count differs')
    helper = prior['dependency_context']['helper']
    closure.require(closure.sha(rom[helper[0]-match.ROM_BASE:helper[1]-match.ROM_BASE]) == helper[3],
                    'current complete helper bytes differ')
    observed = dict(profile=SCHEMA, selector=SELECTOR, address=address, instructions=prior['instructions'],
        original_sha256=closure.sha(original), linked_sha256=closure.sha(linked),
        source_sha256=closure.sha(source), mapping_sha256=closure.sha(mapping), index_sha256=closure.sha(index),
        objects_sha256=closure.sha(objects), bundle_sha256=closure.sha(bundle), environment=before,
        producer_sha256=dict({Path(module.__file__).name: closure.sha(Path(module.__file__).read_bytes())
                         for module in (authority, closure, spans)},
                         **{Path(__file__).name: closure.sha(Path(__file__).read_bytes())}),
        transported_conditional_closure=prior, frozen_artifact_pins=authority.TRUSTED_PINS,
        fresh_fixed_compiler_source_replay_required=True, conditional_original_ELF_transport=True,
        native_admission=False, source_or_ELF_admission=False, physical_memory_permission=False,
        unconditional_termination=False, old_complete_closure_executions=0, compiler_executions=0)
    closure.require(before == closure.environment_fingerprint(), 'transport environment changed')
    closure.require(manifest is None or closure.digest(manifest) == closure.digest(observed),
                    'palette transport manifest differs')
    return observed, prior['instructions']
