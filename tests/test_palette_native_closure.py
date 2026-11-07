"""Synthetic receipt transport and real ELF parsing; no original proof replay.

These fixtures supply synthetic authenticated premises. They test composition
and refusal guards, not whether the small fixture implements the palette.
No assembler, compiler, old verifier or actual ROM qualification is invoked.
"""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import palette_native_closure as closure

A, H = 0x08000100, 0x08000200
DATA = {'data_03003860': 0x03003860, 'data_03003E68': 0x03003E68}


def raw_json(value):
    return json.dumps(value, sort_keys=True).encode()


def pin(raw):
    return dict(bytes=len(raw), sha256=closure.sha(raw))


def call(site, target):
    offset = (target-site-4) & 0x7fffff
    return struct.pack('<HH', 0xf000 | (offset >> 12), 0xf800 | ((offset >> 1) & 0x7ff))


def symbol(name, kind, section, value=0, size=0, bind=1):
    return dict(name=name, type=kind, section=section, value=value, size=size, bind=bind)


def elf(text, symbols, relocations, linked=False, extra_allocated=False):
    """Encode genuine minimal ARM ELF32 sections/symbols/REL records in memory."""
    strings = bytearray(b'\0')
    table = bytearray()
    for item in symbols:
        offset = len(strings); strings.extend(item['name'].encode()+b'\0')
        table.extend(struct.pack('<IIIBBH', offset, item['value'], item['size'],
                                 item['bind'] << 4 | item['type'], 0, item['section']))
    names = b'\0.text\0.rel.text\0.symtab\0.strtab\0.shstrtab\0.extra\0'
    rels = b''.join(struct.pack('<II', site, index << 8 | kind) for site, index, kind in relocations)
    content = [b'', text, rels, bytes(table), bytes(strings), names]
    if extra_allocated: content.append(b'X')
    output = bytearray(52); headers = [(0,)*10]
    metadata = [(1, 1, 6, A if linked else 0, 0, 0, 4, 0),
                (7, 9, 0, 0, 3, 1, 4, 8), (17, 2, 0, 0, 4, 1, 4, 16),
                (25, 3, 0, 0, 0, 0, 1, 0), (33, 3, 0, 0, 0, 0, 1, 0)]
    if extra_allocated: metadata.append((43, 1, 3, 0, 0, 0, 1, 0))
    for data, (name, kind, flags, address, link, info, align, entrysize) in zip(content[1:], metadata):
        output.extend(bytes((-len(output)) % 4)); offset = len(output); output.extend(data)
        headers.append((name, kind, flags, address, offset, len(data), link, info, align, entrysize))
    output.extend(bytes((-len(output)) % 4)); section_offset = len(output)
    for row in headers: output.extend(struct.pack('<10I', *row))
    output[:16] = b'\x7fELF\x01\x01\x01'+bytes(9)
    struct.pack_into('<HHIIIIIHHHHHH', output, 16, 2 if linked else 1, 40, 1,
                     A | 1 if linked else 0, 0, section_offset, 0, 52, 0, 0, 40, len(headers), 5)
    return bytes(output)


class Fixture:
    def __init__(self):
        self.body = struct.pack('<3H', 0xb500, 0x4804, 0x4904)+call(A+6, H)
        self.body += struct.pack('<5H', 0x4a04, 0x4b04, 0x3000, 0xbc02, 0x4708)
        self.body += struct.pack('<4I', *DATA.values(), *DATA.values())
        self.original_text = bytearray(self.body); self.original_text[6:10] = call(A+6, A+6)
        for site in (20, 24, 28, 32): self.original_text[site:site+4] = bytes(4)
        self.original_symbols = [symbol('', 0, 0, bind=0), symbol(f'func_{A:08X}', 2, 1, 1, len(self.body))]
        self.original_symbols += [symbol(name, 0, 0) for name in ('memcpy', *DATA)]
        self.linked_symbols = copy.deepcopy(self.original_symbols)
        self.linked_symbols[1]['value'] = A | 1
        self.linked_symbols[2].update(type=2, section=0xfff1, value=H | 1)
        for row, point in zip(self.linked_symbols[3:], DATA.values()): row.update(type=1, section=0xfff1, value=point)
        self.relocations = [(6, 2, 10), (20, 3, 2), (24, 4, 2), (28, 3, 2), (32, 4, 2)]
        self.linked_relocations = []
        self.extra_allocated = False
        helper = b'\x70\x47'
        rom = bytearray(0x300); rom[A-closure.match.ROM_BASE:A-closure.match.ROM_BASE+len(self.body)] = self.body
        rom[H-closure.match.ROM_BASE:H-closure.match.ROM_BASE+2] = helper
        self.rom = bytes(rom)
        self.source = b'/* synthetic authenticated source premise */'
        self.mapping = raw_json([dict(rom=f'0x{a:08X}', end=f'0x{a+n:08X}', mode='thumb', instrs=count)
                                 for a, n, count in ((A, len(self.body), 9), (H, 2, 1))])
        self.index = f'{A:08X} {A+len(self.body):08X} {len(self.body)} 9\n{H:08X} {H+2:08X} 2 1\n'.encode()
        self.objects = raw_json({name: f'0x{point:08X}' for name, point in DATA.items()})
        context = dict(address=A, end=A+len(self.body), body_sha256=closure.sha(self.body), ROM_sha256=closure.sha(self.rom))
        partition = dict(code_bytes=20, literal_and_table_bytes=16, alignment_bytes=0, alignment=[],
                         words=[dict(address=A+site, value=point, load_sites=[A+2], switch_word=False)
                                for site, point in zip((20, 24, 28, 32), (*DATA.values(), *DATA.values()))])
        self.c = dict(copy=dict(prefix=dict(context, partition=partition), copy=dict(canonical_bytes=2,
            canonical_sha256=closure.sha(helper), observations=[dict(address=H, consumer=A, site=A+6,
                consumer_sha256=closure.sha(self.body), count=12, source=-48, destination=-68,
                transfers=[[-48+i, -68+i] for i in range(12)], SP_restored=True,
                copied_pointer_words=[[-68+4*i, ['pointer', -56+2*i]] for i in range(3)],
                preserved_registers=list(range(4, 13)))])),
            numeric=dict(context, instructions=9, partition=partition),
            frame=dict(context, instructions=9, partition=partition, source_or_ELF_admission=False,
                physical_memory_permission=False, incoming_read_obligations=[[0, 4], [4, 4]],
                helper_push_obligations=[[-88, -76]], external_numerical_envelopes=[[1, 2]],
                required_unproved_conditions=['live frame and incoming words; permitted defined external accesses']),
            loops=dict(context, source_or_ELF_admission=False, physical_memory_permission=False,
                required_unproved_conditions=['instruction completion and noninterference']),
            arithmetic=dict(synthetic='conditional channel certificate'),
            first_use=dict(arithmetic_functions_AST_unchanged=True, composer_AST_diff_only_new_guard_and_evidence=True),
            machine=dict(context, schema='conditional-palette-owner-value-composition-v1', instructions=9,
                complete_instruction_coverage=[A+i for i in (0, 2, 4, 6, 10, 12, 14, 16, 18)],
                conditional_owner_machine_value_trace=True, source_or_ELF_admission=False,
                physical_memory_permission=False, native_admission=False, unconditional_termination=False,
                required_unproved_conditions=['bounded loop execution subject to physical accesses']),
            source=dict(schema='conditional-palette-source-machine-correspondence-v1',
                machine_address=A, machine_end=A+len(self.body), machine_body_sha256=closure.sha(self.body),
                ROM_sha256=closure.sha(self.rom), source=dict(function=f'func_{A:08X}',
                    parameter_names=['first', 'count', 'red', 'green', 'blue', 'restore'],
                    parameter_types=['u16', 'u16', 's16', 's16', 's16', 'u8'],
                    pointer_initializer_order=['red', 'green', 'blue'], history_stride=12,
                    root_return_type='void', external_calls_in_C_body=0, palette='data_03003860', history='data_03003E68',
                    AST_sha256='ab'*32), conditional_C_AST_value_access_correspondence=True,
                source_or_ELF_admission=False, physical_memory_permission=False, native_admission=False,
                C_definedness={'external_first_dimension_extent_established': False},
                read_value_quantification='same ordered defined observations; fresh names per iteration',
                required_unproved_conditions=['target signed16 conversion and C object lifetime/provenance']),
            source_scope=dict(AST_diff_only_added_guard_definition_and_call=True, original_AST_digest_unchanged=True),
            inventory=dict(context, schema='thumb-compiler-local-copy-elf-inventory-v1', inventory_only=True,
                instructions=9, partition=partition, helper_identity=[H, H+2, 1, closure.sha(helper)],
                linked_text_sha256=closure.sha(self.body), relocations=[[6, 10, 'memcpy', H],
                    [20, 2, 'data_03003860', DATA['data_03003860']], [24, 2, 'data_03003E68', DATA['data_03003E68']],
                    [28, 2, 'data_03003860', DATA['data_03003860']], [32, 2, 'data_03003E68', DATA['data_03003E68']]]),
            lineage=dict(complete_translation_unit_AST_equal=True, preprocessor_directives_other_than_line_markers=0,
                remaining_conditions=['actual target layout and ABI remain conditional']),
            compiler=dict(before_after_current_bytes_equal=True, target_semantics_proved=False))
        self.c['source']['entry_argument_transport'] = [dict(parameter=name, C_type=kind, machine_bits=location, width=width)
            for name, kind, location, width in zip(self.c['source']['source']['parameter_names'],
                self.c['source']['source']['parameter_types'], ['R0', 'R1', 'R2', 'R3', 'incoming word at entrySP+0', 'incoming word at entrySP+4'], [16, 16, 16, 16, 16, 8])]
        self.sync()

    def encode(self, name):
        value = self.c[name]
        if name in ('copy', 'numeric'): value = dict(prerequisite=value)
        if name in ('frame', 'loops', 'machine', 'source'): value = dict(receipt=value)
        return raw_json(value)

    def sync(self):
        self.original = elf(bytes(self.original_text), self.original_symbols, self.relocations,
                            extra_allocated=self.extra_allocated)
        self.linked = elf(self.body, self.linked_symbols, self.linked_relocations, linked=True)
        self.c['inventory']['original_text_sha256'] = closure.sha(bytes(self.original_text))
        self.c['frame']['reused_certificate_authority'] = {name+'_sha256': closure.digest(self.c[name]) for name in ('copy', 'numeric')}
        self.c['loops']['reuse_authority'] = {name+'_sha256': closure.digest(self.c[name]) for name in ('frame', 'numeric')}
        self.c['first_use']['actual_arithmetic_capture'] = pin(self.encode('arithmetic'))
        self.c['machine']['reused_certificate_authority'] = dict(independently_established_frozen_certificates=True,
            **{name+'_sha256': closure.digest(self.c[name]) for name in ('copy', 'numeric', 'frame', 'arithmetic', 'first_use', 'loops')},
            arithmetic_file_sha256=closure.sha(self.encode('arithmetic')))
        src = self.c['source']; src['source'].update(source_sha256=closure.sha(self.source), source_bytes=len(self.source))
        original_result = pin(b'synthetic original lineage')
        src['reused_authority'] = dict(independently_established_frozen_certificates=True,
            original_source_and_object_lineage_authenticated=True, machine_sha256=closure.digest(self.c['machine']),
            inventory_sha256=closure.digest(self.c['inventory']), source=pin(self.source),
            original_ET_REL=pin(self.original), linked_ELF=pin(self.linked), original_result=original_result)
        self.c['source_scope'].update(frozen_source_capture=pin(self.encode('source')), source=pin(self.source))
        cc_hash = closure.toolchain_fingerprint()[0][1]
        self.c['lineage'].update(source_scope_guard=pin(self.encode('source_scope')), original_source=pin(self.source),
            original_ET_REL=pin(self.original), original_linked_ELF=pin(self.linked),
            preprocessed_AST_sha256=src['source']['AST_sha256'], source_AST_sha256=src['source']['AST_sha256'],
            current_compiler_binary=dict(sha256=cc_hash), original_result=original_result)
        self.c['compiler'].update(current_compiler=dict(sha256=cc_hash), original_result=original_result)

    def args(self):
        certificates = {name: self.encode(name) for name in closure.KEYS}
        return dict(original=self.original, linked=self.linked, address=A, rom=self.rom, mapping=self.mapping,
            index=self.index, bindings=closure.bindings_for(self.c['inventory']), objects=self.objects,
            source=self.source, certificates=certificates,
            trusted_pins={name: pin(raw) for name, raw in certificates.items()}, selector=closure.SELECTOR)


class PaletteClosureTests(unittest.TestCase):
    def verify(self, fixture=None, **changes):
        args = (fixture or Fixture()).args(); args.update(changes)
        return closure.verify_original(**args)

    def test_complete_conditional_manifest_preserves_all_conditions(self):
        f = Fixture(); report, count = self.verify(f)
        self.assertEqual(count, 9)
        self.assertTrue(report['conditional_full_owner_closure'])
        for key in ('source_or_ELF_admission', 'physical_memory_permission', 'native_admission', 'unconditional_termination'):
            self.assertIs(report[key], False)
        for key in ('compiler_executions', 'old_producer_executions'): self.assertEqual(report[key], 0)
        self.assertEqual(report['entry_argument_transport'], f.c['source']['entry_argument_transport'])
        self.assertIn(closure.LAYOUT_CONDITION, report['required_unproved_conditions'])
        self.assertIn(closure.TRUST_CONDITION, report['required_unproved_conditions'])
        for name in ('frame', 'loops', 'machine', 'source'):
            for condition in f.c[name]['required_unproved_conditions']:
                self.assertIn(condition, report['required_unproved_conditions'])

    def test_new_unrelated_count_context_is_permitted_without_old_producer(self):
        f = Fixture(); rows = json.loads(f.mapping)
        rows.append(dict(rom='0x08000280', end='0x08000282', mode='thumb', instrs=1))
        f.mapping = raw_json(rows); f.index += b'08000280 08000282 2 1\n'
        report, _ = self.verify(f)
        self.assertEqual(report['mapping_sha256'], closure.sha(f.mapping))

    def test_explicit_selector_required(self):
        with self.assertRaisesRegex(ValueError, 'explicit conditional'): self.verify(selector='default')

    def test_immutable_original_and_context_inputs(self):
        f = Fixture()
        with self.assertRaisesRegex(ValueError, 'immutable'): self.verify(f, rom=bytearray(f.rom))

    def test_missing_certificate_and_untrusted_pin_refuse(self):
        f = Fixture(); args = f.args(); del args['certificates']['copy']
        with self.assertRaisesRegex(ValueError, 'complete exact'): closure.verify_original(**args)

    def test_submitted_certificate_change_without_authority_refuses(self):
        args = Fixture().args(); args['certificates']['copy'] += b' '
        with self.assertRaisesRegex(ValueError, 'bytes/pin'): closure.verify_original(**args)

    def test_duplicate_json_members_refuse_even_with_matching_pin(self):
        args = Fixture().args(); raw = b'{"receipt":{},"receipt":{}}'
        args['certificates']['source'] = raw; args['trusted_pins']['source'] = pin(raw)
        with self.assertRaisesRegex(ValueError, 'duplicate JSON'): closure.verify_original(**args)

    def test_machine_reuse_edge_mismatch_refuses(self):
        f = Fixture(); f.c['copy']['copy']['count_range'] = [4]
        with self.assertRaisesRegex(ValueError, 'machine reuse edge'): self.verify(f)

    def test_source_inventory_reuse_edge_mismatch_refuses(self):
        f = Fixture(); f.c['inventory']['instructions'] += 1
        with self.assertRaisesRegex(ValueError, 'source reuse edges'): self.verify(f)

    def test_scope_guard_cannot_be_omitted_or_downgraded(self):
        f = Fixture(); f.c['source_scope']['original_AST_digest_unchanged'] = False; f.sync()
        with self.assertRaisesRegex(ValueError, 'prototype strengthening'): self.verify(f)

    def test_arithmetic_guard_must_be_retained(self):
        f = Fixture(); f.c['first_use']['arithmetic_functions_AST_unchanged'] = False; f.sync()
        with self.assertRaisesRegex(ValueError, 'arithmetic strengthening'): self.verify(f)

    def test_preprocessed_AST_mismatch_refuses(self):
        f = Fixture(); f.c['lineage']['preprocessed_AST_sha256'] = '00'*32
        with self.assertRaisesRegex(ValueError, 'preprocessed AST'): self.verify(f)

    def test_source_bytes_must_match_original_lineage(self):
        f = Fixture()
        with self.assertRaisesRegex(ValueError, 'source authority source'): self.verify(f, source=f.source+b' ')

    def test_full_original_ELF_bytes_must_match_lineage(self):
        f = Fixture()
        with self.assertRaisesRegex(ValueError, 'original_ET_REL'): self.verify(f, original=f.original+b'X')

    def test_full_linked_ELF_bytes_must_match_lineage(self):
        f = Fixture()
        with self.assertRaisesRegex(ValueError, 'linked_ELF'): self.verify(f, linked=f.linked+b'X')

    def test_current_ROM_identity_cannot_be_changed(self):
        f = Fixture(); rom = bytearray(f.rom); rom[0] = 1
        with self.assertRaisesRegex(ValueError, 'owner/body/ROM'): self.verify(f, rom=bytes(rom))

    def test_owner_and_helper_current_counts_are_exact(self):
        f = Fixture(); rows = json.loads(f.mapping); rows[0]['instrs'] = 10; f.mapping = raw_json(rows)
        f.index = f.index.replace(b'36 9', b'36 10')
        with self.assertRaisesRegex(ValueError, 'dependency instruction count'): self.verify(f)

    def test_helper_current_text_count_mismatch_refuses(self):
        f = Fixture(); f.index = f.index.replace(b'2 1', b'2 2')
        with self.assertRaisesRegex(ValueError, 'spans/counts'): self.verify(f)

    def test_overlapping_current_owner_refuses(self):
        f = Fixture(); rows = json.loads(f.mapping)
        rows.append(dict(rom=f'0x{A+2:08X}', end=f'0x{A+4:08X}', mode='thumb', instrs=1)); f.mapping = raw_json(rows)
        with self.assertRaisesRegex(ValueError, 'nonoverlapping'): self.verify(f)

    def test_missing_instruction_coverage_refuses(self):
        f = Fixture(); f.c['machine']['complete_instruction_coverage'].pop(); f.sync()
        with self.assertRaisesRegex(ValueError, 'coverage'): self.verify(f)

    def test_sixth_argument_must_be_second_incoming_word(self):
        f = Fixture(); f.c['source']['entry_argument_transport'][5]['machine_bits'] = 'R5'; f.sync()
        with self.assertRaisesRegex(ValueError, 'six argument'): self.verify(f)

    def test_private_pointer_copy_requires_all_twelve_bytes(self):
        f = Fixture(); f.c['copy']['copy']['observations'][0]['transfers'].pop(); f.sync()
        with self.assertRaisesRegex(ValueError, 'three initialized local pointer'): self.verify(f)

    def test_helper_frame_restoration_is_required(self):
        f = Fixture(); f.c['copy']['copy']['observations'][0]['SP_restored'] = False; f.sync()
        with self.assertRaisesRegex(ValueError, 'restore its frame'): self.verify(f)

    def test_conditional_premise_cannot_claim_native_admission(self):
        f = Fixture(); f.c['machine']['native_admission'] = True; f.sync()
        with self.assertRaisesRegex(ValueError, 'cannot upgrade'): self.verify(f)

    def test_conditions_cannot_be_erased(self):
        f = Fixture(); f.c['source']['required_unproved_conditions'] = []; f.sync()
        with self.assertRaisesRegex(ValueError, 'nonempty explicit conditions'): self.verify(f)

    def test_extra_allocated_section_refuses(self):
        f = Fixture(); f.extra_allocated = True; f.sync()
        with self.assertRaisesRegex(ValueError, 'allocated section'): self.verify(f)

    def test_truncated_owner_symbol_refuses(self):
        f = Fixture(); f.original_symbols[1]['size'] -= 2; f.sync()
        with self.assertRaisesRegex(ValueError, 'complete sized'): self.verify(f)

    def test_unresolved_linked_relocation_refuses(self):
        f = Fixture(); f.linked_relocations = f.relocations[:1]; f.sync()
        with self.assertRaisesRegex(ValueError, 'resolved ET_EXEC'): self.verify(f)

    def test_typed_thumb_helper_definition_required(self):
        f = Fixture(); f.linked_symbols[2]['value'] &= ~1; f.sync()
        with self.assertRaisesRegex(ValueError, 'compiler memcpy Thumb'): self.verify(f)

    def test_genuine_original_symbol_must_remain_undefined(self):
        f = Fixture(); f.original_symbols[2]['section'] = 0xfff1; f.sync()
        with self.assertRaisesRegex(ValueError, 'original unique'): self.verify(f)

    def test_nonzero_BL_addend_refuses(self):
        f = Fixture(); f.original_text[6:10] = call(A+6, A+8); f.sync()
        with self.assertRaisesRegex(ValueError, 'zero-addend compiler'): self.verify(f)

    def test_nonzero_data_addend_refuses(self):
        f = Fixture(); f.original_text[20] = 1; f.sync()
        with self.assertRaisesRegex(ValueError, 'zero-addend referenced'): self.verify(f)

    def test_current_canonical_data_identity_required(self):
        f = Fixture(); data = json.loads(f.objects); data['data_03003860'] = '0x03003864'; f.objects = raw_json(data)
        with self.assertRaisesRegex(ValueError, 'typed data literal'): self.verify(f)

    def test_duplicate_symbol_refuses(self):
        f = Fixture(); f.linked_symbols.append(dict(f.linked_symbols[2])); f.sync()
        with self.assertRaisesRegex(ValueError, 'unique ELF symbol'): self.verify(f)

    def test_missing_repeated_literal_relocation_refuses(self):
        f = Fixture(); f.relocations.pop(); f.sync()
        with self.assertRaisesRegex(ValueError, 'complete original relocation'): self.verify(f)

    def test_unrelocated_original_byte_change_refuses(self):
        f = Fixture(); f.original_text[14] ^= 1; f.sync()
        with self.assertRaisesRegex(ValueError, 'unrelocated compiler'): self.verify(f)

    def test_binding_manifest_must_include_all_repeated_literals(self):
        f = Fixture(); bindings = f.args()['bindings']; bindings['data'].pop()
        with self.assertRaisesRegex(ValueError, 'native binding manifest'): self.verify(f, bindings=bindings)

    def test_stale_or_upgraded_result_manifest_refuses(self):
        with self.assertRaisesRegex(ValueError, 'closure manifest differs'):
            self.verify(manifest={'native_admission': True})

    def test_current_compiler_hash_requires_historical_identity(self):
        f = Fixture(); f.c['compiler']['current_compiler']['sha256'] = '00'*32
        f.c['lineage']['current_compiler_binary']['sha256'] = '00'*32
        with self.assertRaisesRegex(ValueError, 'current compiler differs'): self.verify(f)

    def test_environment_race_refuses(self):
        f = Fixture(); before = closure.environment_fingerprint(); after = copy.deepcopy(before); after['producer_sha256'] = '00'*32
        with patch.object(closure, 'environment_fingerprint', side_effect=[before, after]):
            with self.assertRaisesRegex(ValueError, 'environment changed'): self.verify(f)

    def test_new_guard_rejects_second_name_for_referenced_data_point(self):
        f = Fixture(); data = json.loads(f.objects); data['alias_palette'] = data['data_03003860']; f.objects = raw_json(data)
        with self.assertRaisesRegex(ValueError, 'one canonical name'): self.verify(f)

    def test_new_guard_rejects_seventh_parameter_hidden_by_zip(self):
        f = Fixture(); f.c['source']['source']['parameter_names'].append('extra'); f.sync()
        with self.assertRaisesRegex(ValueError, 'six-argument local-object'): self.verify(f)

    def test_new_guard_rejects_duplicate_parameter_names(self):
        f = Fixture(); f.c['source']['source']['parameter_names'][1] = 'first'; f.sync()
        with self.assertRaisesRegex(ValueError, 'six-argument local-object'): self.verify(f)

    def test_new_guards_accept_six_distinct_renamed_parameters_and_unique_data(self):
        f = Fixture(); model = f.c['source']['source']; model['parameter_names'] = ['a', 'b', 'c', 'd', 'e', 'f']
        model['pointer_initializer_order'] = ['c', 'd', 'e']
        for row, name in zip(f.c['source']['entry_argument_transport'], model['parameter_names']): row['parameter'] = name
        f.sync(); report, _ = self.verify(f)
        self.assertEqual([row['parameter'] for row in report['entry_argument_transport']], model['parameter_names'])
        self.assertIn('every condition therein', report['certificate_premise_scope'])

    def test_missing_data_map_name_refuses_before_elf_bindings(self):
        f = Fixture(); f.objects = b'{}'
        with self.assertRaisesRegex(ValueError, 'one canonical name'): self.verify(f)

    def test_extra_typed_absolute_function_refuses(self):
        f = Fixture(); f.linked_symbols.append(symbol('extra_helper', 2, 0xfff1, H | 1)); f.sync()
        with self.assertRaisesRegex(ValueError, 'extra undefined or absolute typed'): self.verify(f)

    def test_original_overlapping_relocation_refuses(self):
        f = Fixture(); f.relocations.append((22, 3, 2)); f.sync()
        with self.assertRaisesRegex(ValueError, 'overlapping relocation'): self.verify(f)

    def test_unreferenced_literal_cannot_acquire_data_authority(self):
        f = Fixture(); f.c['inventory']['partition']['words'][0]['load_sites'] = []; f.sync()
        with self.assertRaisesRegex(ValueError, 'referenced typed data literal'): self.verify(f)

    def test_bad_helper_body_identity_refuses(self):
        f = Fixture(); f.c['inventory']['helper_identity'][3] = '00'*32; f.sync()
        with self.assertRaisesRegex(ValueError, 'copy helper/effect binding'): self.verify(f)

    def test_malformed_nested_certificate_is_a_closed_valueerror(self):
        f = Fixture(); f.c['source']['entry_argument_transport'] = None; f.sync()
        with self.assertRaisesRegex(ValueError, 'malformed closure input'): self.verify(f)

    def test_old_producers_are_not_invoked_by_composition(self):
        import compiler_local_copy_elf_inventory as inventory
        import palette_source_correspondence as source
        import palette_value_composition as values
        with patch.object(inventory, 'verify', side_effect=AssertionError('old inventory replay')), \
             patch.object(source, 'verify', side_effect=AssertionError('old source replay')), \
             patch.object(values, 'verify', side_effect=AssertionError('old machine replay')):
            report, _ = self.verify()
        self.assertEqual(report['old_producer_executions'], 0)


if __name__ == '__main__':
    unittest.main()
