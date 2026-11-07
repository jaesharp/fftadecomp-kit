"""New bounded callback/path and genuine owner routing checks, no compilers."""
import copy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import known_list_query_closure_profile as query
import named_data_buffer_profile as named
import owner_admission_profile as owner


def text_index(rows):
    return ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
        f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]}\n' for r in rows).encode()


class KnownListTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        rom = bytearray(16*1024*1024); cls.rows = []
        bodies = {a:(n, h) for a, (_, n, _, h) in query.ROOTS.items()}
        bodies.update(query.DEPENDENCIES)
        for address, (count, encoded) in bodies.items():
            body = bytes.fromhex(encoded); start = address-query.ROM_BASE
            rom[start:start+len(body)] = body
            cls.rows.append(dict(rom=f'0x{address:08X}', end=f'0x{address+len(body):08X}',
                                 mode='thumb', instrs=count))
        rom[0x14225e:0x142260] = bytes.fromhex('c046')
        cls.rom = bytes(rom); cls.rom_sha = query.sha(cls.rom)

    def setUp(self):
        self.rows = copy.deepcopy(type(self).rows)
        self.address = 0x08022044

    def args(self):
        return dict(data=bytes.fromhex(query.ROOTS[self.address][3]), address=self.address,
                    rom=self.rom, mapping=json.dumps(self.rows).encode(), index=text_index(self.rows),
                    selector=query.SELECTOR)

    def prove(self, **changes):
        args = dict(self.args(), **changes)
        with patch.object(query, 'ROM_SHA256', self.rom_sha): return query.prove(**args)

    def bindings(self):
        _, _, callback, encoded = query.ROOTS[self.address]
        return dict(calls=[[16, 'func_080C7CC0']], data=[],
                    functions=[[len(bytes.fromhex(encoded))-4, f'func_{callback:08X}']], switches=[])

    def native(self, **changes):
        args = dict(self.args(), objects=b'{}', bindings=self.bindings()); args.update(changes)
        with patch.object(query, 'ROM_SHA256', self.rom_sha): return owner.verify(**args)

    def test_byte_root_all_three_callback_paths_keep_initialized_result(self):
        p = self.prove()
        self.assertEqual(p['query']['initialized'], [dict(offset=0, width=1, value=1)])
        paths = p['callback_effects']['paths']
        self.assertEqual(len(paths), 3)
        self.assertTrue(all(v['return_value'] == 1 for v in paths))
        self.assertEqual([w[1:] for v in paths for w in v['writes']], [(0, 1, ('constant', 0))])

    def test_search_root_keeps_middle_word_opaque_and_unread(self):
        self.address = 0x08099560; p = self.prove()
        self.assertEqual(p['query']['opaque_unread_offsets'], [4, 5, 6, 7])
        paths = p['callback_effects']['paths']
        self.assertEqual(sorted((v['return_value'], bool(v['writes'])) for v in paths), [(0, True), (1, False)])
        self.assertEqual([r[2:] for v in paths for r in v['reads'] if r[1] == 'query'], [(0, 4), (0, 4)])

    def test_byte_write_requires_zero_refinement_from_branch_predicate(self):
        raw = bytearray.fromhex(query.DEPENDENCIES[0x08022194][1]); raw[0x1c:0x1e] = bytes.fromhex('2070')
        with self.assertRaisesRegex(ValueError, 'callback write'):
            query.callback_effects(bytes(raw), 0x08022194, 'byte')

    def test_search_read_of_unknown_middle_word_refuses(self):
        raw = bytearray.fromhex(query.DEPENDENCIES[0x0809AB5C][1]); raw[12:14] = bytes.fromhex('6068')
        with self.assertRaisesRegex(ValueError, 'uninitialized'):
            query.callback_effects(bytes(raw), 0x0809AB5C, 'search')

    def test_query_alias_cannot_reach_wrong_getter_argument(self):
        raw = bytearray.fromhex(query.DEPENDENCIES[0x0809AB5C][1]); raw[2:4] = bytes.fromhex('081c')
        with self.assertRaisesRegex(ValueError, 'getter'):
            query.callback_effects(bytes(raw), 0x0809AB5C, 'search')

    def test_empty_list_expired_R2_is_retained(self):
        p = self.prove(); alias, = p['outward_expired_aliases']
        self.assertEqual(alias['register'], 2); self.assertFalse(alias['accessible_after_return'])
        self.assertFalse(alias['observed_by_root_continuation'])

    def test_iterator_has_no_invented_bound_or_termination(self):
        p = self.prove(); self.assertTrue(p['iterator']['no_iteration_bound'])
        self.assertFalse(p['iterator']['termination_proved'])
        for key in ('source_or_ELF_admission', 'native_admission', 'physical_memory_permission',
                    'actual_C_function_compatibility_proved', 'unconditional_termination'):
            self.assertIs(p[key], False)

    def test_external_access_C_binding_and_noninterference_conditions_remain(self):
        conditions = ' '.join(self.prove()['explicit_conditions'])
        for word in ('live', 'provenance', 'overlap', 'effective types', 'compatible returning ABI'):
            self.assertIn(word, conditions)

    def test_byte_native_owner_preserves_genuine_binding_manifest(self):
        manifest, instructions = self.native()
        self.assertEqual(manifest['profile'], query.SCHEMA)
        self.assertEqual(manifest['bindings'], self.bindings()); self.assertEqual(len(instructions), 14)

    def test_search_native_owner_uses_distinct_literal_offset(self):
        self.address = 0x08099560; manifest, instructions = self.native()
        self.assertEqual(manifest['bindings']['functions'], [[28, 'func_0809AB5C']])
        self.assertEqual(len(instructions), 13)

    def test_native_binding_cannot_invent_data_permission(self):
        bindings = self.bindings(); bindings['data'] = [[0, 'fake', 0]]
        with self.assertRaisesRegex(ValueError, 'genuine typed bindings'): self.native(bindings=bindings)

    def test_wrong_callback_binding_refuses(self):
        bindings = self.bindings(); bindings['functions'][0][1] = 'func_0809AB5C'
        with self.assertRaises(ValueError): self.native(bindings=bindings)

    def test_selector_is_explicit(self):
        with self.assertRaisesRegex(ValueError, 'explicit'): self.prove(selector='ordinary')

    def test_mutable_ROM_refuses(self):
        with self.assertRaisesRegex(ValueError, 'immutable'): self.prove(rom=bytearray(self.rom))

    def test_wrong_full_ROM_refuses(self):
        with self.assertRaisesRegex(ValueError, 'ROM'): self.prove(rom=self.rom[:-2])

    def test_unknown_root_refuses(self):
        with self.assertRaisesRegex(ValueError, 'explicit'): self.prove(address=self.address+2)

    def test_root_byte_mutation_refuses(self):
        with self.assertRaisesRegex(ValueError, 'root'): self.prove(data=b'\0\0'+self.args()['data'][2:])

    def test_dependency_instructioncount_refuses(self):
        next(r for r in self.rows if r['rom'] == '0x080C7CC0')['instrs'] += 1
        with self.assertRaisesRegex(ValueError, 'dependency'): self.prove()

    def test_wrong_callback_span_refuses(self):
        next(r for r in self.rows if r['rom'] == '0x08022194')['end'] = '0x080221BC'
        with self.assertRaises(ValueError): self.prove()

    def test_wrong_callback_mode_refuses(self):
        next(r for r in self.rows if r['rom'] == '0x08022194')['mode'] = 'arm'
        with self.assertRaises(ValueError): self.prove()

    def test_duplicate_owner_refuses(self):
        self.rows.append(dict(self.rows[0]))
        with self.assertRaises(ValueError): self.prove()

    def test_separately_owned_thunk_padding_refuses(self):
        self.rows.append(dict(rom='0x0814225E', end='0x08142260', mode='thumb', instrs=1))
        with self.assertRaisesRegex(ValueError, 'padding'): self.prove()

    def test_only_text_owned_thunk_padding_refuses(self):
        with self.assertRaisesRegex(ValueError, 'padding'):
            self.prove(index=self.args()['index']+b'0814225E 08142260 2 1\n')

    def test_callback_cycle_refuses(self):
        raw = bytearray.fromhex(query.DEPENDENCIES[0x0809AB5C][1]); raw[20:22] = bytes.fromhex('fee7')
        with self.assertRaisesRegex(ValueError, 'forward'):
            query.callback_effects(bytes(raw), 0x0809AB5C, 'search')

    def test_callback_private_return_origin_must_be_preserved(self):
        raw = bytearray.fromhex(query.DEPENDENCIES[0x0809AB5C][1]); raw[-2:] = bytes.fromhex('7047')
        with self.assertRaisesRegex(ValueError, 'return/frame'):
            query.callback_effects(bytes(raw), 0x0809AB5C, 'search')

    def test_report_selector_retains_new_schema(self):
        manifest, instructions = self.native(); a = self.args()
        report = owner.render(self.address, (a['data'], manifest, 'a'*64, a['mapping'],
            a['index'], b'{}', a['rom'], len(instructions), b'original-ELF'))
        self.assertTrue(owner.selected(report)); self.assertEqual(owner.selector_for_report(report), query.SELECTOR)
        self.assertIn(query.CONTROL_FLOW, report)
        self.assertIn(query.SELECTOR, named.SELECTORS); self.assertIn(query.SCHEMA, named.SCHEMAS)

    def test_closed_query_uses_no_old_effect_or_owner_producer(self):
        import known_query_callback_effects as old
        with patch.object(old, 'prove', side_effect=AssertionError('old owner replay')):
            self.assertEqual(self.prove()['old_effect_or_owner_producer_executions'], 0)


if __name__ == '__main__': unittest.main()
