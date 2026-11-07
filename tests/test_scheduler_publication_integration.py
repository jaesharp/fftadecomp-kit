"""New combinations against the published dependencies; no earlier test replay."""
from dataclasses import replace
import unittest
from unittest.mock import Mock, patch

import test_scheduler_requester_callback_state as fixture
import test_scheduler_source_query_state as query_fixture


class ArtifactPortabilityTests(unittest.TestCase):
    def test_query_fixture_does_not_require_a_build_directory(self):
        build = Mock()
        build.is_dir.return_value = False
        root = Mock()
        root.__truediv__ = Mock(return_value=build)
        with patch.object(query_fixture, 'Path') as path:
            path.return_value.resolve.return_value.parents = {1: root}
            query_fixture.artifact('unused.json', {'state': 'conditional'})
        build.is_dir.assert_called_once_with()
        build.write_text.assert_not_called()


@unittest.skipIf(fixture.IMAGE is None, 'set FFTA_SOURCE84_IMAGE to the private authenticated source')
class PublishedDependencyCompositionTests(unittest.TestCase):
    def assert_raw_equal(self, inputs, result, stop_before=None):
        regs, cells, trace, events, pc = fixture.raw(inputs, stop_before=stop_before)
        self.assertEqual(result['trace'], trace)
        self.assertEqual(result['final_PC'], pc)
        self.assertEqual({k: fixture.number(v, inputs['arena_base'])
                          for k, v in result['registers'].items()}, regs)
        actual = fixture.memory(result)
        for address, value in cells.items():
            self.assertEqual(fixture.byte(actual[address-inputs['arena_base']], inputs['arena_base']), value)
        accesses = [(e['site'], e['operation'], e['coordinate'],
                     tuple(fixture.byte(v, inputs['arena_base']) for v in e['bytes']))
                    for e in result['memory_events'] if 'coordinate' in e]
        self.assertEqual(accesses, events)

    def test_parent_chain_and_both_split_allocations_with_truncated_count(self):
        parent, head, tail = 25000, 26000, 27000
        f = fixture.requester_fixture(first=5000, second=6000, count=0xFEDCBA98, parent=parent)
        for address, value in ((parent+16, fixture.P(head)), (head+8, fixture.P(tail)), (tail+8, fixture.I(0))):
            fixture.put(f['cells'], address, value)
        r = fixture.model.derive(**f)
        self.assertTrue(r['conditional_requester_return'], r['boundary'])
        self.assertIsNone(r['boundary'])
        self.assert_raw_equal(f, r)
        memory = fixture.memory(r)
        self.assertEqual(memory[fixture.JOB+30], 0x98)
        self.assertEqual(tuple(memory[tail+8+i] for i in range(4)), fixture.P(fixture.JOB))
        self.assertEqual([e['kind'] for e in r['conditional_image_entries']],
                         ['zero12', 'zero68', 'zero12', 'zero12'])
        self.assertFalse(r['physical_access_proved'])
        self.assertFalse(r['actual_heap_lifetime_proved'])

    def test_published_image_extension_does_not_supply_zero_permission(self):
        f = fixture.requester_fixture(first=5000, second=6000, installed=False, count=0xFEDCBA98)
        r = fixture.model.derive(**f)
        self.assertIn('zero image installation', r['boundary']['reason'])
        self.assertFalse(r['conditional_requester_return'])
        self.assertEqual(r['actual_callback_entries'], [])
        self.assert_raw_equal(f, r, stop_before=fixture.at(f['layout'], 'zero_thunk'))

    def test_opaque_high_registers_and_pointer_descriptor_survive_parent_insertion(self):
        parent = 25000
        f = fixture.requester_fixture(first=5000, second=6000, count=0x1234ABCD, parent=parent)
        fixture.put(f['cells'], parent+16, fixture.I(0))
        fixture.put(f['cells'], fixture.E-24, fixture.P(fixture.ALLOC2+140))
        r = fixture.model.derive(**f)
        self.assertTrue(r['conditional_requester_return'], r['boundary'])
        self.assert_raw_equal(f, r)
        for register in range(4, 12):
            self.assertEqual(r['registers'][register], f['registers'][register])
        memory = fixture.memory(r)
        self.assertEqual(tuple(memory[fixture.E-84+i] for i in range(4)), fixture.P(fixture.ALLOC2+140))
        self.assertFalse(r['physical_access_proved'])

    def test_full_requester_layout_rejects_corrupted_source_image(self):
        layout = fixture.layout()
        def corrupt(node):
            if hasattr(node, 'image'):
                return replace(node, image=node.image[:-1] + bytes([node.image[-1] ^ 1]))
            return replace(node, prior=corrupt(node.prior))
        with self.assertRaisesRegex(ValueError, 'source image'):
            fixture.model.bind(corrupt(layout.prior), selector=fixture.model.SELECTOR)


if __name__ == '__main__':
    unittest.main()
