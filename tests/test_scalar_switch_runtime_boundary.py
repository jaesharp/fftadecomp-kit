"""Ordinary scalar switches select no canonical runtime policy; R3 stays explicit."""
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import match
import owner_admission_profile as owner
import local_long_branch_profile as frame
import framed_switch_inventory as scalar
import owner_graph_profile as graph
import test_scalar_thunk_switch as fixtures


class RuntimeBoundaryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(dir=os.environ['FFTA_TEST_SCRATCH'])
        self.addCleanup(temporary.cleanup)
        self.builder = fixtures.ScalarThunkSwitchTests('runTest')
        self.builder.root = Path(temporary.name)

    def verify_ordinary(self, selector, access=''):
        _, _, values, _ = self.builder.fixture(indirect=False, access=access)
        refinement = owner.refine(values['data'], values['address'], values['mapping'])
        _, _, _, calls, _ = graph.graph(values['data'], values['address'], refinement)
        bindings = scalar.bind_calls(calls, values['mapping'], values['address'],
            len(values['data']), len(values['rom']))
        with patch.object(frame, 'prove_frame', wraps=frame.prove_frame) as prove:
            manifest, instructions = scalar.verify(values['data'], values['address'],
                values['rom'], values['mapping'], values['index'], calls, bindings,
                selector=selector)
        self.assertTrue(instructions)
        self.assertTrue(prove.call_args_list)
        self.assertTrue(all(call.kwargs.get('runtime_calls') is None
                            for call in prove.call_args_list))
        self.assertEqual(manifest['runtime_calls'], [])
        return manifest

    def test_ordinary_fixed_frame_has_no_runtime_policy(self):
        manifest = self.verify_ordinary(scalar.SELECTOR)
        self.assertEqual(manifest['schema'], scalar.SCHEMA)

    def test_one_incoming_word_keeps_its_exclusive_entry_policy(self):
        manifest = self.verify_ordinary(scalar.ENTRY_SELECTOR, 'ldr r2,[sp,#8]')
        self.assertEqual(manifest['schema'], scalar.ENTRY_SCHEMA)
        self.assertTrue(manifest['frame']['entry_stack']['reads'])

    def test_two_incoming_words_keep_their_exclusive_entry_policy(self):
        manifest = self.verify_ordinary(scalar.ENTRY_DATA_SELECTOR,
            'ldr r2,[sp,#8]\nldr r3,[sp,#12]')
        self.assertEqual(manifest['schema'], scalar.ENTRY_DATA_SCHEMA)
        self.assertTrue(manifest['frame']['entry_stack']['reads'])

    def test_actual_r3_thunk_still_passes_exact_nonempty_bindings(self):
        _, _, values, bindings = self.builder.fixture()
        with patch.object(frame, 'prove_frame', wraps=frame.prove_frame) as prove:
            manifest, _ = owner.verify(**values, bindings=bindings)
        self.assertTrue(any(call.kwargs.get('runtime_calls') for call in prove.call_args_list))
        self.assertEqual([name for _, name in
            manifest['proof']['ordinary_switch_inventory']['runtime_calls']], ['_call_via_r3'])
        values['selector'] = owner.DIRECT_SWITCH_SELECTOR
        with self.assertRaises(ValueError): owner.verify(**values, bindings=bindings)


if __name__ == '__main__': unittest.main(verbosity=2)
