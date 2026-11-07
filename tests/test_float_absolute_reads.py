"""Conditional fixed-address reads grant bounds, never contents or stores."""
import copy
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import private_float_argument_effects_inventory as effects
import software_float_profile as runtime
import test_float_pointer_returns as pointers
import test_private_float_pack_effects_inventory as fixtures

A, U, P = pointers.A, pointers.U, pointers.P
FIXED = 0x03005E68
READS = [[FIXED+offset, 4] for offset in range(0, 16, 4)]


def policy(reads=None):
    return {'schema': 'thumb-conditional-absolute-reads-v1',
            'reads': READS if reads is None else reads}


def fixture():
    selected = pointers.fixture(producer=pointers.words(0x4800, 0x4770, 0x5E68, 0x0300))
    selected[3][U] = 2
    next(row for row in selected[1] if int(row['rom'], 16) == U)['instrs'] = 2
    return selected


class FloatAbsoluteReadTests(unittest.TestCase):
    def caller(self, *, selected=None, bounds=None, child=None, pointer_return=None):
        selected = selected or fixture()
        rom, entries, parts, counts = selected
        produced = pointers.FloatPointerReturnTests().producer(selected,
            policy=[['constant', FIXED, 0]])
        consumed = child or runtime.prove_runtime(rom, entries, P, P+len(parts[P]),
            counts[P], {}, call_edges=(), scalar_entries=(),
            argument_effect_policy=effects.policy(((0, offset, 4) for offset in range(0, 16, 4))))
        return runtime.prove_runtime(rom, entries, A, A+len(parts[A]), counts[A],
            {U: produced, P: consumed}, call_edges=((A+10, U), (A+14, P)),
            scalar_entries=(A,), argument_effect_policy=effects.policy(),
            compose_pointer_returns=True, absolute_read_policy=bounds,
            return_pointer_policy=pointer_return)

    def test_exact_selected_reads_are_unknown_and_retained(self):
        result = self.caller(bounds=policy())
        self.assertEqual(result['absolute_reads']['reads'], READS)
        self.assertEqual(result['absolute_reads']['policy'], policy())
        self.assertEqual(result['argument_effects']['reads'], [])
        self.assertEqual(result['writes'], [])
        self.assertEqual(result['absolute_reads']['loaded_values'],
                         'unknown scalars; readability is a conditional premise')

    def test_default_never_grants_literal_pointer_readability(self):
        with self.assertRaisesRegex(ValueError, 'external read'):
            self.caller()

    def test_each_word_is_required_at_exact_width_and_address(self):
        for reads in (READS[:-1], [[FIXED+offset, 2] for offset in range(0, 16, 4)],
                      [[FIXED+4+offset, 4] for offset in range(0, 16, 4)]):
            with self.subTest(reads=reads), self.assertRaisesRegex(ValueError, 'conditional footprint'):
                self.caller(bounds=policy(reads))

    def test_loaded_value_cannot_be_relabelled_as_a_pointer(self):
        with self.assertRaisesRegex(ValueError, 'unknown pointer'):
            self.caller(bounds=policy(), pointer_return=[['constant', FIXED, 0]])

    def test_policy_requires_exact_typed_unique_nonwrapping_aligned_footprints(self):
        for reads in (READS[::-1], READS+[READS[-1]], [[True, 1]], [[FIXED, True]],
                      [[FIXED+1, 4]], [[0xFFFFFFFF, 4]], [[FIXED, 8]], [[-4, 4]],
                      [[FIXED, 4, 0]], tuple(READS), [[FIXED+4*i, 4] for i in range(65)]):
            with self.subTest(reads=reads), self.assertRaisesRegex(ValueError, 'finite aligned'):
                self.caller(bounds=policy(reads))
        for bounds in ({'schema': 'old', 'reads': READS}, {'reads': READS},
                       {**policy(), 'initialized': True}):
            with self.subTest(bounds=bounds), self.assertRaisesRegex(ValueError, 'explicit conditional'):
                self.caller(bounds=bounds)

    def test_absolute_policy_needs_explicit_argument_effects(self):
        rom, entries, parts, counts = fixture()
        with self.assertRaisesRegex(ValueError, 'explicit conditional'):
            runtime.prove_runtime(rom, entries, U, U+len(parts[U]), counts[U], {},
                call_edges=(), absolute_read_policy=policy())

    def direct(self, instruction=0x6808, bounds=None):
        body = pointers.words(0x4901, instruction, 0x4770, 0x46C0, 0x5E68, 0x0300)
        rom, entries, _, _ = fixtures.image({P: body}, {P: 3})
        return runtime.prove_runtime(rom, entries, P, P+len(body), 3, {},
            call_edges=(), scalar_entries=(), argument_effect_policy=effects.policy(),
            absolute_read_policy=policy() if bounds is None else bounds)

    def test_direct_read_and_store_permission_are_distinct(self):
        self.assertEqual(self.direct()['absolute_reads']['reads'], [[FIXED, 4]])
        with self.assertRaisesRegex(ValueError, 'external write'):
            self.direct(instruction=0x6008)

    def absolute_child(self):
        selected = fixture()
        rom, entries, parts, counts = selected
        parts[P] = pointers.words(0x4901, 0x6808, 0x4770, 0x46C0, 0x5E68, 0x0300)
        counts[P] = 3
        rom, entries, _, _ = fixtures.image(parts, counts)
        selected = rom, entries, parts, counts
        child = runtime.prove_runtime(rom, entries, P, P+len(parts[P]), counts[P], {},
            call_edges=(), scalar_entries=(), argument_effect_policy=effects.policy(),
            absolute_read_policy=policy())
        return selected, child

    def test_child_absolute_reads_are_propagated_and_rechecked(self):
        selected, child = self.absolute_child()
        self.assertEqual(self.caller(selected=selected, child=child, bounds=policy())[
            'absolute_reads']['reads'], [[FIXED, 4]])
        with self.assertRaisesRegex(ValueError, 'external read'):
            self.caller(selected=selected, child=child)
        with self.assertRaisesRegex(ValueError, 'conditional footprint'):
            self.caller(selected=selected, child=child, bounds=policy([]))

    def test_stale_forged_or_out_of_policy_child_receipts_refuse(self):
        selected, child = self.absolute_child()
        for field, value in (('schema', 'old'), ('complete', False), ('address', True),
                             ('end', P+2), ('body_sha256', '0'*64),
                             ('loaded_values', 'initialized'), ('reads', [[FIXED+16, 4]]),
                             ('policy', policy([]))):
            altered = copy.deepcopy(child)
            altered['absolute_reads'][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'receipt|policy'):
                self.caller(selected=selected, child=altered, bounds=policy())


if __name__ == '__main__':
    unittest.main(verbosity=2)
