"""Finite returned-pointer provenance with real Thumb CFGs and frame checks."""
import copy
import hashlib
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import private_float_argument_effects_inventory as effects
import software_float_profile as runtime
import test_private_float_pack_effects_inventory as fixtures

A, U, P = fixtures.ADDRESS, fixtures.UNPACK, fixtures.PACK
words, call = fixtures.words, fixtures.call
ARGUMENTS = [['argument', number, 0] for number in range(3)]


def fixture(*, pointer=8, producer=None):
    # All three branches join at the same BX, exercising the abstract join.
    producer = producer or words(0x2B00, 0xD002, 0x2B01, 0xD002,
                                 0xE002, 0x1C08, 0xE000, 0x1C10, 0x4770)
    consumer = words(0x6802, 0x6842, 0x6882, 0x68C0, 0x4770)
    caller = words(0xB500, 0xB08C, 0x4668, 0xA904, 0xAA00 | pointer)
    caller += call(A+10, U) + call(A+14, P) + words(0xB00C, 0xBC02, 0x4708)
    parts = {A: caller, U: producer, P: consumer}
    counts = {start: len(list(fixtures.Cs(fixtures.CS_ARCH_ARM,
        fixtures.CS_MODE_THUMB).disasm(body, start))) for start, body in parts.items()}
    rom, rows, _, _ = fixtures.image(parts, counts)
    return rom, rows, parts, counts


class FloatPointerReturnTests(unittest.TestCase):
    def producer(self, selected=None, *, policy=None, reads=()):
        rom, entries, parts, counts = selected or fixture()
        return runtime.prove_runtime(rom, entries, U, U+len(parts[U]), counts[U], {},
            call_edges=(), scalar_entries=(), argument_effect_policy=effects.policy(reads),
            return_pointer_policy=ARGUMENTS if policy is None else policy)

    def caller(self, selected=None, *, producer=None, compose=True):
        selected = selected or fixture()
        rom, entries, parts, counts = selected
        produced = self.producer(selected) if producer is None else producer
        consumed = runtime.prove_runtime(rom, entries, P, P+len(parts[P]), counts[P], {},
            call_edges=(), scalar_entries=(),
            argument_effect_policy=effects.policy(((0, offset, 4) for offset in range(0, 16, 4))))
        return runtime.prove_runtime(rom, entries, A, A+len(parts[A]), counts[A],
            {U: produced, P: consumed}, call_edges=((A+10, U), (A+14, P)),
            scalar_entries=(A,), argument_effect_policy=effects.policy(),
            compose_pointer_returns=compose)

    def test_all_reached_return_alternatives_are_preserved_at_join(self):
        proof = self.producer()
        self.assertEqual(proof['return_pointers']['values'], ARGUMENTS)
        self.assertEqual(proof['return_pointers']['body_sha256'],
                         hashlib.sha256(fixture()[2][U]).hexdigest())
        self.assertEqual(proof['return_pointers']['address'], U)

    def test_composition_checks_each_possible_local_record(self):
        proof = self.caller()
        self.assertEqual(proof['argument_effects']['reads'], [])
        self.assertEqual(proof['writes'], [])
        self.assertEqual(proof['stack_reads'], [])
        self.assertEqual(len(proof['argument_accesses']), 4)
        pointer = proof['argument_accesses'][0][-1]
        self.assertEqual(pointer[0], 'alternatives')
        self.assertEqual(pointer[1], (('stack', 0, -52), ('stack', 0, -36), ('stack', 0, -20)))

    def test_default_does_not_consume_pointer_return_receipts(self):
        with self.assertRaisesRegex(ValueError, 'external read'):
            self.caller(compose=False)

    def test_one_saved_or_incoming_alternative_refuses_entire_access(self):
        for pointer in (12, 13):
            with self.subTest(pointer=pointer), self.assertRaisesRegex(ValueError, 'saved|frame'):
                self.caller(fixture(pointer=pointer))

    def test_missing_return_alternative_is_not_a_proof(self):
        with self.assertRaisesRegex(ValueError, 'exceeds its policy'):
            self.producer(policy=ARGUMENTS[:2])

    def test_loaded_scalar_cannot_be_declared_a_returned_pointer(self):
        with self.assertRaisesRegex(ValueError, 'unknown pointer'):
            self.producer(fixture(producer=words(0x6800, 0x4770)), reads=((0, 0, 4),))

    def test_literal_return_tracks_identity_without_granting_readability(self):
        # LDR R0,[PC,#0]; BX LR; an actual fixed address, with no memory permission.
        selected = fixture(producer=words(0x4800, 0x4770, 0x5E68, 0x0300))
        rom, entries, parts, counts = selected
        counts[U] = 2
        next(row for row in entries if int(row['rom'], 16) == U)['instrs'] = 2
        proof = self.producer(selected, policy=[['constant', 0x03005E68, 0]])
        self.assertEqual(proof['return_pointers']['values'], [['constant', 0x03005E68, 0]])
        with self.assertRaisesRegex(ValueError, 'external read'):
            self.caller(selected, producer=proof)

    def test_malformed_or_stale_child_receipts_refuse(self):
        original = self.producer()
        for field, value in (('schema', 'old'), ('complete', False), ('address', U+2),
                             ('end', U+2), ('body_sha256', '0'*64),
                             ('values', [['argument', True, 0]]),
                             ('values', [['argument', 3, 0]]),
                             ('policy', ARGUMENTS[:1])):
            changed = copy.deepcopy(original)
            changed['return_pointers'][field] = value
            with self.subTest(field=field, value=value), self.assertRaisesRegex(
                    ValueError, 'receipt|provenance|exceed'):
                self.caller(producer=changed)

    def test_policy_is_typed_ordered_unique_and_requires_effects(self):
        for policy in ([], ARGUMENTS[::-1], ARGUMENTS+[ARGUMENTS[-1]],
                       [['constant', -1, 0]], [['argument', 0, True]]):
            with self.subTest(policy=policy), self.assertRaisesRegex(ValueError, 'provenance'):
                self.producer(policy=policy)
        rom, entries, parts, counts = fixture()
        with self.assertRaisesRegex(ValueError, 'explicit argument effects'):
            runtime.prove_runtime(rom, entries, U, U+len(parts[U]), counts[U], {},
                call_edges=(), return_pointer_policy=ARGUMENTS)

    def test_unknown_scalar_on_one_branch_remains_unknown(self):
        body = words(0x2B00, 0xD001, 0x6800, 0xE000, 0x1C08, 0x4770)
        with self.assertRaisesRegex(ValueError, 'unknown pointer'):
            self.producer(fixture(producer=body), reads=((0, 0, 4),))

    def test_missing_child_projection_keeps_result_unknown(self):
        proof = self.producer()
        del proof['return_pointers']
        with self.assertRaisesRegex(ValueError, 'external read'):
            self.caller(producer=proof)

    def test_store_through_alternatives_does_not_initialize_all_slots(self):
        rom, entries, parts, counts = fixture()
        produced = self.producer((rom, entries, parts, counts))
        body = words(0xB500, 0xB083, 0x2300, 0x9300, 0x9301, 0x9302,
                     0x4668, 0xA901, 0xAA02)
        body += call(A+18, U)
        body += words(0x2301, 0x6003, 0x9800, 0xB003, 0xBC02, 0x4708)
        parts[A] = body
        counts[A] = len(list(fixtures.Cs(fixtures.CS_ARCH_ARM,
            fixtures.CS_MODE_THUMB).disasm(body, A)))
        rom, entries, _, _ = fixtures.image(parts, counts)
        with self.assertRaisesRegex(ValueError, 'unknown pointer'):
            runtime.prove_runtime(rom, entries, A, A+len(body), counts[A], {U: produced},
                call_edges=((A+18, U),), scalar_entries=(A,), argument_effect_policy=effects.policy(),
                compose_pointer_returns=True, return_pointer_policy=[['constant', 1, 0]])


if __name__ == '__main__':
    unittest.main(verbosity=2)
