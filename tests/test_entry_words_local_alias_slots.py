"""Raw Thumb checks for the explicit incoming-word/local-slot composition."""
import struct
import unittest

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

import local_alias_slot_profile as slots
import local_long_branch_profile as frame
import readonly_entry_stack_words_profile as incoming


ADDRESS = 0x08020000
HEAD = [0xB510, 0xB084]  # Save R4/LR; allocate four local words.
READS = [0x9806, 0x9907]  # Incoming words zero and one, past the 24-byte frame.
SPILL = [0x466C, 0x9403, 0x9C03, 0x6820, 0x2400]
TAIL = [0x2000, 0xB004, 0xBC10, 0xBC02, 0x4708]


def prove(middle, *, reads=READS, tail=TAIL, **overrides):
    sequence = HEAD + list(reads) + middle + list(tail)
    body = bytearray()
    for word in sequence:
        if word == 'call':
            displacement = ADDRESS + 0x1000 - (ADDRESS + len(body) + 4)
            body.extend(struct.pack('<HH', 0xF000 | ((displacement >> 12) & 0x7FF),
                                    0xF800 | ((displacement >> 1) & 0x7FF)))
        else:
            body.extend(struct.pack('<H', word))
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    instructions = {item.address: item for item in decoder.disasm(bytes(body), ADDRESS)}
    if sum(item.size for item in instructions.values()) != len(body):
        raise AssertionError('Fixture must decode completely')
    edges, calls = {}, {}
    for site, item in instructions.items():
        if item.mnemonic == 'bx':
            edges[site] = ()
        elif item.mnemonic == 'b':
            edges[site] = (item.operands[0].imm,)
        elif item.mnemonic.startswith('b') and item.mnemonic != 'bl':
            edges[site] = (item.operands[0].imm, site + item.size)
        else:
            edges[site] = (site + item.size,)
        if item.mnemonic == 'bl':
            calls[site] = item.operands[0].imm
    policy = dict(stack_aliases=True, local_alias_slot_policy=slots.SELECTOR,
                  entry_stack_policy={'schema': incoming.SCHEMA, 'words': [0, 1]},
                  entry_stack_alias_slot_policy=slots.ENTRY_WORDS_POLICY)
    policy.update(overrides)
    return frame.prove_frame(instructions, edges, ADDRESS, {}, calls, **policy)


class EntryWordsLocalSlotsTests(unittest.TestCase):
    def test_spill_reload_and_both_incoming_reads_share_the_actual_frame(self):
        proof = prove(SPILL)
        self.assertEqual(proof['maximum_frame_bytes'], 24)
        self.assertEqual(proof['entry_stack_alias_slot_policy'], slots.ENTRY_WORDS_POLICY)
        self.assertEqual(proof['entry_stack']['words'], [0, 1])
        self.assertEqual([row[1] for row in proof['entry_stack']['reads']], [0, 4])
        self.assertEqual(proof['entry_stack']['loaded_value'], 'unknown scalar; no provenance facts')
        self.assertEqual([row[1:] for row in proof['local_alias_slots']['stores']], [[-12, -24]])
        self.assertEqual([row[1] for row in proof['local_alias_slots']['loads']], [-12])
        self.assertFalse(proof['local_alias_slots']['callee_pointer_arguments'])
        self.assertEqual(proof['local_aliases']['buffer_calls'], [])

    def test_six_incoming_words_use_offsets_beyond_saved_words(self):
        reads = [0x9800 | (6 + word) for word in range(6)]
        proof = prove(SPILL, reads=reads,
                      entry_stack_policy={'schema': incoming.SCHEMA, 'words': list(range(6))})
        self.assertEqual([row[1] for row in proof['entry_stack']['reads']], list(range(0, 24, 4)))
        self.assertEqual(proof['maximum_frame_bytes'], 24)

    def test_default_still_refuses_combined_policies(self):
        with self.assertRaisesRegex(ValueError, 'exclusive local-only'):
            prove(SPILL, entry_stack_alias_slot_policy=None)

    def test_composition_requires_the_exact_string_selector(self):
        for selector in ('other', True, {}, 1):
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'explicit composition'):
                prove(SPILL, entry_stack_alias_slot_policy=selector)

    def test_composition_requires_local_slots_and_stack_alias_opt_in(self):
        for overrides in ({'local_alias_slot_policy': None}, {'local_alias_slot_policy': 'other'},
                          {'stack_aliases': False}):
            with self.subTest(overrides=overrides), self.assertRaises(ValueError):
                prove(SPILL, **overrides)

    def test_incoming_contract_remains_exact_and_contiguous(self):
        policies = [None, {'schema': incoming.SCHEMA, 'words': [0]},
                    {'schema': incoming.SCHEMA, 'words': [0, 2]},
                    {'schema': incoming.SCHEMA, 'words': [False, 1]},
                    {'schema': incoming.SCHEMA, 'words': list(range(7))},
                    {'schema': 'other', 'words': [0, 1]},
                    {'schema': incoming.SCHEMA, 'words': [0, 1], 'writable': True}]
        for policy in policies:
            with self.subTest(policy=policy), self.assertRaisesRegex(ValueError, 'read-only two-to-six-word'):
                prove(SPILL, entry_stack_policy=policy)

    def test_other_proof_policies_cannot_be_silently_composed(self):
        names = ('buffer_proof', 'bounded_output_proof', 'runtime_calls', 'call_preservation',
                 'zero_index_profile', 'finite_stack_index_policy', 'discarded_exit_scratch',
                 'formal_stack_callee_proof', 'formal_stack_alias_constant_policy',
                 'formal_stack_entry_word_policy', 'formal_stack_entry_words_policy',
                 'mutable_stack_index_policy', 'consumer_scratch_proof', 'entry_recursive_calls',
                 'native_three_call_policy')
        for name in names:
            with self.subTest(policy=name), self.assertRaises(ValueError):
                prove(SPILL, **{name: object()})

    def test_incoming_words_are_read_only(self):
        with self.assertRaisesRegex(ValueError, 'exact direct aligned'):
            prove([0x9006] + SPILL)

    def test_undeclared_incoming_word_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'leaves the declared incoming words'):
            prove([0x9808] + SPILL)

    def test_every_declared_incoming_word_must_be_read(self):
        with self.assertRaisesRegex(ValueError, 'cover exactly every declared'):
            prove(SPILL, reads=READS[:1])

    def test_incoming_load_cannot_forge_entry_return_provenance(self):
        with self.assertRaisesRegex(ValueError, 'original entry LR'):
            prove(SPILL, tail=[0x2000, 0xB004, 0xBC10, 0xBC04, 0x4708])

    def test_incoming_load_cannot_restore_a_saved_register_origin(self):
        with self.assertRaisesRegex(ValueError, 'restore SP, r4-r11'):
            prove([0x9C06], tail=[0x2000, 0xB004, 0xBC01, 0xBC02, 0x4708])

    def test_incoming_load_cannot_supply_a_small_local_index_fact(self):
        with self.assertRaises(ValueError):
            prove([0x466C, 0x9403, 0x9C03, 0x9906, 0x5660, 0x2400])

    def test_incoming_scalar_overwrite_clears_a_previous_pointer_slot(self):
        proof = prove([0x466C, 0x9403, 0x9C06, 0x9403, 0x9803, 0x2400])
        self.assertEqual(len(proof['local_alias_slots']['stores']), 1)
        self.assertEqual(proof['local_alias_slots']['loads'], [])

    def test_slot_store_cannot_overwrite_saved_registers(self):
        for word in (0x9404, 0x9405):
            with self.subTest(word=word), self.assertRaisesRegex(ValueError, 'overwrites a saved register'):
                prove([0x466C, word, 0x2400])

    def test_partial_slot_overwrite_retains_ambiguous_pointer_taint(self):
        with self.assertRaisesRegex(ValueError, 'ambiguous or expired lifetime'):
            prove([0x466C, 0x9403, 0xAB03, 0x2100, 0x7059, 0x9803, 0x7800, 0x2400, 0x2300])

    def test_reallocation_cannot_revive_a_released_pointer_slot(self):
        with self.assertRaisesRegex(ValueError, 'ambiguous or expired lifetime'):
            prove([0x466C, 0x9403, 0xB004, 0xB084, 0x9803, 0x7800, 0x2400])

    def test_missing_store_path_retains_pointer_taint_at_join(self):
        with self.assertRaisesRegex(ValueError, 'ambiguous or expired lifetime'):
            prove([0x466C, 0x2800, 0xD000, 0x9403, 0x9803, 0x7800, 0x2400])

    def test_live_local_argument_still_requires_native_buffer_proof(self):
        with self.assertRaisesRegex(ValueError, 'crossing calls require native buffer proof'):
            prove([0x4668, 'call'])

    def test_reloaded_local_argument_still_requires_native_buffer_proof(self):
        with self.assertRaisesRegex(ValueError, 'crossing calls require native buffer proof'):
            prove([0x466C, 0x9403, 0x9803, 'call', 0x2400])

    def test_unpassed_slot_survives_an_ordinary_ABI_call(self):
        proof = prove([0x466C, 0x9403, 'call', 0x9C03, 0x6820, 0x2400])
        self.assertEqual(len(proof['local_alias_slots']['loads']), 1)
        self.assertEqual(proof['local_aliases']['buffer_calls'], [])
        self.assertEqual(proof['external_calls'], 'existing-direct-call-ABI-summary')


if __name__ == '__main__':
    unittest.main()
