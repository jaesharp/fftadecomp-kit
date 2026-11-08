"""New manager-field interface, including an independent raw Thumb load oracle."""
from pathlib import Path
import struct
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import owner_admission_profile as owner
import conditional_local_buffer_profile as local
import scheduler_entry_profile as old
import scheduler_manager_field_profile as profile
from test_scheduler_entry import bound
from test_scheduler_predicates import A, half, bl, R0, LOCAL, SAVED

POINT = 0x02004000


def caller(*, loads=(0x6800, 0x6800), parent=0x9200, descriptor=1,
           before_call=(), join=False, frame=8):
    data = half(0xB500, 0xB080+frame, 0xAB00+descriptor, 0x4800)
    if join:
        data += half(0x2900, 0xD000)  # one path skips the first dereference
    data += half(*loads, 0x2200, parent, 0x2228, *before_call)
    site = A+len(data)
    data += bl(site, old.DIRECT)+half(0xB000+frame, 0xBC02, 0x4708)
    data += bytes((-len(data)) % 4)
    offset = len(data)
    instruction = 0x4800 | ((A+offset-((A+6+4) & ~3))//4)
    data = data[:6]+half(instruction)+data[8:]+struct.pack('<I', POINT)
    return data, {site: old.DIRECT}, offset


def verified(**kwargs):
    data, calls, literal = caller(**kwargs)
    proof = bound(data, calls, policy=profile.SELECTOR)
    match.verify_leaf_instructions(data, A, True, calls, buffer_proof=proof)
    return proof, data, calls, literal


def raw_until_call(data, memory):
    """Decode the fixture's raw halfwords without Capstone or producer helpers."""
    registers = [0]*16
    registers[13] = 0x03007F00
    reads, pc = [], 0
    while pc < len(data):
        word = int.from_bytes(data[pc:pc+2], 'little')
        if word & 0xF800 == 0xF000:
            return registers, reads, A+pc
        if word == 0xB500:
            registers[13] -= 4
        elif word & 0xFF80 == 0xB080:
            registers[13] -= (word & 127)*4
        elif word & 0xF800 == 0xA800:
            registers[(word >> 8) & 7] = registers[13]+(word & 255)*4
        elif word & 0xF800 == 0x4800:
            location = ((A+pc+4) & ~3)+(word & 255)*4
            registers[(word >> 8) & 7] = int.from_bytes(data[location-A:location-A+4], 'little')
        elif word & 0xF800 == 0x6800:
            destination, base = word & 7, (word >> 3) & 7
            location = registers[base]+((word >> 6) & 31)*4
            reads.append((A+pc, location))
            registers[destination] = memory[location]
        elif word & 0xF800 == 0x2000:
            registers[(word >> 8) & 7] = word & 255
        elif word & 0xF800 == 0x9000:
            memory[registers[13]+(word & 255)*4] = registers[(word >> 8) & 7]
        else:
            raise AssertionError('unsupported raw fixture instruction: '+hex(word))
        pc += 2
    raise AssertionError('fixture did not reach its call')


class ManagerFieldTests(unittest.TestCase):
    def test_ordered_loads_agree_with_independent_raw_oracle(self):
        proof, data, calls, literal = verified()
        report = proof.contract_manifest()
        chain = report['entry']['manager']
        self.assertEqual(chain['literal_offset'], literal)
        for pointer, manager in ((0x02005000, 0x02006000), (0x03001000, 0x02008000),
                                 (0x02007000, 0x02005000)):
            with self.subTest(pointer=pointer):
                regs, reads, site = raw_until_call(data, {POINT: pointer, pointer: manager})
                self.assertEqual(regs[0], manager)
                self.assertEqual(reads, [(chain['pointer_load_site'], POINT),
                                        (chain['dereference_site'], pointer)])
                self.assertEqual(site, next(iter(calls)))
                self.assertEqual(regs[3]-0x03007F00, report['observations'][0]['local_offset'])

    def test_missing_second_storage_word_is_not_invented_by_raw_oracle(self):
        _, data, _, _ = verified()
        with self.assertRaises(KeyError):
            raw_until_call(data, {POINT: 0x02005000})

    def test_manifest_records_all_conditional_memory_and_frame_premises(self):
        report = verified()[0].contract_manifest()
        self.assertEqual(report['schema'], profile.SCHEMA)
        for flag in ('actual_callback_effects_proved', 'nonescape_proved',
                     'termination_proved', 'manager_memory_access_proved'):
            self.assertFalse(report[flag])
        text = ' '.join(report['assumptions'])
        for phrase in ('both storage words', 'readable aligned', 'ordered loads',
                       'ambient original R9', 'separate from every caller stack word',
                       'initialization is not checked'):
            self.assertIn(phrase, text)
        self.assertNotIn('is the word loaded from the recorded typed named data literal', text)
        self.assertEqual(report['entry']['manager']['dereference_count'], 2)

    def test_default_and_previous_selectors_refuse_new_chain(self):
        data, calls, _ = caller()
        for policy in (old.SELECTOR, local.SCHEDULER, local.SCHEDULER_PAYLOAD):
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                bound(data, calls, policy=policy)

    def test_only_one_direct_scheduler_call_is_eligible(self):
        for calls in ({}, {A: old.POOL}, {A: old.DIRECT, A+4: old.DIRECT}):
            with self.subTest(calls=calls), self.assertRaisesRegex(ValueError, 'one direct'):
                profile.bind(b'', A, {}, {}, calls)

    def test_single_dereference_does_not_enter_new_selector(self):
        with self.assertRaises(ValueError):
            verified(loads=(0x6800,))

    def test_three_dereferences_are_not_silently_generalized(self):
        with self.assertRaisesRegex(ValueError, 'exactly two'):
            verified(loads=(0x6800, 0x6800, 0x6800))

    def test_displaced_field_refused(self):
        with self.assertRaisesRegex(ValueError, 'zero-offset'):
            verified(loads=(0x6800, 0x6840))

    def test_different_base_register_refused(self):
        with self.assertRaisesRegex(ValueError, 'zero-offset'):
            verified(loads=(0x6800, 0x6808))

    def test_byte_load_is_not_a_pointer_word(self):
        with self.assertRaisesRegex(ValueError, 'word dereferences'):
            verified(loads=(0x6800, 0x7800))

    def test_halfword_load_is_not_a_pointer_word(self):
        with self.assertRaisesRegex(ValueError, 'word dereferences'):
            verified(loads=(0x6800, 0x8800))

    def test_overwritten_manager_refused(self):
        with self.assertRaisesRegex(ValueError, 'exactly two'):
            verified(before_call=(0x2000,))

    def test_branch_join_refused(self):
        with self.assertRaisesRegex(ValueError, 'straight-line'):
            verified(join=True)

    def test_parent_local_pointer_refused(self):
        with self.assertRaisesRegex(ValueError, 'additional register or pointer-word'):
            verified(parent=0x9300)

    def test_descriptor_outgoing_parent_overlap_refused(self):
        with self.assertRaisesRegex(ValueError, 'outgoing argument word'):
            verified(descriptor=0)

    def test_descriptor_past_frame_refused(self):
        with self.assertRaises(ValueError):
            verified(frame=7)

    def test_additional_outgoing_local_alias_refused(self):
        with self.assertRaisesRegex(ValueError, 'additional register or pointer-word'):
            verified(before_call=(0x1C19,))  # r1 = r3

    def test_only_typed_zero_addend_literal_binding_accepted(self):
        proof, _, _, literal = verified()
        report = proof.contract_manifest()
        profile.check_bindings(report, {'data': [[literal, 'data_02004000', 0]]})
        for rows in ([], [[literal, 'data_02004000', 4]],
                     [[literal+4, 'data_02004000', 0]],
                     [[literal, 'data_02004000', 0], [literal, 'data_02004004', 0]]):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                profile.check_bindings(report, {'data': rows})

    def test_dependency_identity_remains_required(self):
        data, calls, _ = caller()
        with self.assertRaisesRegex(ValueError, 'dependency identity'):
            bound(data, calls, policy=profile.SELECTOR, pins={old.DIRECT: (206, '0'*64)})

    def test_selector_registered_in_owner_and_cli(self):
        self.assertIn(profile.SELECTOR, owner.named_buffer.SELECTORS)
        self.assertEqual(owner.selector_for_report('* verification: `'+profile.SCHEMA+'`'), profile.SELECTOR)
        run = subprocess.run([sys.executable, '-B', str(Path(match.__file__)),
                              '--owner-runtime-profile', profile.SELECTOR, '--help'],
                             capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)


if __name__ == '__main__':
    unittest.main()
