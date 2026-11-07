import unittest

import scheduler_callback_entry_state as entry
import scheduler_copy_state as copy
from scheduler_callback_zero_phase import DISPATCH

C = 0x08004000
E = 4096
D = 128
BODY = DISPATCH[:12]+bytes(646)


def binding():
    return entry.bind(BODY, C, selector=entry.SELECTOR)


def fixture(phase=(0, 0), descriptor=D):
    regs = {r: copy._constant(0x100+r) for r in range(15)}
    regs.update({1: copy._pointer(descriptor), 3: copy._constant(C | 1), 13: copy._pointer(E)})
    cells = {descriptor+i: value for i, value in enumerate(phase)}
    return cells, regs


def run(cells, regs, **kw):
    return entry.derive(binding(), cells, regs, selector=entry.SELECTOR, **kw)


def raw_prefix(cells, regs):
    """Independent halfword decoder for exactly the six supplied instructions."""
    memory, registers, events = dict(cells), dict(regs), []
    pointer = lambda w: w[0][1]
    for offset in range(0, 12, 2):
        op = int.from_bytes(BODY[offset:offset+2], 'little')
        if op & 0xfe00 == 0xb400:
            saved = [r for r in range(8) if op & (1 << r)] + ([14] if op & 0x100 else [])
            sp = pointer(registers[13])-4*len(saved)
            for i, r in enumerate(saved):
                at = sp+4*i
                for n, value in enumerate(registers[r]):
                    memory[at+n] = value
                events.append(dict(site=C+offset, operation='write32', coordinate=at, bytes=registers[r]))
            registers[13] = copy._pointer(sp)
        elif op & 0xff80 == 0xb080:
            registers[13] = copy._pointer(pointer(registers[13])-4*(op & 127))
        elif op & 0xfe00 == 0x1c00:
            assert (op >> 6) & 7 == 0
            registers[op & 7] = registers[(op >> 3) & 7]
        elif op & 0xf800 == 0x8800:
            at = pointer(registers[(op >> 3) & 7])+2*((op >> 6) & 31)
            word = tuple(memory[at+i] for i in range(2))
            registers[op & 7] = word+(0, 0)
            events.append(dict(site=C+offset, operation='read16', coordinate=at, bytes=word))
        else:
            raise AssertionError(hex(op))
    return memory, registers, events


class EntryTests(unittest.TestCase):
    def test_copied_zero_is_read_after_saves(self):
        cells, regs = fixture()
        result = run(cells, regs)
        self.assertTrue(result['reaches_phase_comparison'])
        self.assertEqual(result['conditional_phase_value'], 0)
        self.assertEqual(result['registers'][13], copy._pointer(E-36))
        self.assertFalse(result['actual_phase_zero_proved'])

    def test_save_alias_changes_preentry_zero_phase(self):
        cells, regs = fixture(descriptor=E-20)
        regs[4] = copy._constant(258)
        result = run(cells, regs)
        self.assertEqual(result['conditional_phase_value'], 258)
        self.assertEqual(result['observed_phase_bytes'], (2, 1))

    def test_opaque_phase_bytes_retain_their_origins(self):
        phase = (('opaque-byte', 'observed', 7), ('opaque-byte', 'observed', 8))
        result = run(*fixture(phase))
        self.assertTrue(result['reaches_phase_comparison'])
        self.assertIsNone(result['conditional_phase_value'])
        self.assertEqual(result['registers'][1], phase+(0, 0))

    def test_unmodeled_frame_cannot_supply_old_phase(self):
        result = run(*fixture(descriptor=E-28))
        self.assertIn('unmodeled private-frame', result['boundary']['reason'])
        self.assertEqual(len(result['memory_events']), 5)

    def test_saved_pointer_cannot_be_read_as_known_phase(self):
        cells, regs = fixture(descriptor=E-16)
        regs[5] = copy._pointer(0)
        result = run(cells, regs)
        self.assertIn('pointer phase bytes', result['boundary']['reason'])

    def test_missing_phase_refuses_after_real_saves(self):
        cells, regs = fixture()
        del cells[D+1]
        result = run(cells, regs)
        self.assertIn('missing byte', result['boundary']['reason'])
        self.assertEqual(len(result['changed_cells']), 20)

    def test_other_or_even_target_refuses_before_effects(self):
        for target in (0, C, C+3):
            cells, regs = fixture()
            regs[3] = copy._constant(target)
            result = run(cells, regs)
            self.assertFalse(result['reaches_phase_comparison'])
            self.assertEqual(result['changed_cells'], {})

    def test_protected_save_refuses_without_inventing_preservation(self):
        result = run(*fixture(), protected_spans=((E-12, E-8),))
        self.assertIn('protected bytes', result['boundary']['reason'])
        self.assertEqual(len(result['memory_events']), 2)

    def test_scalar_descriptor_bits_do_not_grant_pointer_origin(self):
        cells, regs = fixture()
        regs[1] = copy._constant(D)
        self.assertIn('pointer origin', run(cells, regs)['boundary']['reason'])

    def test_frame_underflow_and_unaligned_phase_refuse(self):
        cells, regs = fixture()
        regs[13] = copy._pointer(-(2**31)+32)
        self.assertIn('wraps', run(cells, regs)['boundary']['reason'])
        self.assertIn('unaligned', run(*fixture(descriptor=D+1))['boundary']['reason'])

    def test_input_state_is_not_mutated(self):
        cells, regs = fixture((1, 1))
        original_cells, original_regs = dict(cells), dict(regs)
        run(cells, regs)
        self.assertEqual(cells, original_cells)
        self.assertEqual(regs, original_regs)

    def test_incomplete_origins_and_implicit_selector_refuse(self):
        cells, regs = fixture()
        del regs[12]
        with self.assertRaisesRegex(ValueError, 'complete R0'):
            run(cells, regs)
        with self.assertRaisesRegex(ValueError, 'explicit'):
            entry.bind(BODY, C, selector='default')

    def test_complete_body_and_prefix_identity_are_required(self):
        with self.assertRaises(ValueError):
            entry.bind(BODY[:-2], C, selector=entry.SELECTOR)
        with self.assertRaises(ValueError):
            entry.bind(bytes(658), C, selector=entry.SELECTOR)

    def test_independent_thumb_decoder_four_new_entry_states(self):
        for i, descriptor in enumerate((D+32, D+64, E-20, E-4)):
            cells, regs = fixture((i+7, i+11), descriptor=descriptor)
            regs[4], regs[14] = copy._constant(i*257+2), copy._constant(C+0x201+i*2)
            expected_memory, expected_regs, expected_events = raw_prefix(cells, regs)
            result = run(cells, regs)
            self.assertTrue(result['reaches_phase_comparison'], result['boundary'])
            self.assertEqual(result['registers'], expected_regs)
            self.assertEqual(result['memory_events'], expected_events)
            actual_memory = dict(cells)
            actual_memory.update({int(k): v for k, v in result['changed_cells'].items()})
            self.assertEqual(actual_memory, expected_memory)


if __name__ == '__main__':
    unittest.main()
