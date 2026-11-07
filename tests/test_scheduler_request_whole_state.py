"""New full request states and independent instruction replay of their tails."""
import copy
from dataclasses import replace
import unittest

import scheduler_request_whole_state as whole
import scheduler_request_entry_state as entry
import scheduler_copy_state as words
import allocator_remove_relation as branch
import test_scheduler_whole_state as chain_oracle
import test_scheduler_request_entry_state as entry_oracle

BASE = 0x02000000
C = 0x080a0000
E = 4096
P = 7000
Q = 6400
put, half, opaque = chain_oracle.put, chain_oracle.half, chain_oracle.opaque


def layout(chain, address=C):
    body = bytearray(230)
    body[:48] = entry.HEAD
    body[48:52] = (257).to_bytes(4, 'little')
    body[136:174] = entry.SELECTED
    body[174:178] = branch._bl(address+174, chain.outer.wrapper)
    body[178:186] = bytes.fromhex('e060288801300fe0')
    body[188:192] = (chain.effect.callback | 1).to_bytes(4, 'little')
    body[218:230] = bytes.fromhex('2880002009b070bc02bc0847')
    return whole.Layout(entry.Layout(address, bytes(body), chain.outer, chain.effect), chain)


def fixture(*, payload=P, request=Q, phase=257, completion=7, parent=None, nodes=(), e=E):
    f = chain_oracle.fixture(parent=parent, chain=nodes, e=e-52)
    r, m = f['registers'], f['cells']
    parent_word = r[3]
    r.update({0:parent_word, 1:words._pointer(request), 2:words._pointer(payload),
              13:words._pointer(e), 14:words._constant(0x080123f1)})
    half(m, request, phase)
    m[payload+3] = completion
    put(m, payload+16, words._pointer(11000))
    f.update(layout=layout(f['layout']), selector=whole.SELECTOR)
    return f


def run(f):
    return whole.derive(**f)


def memory(report):
    return {int(k):v for k, v in report['post_cells'].items()}


def raw_tail(l, registers, cells):
    """Decode the selected Thumb tail; no production transition helpers."""
    r, m, trace, events = dict(registers), dict(cells), [], []
    pc = l.address+178
    def number(w):
        assert all(type(v) is int for v in w)
        return sum(v << (8*i) for i, v in enumerate(w))
    def coordinate(reg):
        w = r[reg]
        assert w == words._pointer(w[0][1])
        return w[0][1]
    def read(at, width):
        w = tuple(m[at+i] for i in range(width))
        events.append((pc, 'read'+str(width*8), at, w))
        return w if width == 4 else words._constant(number(w))
    def write(at, width, w):
        put(m, at, w[:width])
        events.append((pc, 'write'+str(width*8), at, w[:width]))
    for _ in range(20):
        trace.append(pc)
        offset = pc-l.address
        op = int.from_bytes(l.data[offset:offset+2], 'little')
        nxt = pc+2
        if op & 0xf800 == 0x6000:
            write(coordinate((op >> 3) & 7)+4*((op >> 6) & 31), 4, r[op & 7])
        elif op & 0xf800 == 0x8800:
            r[op & 7] = read(coordinate((op >> 3) & 7)+2*((op >> 6) & 31), 2)
        elif op & 0xf800 == 0x3000:
            reg = (op >> 8) & 7
            r[reg] = words._constant((number(r[reg])+(op & 255)) & 0xffffffff)
        elif op & 0xf800 == 0xe000:
            signed = op & 2047
            if signed & 1024:signed -= 2048
            nxt = pc+4+2*signed
        elif op & 0xf800 == 0x8000:
            write(coordinate((op >> 3) & 7)+2*((op >> 6) & 31), 2, r[op & 7])
        elif op & 0xf800 == 0x2000:
            r[(op >> 8) & 7] = words._constant(op & 255)
        elif op & 0xff80 == 0xb000:
            r[13] = words._pointer(coordinate(13)+4*(op & 127))
        elif op & 0xff00 == 0xbc00:
            selected = [i for i in range(8) if op & (1 << i)]
            start = coordinate(13)
            for i, reg in enumerate(selected):r[reg] = read(start+4*i, 4)
            r[13] = words._pointer(start+4*len(selected))
        elif op & 0xff87 == 0x4700:
            assert (op >> 3) & 15 == 1
            return r, m, trace, events
        else:raise AssertionError(hex(op))
        pc = nxt
    raise AssertionError('selected tail did not reach BX')


class RequestWholeTests(unittest.TestCase):
    def successful(self, f):
        r = run(f)
        self.assertTrue(r['returns_to_input_continuation_under_conditions'], r['boundary'])
        return r

    def test_complete_chain_returns_zero_and_increments_actual_request(self):
        f = fixture(completion=11); r = self.successful(f)
        self.assertEqual(r['phase_observed_after_wrapper'], 257)
        self.assertEqual(r['phase_stored'], 258)
        self.assertEqual(r['registers'][0], words._constant(0))
        self.assertEqual(r['registers'][13], words._pointer(E))
        self.assertEqual(r['observed_return_word'], f['registers'][14])
        self.assertEqual(tuple(memory(r)[P+12+i] for i in range(4)), words._pointer(140))
        for reg in (4, 5, 6):self.assertEqual(r['registers'][reg], f['registers'][reg])
        self.assertEqual(r['retired_spans'], [(E-240, E)])

    def test_root_partial_descriptor_stays_opaque_until_observed_overwrite(self):
        r = self.successful(fixture(completion=13))
        source = r['stages']['whole-wrapper']['stages']['allocator-copy']['descriptor_bytes']
        self.assertEqual(source[20:24], (158, 0, 1, 0))
        root_memory = memory(r['stages']['root-entry'])
        self.assertTrue(all(root_memory[E-44+i][0] == 'opaque-byte' for i in range(4)))
        self.assertEqual(source[:2], (0, 0))
        self.assertTrue(all(v[0] == 'opaque-byte' for v in source[2:4]))
        self.assertEqual(r['stages']['whole-wrapper']['stages']['allocator-copy']['descriptor_phase_under_conditions'], 0)
        self.assertFalse(r['descriptor_phase_initialized'])

    def test_request_alias_reads_fresh_allocation_status(self):
        r = self.successful(fixture(request=160, completion=17))
        self.assertEqual((r['phase_observed_after_wrapper'], r['phase_stored']), (256, 257))

    def test_request_alias_reads_fresh_scheduler_toggled_phase(self):
        f = fixture(request=162, completion=19); half(f['cells'], chain_oracle.S+12, 0x2468)
        r = self.successful(f)
        self.assertEqual((r['phase_observed_after_wrapper'], r['phase_stored']), (0x2469, 0x246a))

    def test_request_alias_observes_actual_callback_zero(self):
        r = self.successful(fixture(request=216, completion=23))
        self.assertEqual((r['phase_observed_after_wrapper'], r['phase_stored']), (0, 1))

    def test_phase_increment_wraps_only_at_actual_halfword_store(self):
        f = fixture(request=162, completion=29); half(f['cells'], chain_oracle.S+12, 65534)
        r = self.successful(f)
        self.assertEqual((r['phase_observed_after_wrapper'], r['phase_stored']), (65535, 0))

    def test_payload_store_pointer_bytes_cannot_be_read_as_phase_bits(self):
        f = fixture(request=P+12, completion=31); r = run(f)
        self.assertEqual(r['boundary']['site'], C+180)
        self.assertIn('pointer', r['boundary']['reason'])
        self.assertEqual(tuple(memory(r)[P+12+i] for i in range(4)), words._pointer(140))
        self.assertFalse(r['descriptor_retired'])

    def test_payload_alias_overwrites_real_saved_LR_and_refuses_return(self):
        f = fixture(payload=E-16, completion=37)
        f['registers'][4] = words._constant(0x07000000)
        r = run(f)
        self.assertTrue(r['reaches_root_return_thunk'], r['boundary'])
        self.assertEqual(r['boundary']['site'], C+228)
        self.assertEqual(r['observed_return_word'], words._pointer(140))
        self.assertFalse(r['returns_to_input_continuation_under_conditions'])

    def test_phase_alias_changes_actual_saved_R4_without_ABI_assumption(self):
        f = fixture(request=E-16, completion=41)
        f['registers'][4] = words._constant(257)
        r = self.successful(f)
        self.assertEqual(r['registers'][4], words._constant(258))
        self.assertNotEqual(r['registers'][4], f['registers'][4])

    def test_phase_alias_changes_saved_return_low_halfword(self):
        f = fixture(request=E-4, completion=43)
        f['registers'][14] = words._constant(0x08000101)
        r = run(f)
        self.assertEqual(r['boundary']['site'], C+228)
        self.assertEqual(r['observed_return_word'], words._constant(0x08000102))

    def test_tail_store_into_still_live_root_descriptor_is_allowed(self):
        f = fixture(payload=E-56, completion=47); r = self.successful(f)
        self.assertEqual(tuple(memory(r)[E-44+i] for i in range(4)), words._pointer(140))
        self.assertEqual([e['site'] for e in r['tail_memory_events'] if e['operation']=='retire-frame'],
                         [C+222, C+224, C+226])
        self.assertTrue(r['descriptor_retired'])

    def test_tail_store_into_retired_wrapper_frame_refuses(self):
        r = run(fixture(payload=E-68, completion=53))
        self.assertEqual(r['boundary']['site'], C+178)
        self.assertIn('retired', r['boundary']['reason'])
        self.assertFalse(r['descriptor_retired'])

    def test_tail_read_from_retired_frame_refuses_after_payload_store(self):
        r = run(fixture(request=E-60, completion=59))
        self.assertEqual(r['boundary']['site'], C+180)
        self.assertIn('retired', r['boundary']['reason'])
        self.assertEqual(tuple(memory(r)[P+12+i] for i in range(4)), words._pointer(140))

    def test_protected_payload_store_retains_completed_nested_effects(self):
        f = fixture(completion=61); f['protected_spans'] = ((P+12, P+16),)
        r = run(f)
        self.assertEqual(r['boundary']['site'], C+178)
        self.assertTrue(r['stages']['whole-wrapper']['reaches_outer_return_thunk'])
        self.assertFalse(r['descriptor_retired'])

    def test_protected_request_store_retains_real_read_and_increment(self):
        f = fixture(completion=67); f['protected_spans'] = ((Q, Q+2),)
        r = run(f)
        self.assertEqual(r['boundary']['site'], C+218)
        self.assertEqual(r['registers'][0], words._constant(258))
        self.assertIsNone(r['phase_stored'])

    def test_nonselected_phase_stops_without_calling_wrapper(self):
        r = run(fixture(phase=258, completion=71))
        self.assertEqual(r['boundary']['site'], C+192)
        self.assertNotIn('whole-wrapper', r['stages'])
        self.assertEqual(r['tail_trace'], [])

    def test_completion_two_preserves_original_unmodeled_branch(self):
        r = run(fixture(completion=2))
        self.assertEqual(r['boundary']['site'], C+218)
        self.assertNotIn('whole-wrapper', r['stages'])

    def test_missing_zero_image_permission_remains_a_nested_refusal(self):
        f = fixture(completion=73); f['observed_zero_target'] = None
        r = run(f)
        self.assertEqual(r['stage'], 'whole-wrapper')
        self.assertFalse(r['reaches_selected_root_continuation'])
        self.assertIsNone(r['registers'])

    def test_numeric_payload_is_not_promoted_to_pointer(self):
        f = fixture(completion=79); f['registers'][2] = words._constant(BASE+P)
        r = run(f)
        self.assertEqual(r['boundary']['site'], C+136)
        self.assertNotIn('whole-wrapper', r['stages'])

    def test_single_input_state_immutable_and_no_actual_admission_claim(self):
        f = fixture(completion=83); before = copy.deepcopy(f); r = self.successful(f)
        self.assertEqual(f, before)
        for key in ['fabricated_saved_words', 'role_separation_assumed', 'ABI_preservation_assumed',
                    'actual_reaching_state_proved', 'actual_heap_or_SP_proved', 'physical_access_proved',
                    'actual_code_execution_proved', 'actual_termination_proved', 'actual_return_executed',
                    'full_scheduler_proved', 'whole_owner_CFG_closed', 'source_or_ELF_admission', 'native_admission']:
            self.assertFalse(r[key], key)
        self.assertTrue(all(not o['proved'] for o in r['obligations']))

    def test_unknown_return_origin_is_preserved_without_executable_permission(self):
        f = fixture(completion=89); f['registers'][14] = opaque('new root unknown caller LR')
        r = self.successful(f)
        self.assertEqual(r['observed_return_word'], f['registers'][14])
        self.assertFalse(r['actual_return_executed'])

    def test_tail_register_updates_do_not_rewrite_frozen_stage_poststates(self):
        f = fixture(completion=149); r = self.successful(f)
        nested = r['stages']['whole-wrapper']
        self.assertEqual(nested['registers'][0], words._pointer(140))
        self.assertEqual(nested['registers'][13], words._pointer(E-52))
        self.assertEqual(nested['registers'][1], words._constant((C+178) | 1))
        self.assertEqual(nested['registers'], nested['stages']['return-consumer']['registers'])
        self.assertEqual(r['stages']['root-entry']['registers'][1], words._constant(64))
        self.assertEqual(r['registers'][0], words._constant(0))
        self.assertIsNot(r['registers'], nested['registers'])

    def test_four_new_raw_root_chain_tail_compositions(self):
        scenarios = [dict(completion=97), dict(completion=101, parent=2600, nodes=(2800, 2900)),
                     dict(completion=103, request=160), dict(completion=107, request=E-16)]
        for options in scenarios:
            with self.subTest(options=options):
                f = fixture(**options)
                if options.get('request') == E-16:f['registers'][4] = words._constant(257)
                r = self.successful(f)
                regs, mem, trace, _, reached, _ = entry_oracle.raw(dict(f, layout=f['layout'].root))
                self.assertTrue(reached)
                self.assertEqual(regs, r['stages']['root-entry']['registers'])
                self.assertEqual(mem, memory(r['stages']['root-entry']))
                self.assertEqual(trace, r['stages']['root-entry']['trace'])
                nested = r['stages']['whole-wrapper']; incoming = dict(regs)
                regs, mem = chain_oracle.raw_copy_and_entry(dict(layout=f['layout'].chain, arena_base=BASE,
                    cells=mem, registers=regs), nested)
                regs, mem, _, _, cut = chain_oracle.callback_oracle.raw(dict(layout=f['layout'].chain.effect,
                    registers=regs, cells=mem, entry_sp=E-132))
                self.assertIsNone(cut)
                regs, mem, _ = chain_oracle.return_oracle.raw_continuation(dict(layout=f['layout'].chain.outer,
                    post_registers=regs, post_cells=mem, arena_base=BASE, entry_registers=incoming))
                self.assertEqual(regs, nested['registers']); self.assertEqual(mem, memory(nested))
                regs, mem, trace, events = raw_tail(f['layout'].root, regs, mem)
                self.assertEqual(regs, r['registers']); self.assertEqual(mem, memory(r))
                self.assertEqual(trace, r['tail_trace'])
                observed = [(e['site'], e['operation'], e['coordinate'], e['bytes'])
                    for e in r['tail_memory_events'] if e['operation'].startswith(('read', 'write'))]
                self.assertEqual(events, observed)


class BindingTests(unittest.TestCase):
    def test_new_composition_accepts_exact_synthetic_selected_tail(self):
        l = fixture(completion=109)['layout']
        self.assertEqual(whole.bind(l.root, l.chain, selector=whole.SELECTOR), l)

    def test_each_selected_tail_instruction_and_branch_is_guarded(self):
        l = fixture(completion=113)['layout']
        for offset in [178, 180, 182, 184, 218, 220, 222, 224, 226, 228]:
            b = bytearray(l.root.data); b[offset] ^= 1
            with self.assertRaises(ValueError):whole.bind(replace(l.root, data=bytes(b)), l.chain, selector=whole.SELECTOR)

    def test_nested_owner_overlap_is_rejected_even_outside_entry_owner_checks(self):
        l = fixture(completion=127)['layout']
        overlap = layout(l.chain, l.chain.outer.callee.allocator.allocator.address)
        with self.assertRaisesRegex(ValueError, 'nested code owner'):whole._validate(overlap)

    def test_different_wrapper_chain_identity_is_rejected(self):
        l = fixture(completion=131)['layout']
        other = chain_oracle.layout(point=BASE+2052)
        with self.assertRaisesRegex(ValueError, 'same retained chain'):
            whole.bind(l.root, other, selector=whole.SELECTOR)

    def test_complete_extent_and_explicit_selector_remain_required(self):
        l = fixture(completion=137)['layout']
        with self.assertRaises(ValueError):whole.bind(replace(l.root, data=l.root.data[:-2]), l.chain, selector=whole.SELECTOR)
        with self.assertRaises(ValueError):whole.bind(l.root, l.chain, selector='default')

    def test_malformed_state_and_unbounded_protections_are_rejected(self):
        for change in [dict(arena_base=True), dict(registers={}), dict(cells={0:True}),
                       dict(protected_spans=tuple((i*4, i*4+1) for i in range(25)))]:
            f = fixture(completion=139); f.update(change)
            with self.assertRaises(ValueError):run(f)


if __name__ == '__main__':
    unittest.main()
