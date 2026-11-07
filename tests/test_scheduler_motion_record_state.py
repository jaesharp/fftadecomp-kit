"""Fresh leaf-entry states only; no frozen producer or original invocation."""
from dataclasses import replace
import copy
import unittest

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
import scheduler_motion_record_state as record
import scheduler_copy_state as words
import allocator_remove_relation as branch
import test_scheduler_coordinate_common_state as layouts

BASE, E, DEST = 0x02000000, 1024, 3000
A = layouts.SQRT + 0x1000


def put(m, at, value):
    m.update({at + i: v for i, v in enumerate(value)})


def opaque(name):
    return tuple(('opaque-byte', name, i) for i in range(4))


def fixture(*, x=3, y=5, tx=13, ty=17, dest=DEST, second=False):
    # Construct frozen layouts only; do not call their bind/derive producers.
    l = record.Layout(layouts.layout(), A, record.BODY)
    site = l.coordinate.motion + (226 if second else 206)
    registers = {i: opaque('077 incoming R' + str(i)) for i in range(15)}
    registers.update({0: words._pointer(dest), 1: words._constant(x & 0xffffffff),
        2: words._constant(y & 0xffffffff), 3: words._constant(tx & 0xffffffff),
        4: words._pointer(5000), 13: words._pointer(E), 14: words._constant((site + 4) | 1)})
    cells = {}
    put(cells, E, words._constant(ty & 0xffffffff))
    return dict(layout=l, arena_base=BASE, cells=cells, registers=registers,
                call_site=site, selector=record.SELECTOR)


def mem(report):
    return {int(k): v for k, v in report['post_cells'].items()}


def word(m, at):
    return tuple(m[at + i] for i in range(4))


def number(value):
    assert all(type(v) is int for v in value)
    return int.from_bytes(bytes(value), 'little')


def signed(value):
    return value - 2**32 if value & 0x80000000 else value


def raw(f):
    """Independent disassembler-driven scalar/byte execution of the leaf."""
    r, m, pc = dict(f['registers']), dict(f['cells']), f['layout'].initializer
    start = pc
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    trace, events, comparison = [], [], None

    def reg(op):
        name = decoder.reg_name(op.reg)
        return {'sp': 13, 'lr': 14}.get(name, int(name[1:]) if name.startswith('r') else -1)

    def ptr(n):
        w = r[n]
        assert w == words._pointer(w[0][1])
        return w[0][1]

    def load(at):
        value = word(m, at)
        events.append((pc, 'read32', at, value))
        return value

    def store(at, value):
        put(m, at, value)
        events.append((pc, 'write32', at, value))

    for _ in range(48):
        ins = next(decoder.disasm(f['layout'].initializer_data[pc-start:], pc, 1))
        trace.append(pc)
        ops, name, nxt = ins.operands, ins.mnemonic, pc + ins.size
        if name == 'push':
            selected = [reg(op) for op in ops]
            at = ptr(13) - 4*len(selected)
            for i, n in enumerate(selected):
                store(at + 4*i, r[n])
            r[13] = words._pointer(at)
        elif name == 'pop':
            selected = [reg(op) for op in ops]
            at = ptr(13)
            values = [load(at + 4*i) for i in range(len(selected))]
            for n, value in zip(selected, values):
                r[n] = value
            r[13] = words._pointer(at + 4*len(selected))
        elif name == 'adds':
            assert ops[2].imm == 0
            r[reg(ops[0])] = r[reg(ops[1])]
        elif name in ('ldr', 'str'):
            bname = decoder.reg_name(ops[1].mem.base)
            bn = 13 if bname == 'sp' else int(bname[1:])
            at = ptr(bn) + ops[1].mem.disp
            if name == 'ldr':
                r[reg(ops[0])] = load(at)
            else:
                store(at, r[reg(ops[0])])
        elif name == 'subs':
            r[reg(ops[0])] = words._constant((number(r[reg(ops[1])]) - number(r[reg(ops[2])])) & 0xffffffff)
        elif name == 'rsbs':
            assert ops[2].imm == 0
            r[reg(ops[0])] = words._constant((-number(r[reg(ops[1])])) & 0xffffffff)
        elif name == 'movs':
            r[reg(ops[0])] = words._constant(ops[1].imm)
        elif name == 'asrs':
            r[reg(ops[0])] = words._constant((signed(number(r[reg(ops[1])])) >> ops[2].imm) & 0xffffffff)
        elif name == 'cmp':
            assert ops[1].imm == 0
            comparison = signed(number(r[reg(ops[0])]))
        elif name in ('bge', 'bne'):
            if comparison >= 0 if name == 'bge' else comparison != 0:
                nxt = ops[0].imm
        elif name == 'b':
            nxt = ops[0].imm
        elif name == 'bx':
            return r, m, trace, events, number(r[reg(ops[0])])
        else:
            raise AssertionError((hex(pc), name, ins.op_str))
        pc = nxt
    raise AssertionError('raw initializer exceeded its acyclic bound')


class RecordTests(unittest.TestCase):
    def test_fresh_uninitialized_record_is_written_and_real_return_observed(self):
        f = fixture()
        r = record.derive(**f)
        self.assertTrue(r['reaches_motion_return'], r['boundary'])
        m = mem(r)
        expected = [3, 5, 13, 17, 1, 1, 10, 12, 0, 6, 12]
        self.assertEqual([number(word(m, DEST + 4*i)) for i in range(11)], expected)
        self.assertEqual(r['registers'][0], f['registers'][14])
        self.assertEqual(r['registers'][1], words._constant(0))
        self.assertEqual(r['return_cutpoint']['target'], f['call_site'] + 4)
        self.assertFalse(r['return_cutpoint']['caller_executed'])

    def test_second_real_caller_site_has_its_own_return_word(self):
        f = fixture(second=True)
        r = record.derive(**f)
        self.assertTrue(r['reaches_motion_return'])
        self.assertEqual(r['return_cutpoint']['target'], layouts.B + 230)

    def test_negative_differences_store_negative_steps_and_magnitudes(self):
        r = record.derive(**fixture(x=13, y=17, tx=3, ty=5))
        m = mem(r)
        self.assertEqual([number(word(m, DEST+i)) for i in (16, 20, 24, 28, 36, 40)],
                         [0xffffffff, 0xffffffff, 10, 12, 6, 12])

    def test_zero_second_difference_rewrites_first_field_at_actual_final_store(self):
        r = record.derive(**fixture(x=3, tx=19, y=17, ty=17))
        stores = [e for e in r['memory_events'] if e['operation'] == 'write32' and e['coordinate'] == DEST]
        self.assertEqual([(e['site'], number(e['bytes'])) for e in stores], [(A+6, 3), (A+74, 19)])
        self.assertEqual(number(word(mem(r), DEST+20)), 1)

    def test_minimum_signed_differences_wrap_negation_and_keep_arithmetic_shift(self):
        r = record.derive(**fixture(x=0, tx=0x80000000, y=0, ty=0x80000000))
        m = mem(r)
        self.assertEqual([number(word(m, DEST+i)) for i in (16, 20, 24, 28, 36, 40)],
                         [0xffffffff, 0xffffffff, 0x80000000, 0x80000000, 0xc0000000, 0x80000000])

    def test_subtraction_uses_wrapped_difference_before_signed_guard(self):
        r = record.derive(**fixture(x=0x80000000, tx=1, y=0x7fffffff, ty=0xffffffff))
        m = mem(r)
        self.assertEqual(number(word(m, DEST+24)), 0x7fffffff)
        self.assertEqual(number(word(m, DEST+16)), 0xffffffff)
        self.assertEqual(number(word(m, DEST+28)), 0x80000000)

    def test_fifth_word_is_loaded_after_push_and_before_aliasing_record_writes(self):
        f = fixture(dest=E, ty=57)
        r = record.derive(**f)
        self.assertTrue(r['reaches_motion_return'])
        self.assertEqual(number(word(mem(r), E+12)), 57)
        events = r['memory_events']
        read = next(i for i, e in enumerate(events) if e['site'] == A+4)
        write = next(i for i, e in enumerate(events) if e['site'] == A+6)
        self.assertLess(read, write)
        self.assertEqual(events[read]['coordinate'], E)

    def test_record_over_saved_R4_R5_observes_corruption_and_refuses_real_BX(self):
        f = fixture(dest=E-12)
        r = record.derive(**f)
        self.assertEqual(r['registers'][4], words._constant(3))
        self.assertEqual(r['registers'][5], words._constant(5))
        self.assertEqual(r['registers'][0], words._constant(13))
        self.assertEqual(r['boundary']['site'], A+80)
        self.assertFalse(r['reaches_motion_return'])
        self.assertIn('return word', r['boundary']['reason'])

    def test_aliasing_save_that_reconstructs_correct_return_is_allowed(self):
        f = fixture(dest=E-12)
        f['registers'][3] = f['registers'][14]
        r = record.derive(**f)
        self.assertTrue(r['reaches_motion_return'], r['boundary'])
        self.assertEqual(r['registers'][4], words._constant(3))
        self.assertFalse(r['ABI_preservation_assumed'])

    def test_opaque_first_argument_is_stored_then_rejected_at_real_subtract(self):
        f = fixture()
        f['registers'][1] = opaque('unknown first value')
        r = record.derive(**f)
        self.assertEqual(word(mem(r), DEST), f['registers'][1])
        self.assertEqual(r['boundary']['site'], A+14)
        self.assertIn('opaque', r['boundary']['reason'])

    def test_pointer_fifth_word_is_copied_without_becoming_numeric(self):
        f = fixture()
        put(f['cells'], E, words._pointer(6500))
        r = record.derive(**f)
        self.assertEqual(word(mem(r), DEST+12), words._pointer(6500))
        self.assertEqual(r['boundary']['site'], A+36)

    def test_opaque_second_value_preserves_first_difference_effects_before_refusal(self):
        f = fixture()
        f['registers'][2] = opaque('unknown second value')
        r = record.derive(**f)
        self.assertEqual(r['boundary']['site'], A+36)
        self.assertEqual(number(word(mem(r), DEST+24)), 10)
        self.assertEqual(word(mem(r), DEST+4), f['registers'][2])

    def test_missing_fifth_word_preserves_only_real_push_writes(self):
        f = fixture()
        del f['cells'][E+2]
        r = record.derive(**f)
        self.assertEqual(r['boundary']['site'], A+4)
        self.assertEqual(set(map(int, r['changed_cells'])), set(range(E-12, E)))

    def test_numeric_record_address_does_not_gain_common_base_provenance(self):
        f = fixture()
        f['registers'][0] = words._constant(BASE+DEST)
        r = record.derive(**f)
        self.assertEqual(r['boundary']['site'], A+6)
        self.assertIn('provenance', r['boundary']['reason'])

    def test_opaque_stack_pointer_refuses_before_any_memory_effect(self):
        f = fixture()
        f['registers'][13] = opaque('unknown stack')
        r = record.derive(**f)
        self.assertEqual(r['changed_cells'], {})
        self.assertEqual(r['memory_events'], [])

    def test_wrong_entry_LR_refuses_before_push(self):
        f = fixture()
        f['registers'][14] = words._constant(0x08100001)
        r = record.derive(**f)
        self.assertEqual(r['trace'], [])
        self.assertEqual(r['changed_cells'], {})

    def test_protected_record_word_retains_ordered_prefix_writes(self):
        f = fixture()
        f['protected_spans'] = ((DEST+8, DEST+12),)
        r = record.derive(**f)
        self.assertEqual(r['boundary']['site'], A+10)
        self.assertEqual(number(word(mem(r), DEST)), 3)
        self.assertNotIn(str(DEST+8), r['post_cells'])

    def test_protected_save_frame_stops_before_all_push_writes(self):
        f = fixture()
        f['protected_spans'] = ((E-4, E),)
        r = record.derive(**f)
        self.assertEqual(r['boundary']['site'], A)
        self.assertEqual(r['changed_cells'], {})

    def test_retired_record_remains_inaccessible(self):
        f = fixture()
        f['retired_spans'] = ((DEST, DEST+44),)
        r = record.derive(**f)
        self.assertEqual(r['boundary']['site'], A+6)
        self.assertIn('retired', r['boundary']['reason'])

    def test_retired_fifth_word_is_not_reactivated_by_adjacent_push(self):
        f = fixture()
        f['retired_spans'] = ((E-20, E+4),)
        r = record.derive(**f)
        self.assertEqual(r['boundary']['site'], A+4)
        self.assertIn((E, E+4), r['retired_spans'])

    def test_actual_push_reactivates_only_its_bytes_and_return_retires_them(self):
        f = fixture()
        f['retired_spans'] = ((E-20, E),)
        r = record.derive(**f)
        self.assertTrue(r['reaches_motion_return'])
        self.assertEqual(r['retired_spans'], [(E-20, E-12), (E-12, E-4), (E-4, E)])

    def test_return_reports_alias_to_newly_retired_frame(self):
        f = fixture()
        f['registers'][6] = words._pointer(E-8)
        r = record.derive(**f)
        self.assertTrue(r['reaches_motion_return'])
        self.assertEqual(r['known_retired_alias_registers']['6'], E-8)

    def test_unaligned_and_wrapping_records_stop_at_first_store(self):
        for dest in (DEST+2, -BASE-4, 2**31-4):
            with self.subTest(dest=dest):
                f = fixture(dest=dest)
                if dest == 2**31-4:
                    f['arena_base'] = 0x80000000
                r = record.derive(**f)
                # The last aligned32bit address admits one word; the next
                # store is the first wrapping access and keeps that write.
                self.assertEqual(r['boundary']['site'], A+(8 if dest == 2**31-4 else 6))
                if dest == 2**31-4:
                    self.assertEqual(word(mem(r), dest), words._constant(3))
                self.assertFalse(r['reaches_motion_return'])

    def test_budget_stops_push_before_any_effect(self):
        f = fixture()
        f['cells'].update({100000+i: 0 for i in range(4092)})
        r = record.derive(**f)
        self.assertEqual(r['boundary']['site'], A)
        self.assertEqual(r['changed_cells'], {})
        self.assertEqual(r['memory_events'], [])

    def test_budget_stops_record_growth_after_prior_successful_writes(self):
        f = fixture()
        f['cells'].update({100000+i: 0 for i in range(4072)})
        r = record.derive(**f)
        # 4076 entry bytes, 12 saves, then two4B record writes fill4096.
        self.assertEqual(r['boundary']['site'], A+10)
        self.assertEqual(len(r['post_cells']), 4096)

    def test_input_state_unchanged_and_no_external_claims_granted(self):
        f = fixture()
        before = copy.deepcopy(f)
        r = record.derive(**f)
        self.assertEqual(f, before)
        for key in ('fabricated_callee_effects', 'fabricated_saved_words', 'output_initialization_assumed',
                    'role_separation_assumed', 'ABI_preservation_assumed', 'actual_reaching_state_proved',
                    'Sqrt_effect_proved', 'physical_access_proved', 'actual_heap_or_SP_proved',
                    'actual_lifetime_proved', 'actual_code_execution_proved', 'actual_termination_proved',
                    'flags_proved', 'returns_to_root', 'full_CFG_closed', 'source_or_ELF_admission', 'native_admission'):
            self.assertFalse(r[key], key)
        for i in range(6, 13):
            self.assertEqual(r['registers'][i], f['registers'][i])

    def test_independent_raw_register_memory_trace_for_signed_edge_cross_product(self):
        values = [0, 1, 0xffffffff, 0x7fffffff, 0x80000000, 0x80000001, 0x12345678]
        for i, x in enumerate(values):
            for j, ty in enumerate(values):
                f = fixture(x=x, y=values[(i+3)%7], tx=values[(j+2)%7], ty=ty, second=bool((i+j)%2))
                r = record.derive(**f)
                regs, memory, trace, events, target = raw(f)
                self.assertTrue(r['reaches_motion_return'], r['boundary'])
                self.assertEqual(r['registers'], regs)
                self.assertEqual(mem(r), memory)
                self.assertEqual(r['trace'], trace)
                actual = [(e['site'], e['operation'], e['coordinate'], e['bytes']) for e in r['memory_events']
                          if e['operation'] in ('read32', 'write32')]
                self.assertEqual(actual, events)
                self.assertEqual(target, (f['call_site']+4)|1)

    def test_independent_raw_aliases_include_corrupted_and_reconstructed_return(self):
        for dest, reconstructed in [(E, False), (E-12, False), (E-12, True), (E-40, False)]:
            f = fixture(dest=dest)
            if reconstructed:
                f['registers'][3] = f['registers'][14]
            r = record.derive(**f)
            regs, memory, trace, events, target = raw(f)
            self.assertEqual(r['registers'], regs)
            self.assertEqual(mem(r), memory)
            self.assertEqual(r['trace'], trace)
            self.assertEqual(r['reaches_motion_return'], target == ((f['call_site']+4)|1))
            actual = [(e['site'], e['operation'], e['coordinate'], e['bytes']) for e in r['memory_events']
                      if e['operation'] in ('read32', 'write32')]
            self.assertEqual(actual, events)


class BindingTests(unittest.TestCase):
    def test_new_complete_synthetic_binding_accepts_only_current_context(self):
        l = fixture()['layout']
        self.assertEqual(record.bind(l.coordinate, l.initializer_data, l.initializer, selector=record.SELECTOR), l)

    def test_all_complete_leaf_halfwords_are_guarded(self):
        l = fixture()['layout']
        for offset in range(0, 82, 2):
            data = bytearray(l.initializer_data)
            data[offset] ^= 1
            with self.assertRaises(ValueError):
                record._validate(replace(l, initializer_data=bytes(data)))

    def test_both_real_motion_call_identities_are_required(self):
        l = fixture()['layout']
        for offset in (206, 226):
            data = bytearray(l.coordinate.motion_data)
            data[offset:offset+4] = branch._bl(l.coordinate.motion+offset, A+0x1000)
            with self.assertRaisesRegex(ValueError, 'call identities'):
                record._validate(replace(l, coordinate=replace(l.coordinate, motion_data=bytes(data))))

    def test_unresolved_sqrt_target_must_remain_separate(self):
        l = fixture()['layout']
        data = bytearray(l.coordinate.motion_data)
        data[128:132] = branch._bl(l.coordinate.motion+128, A+4)
        with self.assertRaisesRegex(ValueError, 'Sqrt'):
            record._validate(replace(l, coordinate=replace(l.coordinate, motion_data=bytes(data))))

    def test_extent_alignment_and_overlap_guards(self):
        l = fixture()['layout']
        for changes in (dict(initializer=A+1), dict(initializer=True), dict(initializer=2**32-80),
                        dict(initializer_data=record.BODY[:-2]), dict(initializer=l.coordinate.motion)):
            with self.assertRaises(ValueError):
                record._validate(replace(l, **changes))

    def test_selector_callsite_and_state_shapes_are_closed(self):
        f = fixture()
        for changes in (dict(selector='default'), dict(call_site=layouts.B+128), dict(call_site=True),
                        dict(arena_base=True), dict(registers={}), dict(cells={0:True}),
                        dict(protected_spans=[(0,4)]), dict(retired_spans=((8,4),))):
            with self.assertRaises(ValueError):
                record.derive(**dict(f, **changes))
        l = f['layout']
        with self.assertRaises(ValueError):
            record.bind(l.coordinate, l.initializer_data, A, selector='default')


if __name__ == '__main__':
    unittest.main()
