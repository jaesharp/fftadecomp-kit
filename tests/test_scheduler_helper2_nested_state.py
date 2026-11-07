"""New helper2-to-count40 compositions using independent retained raw decoders."""
import copy
from dataclasses import replace
import hashlib
import json
import os
from pathlib import Path
import unittest
from unittest.mock import patch

import scheduler_helper2_nested_state as model
import test_scheduler_helper2_state as upstream
import test_scheduler_small_entry_state as entry_oracle
import test_scheduler_zero40_state as zero_oracle

INPUT = Path(os.environ.get('FFTA_HELPER2_NESTED_INPUTS', 'inputs/helper2-nested-inputs.json'))
if not INPUT.is_file():
    raise unittest.SkipTest('Set FFTA_HELPER2_NESTED_INPUTS to the retained external layout manifest')

BASE, E, SCHED = upstream.BASE, upstream.E, 5000
W, P = model.words._constant, model.words._pointer
put = upstream.put


def read(path):
    return json.loads(Path(path).read_text())


def layout():
    """Reconstruct immutable prior dataclasses without any old bind or derive."""
    inputs = read(INPUT)
    saved = read(inputs['nested_small_layout']['path'])
    coordinate = read(inputs['coordinate_layout']['path'])
    common = read(inputs['helper_common_layout']['path'])
    args = lambda rows: [v for row in rows for v in
                         (row['address'], Path(row['body']['path']).read_bytes())]
    small = model.small
    c = small.coordinate.Layout(small.coordinate.prior.Layout(*args(common['owners'])),
                                *args(coordinate['owners']))
    state = small.state
    s = read(saved['retained_scheduler_layout']['path'])
    a, ins = s['allocator']['allocator'], s['allocator']['allocator']['insertion']
    il = state.split.insert.Layout(ins['address'], ins['sha256'],
        state.split.insert.search.Layout(**ins['search']), state.remove.Layout(**ins['median']))
    al = state.split.Layout(a['address'], a['sha256'], il, a['thunk'], a['pointer_literal'])
    w = s['allocator']
    wl = state.wrapper.Layout(w['address'], w['sha256'], al)
    sc = state.Layout(s['address'], s['sha256'], wl, s['callback_thunk'])
    child = small.Layout(c, sc, int(saved['callback']['index']['rom'], 16),
        Path(saved['callback']['body']['path']).read_bytes(),
        Path(saved['zero_pointer_literal']['body']['path']).read_bytes())
    nested = model.zero.Layout(child, Path(saved['image']['path']).read_bytes(), model.zero.IMAGE_BASE)
    callback = model.helper.prefix.Layout(sc, model.helper.prefix.ADDRESS, upstream.CB)
    helper = model.helper.Layout(model.helper.cpuset.Layout(callback, model.helper.cpuset.bios.WRAPPER),
                                model.helper.ADDRESS, upstream.HELPER)
    return model.Layout(helper, nested)


def fixture(*, parent=None, head=None, size=10):
    l = layout()
    source = upstream.fixture()
    source['layout'] = l.helper
    m = source['cells']
    m.update(entry_oracle.heap(size=size))
    put(m, upstream.G, P(SCHED))
    put(m, SCHED, P(0))
    put(m, SCHED+4 if parent is None else parent+16, W(0) if head is None else P(head))
    put(m, SCHED+12, W(37))
    put(m, E+4, W(0) if parent is None else P(parent))
    if head is not None:
        put(m, head+8, W(0))
    report = model.helper.derive(**source)
    if not report['reaches_scheduler_boundary']:
        raise AssertionError(report['boundary'])
    return dict(layout=l, arena_base=BASE, report=report, selector=model.SELECTOR), source


def memory(report):
    return {int(k):v for k, v in report['post_cells'].items()}


class NestedStateTests(unittest.TestCase):
    def test_stage_reports_end_at_their_own_cutpoints(self):
        f, _ = fixture(parent=7400)
        out = model.continue_from_helper(**f)
        self.assertTrue(out['returns_to_callback_under_conditions'], out['boundary'])
        last = out['stages']['zero-copy-callback-return']
        self.assertEqual(last['final_PC'], model.helper.ADDRESS+270)
        self.assertEqual(last['registers'][13], P(E-72))
        self.assertEqual(last['registers'][1], W(model.helper.ADDRESS+271))
        self.assertIsNot(last['registers'], out['registers'])
        self.assertEqual(out['registers'][13], P(E))
        out['registers'][13] = W(0)
        self.assertEqual(last['registers'][13], P(E-72))

    def test_real_nested_chain_and_return_match_independent_decoders(self):
        f, source = fixture()
        before = copy.deepcopy(f['report'])
        with patch.object(model.helper, 'derive', side_effect=AssertionError('producer replay')):
            out = model.continue_from_helper(**f)
        self.assertTrue(out['returns_to_callback_under_conditions'], out['boundary'])
        self.assertEqual(f['report'], before)
        first = out['stages']['allocator']
        r = dict(before['registers'])
        r[14] = W(model.helper.ADDRESS+271)
        raw_in = dict(layout=f['layout'].nested.prior, arena_base=BASE,
                      cells=memory(before), registers=r)
        rr, mm, trace, _ = entry_oracle.raw(raw_in)
        self.assertEqual(first['trace'], trace)
        self.assertEqual({i:entry_oracle.concrete_word(v) for i, v in first['registers'].items()}, rr)
        # SUB SP reserves bytes without writing or initializing them. The
        # retained relation forgets those bytes rather than expose old values.
        unknown = {BASE+k for k, v in memory(first).items() if type(v) is tuple and
                   v[0] == 'opaque-byte' and v[1].startswith('small scheduler local')}
        self.assertEqual({BASE+k:entry_oracle.concrete_byte(v) for k, v in memory(first).items()
                          if BASE+k not in unknown}, {k:v for k, v in mm.items() if k not in unknown})
        last = out['stages']['zero-copy-callback-return']
        raw_zero = dict(layout=f['layout'].nested, arena_base=BASE, cells=memory(first),
                        registers=first['registers'], scheduler_entry_sp=E-72)
        rr, mm, trace, _, pc = zero_oracle.raw(raw_zero)
        self.assertEqual(last['trace'], trace)
        self.assertEqual(last['final_PC'], pc)
        self.assertEqual({i:zero_oracle.number(v) for i, v in last['registers'].items()}, rr)
        self.assertEqual({BASE+k:zero_oracle.byte(v) for k, v in memory(last).items()}, mm)
        self.assertEqual(out['final_PC'], model.helper.prefix.ADDRESS+142)
        self.assertEqual(out['registers'][13], P(E))
        self.assertEqual(out['registers'][4], source['registers'][4])
        self.assertEqual(out['registers'][7], source['registers'][7])
        self.assertEqual(out['registers'][1], W(model.helper.prefix.ADDRESS+143))

    def test_descriptor_pointer_and_unknown_high_byte_survive_exact_transfers(self):
        f, _ = fixture()
        out = model.continue_from_helper(**f)
        self.assertTrue(out['returns_to_callback_under_conditions'], out['boundary'])
        e = E-72
        first, last = out['stages'].values()
        node = model.words.observe(first['registers'][0])['coordinate']
        self.assertEqual(tuple(memory(last)[e-52+i] for i in range(4)), P(e+44))
        self.assertEqual(tuple(memory(last)[node+24+i] for i in range(3)), (0, 0, 2))
        self.assertEqual(tuple(memory(last)[node+28+i] for i in range(4)), W(0x0839D7E4))
        self.assertEqual(memory(out)[e+47], f['report']['post_cells'][str(e+47)])
        self.assertIsInstance(memory(out)[e+47], tuple)

    def test_actual_parent_word_selects_parent_list(self):
        f, _ = fixture(parent=7000)
        out = model.continue_from_helper(**f)
        self.assertTrue(out['returns_to_callback_under_conditions'], out['boundary'])
        node = model.words.observe(out['registers'][0])['coordinate']
        self.assertEqual(tuple(memory(out)[7016+i] for i in range(4)), P(node))
        self.assertEqual(tuple(memory(out)[node+12+i] for i in range(4)), P(7000))

    def test_existing_parent_chain_is_walked_from_current_bytes(self):
        f, _ = fixture(parent=7000, head=7200)
        out = model.continue_from_helper(**f)
        self.assertTrue(out['returns_to_callback_under_conditions'], out['boundary'])
        node = model.words.observe(out['registers'][0])['coordinate']
        self.assertEqual(tuple(memory(out)[7208+i] for i in range(4)), P(node))
        self.assertEqual(tuple(memory(out)[node+4+i] for i in range(4)), P(7200))

    def test_corrupted_helper_saved_return_is_observed_by_real_pop(self):
        f, _ = fixture()
        for i, value in enumerate(P(7600)):
            f['report']['post_cells'][str(E-4+i)] = value
        out = model.continue_from_helper(**f)
        self.assertFalse(out['returns_to_callback_under_conditions'])
        self.assertEqual(out['boundary']['site'], model.helper.ADDRESS+276)
        self.assertIn('popped return', out['boundary']['reason'])
        self.assertEqual(model.words.observe(out['registers'][1])['kind'], 'base-plus')

    def test_nested_write_to_saved_R4_changes_actual_restored_value(self):
        f, _ = fixture(head=E-28)
        out = model.continue_from_helper(**f)
        self.assertTrue(out['returns_to_callback_under_conditions'], out['boundary'])
        self.assertEqual(out['registers'][4], out['registers'][0])

    def test_protected_scheduler_push_stops_before_any_write(self):
        f, _ = fixture()
        e = E-72
        out = model.continue_from_helper(**f, protected_spans=((e-20, e),))
        self.assertFalse(out['returns_to_callback_under_conditions'])
        self.assertIn('protected', out['boundary']['reason'])
        self.assertFalse([v for v in out['memory_events'] if v['operation'].startswith('write')])
        self.assertEqual(out['registers'][14], W(model.helper.ADDRESS+271))

    def test_missing_heap_byte_preserves_exact_prefix_refusal(self):
        f, _ = fixture()
        del f['report']['post_cells']['134']
        out = model.continue_from_helper(**f)
        self.assertFalse(out['returns_to_callback_under_conditions'])
        self.assertIn('reaching', out['boundary']['reason'])
        self.assertEqual(set(out['stages']), {'allocator'})

    def test_split_without_zero12_stays_at_its_real_boundary(self):
        f, _ = fixture(size=40)
        out = model.continue_from_helper(**f)
        self.assertFalse(out['returns_to_callback_under_conditions'])
        self.assertEqual(set(out['stages']), {'allocator'})
        self.assertEqual(out['stages']['allocator']['registers'][1], W(12))
        self.assertIn('installed-code', out['boundary']['reason'])

    def test_conditional_split_uses_retained_zero12_once(self):
        f, _ = fixture(size=40)
        receipt = (Path(__file__).resolve().parents[1]/'inputs/retained-zero12.json').read_bytes()
        out = model.continue_from_helper(**f, zero12_receipt=receipt)
        self.assertTrue(out['returns_to_callback_under_conditions'], out['boundary'])
        self.assertEqual(len(out['stages']['allocator']['retained_zero12_compositions']), 1)

    def test_explicit_retired_frame_reuse_is_required(self):
        f, _ = fixture()
        retired = (E-204, E-72)
        f['report']['retired_spans'] = [retired]
        out = model.continue_from_helper(**f)
        self.assertEqual(out['boundary']['site'], model.helper.ADDRESS+266)
        self.assertIn('nonreusable', out['boundary']['reason'])
        self.assertEqual(out['trace'], [])

    def test_contiguous_reuse_permissions_allow_actual_new_stack_allocations(self):
        f, _ = fixture()
        f['report']['retired_spans'] = [(E-204, E-72)]
        out = model.continue_from_helper(**f,
            reusable_frame_spans=((E-204, E-140), (E-140, E-72)))
        self.assertTrue(out['returns_to_callback_under_conditions'], out['boundary'])
        self.assertTrue(any(lo <= E-72 and hi >= E for lo, hi in
                            [(min(a for a, b in out['retired_spans']), max(b for a, b in out['retired_spans']))]))

    def test_inherited_lifetime_still_blocks_parent_reads_outside_new_frames(self):
        f, _ = fixture(parent=7000)
        f['report']['retired_spans'] = [(7016, 7020)]
        out = model.continue_from_helper(**f)
        self.assertIn('retired', out['boundary']['reason'])
        self.assertFalse(out['returns_to_callback_under_conditions'])

    def test_malformed_report_cannot_claim_a_different_call(self):
        f, _ = fixture()
        for key, value in [('schema', 'wrong'), ('final_PC', 0), ('helper_entry_SP', True),
                           ('descriptor_bytes', (0,)*28), ('pending_call', {})]:
            with self.subTest(key=key):
                bad = copy.deepcopy(f)
                bad['report'][key] = value
                with self.assertRaises(ValueError):
                    model.continue_from_helper(**bad)

    def test_register_and_cell_origins_are_not_repaired(self):
        f, _ = fixture()
        for reg, value in [(13, W(E-72)), (14, W(1)), (1, W(0)), (2, W(40))]:
            bad = copy.deepcopy(f)
            bad['report']['registers'][reg] = value
            with self.assertRaises(ValueError):
                model.continue_from_helper(**bad)
        for key in [0, '00', True]:
            bad = copy.deepcopy(f)
            bad['report']['post_cells'][key] = 0
            with self.assertRaises(ValueError):
                model.continue_from_helper(**bad)

    def test_complete_owner_mutation_cannot_bind(self):
        l = layout()
        body = l.helper.body[:-1]+bytes([l.helper.body[-1]^1])
        with self.assertRaises(ValueError):
            model.bind(replace(l.helper, body=body), l.nested, selector=model.SELECTOR)
        with self.assertRaises(ValueError):
            model.bind(l.helper, replace(l.nested, image=l.nested.image+b'0'), selector=model.SELECTOR)

    def test_step_bound_is_not_termination_or_return_evidence(self):
        f, _ = fixture()
        out = model.continue_from_helper(**f, max_steps=1)
        self.assertIn('bound exhausted', out['boundary']['reason'])
        self.assertFalse(out['actual_termination_proved'])
        self.assertFalse(out['returns_to_callback_under_conditions'])

    def test_remaining_authority_stays_explicitly_unproved(self):
        f, _ = fixture()
        f['report']['inherited_CpuSet_obligations'] = [{'id':'BIOS', 'proved':False}]
        out = model.continue_from_helper(**f)
        for key in ('actual_prior_report_authentication_proved', 'producer_replayed',
                    'actual_reaching_state_proved', 'physical_access_proved',
                    'actual_installed_identity_proved', 'actual_lifetime_proved',
                    'actual_termination_proved', 'full_CFG_closed', 'source_or_native_admission'):
            self.assertIs(out[key], False, key)
        self.assertEqual(out['inherited_CpuSet_obligations'], f['report']['inherited_CpuSet_obligations'])
        self.assertEqual(out['inherited_helper_obligations'], f['report']['obligations'])
