"""New helper states checked against the retained independent Thumb oracle."""
from dataclasses import replace
from types import SimpleNamespace
import copy
import unittest

import scheduler_source_predicate_state as model
import test_scheduler_phase256_state as support

I, P, O = support.I, support.P, support.O
BASE, SP, OBJECT = 0x02000000, 16384, 4096


def layout():
    prior = support.layout()
    addresses = {name: 0x08200000+i*0x400 for i, name in enumerate(sorted(model.SHAPES))}
    rows = []
    for name, address, data in prior.owners:
        if name == 'next':
            data = bytearray(data)
            data[16:20] = model.phase.removal._bl(address+16, addresses['predicate'])
            data[44:48] = model.phase.removal._bl(address+44, 0x082F0000)
            data[52:56] = (0x082F1001).to_bytes(4, 'little')
            data = bytes(data)
        rows.append((name, address, data))
    prior = replace(prior, owners=tuple(rows))
    owners = []
    for name, shape in model.SHAPES.items():
        address = addresses[name]; data = bytearray(shape)
        for offset, target in model.EDGES.get(name, {}).items():
            data[offset:offset+4] = model.phase.removal._bl(address+offset, addresses[target])
        owners.append((name, address, bytes(data)))
    return model.Layout(prior, tuple(owners))


def at(l, role, offset=0):
    if role in ('helper', 'root'):
        return support.at(l.prior, 'next' if role == 'helper' else 'root', offset)
    return next(a for name, a, _ in l.owners if name == role)+offset


def fixture(flags=0, byte=0, obj=OBJECT):
    l = layout(); m = {}
    r = {i: O('source predicate incoming '+str(i)) for i in range(15)}
    r.update({0: P(obj), 1: I(0xABCDEF05), 2: I(0xFEDCBA00), 3: P(12003),
              13: P(SP), 14: I(at(l, 'root', 124) | 1)})
    support.half(m, obj+4, flags)
    m[obj+704] = byte
    support.put(m, SP, P(2500))
    return dict(layout=l, arena_base=BASE, cells=m, registers=r, selector=model.SELECTOR)


def oracle_fixture(f):
    l = f['layout']
    owners = (('root', at(l, 'helper'), support.role(l.prior, 'next')[1]),)+l.owners
    return dict(layout=SimpleNamespace(owners=owners), arena_base=f['arena_base'],
                cells=f['cells'], registers=f['registers'])


_PREFIXES = {}


def prefix_fixture(*, released=False, flags=0):
    key = released, flags
    if key in _PREFIXES:
        return copy.deepcopy(_PREFIXES[key])
    l = layout()
    f = support.fixture(node=support.NODE if released else None)
    f['layout'] = l.prior
    obj = support.NODE if released else 6600
    support.put(f['cells'], support.PAYLOAD+16, P(obj))
    f['registers'][8] = O('new composed source predicate state')
    if not released:
        support.half(f['cells'], obj+4, flags)
    f['cells'][obj+704] = 0
    prefix = model.phase.derive(**f)
    _PREFIXES[key] = l, f, prefix
    return copy.deepcopy(_PREFIXES[key])


class SourcePredicateTests(unittest.TestCase):
    def assert_raw(self, f, result, stop_before=None):
        regs, mem, trace, events, pc = support.raw(oracle_fixture(f), stop_before)
        self.assertEqual(result['trace'], trace)
        self.assertEqual(result['final_PC'], pc)
        self.assertEqual({k: support.number(v, f['arena_base']) for k, v in result['registers'].items()}, regs)
        got = support.memory(result)
        for a, value in mem.items():
            self.assertEqual(support.byte(got[a-f['arena_base']], f['arena_base']), value)
        observed = [(e['site'], e['operation'], e['coordinate'],
                     tuple(support.byte(v, f['arena_base']) for v in e['bytes']))
                    for e in result['memory_events'] if 'coordinate' in e]
        self.assertEqual(observed, events)

    def creation(self, f, result):
        self.assertFalse(result['conditional_helper_return'])
        self.assertEqual(result['final_PC'], at(f['layout'], 'helper', 44))
        self.assertEqual(result['boundary']['target'], 0x082F0000)
        self.assert_raw(f, result, result['final_PC'])

    def test_clear_fields_return_null_through_actual_saved_registers(self):
        f = fixture(); result = model.derive(**f)
        self.assertTrue(result['conditional_helper_return'])
        self.assertEqual(result['final_PC'], at(f['layout'], 'root', 124))
        self.assertEqual(result['registers'][0], I(0))
        self.assertEqual(result['registers'][13], P(SP))
        for reg in (4, 5, 6, 7):
            self.assertEqual(result['registers'][reg], f['registers'][reg])
        self.assert_raw(f, result)

    def test_bit_eight_short_circuits_later_predicate_loads(self):
        f = fixture(flags=8); del f['cells'][OBJECT+704]
        result = model.derive(**f); self.creation(f, result)
        self.assertNotIn(at(f['layout'], 'flag_test'), result['trace'])
        self.assertNotIn(at(f['layout'], 'byte_test'), result['trace'])

    def test_bit_thirty_two_reloads_the_halfword_and_skips_byte(self):
        f = fixture(flags=32); result = model.derive(**f); self.creation(f, result)
        reads = [e for e in result['memory_events'] if e.get('coordinate') == OBJECT+4]
        self.assertEqual(len(reads), 2)
        self.assertNotIn(at(f['layout'], 'byte_load'), result['trace'])

    def test_nonzero_byte_uses_all_actual_nested_returns(self):
        f = fixture(byte=255); result = model.derive(**f); self.creation(f, result)
        self.assertEqual([e['role'] for e in result['observed_returns']],
                         ['identity', 'identity', 'flag_test', 'byte_load', 'byte_test', 'predicate'])

    def test_unrelated_halfword_flags_do_not_select_creation(self):
        f = fixture(flags=0xFFD7); result = model.derive(**f)
        self.assertTrue(result['conditional_helper_return']); self.assert_raw(f, result)

    def test_descriptor_fields_and_scheduler_arguments_preserve_origins(self):
        f = fixture(flags=8); result = model.derive(**f); self.creation(f, result)
        m = support.memory(result); local = SP-48
        self.assertEqual(tuple(m[local+20+i] for i in range(4)), (5, 0, 0, 0))
        self.assertEqual(tuple(m[local+4+i] for i in range(4)), P(OBJECT))
        self.assertEqual(tuple(m[local+8+i] for i in range(4)), P(12003))
        self.assertEqual([result['registers'][i] for i in range(4)],
                         [I(0x082F1001), I(84), P(local), P(2500)])
        # BX through the saved caller word does not restore the LR register.
        self.assertEqual(result['registers'][14], I(at(f['layout'], 'predicate', 8) | 1))
        self.assertTrue(all(type(m[local+i]) is tuple for i in (0, 1, 2, 3, 12, 13, 24, 25)))
        self.assertFalse(any(result[k] for k in ('actual_reaching_proved', 'physical_access_proved',
                         'actual_heap_lifetime_proved', 'actual_termination_proved', 'whole_CFG_closed', 'native_admission')))

    def test_discarded_unknown_argument_high_bytes_are_not_observed(self):
        f = fixture(flags=8)
        f['registers'][1] = (7,)+O('discarded high argument')[1:]
        f['registers'][2] = (3,)+O('other discarded high argument')[1:]
        result = model.derive(**f); self.creation(f, result)
        m = support.memory(result)
        self.assertEqual(tuple(m[SP-28+i] for i in range(4)), (7, 0, 3, 0))

    def test_unknown_low_argument_byte_remains_unknown_at_halfword_store(self):
        f = fixture(flags=8); f['registers'][1] = O('unknown selected low byte')
        result = model.derive(**f)
        self.assertEqual(result['boundary']['site'], at(f['layout'], 'helper', 28))
        self.assertIn('narrow store', result['boundary']['reason'])

    def test_unknown_arguments_are_unused_on_null_return_path(self):
        f = fixture(); f['registers'][1] = O('unused first byte'); f['registers'][2] = O('unused second byte')
        result = model.derive(**f)
        self.assertTrue(result['conditional_helper_return']); self.assert_raw(f, result)

    def test_opaque_object_is_not_inferred_from_numeric_bits(self):
        f = fixture(); f['registers'][0] = O('unknown predicate object')
        result = model.derive(**f)
        self.assertEqual(result['boundary']['site'], at(f['layout'], 'predicate', 8))
        self.assertIn('provenance', result['boundary']['reason'])

    def test_missing_flag_byte_stops_at_real_halfword_load(self):
        f = fixture(); del f['cells'][OBJECT+5]
        result = model.derive(**f)
        self.assertEqual(result['boundary']['site'], at(f['layout'], 'predicate', 8))
        self.assertIn('reaching', result['boundary']['reason'])

    def test_opaque_flag_lane_is_not_promoted_to_scalar(self):
        f = fixture(); f['cells'][OBJECT+5] = O('unknown flag lane')[0]
        result = model.derive(**f)
        self.assertIn('narrow read', result['boundary']['reason'])

    def test_missing_byte_stops_after_prior_actual_callee_returns(self):
        f = fixture(); del f['cells'][OBJECT+704]
        result = model.derive(**f)
        self.assertEqual(result['boundary']['site'], at(f['layout'], 'byte_load', 6))
        self.assertEqual(result['observed_returns'][-1]['role'], 'flag_test')

    def test_retired_object_read_is_refused(self):
        f = fixture(); f['retired_spans'] = ((OBJECT, OBJECT+8),)
        result = model.derive(**f)
        self.assertIn('retired', result['boundary']['reason'])

    def test_protected_descriptor_store_preserves_previous_bytes(self):
        f = fixture(flags=8); support.half(f['cells'], SP-28, 0x1234)
        f['protected_spans'] = ((SP-28, SP-26),)
        result = model.derive(**f)
        self.assertEqual(result['boundary']['site'], at(f['layout'], 'helper', 28))
        self.assertEqual(tuple(support.memory(result)[SP-28+i] for i in range(2)), (0x34, 0x12))

    def test_protected_first_save_word_stops_before_push_write(self):
        f = fixture(); f['protected_spans'] = ((SP-20, SP-16),)
        result = model.derive(**f)
        self.assertEqual(result['final_PC'], at(f['layout'], 'helper'))
        self.assertFalse(any(e['operation'].startswith('write') for e in result['memory_events']))

    def test_retired_stack_bytes_require_explicit_reuse_interval(self):
        f = fixture(); f['retired_spans'] = ((SP-20, SP),)
        result = model.derive(**f)
        self.assertIn('nonreusable', result['boundary']['reason'])

    def test_reusing_stack_retains_existing_local_alias_bytes(self):
        f = fixture(flags=8)
        f['retired_spans'] = f['reusable_frame_spans'] = ((SP-48, SP),)
        support.put(f['cells'], SP-48, I(0xDECAFBAD))
        result = model.derive(**f); self.creation(f, result)
        self.assertEqual(tuple(support.memory(result)[SP-48+i] for i in range(4)), I(0xDECAFBAD))

    def test_unavailable_payload_cannot_be_revived_as_stack(self):
        f = fixture(); f['retired_spans'] = f['reusable_frame_spans'] = ((SP-20, SP),)
        f['unavailable_spans'] = ((SP-20, SP),)
        result = model.derive(**f)
        self.assertIn('unavailable', result['boundary']['reason'])

    def test_save_write_cannot_modify_any_bound_owner(self):
        f = fixture(); f['arena_base'] = at(f['layout'], 'helper')-SP+20
        result = model.derive(**f)
        self.assertIn('immutable complete owner', result['boundary']['reason'])

    def test_save_alias_changes_object_flags_before_actual_read(self):
        f = fixture(obj=SP-24); f['registers'][4] = I(8)
        result = model.derive(**f); self.creation(f, result)
        reads = [e for e in result['memory_events'] if e.get('coordinate') == SP-20 and e['operation'] == 'read16']
        self.assertEqual(reads[0]['bytes'], (8, 0))

    def test_predicate_save_alias_changes_later_byte_observation(self):
        f = fixture(obj=SP-56-704)
        result = model.derive(**f); self.creation(f, result)
        reads = [e for e in result['memory_events'] if e.get('coordinate') == SP-56 and e['operation'] == 'read8']
        self.assertEqual(reads[0]['bytes'], (5,))

    def test_stale_nested_save_alias_is_not_live_object_storage(self):
        f = fixture(obj=SP-64-704)
        result = model.derive(**f)
        self.assertEqual(result['boundary']['site'], at(f['layout'], 'byte_load', 6))
        self.assertIn('retired', result['boundary']['reason'])

    def test_fresh_phase256_null_continuation_reuses_real_retired_frames(self):
        l, f, prefix = prefix_fixture()
        self.assertEqual(prefix['final_PC'], at(l, 'helper'))
        result = model.continue_from_phase256(l, prefix, f['arena_base'], selector=model.SELECTOR)
        self.assertTrue(result['conditional_helper_return'])
        self.assertEqual(result['prefix_calls_remaining'], [])
        direct = dict(layout=l, arena_base=f['arena_base'], registers=prefix['registers'],
                      cells={int(k): v for k, v in prefix['post_cells'].items()})
        self.assert_raw(direct, result)

    def test_fresh_phase256_creation_preserves_real_parent_argument(self):
        l, f, prefix = prefix_fixture(flags=8)
        result = model.continue_from_phase256(l, prefix, f['arena_base'], selector=model.SELECTOR)
        direct = dict(layout=l, arena_base=f['arena_base'], registers=prefix['registers'],
                      cells={int(k): v for k, v in prefix['post_cells'].items()})
        self.creation(direct, result)
        self.assertEqual(result['registers'][3], prefix['registers'][6])

    def test_freed_prefix_payload_remains_unavailable_in_helper(self):
        l, f, prefix = prefix_fixture(released=True)
        self.assertEqual(prefix['final_PC'], at(l, 'helper'))
        result = model.continue_from_phase256(l, prefix, f['arena_base'], selector=model.SELECTOR)
        self.assertEqual(result['boundary']['site'], at(l, 'predicate', 8))
        self.assertIn('unavailable', result['boundary']['reason'])
        self.assertEqual(result['unavailable_spans'], ((support.NODE, support.NODE+128),))

    def test_changed_prefix_owner_pin_cannot_bind_old_state(self):
        l, f, prefix = prefix_fixture(); prefix = copy.deepcopy(prefix)
        prefix['complete_owner_pins'][0]['sha256'] = '0'*64
        with self.assertRaises(ValueError):
            model.continue_from_phase256(l, prefix, f['arena_base'], selector=model.SELECTOR)

    def test_changed_pending_sp_does_not_supply_parent_call_relation(self):
        l, f, prefix = prefix_fixture(); prefix['pending_calls'][-1]['entry_sp'] += 4
        with self.assertRaises(ValueError):
            model.continue_from_phase256(l, prefix, f['arena_base'], selector=model.SELECTOR)

    def test_complete_owner_mutation_and_wrong_direct_edge_are_refused(self):
        l = layout()
        for offset in (0, 4):
            owners = list(l.owners); index = next(i for i, row in enumerate(owners) if row[0] == 'predicate')
            name, a, body = owners[index]; changed = bytearray(body); changed[offset] ^= 1
            owners[index] = name, a, bytes(changed)
            with self.assertRaises(ValueError):
                model.bind(l.prior, tuple(owners), selector=model.SELECTOR)

    def test_duplicate_roles_and_prior_overlap_are_refused(self):
        l = layout(); rows = list(l.owners); rows[1] = rows[0]
        with self.assertRaises(ValueError):
            model.bind(l.prior, tuple(rows), selector=model.SELECTOR)
        owners = tuple((name, at(l, 'helper') if name == 'identity' else a, body) for name, a, body in l.owners)
        with self.assertRaises(ValueError):
            model.bind(l.prior, owners, selector=model.SELECTOR)

    def test_selector_is_explicit_and_budget_exhaustion_keeps_boundary(self):
        f = fixture()
        with self.assertRaises(ValueError):
            model.derive(**dict(f, selector=''))
        result = model.derive(**dict(f, max_steps=1))
        self.assertIn('budget exhausted', result['boundary']['reason'])
        self.assertFalse(result['conditional_helper_return'])

    def test_unaligned_object_and_numeric_pointer_wrap_are_refused(self):
        f = fixture(obj=OBJECT+1); result = model.derive(**f)
        self.assertIn('unaligned', result['boundary']['reason'])
        f = fixture()
        # A positive base with a near-maximum coordinate cannot wrap the byte-load address.
        f['registers'][0] = P(2**31-512)
        support.half(f['cells'], 2**31-508, 0)
        result = model.derive(**f)
        self.assertIn('wraps', result['boundary']['reason'])

    def test_entry_lr_requires_the_bound_parent_call(self):
        f = fixture(); f['registers'][14] = I(0x08000001)
        result = model.derive(**f)
        self.assertIn('entry LR', result['boundary']['reason'])
        self.assertEqual(result['memory_events'], [])
