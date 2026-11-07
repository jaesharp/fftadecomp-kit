"""New count112 allocation/copy states and the additional twenty-byte aliases."""
import hashlib
import json
from pathlib import Path
import unittest

import scheduler_allocator_state as state
import scheduler_copy_state as copy
from test_scheduler_copy_state import layout

INPUTS = Path(__file__).resolve().parents[1] / 'inputs'
Z12 = (INPUTS / 'retained-zero12.json').read_bytes()
Z92 = (INPUTS / 'retained-zero92.json').read_bytes()
Z112 = (INPUTS / 'retained-zero112.json').read_bytes()
E, S, D, NODE, CALLBACK = -768, 2000, 1600, 140, 0x080FDB99


def half(cells, at, value):
    cells.update({at+i: (value >> (8*i)) & 255 for i in range(2)})


def pointer(cells, at, value):
    cells.update({at+i: 0 if value is None else ('base-plus-byte', value, i) for i in range(4)})


def fixture(phase, *, descriptor=D, parent=None, chain=(), block=61):
    cells = {}
    for at, value in [(0,32), (2,32), (4,1), (130,0), (134,block), (136,0), (138,0)]:
        half(cells, at, value)
    pointer(cells, E, parent)
    pointer(cells, S, 0)
    pointer(cells, S+4, None)
    half(cells, S+12, phase)
    pointer(cells, S+4 if parent is None else parent+16, chain[0] if chain else None)
    for i, node in enumerate(chain):
        pointer(cells, node+8, chain[i+1] if i+1 < len(chain) else None)
    for i in range(28):
        cells[descriptor+i] = ('opaque-byte', 'count112 descriptor '+str(phase), i)
    return cells


def run(phase, *, size=84, descriptor=D, copied=False, cells=None, **options):
    cells = fixture(phase, descriptor=descriptor) if cells is None else cells
    kw = dict(selector=copy.SELECTOR if copied else state.SELECTOR,
              zero12_receipt=Z12, zero92_receipt=Z92, zero112_receipt=Z112,
              observed_zero_target=0x03005E79)
    kw.update(options)
    args = (layout(), size, cells, S, descriptor, CALLBACK, E)
    if copied:
        ambient = {i: tuple(('opaque-byte', 'count112 ambient '+str(i), j) for j in range(4))
                   for i in (10,11,12)}
        return copy.derive(*args, ambient, **kw)
    return state.derive(*args, **kw)


def writes(report):
    return [e for e in report['memory_events'] if e.get('origin') == 'retained direct count112 effect']


class Zero112Tests(unittest.TestCase):
    def test_certificate_has_exact_new_count_and_no_admission_authority(self):
        r = json.loads(Z112)
        self.assertEqual(hashlib.sha256(Z112).hexdigest(), state.ZERO112_SHA256)
        self.assertEqual((r['count'], r['zero_write_span'], r['private_save_span']), (112,[0,112],[-4,0]))
        self.assertEqual(r['image_sha256'], json.loads(Z92)['image_sha256'])
        for key in ('installed_identity_proved', 'allocator_or_memory_permissions_proved',
                    'actual_caller_count_proved', 'source_or_native_admission'):
            self.assertIs(r[key], False)

    def test_certificate_all_alignments_cover_each_destination_byte_once(self):
        cases = json.loads(Z112)['alignment_cases']
        self.assertEqual([r['alignment'] for r in cases], [0,1,2,3])
        for r in cases:
            offsets = [i for region, at, width in r['writes'] if region == 'destination'
                       for i in range(at,at+width)]
            self.assertEqual(offsets, list(range(112)))
            self.assertEqual(r['reads'], [['stack',-4,4]])
            self.assertTrue(r['protected_return'] and r['SP_restored'])

    def test_default_path_refuses112_at_direct_zero_after_allocator(self):
        r = run(71, zero112_receipt=None)
        self.assertFalse(r['reaches_copy_cutpoint'])
        self.assertTrue(r['allocator_relation']['returns_under_witness'])
        self.assertEqual(r['boundary']['site'], layout().address+48)
        self.assertIn('count92', r['boundary']['reason'])
        self.assertEqual(writes(r), [])

    def test_changed_certificate_bytes_refuse_before_any112_write(self):
        r = run(72, zero112_receipt=Z112+b' ')
        self.assertIn('certificate', r['boundary']['reason'])
        self.assertEqual(writes(r), [])

    def test_92_certificate_cannot_be_substituted_for112(self):
        r = run(73, zero112_receipt=Z92)
        self.assertFalse(r['reaches_copy_cutpoint'])
        self.assertIn('count112 zero certificate', r['boundary']['reason'])

    def test_explicit112_effect_refuses_a_different_actual_count(self):
        r = run(74, size=88)
        self.assertEqual(r['count'], 116)
        self.assertIn('differs from retained count112', r['boundary']['reason'])
        self.assertEqual(writes(r), [])

    def test_112_opt_in_does_not_silently_fall_back_to92(self):
        r = run(75, size=64)
        self.assertEqual(r['count'], 92)
        self.assertIn('count112', r['boundary']['reason'])

    def test_scheduler_size_uses_actual_low16_bits(self):
        r = run(76, size=0xD00D0054)
        self.assertTrue(r['reaches_copy_cutpoint'], r['boundary'])
        self.assertEqual(r['count'], 112)
        self.assertEqual([e['coordinate'] for e in writes(r)], list(range(NODE,NODE+112,4)))

    def test_full112_zero_then_callback_phase_and_global_head(self):
        r = run(77)
        self.assertTrue(r['reaches_copy_cutpoint'], r['boundary'])
        self.assertEqual(r['allocation'], NODE)
        out = {int(k):v for k,v in r['changed_cells'].items()}
        self.assertEqual(tuple(out[S+4+i] for i in range(4)), copy._pointer(NODE))
        self.assertEqual(tuple(out[NODE+i] for i in range(4)), copy._constant(CALLBACK))
        self.assertEqual((out[NODE+22],out[NODE+23]), (77,0))
        self.assertEqual([out[NODE+i] for i in range(92,112)], [0]*20)
        self.assertFalse(r['installed_identity_proved'] or r['physical_access_proved'])

    def test_real_parent_head_and_parent_slot_are_written_after_zero(self):
        r = run(78, cells=fixture(78, parent=900))
        self.assertTrue(r['reaches_copy_cutpoint'], r['boundary'])
        out = {int(k):v for k,v in r['changed_cells'].items()}
        self.assertEqual(tuple(out[916+i] for i in range(4)), copy._pointer(NODE))
        self.assertEqual(tuple(out[NODE+12+i] for i in range(4)), copy._pointer(900))

    def test_chain_tail_retains_actual_pointer_reload_order(self):
        r = run(79, cells=fixture(79, chain=(700,760)))
        self.assertTrue(r['reaches_copy_cutpoint'], r['boundary'])
        self.assertEqual(r['visited_nodes'], [700,760])
        self.assertEqual([e['coordinate'] for e in r['memory_events']
                          if e.get('role') in ('initial next test','loop advance reload','loop next test')],
                         [708,708,768])

    def test_descriptor_in_new_twenty_bytes_observes_zero_and_remaining_origins(self):
        at = NODE+92
        r = run(80, descriptor=at, cells=fixture(80, descriptor=at, block=28))
        self.assertTrue(r['reaches_copy_cutpoint'], r['boundary'])
        self.assertEqual(r['descriptor_snapshot'][:20], [0]*20)
        self.assertEqual(r['descriptor_snapshot'][20:], [('opaque-byte','count112 descriptor 80',i) for i in range(20,28)])

    def test_protected_new_tail_byte_refuses_before_all_direct_zero_stores(self):
        r = run(81, protected_spans=((NODE+108,NODE+109),))
        self.assertFalse(r['reaches_copy_cutpoint'])
        self.assertEqual(r['boundary']['site'], layout().address+48)
        self.assertIn('protected', r['boundary']['reason'])
        self.assertEqual(writes(r), [])

    def test_descriptor_copy112_preserves_unknown_payload_and_exposes_real_callback(self):
        r = run(82, copied=True)
        self.assertTrue(r['reaches_callback_thunk'], r['boundary'])
        self.assertEqual(r['prefix']['count'], 112)
        self.assertEqual(r['descriptor_bytes'], (0,0)+tuple(('opaque-byte','count112 descriptor 82',i) for i in range(2,28)))
        self.assertEqual(r['observed_callback_word'], copy._constant(CALLBACK))
        self.assertEqual(r['callback_registers'][2], copy._pointer(NODE+24))
        self.assertFalse(r['callback_entry_reached'] or r['actual_callback_target_proved'])

    def test_copy_consumes_new_tail_zero_alias_instead_of_original_source(self):
        r = run(83, descriptor=NODE+92, copied=True,
                cells=fixture(83, descriptor=NODE+92, block=28))
        self.assertTrue(r['reaches_callback_thunk'], r['boundary'])
        self.assertEqual(r['descriptor_bytes'][:20], (0,)*20)
        self.assertEqual(r['descriptor_bytes'][20:], tuple(('opaque-byte','count112 descriptor 83',i) for i in range(20,28)))

    def test_copy_requires_explicit112_receipt_too(self):
        r = run(84, copied=True, zero112_receipt=None)
        self.assertFalse(r['reaches_callback_thunk'])
        self.assertIn('count92', r['boundary']['reason'])
        self.assertIsNone(r['callback_registers'])

    def test_copy_retains_all_ambient_register_origins(self):
        r = run(85, copied=True)
        self.assertTrue(r['reaches_callback_thunk'], r['boundary'])
        for i in (10,11,12):
            self.assertEqual(r['callback_registers'][i], tuple(('opaque-byte','count112 ambient '+str(i),j) for j in range(4)))

    def test_small_block_null_result_never_becomes_writable112_span(self):
        r = run(86, cells=fixture(86, block=27))
        self.assertFalse(r['reaches_copy_cutpoint'])
        self.assertIn('destination is null', r['boundary']['reason'])
        self.assertEqual(writes(r), [])

    def test_direct_effect_rejects_wrong_thumb_target_before_mutating_arena(self):
        m = state._Arena({600:93}, (), (-900,-768))
        with self.assertRaises(state.remove._Boundary):
            state._zero112(m,Z112,0x03005E78,112,400,-840,0x08030030)
        self.assertEqual(m.cells, {600:93})
        self.assertEqual(m.events, [])

    def test_direct_effect_private_save_protection_precedes_destination_writes(self):
        m = state._Arena({601:94}, ((-844,-840),), (-900,-768))
        with self.assertRaises(state.remove._Boundary):
            state._zero112(m,Z112,0x03005E79,112,404,-840,0x08030030)
        self.assertEqual(m.cells, {601:94})
        self.assertEqual(m.events, [])

    def test_direct_zero_cannot_reuse_unmodeled_scheduler_frame_as_destination(self):
        m = state._Arena({}, (), (-900,-768))
        with self.assertRaises(state.remove._Boundary):
            state._zero112(m,Z112,0x03005E79,112,-820,-840,0x08030030)
        self.assertEqual(m.cells, {})

    def test_untouched_bytes_beyond112_are_never_initialized(self):
        cells = fixture(87, block=28)
        cells[NODE+112] = ('opaque-byte','outside zero112',0)
        r = run(87, cells=cells)
        self.assertTrue(r['reaches_copy_cutpoint'], r['boundary'])
        self.assertNotIn(str(NODE+112), r['changed_cells'])
        self.assertEqual(cells[NODE+112], ('opaque-byte','outside zero112',0))
