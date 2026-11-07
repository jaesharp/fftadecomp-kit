"""Fresh byte-transport, exposure, alias and frame compositions only."""
from pathlib import Path
import hashlib
import unittest

import scheduler_copy_state as copy
import scheduler_allocator_state as state
import allocator_wrapper_relation as wrapper
import allocator_split_relation as split
import allocator_insert_relation as insert
import allocator_search_relation as search
import allocator_remove_relation as remove

INPUTS = Path(__file__).resolve().parents[1]/'inputs'
Z12 = (INPUTS/'retained-zero12.json').read_bytes()
Z92 = (INPUTS/'retained-zero92.json').read_bytes()
CALLBACK = 0x080e5f51
E = -256
SCHEDULER = 1536
DESCRIPTOR = 1200


def digest(data):
    return hashlib.sha256(data).hexdigest()


def layout():
    # Reconstruct synthetic retained identities, with no old bind invocation.
    a = 0x08030000
    sl = search.Layout(a+0x3000, digest(search.SHAPE))
    r, m, i, c, w, t, cb = [a+n*0x1000 for n in [4,5,6,2,1,7,8]]
    ml = remove.Layout(r, m, digest(remove.REMOVE_HEAD+remove._bl(r+124,m)+remove.REMOVE_TAIL), digest(remove.MEDIAN))
    ib = insert.HEAD+remove._bl(i+22,sl.address)+insert.MIDDLE+remove._bl(i+138,m)+insert.TAIL
    il = insert.Layout(i, digest(ib), sl, ml)
    al = split.Layout(c, digest(split._encoded(c,il,t,0x08300000)), il, t, 0x08300000)
    wl = wrapper.Layout(w, digest(wrapper.HEAD+remove._bl(w+34,c)+wrapper.TAIL), al)
    return state.Layout(a, digest(state._encoded(a,wl,cb)), wl, cb)


def half(cells, at, value):
    cells[at] = value & 255
    cells[at+1] = value >> 8 & 255


def pointer(cells, at, value):
    cells.update({at+i: 0 if value is None else ('base-plus-byte',value,i) for i in range(4)})


def fixture(*, descriptor=DESCRIPTOR, parent=None, phase=29, chain=()):
    cells = {}
    for at,value in [(0,32),(2,32),(4,1),(130,0),(134,43),(136,0),(138,0)]:
        half(cells,at,value)
    pointer(cells,E,parent)
    pointer(cells,SCHEDULER,0)
    pointer(cells,SCHEDULER+4,None)
    half(cells,SCHEDULER+12,phase)
    pointer(cells,SCHEDULER+4 if parent is None else parent+16,chain[0] if chain else None)
    for n,node in enumerate(chain):pointer(cells,node+8,chain[n+1] if n+1<len(chain) else None)
    for i in range(28):cells[descriptor+i] = ('opaque-byte','copy-state-new-source',i)
    half(cells,descriptor+20,158)
    half(cells,descriptor+22,1)
    return cells


def ambient():
    return {10: copy._pointer(DESCRIPTOR), 11: copy._pointer(E-56),
            12: tuple(('opaque-byte','ambient incoming R12',i) for i in range(4))}


def run(cells=None, *, descriptor=DESCRIPTOR, callback=CALLBACK, **kwargs):
    options = dict(selector=copy.SELECTOR,zero12_receipt=Z12,zero92_receipt=Z92,
                   observed_zero_target=0x03005e79)
    options.update(kwargs)
    return copy.derive(layout(),64,fixture() if cells is None else cells,SCHEDULER,descriptor,
                       callback,E,ambient(),**options)


def raw_suffix(report, cells):
    """Independent Thumb suffix interpreter; prefix report is consumed once."""
    p = report['prefix']
    memory = dict(cells)
    memory.update({int(k):v for k,v in p['changed_cells'].items()})
    r = dict(ambient())
    def word(value):
        if type(value) is int:return copy._constant(value)
        if value[0]=='base-plus':return copy._pointer(value[1])
        return tuple(('opaque-byte',value[1],i) for i in range(4))
    for name,value in p['conditional_cutpoint_registers'].items():
        r[13 if name=='SP' else int(name[1:])] = copy._pointer(value) if name=='SP' else word(value)
    def address(reg):
        value=r[reg]
        assert all(value[i]==('base-plus-byte',value[0][1],i) for i in range(4))
        return value[0][1]
    b=state._encoded(layout().address,layout().allocator,layout().callback_thunk)
    events=[]
    for offset in range(154,180,2):
        op=int.from_bytes(b[offset:offset+2],'little');site=layout().address+offset
        if op&0xff00==0x4600:
            src=(op>>3)&15;dst=(op&7)|((op>>4)&8);r[dst]=r[src]
        elif op&0xf800==0x2000:r[(op>>8)&7]=copy._constant(op&255)
        elif op&0xf000==0xc000:
            base=(op>>8)&7;regs=[i for i in range(8) if op&(1<<i)];start=address(base)
            values=[tuple(memory[start+4*j+i] for i in range(4)) for j in range(len(regs))] if op&0x0800 else [r[i] for i in regs]
            for j,(reg,value) in enumerate(zip(regs,values)):
                at=start+4*j
                if op&0x0800:r[reg]=value
                else:memory.update({at+i:v for i,v in enumerate(value)})
                events.append(dict(site=site,operation='read32' if op&0x0800 else 'write32',coordinate=at,bytes=value))
            r[base]=copy._pointer(start+4*len(regs))
        elif op&0xf800 in [0x6000,0x6800]:
            reg=op&7;base=(op>>3)&7;at=address(base)+4*((op>>6)&31)
            if op&0x0800:r[reg]=tuple(memory[at+i] for i in range(4))
            else:memory.update({at+i:v for i,v in enumerate(r[reg])})
            events.append(dict(site=site,operation='read32' if op&0x0800 else 'write32',coordinate=at,bytes=r[reg]))
        elif op&0xf800==0x8000:
            reg=op&7;at=address((op>>3)&7)+2*((op>>6)&31)
            memory.update({at+i:r[reg][i] for i in range(2)})
            events.append(dict(site=site,operation='write16',coordinate=at,value=r[reg][0]|r[reg][1]<<8))
        elif op&0xfe00==0x1c00:
            assert (op>>6)&7==0
            r[op&7]=r[(op>>3)&7]
        else:raise AssertionError(hex(op))
    r[14]=copy._constant((layout().address+184)|1)
    return r,memory,events


class TransportTests(unittest.TestCase):
    def test_concrete_copy_preserves_26bytes_and_zeroes_only_phase(self):
        source=tuple(range(28));r=copy._transport(source)
        self.assertEqual(r['bytes'],(0,0)+source[2:])
        self.assertEqual((r['R4'],r['R5']),(source[16:20],source[20:24]))

    def test_unique_opaque_indices_are_not_reduced_modulo_word_width(self):
        source=tuple(('opaque-byte','long source origin',1000+i) for i in range(28))
        self.assertEqual(copy._transport(source)['bytes'],(0,0)+source[2:])

    def test_repeated_origins_and_colliding_debug_names_keep_exact_identity(self):
        source=tuple(('opaque-byte','transport-byte:0',i%5) for i in range(28))
        self.assertEqual(copy._transport(source)['bytes'][2:],source[2:])

    def test_payload_pointer_words_transport_without_access_permission(self):
        source=list(range(28));source[4:8]=copy._pointer(0x7fffffff)
        self.assertEqual(copy._transport(tuple(source))['bytes'][4:8],tuple(source[4:8]))

    def test_partial_payload_pointer_stays_partial_not_numeric(self):
        source=list(range(28));source[18]=('base-plus-byte',-4000,2)
        got=copy._transport(tuple(source))['R4']
        self.assertEqual(copy.observe(got)['kind'],'opaque-or-partial')

    def test_phase_pointer_overwrite_retains_old_refusal(self):
        for lane in range(4):
            source=list(range(28));source[lane]=('base-plus-byte',400,lane)
            with self.subTest(lane=lane),self.assertRaisesRegex(ValueError,'partial pointer overwrite'):
                copy._transport(tuple(source))

    def test_missing_byte_does_not_become_unknown_initialization(self):
        source=list(range(28));source[9]=None
        with self.assertRaisesRegex(ValueError,'complete 28'):copy._transport(tuple(source))

    def test_bool_and_mutable_byte_atoms_refuse(self):
        for value in [True,['opaque-byte','x',0],('opaque-byte','',0),256]:
            source=list(range(28));source[4]=value
            with self.subTest(value=value),self.assertRaises(ValueError):copy._transport(tuple(source))

    def test_transport_has_exact_retained_read_write_offsets(self):
        r=copy._transport(tuple(range(28)))
        self.assertEqual(r['shadow_reads'],[-28,-24,-20,-16,-12,-8,-4,-56])
        self.assertEqual(r['shadow_writes'],[-56,-52,-48,-44,-40,-36,-32,-56])

    def test_observe_constant_does_not_confer_function_identity(self):
        self.assertEqual(copy.observe(copy._constant(CALLBACK)),dict(kind='constant',value=CALLBACK))

    def test_observe_requires_lane_order_for_pointer(self):
        value=copy._pointer(140)
        self.assertEqual(copy.observe(value),dict(kind='base-plus',coordinate=140))
        self.assertEqual(copy.observe(value[::-1])['kind'],'opaque-or-partial')

    def test_observe_missing_word_refuses(self):
        with self.assertRaises(ValueError):copy.observe((0,0,0))


class CompositionTests(unittest.TestCase):
    def test_new_empty_list_exposes_tag_option_and_distinct_phases(self):
        r=run();self.assertTrue(r['reaches_callback_thunk'],r['boundary'])
        self.assertEqual((r['descriptor_phase_under_conditions'],r['scheduler_phase_under_conditions']),(0,29))
        self.assertEqual(r['descriptor_bytes'][20:24],(158,0,1,0))
        self.assertEqual(r['callback_word_observation'],dict(kind='constant',value=CALLBACK))
        self.assertFalse(r['actual_observed_phase_proved']);self.assertFalse(r['native_admission'])

    def test_register_clobbers_and_all_ambient_aliases_survive(self):
        cells=fixture(phase=31);r=run(cells);regs=r['callback_registers']
        self.assertEqual(regs[4],tuple(cells[DESCRIPTOR+i] for i in range(16,20)))
        self.assertEqual(regs[5],(158,0,1,0))
        self.assertEqual({k:regs[k] for k in [10,11,12]},ambient())
        self.assertEqual(set(regs),set(range(15)))
        self.assertEqual((regs[0],regs[1],regs[2]),(copy._pointer(140),copy._pointer(E-56),copy._pointer(164)))

    def test_post_zero_descriptor_alias_uses_new_bytes(self):
        cells=fixture(descriptor=176,phase=37);r=run(cells,descriptor=176)
        self.assertTrue(r['reaches_callback_thunk'],r['boundary']);self.assertEqual(r['descriptor_bytes'],(0,)*28)

    def test_parent_list_alias_replaces_callback_identity(self):
        cells=fixture(parent=124,phase=41);r=run(cells,callback=0)
        self.assertTrue(r['reaches_callback_thunk'],r['boundary'])
        self.assertEqual(r['callback_word_observation'],dict(kind='base-plus',coordinate=140))
        self.assertEqual(r['callback_registers'][8],(0,)*4)
        self.assertEqual(r['callback_registers'][3],copy._pointer(140))
        self.assertFalse(r['actual_callback_target_proved'])

    def test_opaque_callback_word_remains_opaque(self):
        r=run(fixture(phase=43),callback=('word-origin','unknown actual callback'))
        self.assertTrue(r['reaches_callback_thunk'],r['boundary'])
        self.assertEqual(r['callback_word_observation']['kind'],'opaque-or-partial')

    def test_source_own_frame_refuses_stale_byte_copy(self):
        cells=fixture(descriptor=E-40,phase=47);r=run(cells,descriptor=E-40)
        self.assertFalse(r['reaches_callback_thunk']);self.assertIn('unmodeled private-frame',r['boundary']['reason'])
        self.assertEqual(r['copy_events'],[])

    def test_source_expired_nested_frame_is_still_refused(self):
        cells=fixture(descriptor=E-124,phase=53);r=run(cells,descriptor=E-124)
        self.assertFalse(r['reaches_callback_thunk']);self.assertIn('unmodeled private-frame',r['boundary']['reason'])

    def test_source_protected_caller_span_refuses(self):
        r=run(fixture(phase=59),protected_spans=((DESCRIPTOR+4,DESCRIPTOR+8),))
        self.assertFalse(r['reaches_callback_thunk']);self.assertIn('descriptor source overlaps protected',r['boundary']['reason'])

    def test_copy_destination_external_protection_refuses(self):
        r=run(fixture(phase=61),protected_spans=((E-52,E-48),))
        self.assertFalse(r['reaches_callback_thunk']);self.assertIn('descriptor destination overlaps protected',r['boundary']['reason'])

    def test_missing_source_byte_refuses_at_copy_boundary(self):
        cells=fixture(phase=67);del cells[DESCRIPTOR+17];r=run(cells)
        self.assertFalse(r['reaches_callback_thunk']);self.assertEqual(r['boundary']['site'],layout().address+158)

    def test_prior_list_refusal_is_retained_without_copy(self):
        cells=fixture(phase=71,chain=(960,));pointer(cells,968,960);r=run(cells)
        self.assertFalse(r['reaches_callback_thunk']);self.assertIn('cycle',r['boundary']['reason'])
        self.assertEqual(r['copy_events'],[])

    def test_selector_cannot_be_implicit(self):
        with self.assertRaisesRegex(ValueError,'explicit'):run(selector='default')

    def test_missing_ambient_register_cannot_hide_live_alias(self):
        with self.assertRaisesRegex(ValueError,'ambient'):
            copy.derive(layout(),64,fixture(phase=73),SCHEDULER,DESCRIPTOR,CALLBACK,E,{10:copy._constant(0)},selector=copy.SELECTOR)

    def test_copy_first_word_pointer_refuses_after_prefix(self):
        cells=fixture(phase=79);pointer(cells,DESCRIPTOR,896);r=run(cells)
        self.assertTrue(r['prefix']['reaches_copy_cutpoint']);self.assertFalse(r['reaches_callback_thunk'])
        self.assertIn('partial pointer overwrite',r['boundary']['reason'])

    def test_read_callback_slot_occurs_after_phase_zero_store(self):
        r=run(fixture(phase=83));events=r['copy_events']
        self.assertEqual([(e['site']-layout().address,e['operation']) for e in events[-2:]],[(174,'write16'),(176,'read32')])
        self.assertEqual(len(events),16)

    def test_independent_raw_suffix_four_new_composed_states(self):
        for n,(phase,parent,chain,callback) in enumerate([(89,None,(),CALLBACK+4),(97,880,(),CALLBACK+8),
                                                       (101,None,(992,1040),CALLBACK+12),(103,124,(),0)]):
            with self.subTest(n=n):
                cells=fixture(phase=phase,parent=parent,chain=chain)
                for i in range(16,20):cells[DESCRIPTOR+i]=(n*71+i)&255
                r=run(cells,callback=callback);self.assertTrue(r['reaches_callback_thunk'],r['boundary'])
                regs,memory,events=raw_suffix(r,cells)
                self.assertEqual(regs,r['callback_registers'])
                self.assertEqual(tuple(memory[E-56+i] for i in range(28)),r['descriptor_bytes'])
                self.assertEqual(events,r['copy_events'])


class DispatchBoundaryTests(unittest.TestCase):
    def test_null_target_reaches_thunk_without_callback_execution(self):
        r=run(fixture(phase=107),callback=0)
        self.assertTrue(r['reaches_callback_thunk'],r['boundary'])
        self.assertFalse(r['callback_entry_reached'])
        self.assertEqual(r['callback_word_observation'],dict(kind='constant',value=0))

    def test_even_target_does_not_invent_thumb_or_arm_contract(self):
        r=run(fixture(phase=109),callback=0x080e5f50)
        self.assertTrue(r['reaches_callback_thunk'],r['boundary'])
        self.assertFalse(r['callback_entry_reached']);self.assertFalse(r['actual_callback_target_proved'])

    def test_numeric_thumb_word_is_not_itself_executable_identity(self):
        r=run(fixture(phase=113),callback=0x080e5f61)
        self.assertTrue(r['reaches_callback_thunk'],r['boundary'])
        self.assertFalse(r['callback_entry_reached']);self.assertFalse(r['callback_effects_closed'])
        self.assertEqual(r['descriptor_phase_under_conditions'],0)


if __name__=='__main__':unittest.main()
