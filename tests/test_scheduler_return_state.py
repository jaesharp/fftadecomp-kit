"""New postcallback return/frame/alias states; no old proof executions."""
from dataclasses import replace
import hashlib
import unittest

import scheduler_return_state as ret
import scheduler_allocator_state as state
import scheduler_copy_state as words
import allocator_wrapper_relation as wrapper
import allocator_split_relation as split
import allocator_insert_relation as insert
import allocator_search_relation as search
import allocator_remove_relation as remove

BASE=0x02000000
POINT=0x02008ff0
E=1024
ALLOCATION=4096
SCHEDULER=6144


def sha(data):return hashlib.sha256(data).hexdigest()


def state_layout():
    a=0x08050000
    s,r,m,i,c,w,t,cb=[a+n*0x1000 for n in [3,4,5,6,2,1,7,8]]
    sl=search.Layout(s,sha(search.SHAPE))
    ml=remove.Layout(r,m,sha(remove.REMOVE_HEAD+remove._bl(r+124,m)+remove.REMOVE_TAIL),sha(remove.MEDIAN))
    il=insert.Layout(i,sha(insert.HEAD+remove._bl(i+22,s)+insert.MIDDLE+remove._bl(i+138,m)+insert.TAIL),sl,ml)
    al=split.Layout(c,sha(split._encoded(c,il,t,0x08304000)),il,t,0x08304000)
    wl=wrapper.Layout(w,sha(wrapper.HEAD+remove._bl(w+34,c)+wrapper.TAIL),al)
    return state.Layout(a,sha(state._encoded(a,wl,cb)),wl,cb)


def layout(w=0x0804f000,point=POINT):
    s=state_layout();data=ret._wrapper(w,s,point)
    return ret.Layout(w,sha(data),point,s)


def opaque(label):return tuple(('opaque-byte',label,i) for i in range(4))


def put(cells,at,value):cells.update({at+i:v for i,v in enumerate(value)})


def fixture(*,phase=0x1234,allocation=ALLOCATION,scheduler=SCHEDULER,e=E,base=BASE):
    l=layout()
    entry={r:opaque('entry R'+str(r)) for r in list(range(13))+[14]}
    entry.update({0:words._constant(0x080e5f51),1:words._constant(64),2:words._pointer(e+32)})
    post={r:opaque('post R'+str(r)) for r in range(15)}
    post.update({7:words._pointer(allocation),10:words._pointer(e-80),11:words._pointer(e+32),13:words._pointer(e-80)})
    cells={}
    for at,value in ret._saved(l,entry,e).items():put(cells,at,value)
    put(cells,POINT-base,words._pointer(scheduler))
    cells[scheduler+12]=phase&255;cells[scheduler+13]=phase>>8&255
    return dict(layout=l,arena_base=base,entry_sp=e,allocation_offset=allocation,
                entry_registers=entry,post_registers=post,post_cells=cells,selector=ret.SELECTOR)


def run(**kw):return ret.derive(**kw)


def raw_continuation(f):
    """Independent instruction interpreter for both exact suffixes."""
    l=f['layout'];r=dict(f['post_registers']);memory=dict(f['post_cells']);events=[]
    def numeric(word):
        assert all(type(b)is int for b in word)
        return sum(b<<(8*i) for i,b in enumerate(word))
    def coordinate(reg):
        value=r[reg]
        if all(type(b)is int for b in value):return numeric(value)-f['arena_base']
        assert value==words._pointer(value[0][1]);return value[0][1]
    def load(at,width):
        value=tuple(memory[at+i] for i in range(width))
        return value if width==4 else words._constant(value[0]|value[1]<<8)
    cb=state._encoded(l.callee.address,l.callee.allocator,l.callee.callback_thunk)
    wb=ret._wrapper(l.wrapper,l.callee,l.scheduler_point)
    sequences=[(l.callee.address,cb,184,206),(l.wrapper,wb,34,56)]
    for owner,body,start,end in sequences:
        for offset in range(start,end,2):
            op=int.from_bytes(body[offset:offset+2],'little');site=owner+offset
            if op&0xf800==0x2000:r[(op>>8)&7]=words._constant(op&255)
            elif op&0xf800==0x0000:
                r[op&7]=words._constant(numeric(r[(op>>3)&7])<<((op>>6)&31)&0xffffffff)
            elif op&0xf800==0x8000:
                at=coordinate((op>>3)&7)+2*((op>>6)&31);value=numeric(r[op&7])&65535
                memory[at]=value&255;memory[at+1]=value>>8
                events.append((site,'write16',at,value))
            elif op&0xfe00==0x1c00:
                assert (op>>6)&7==0;r[op&7]=r[(op>>3)&7]
            elif op&0xff80==0xb000:r[13]=words._pointer(coordinate(13)+4*(op&127))
            elif op&0xff00==0xbc00:
                nums=[n for n in range(8) if op&(1<<n)];at=coordinate(13)
                for i,n in enumerate(nums):
                    r[n]=load(at+4*i,4);events.append((site,'read32',at+4*i,r[n]))
                r[13]=words._pointer(at+4*len(nums))
            elif op&0xff00==0x4600:r[(op&7)|((op>>4)&8)]=r[(op>>3)&15]
            elif op&0xf800==0x6800:
                at=coordinate((op>>3)&7)+4*((op>>6)&31);r[op&7]=load(at,4);events.append((site,'read32',at,r[op&7]))
            elif op&0xf800==0x8800:
                at=coordinate((op>>3)&7)+2*((op>>6)&31);r[op&7]=load(at,2);events.append((site,'read16',at,numeric(r[op&7])))
            elif op&0xffc0==0x4040:r[op&7]=words._constant(numeric(r[op&7])^numeric(r[(op>>3)&7]))
            elif op&0xff87==0x4700:
                if owner==l.callee.address:assert r[(op>>3)&15]==words._constant((l.wrapper+34)|1)
                else:assert r[(op>>3)&15]==f['entry_registers'][14]
            else:raise AssertionError(hex(op))
    return r,memory,events


class BindingTests(unittest.TestCase):
    def test_new_complete_wrapper_bind_reuses_saved_state_without_oldbind(self):
        l=layout();got=ret.bind(ret._wrapper(l.wrapper,l.callee,l.scheduler_point),l.wrapper,27,l.callee,selector=ret.SELECTOR)
        self.assertEqual(got,l)

    def test_actual_count_extent_and_instruction_mutations_refuse(self):
        l=layout();b=ret._wrapper(l.wrapper,l.callee,l.scheduler_point)
        for at in [0,18,30,34,36,40,42,54]:
            changed=bytearray(b);changed[at]^=1
            with self.subTest(at=at),self.assertRaises(ValueError):ret.bind(bytes(changed),l.wrapper,27,l.callee,selector=ret.SELECTOR)
        for body,count in [(b[:-2],27),(b,28),(b,True)]:
            with self.subTest(count=count),self.assertRaises(ValueError):ret.bind(body,l.wrapper,count,l.callee,selector=ret.SELECTOR)

    def test_relocated_wrapper_and_distinct_aligned_point_bind_generically(self):
        l=layout(0x0804e000,0x02009000)
        self.assertEqual(ret.bind(ret._wrapper(l.wrapper,l.callee,l.scheduler_point),l.wrapper,27,l.callee,selector=ret.SELECTOR),l)

    def test_overlapping_complete_owner_refuses(self):
        l=layout();w=l.callee.address
        with self.assertRaisesRegex(ValueError,'overlaps'):ret.bind(ret._wrapper(w,l.callee,l.scheduler_point),w,27,l.callee,selector=ret.SELECTOR)

    def test_selector_and_changed_retained_identity_refuse(self):
        f=fixture();f['selector']='default'
        with self.assertRaises(ValueError):run(**f)
        f=fixture();f['layout']=replace(f['layout'],wrapper_sha256='0'*64)
        with self.assertRaises(ValueError):run(**f)


class ReturnTests(unittest.TestCase):
    def test_exact_field_order_return_origins_and_live_ambient_state(self):
        f=fixture();r=run(**f);self.assertTrue(r['reaches_outer_return_thunk'],r['boundary'])
        self.assertEqual(r['changed_cells'],{str(ALLOCATION+20):0,str(ALLOCATION+21):1,str(ALLOCATION+22):0x35,str(ALLOCATION+23):0x12})
        for reg in [4,5,6,7,8,9]:self.assertEqual(r['registers'][reg],f['entry_registers'][reg])
        for reg in [10,11,12,14]:self.assertEqual(r['registers'][reg],f['post_registers'][reg])
        self.assertEqual(r['registers'][0],words._pointer(ALLOCATION));self.assertEqual(r['registers'][13],words._pointer(E))
        self.assertFalse(r['actual_outer_return_executed']);self.assertFalse(r['actual_callback_return_proved'])

    def test_status_write_aliases_phase_read_and_changes_toggled_value(self):
        f=fixture(phase=13,scheduler=ALLOCATION+8);r=run(**f)
        self.assertTrue(r['reaches_outer_return_thunk'],r['boundary']);self.assertEqual(r['observed_scheduler_phase'],256)
        self.assertEqual((r['changed_cells'][str(ALLOCATION+22)],r['changed_cells'][str(ALLOCATION+23)]),(1,1))

    def test_phase_read_before_same_slot_write_toggles_old_bits(self):
        f=fixture(phase=255,scheduler=ALLOCATION+10);r=run(**f)
        self.assertTrue(r['reaches_outer_return_thunk'],r['boundary']);self.assertEqual(r['observed_scheduler_phase'],255)
        self.assertEqual(r['changed_cells'][str(ALLOCATION+22)],254)

    def test_status_write_can_corrupt_fixed_point_pointer_and_refuses(self):
        allocation=POINT-BASE-20;f=fixture(phase=17,allocation=allocation);r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertIn('pointer provenance',r['boundary']['reason'])
        self.assertEqual(r['boundary']['site'],f['layout'].wrapper+36)
        self.assertTrue(r['descriptor_local_retired']);self.assertTrue(r['callee_reaches_wrapper_continuation'])

    def test_callback_changed_scheduler_pointer_is_freshly_used(self):
        f=fixture(phase=19,scheduler=7000);r=run(**f)
        self.assertTrue(r['reaches_outer_return_thunk'],r['boundary']);self.assertEqual(r['observed_scheduler_coordinate'],7000)

    def test_changed_R7_refuses_without_an_ABI_premise(self):
        f=fixture(phase=23);f['post_registers'][7]=words._pointer(ALLOCATION+4);r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertIn('R7',r['boundary']['reason']);self.assertEqual(r['changed_cells'],{})

    def test_changed_SP_refuses_before_memory_effect(self):
        f=fixture(phase=29);f['post_registers'][13]=words._pointer(E-76);r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertIn('return SP',r['boundary']['reason']);self.assertEqual(r['memory_events'],[])

    def test_each_saved_origin_corruption_refuses_at_cutpoint(self):
        for at in sorted(ret._saved(layout(),fixture()['entry_registers'],E)):
            with self.subTest(at=at):
                f=fixture(phase=31);f['post_cells'][at]=('opaque-byte','corrupted saved byte',0);r=run(**f)
                self.assertFalse(r['reaches_outer_return_thunk']);self.assertEqual(r['boundary']['coordinate'],at)

    def test_missing_saved_byte_is_not_initialized_from_entry_metadata(self):
        f=fixture(phase=37);del f['post_cells'][E-49];r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertEqual(r['boundary']['coordinate'],E-52)

    def test_status_store_into_own_frame_refuses(self):
        f=fixture(phase=41,allocation=E-40);r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertIn('private-frame envelope',r['boundary']['reason'])

    def test_status_store_into_expired_allocator_frame_refuses(self):
        f=fixture(phase=43,allocation=E-144);r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertIn('private-frame envelope',r['boundary']['reason'])

    def test_scheduler_phase_read_in_retired_descriptor_refuses(self):
        f=fixture(phase=47,scheduler=E-92);r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertTrue(r['descriptor_local_retired'])
        self.assertIn('private-frame envelope',r['boundary']['reason'])

    def test_opaque_scheduler_phase_has_no_numeric_xor_witness(self):
        f=fixture(phase=53);f['post_cells'][SCHEDULER+12]=('opaque-byte','phase unknown',0);r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertIn('opaque bits',r['boundary']['reason'])

    def test_numeric_nonzero_scheduler_word_is_not_pointer_authority(self):
        f=fixture(phase=59);put(f['post_cells'],POINT-BASE,words._constant(BASE+SCHEDULER));r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertIn('pointer provenance',r['boundary']['reason'])

    def test_null_scheduler_word_does_not_grant_null_access(self):
        f=fixture(phase=61);put(f['post_cells'],POINT-BASE,words._constant(0));r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertIn('pointer provenance',r['boundary']['reason'])

    def test_caller_protected_allocation_write_refuses(self):
        f=fixture(phase=67);f['protected_spans']=((ALLOCATION+20,ALLOCATION+24),);r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertIn('protected caller',r['boundary']['reason'])

    def test_caller_protected_scheduler_read_refuses(self):
        f=fixture(phase=71);f['protected_spans']=((SCHEDULER+12,SCHEDULER+14),);r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertIn('protected caller',r['boundary']['reason'])

    def test_numeric_base_wrap_refuses_private_stack(self):
        f=fixture(phase=73);f['arena_base']=0xfffffc00;r=run(**f)
        # Keep every supplied cell coordinate bounded; the contradictory base
        # now reaches the intended numeric guard before any actual memory read.
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertIn('wraps',r['boundary']['reason'])

    def test_ambient_copy_pointer_is_retired_without_erasure_or_nonescape(self):
        f=fixture(phase=79);r=run(**f)
        self.assertTrue(r['reaches_outer_return_thunk']);self.assertEqual(r['known_retired_alias_registers'],{'10':E-80})
        self.assertFalse(r['nonescape_proved']);self.assertFalse(r['dead_bytes_erased'])
        self.assertTrue(r['possible_unknown_escaped_aliases'])

    def test_restored_entry_alias_to_dead_frame_is_not_silently_dropped(self):
        f=fixture(phase=83);f['entry_registers'][9]=words._pointer(E-68);put(f['post_cells'],E-48,f['entry_registers'][9]);r=run(**f)
        self.assertTrue(r['reaches_outer_return_thunk']);self.assertEqual(r['known_retired_alias_registers']['9'],E-68)

    def test_all_ambient_registers_required(self):
        f=fixture();del f['post_registers'][12]
        with self.assertRaises(ValueError):run(**f)

    def test_unknown_entry_size_cannot_materialize_saved_numeric_word(self):
        f=fixture();f['entry_registers'][1]=opaque('size unknown')
        with self.assertRaisesRegex(ValueError,'size'):run(**f)

    def test_raw_thumb_both_suffixes_match_five_new_alias_states(self):
        for n,(phase,scheduler) in enumerate([(89,7200),(0,ALLOCATION+8),(65535,ALLOCATION+10),(257,7400),(258,7600)]):
            with self.subTest(n=n):
                f=fixture(phase=phase,scheduler=scheduler);f['post_registers'][12]=opaque('new raw post '+str(n));r=run(**f)
                self.assertTrue(r['reaches_outer_return_thunk'],r['boundary']);regs,memory,events=raw_continuation(f)
                self.assertEqual(regs,r['registers'])
                actual=[(x['site'],x['operation'],x['coordinate'],x.get('bytes',x.get('value'))) for x in r['memory_events'] if x['operation'] in ['read32','read16','write16']]
                self.assertEqual(events,actual)
                self.assertEqual({str(k):memory[int(k)] for k in r['changed_cells']},r['changed_cells'])


class NumericFrameTests(unittest.TestCase):
    def test_one_past_u32_SP_refuses_before_otherwise_valid_frame_reads(self):
        f=fixture(phase=127,allocation=-256);f['arena_base']=0xfffffc00;r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertEqual(r['boundary']['coordinate'],E)
        self.assertEqual(r['memory_events'],[])

    def test_representable_SP_but_wrapping_field_refuses_at_real_store(self):
        f=fixture(phase=131,e=-256);f['arena_base']=0xffffff00;r=run(**f)
        self.assertFalse(r['reaches_outer_return_thunk']);self.assertEqual(r['boundary']['site'],f['layout'].callee.address+188)
        self.assertTrue(r['checked_saved_origins'])

    def test_representable_positive_and_negative_SP_coordinates_both_restore(self):
        for e,phase in [(1280,137),(-512,139)]:
            with self.subTest(e=e):
                f=fixture(phase=phase,e=e);r=run(**f)
                self.assertTrue(r['reaches_outer_return_thunk'],r['boundary'])
                self.assertEqual(r['registers'][13],words._pointer(e))


if __name__=='__main__':unittest.main()
