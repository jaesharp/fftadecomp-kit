"""New outer-wrapper states and independent execution of its complete body."""
from pathlib import Path
import unittest
import allocator_wrapper_relation as wrapper
import allocator_split_relation as split
import allocator_search_relation as search
import allocator_remove_relation as remove
import allocator_insert_relation as insert

ZERO=(Path(__file__).resolve().parents[1]/'inputs/retained-zero12.json').read_bytes()


def layout(a=0x08010000):
    c=(a+0x1000)&~3;s=a+0x2000;r=a+0x3000;m=a+0x4000;i=a+0x5000;t=a+0x6000
    sl=search.bind(search.SHAPE,s,87,selector=search.SELECTOR)
    ml=remove.bind(remove.REMOVE_HEAD+remove._bl(r+124,m)+remove.REMOVE_TAIL,r,remove.MEDIAN,m,(66,51),selector=remove.SELECTOR)
    il=insert.bind(insert.HEAD+remove._bl(i+22,s)+insert.MIDDLE+remove._bl(i+138,m)+insert.TAIL,i,73,sl,ml,selector=insert.SELECTOR)
    al=split.bind(split._encoded(c,il,t,0x08020000),c,127,il,t,b'\x10\x47',0x08020000,selector=split.SELECTOR)
    data=wrapper.HEAD+remove._bl(a+34,c)+wrapper.TAIL
    return wrapper.bind(data,a,26,al,selector=wrapper.SELECTOR)


def heap(size):
    cells={}
    for at,value in [(0,32),(2,32),(4,1),(130,0),(134,size),(136,0),(138,0)]:
        cells[at]=value&255;cells[at+1]=(value>>8)&255
    return cells


def run(size,cells=None,**kw):
    kw.setdefault('zero12_receipt',ZERO);kw.setdefault('observed_zero_target',0x03005e79)
    return wrapper.derive(layout(),size,{} if cells is None else cells,-64,selector=wrapper.SELECTOR,**kw)


class WrapperTests(unittest.TestCase):
    def test_complete_shape_relocated_and_single_exact_call(self):
        l=layout(0x08028002)
        self.assertEqual(len(wrapper.HEAD)+4+len(wrapper.TAIL),54)
        self.assertEqual(l.address,0x08028002)

    def test_wrong_count_call_and_body_mutation_refuse(self):
        l=layout();b=wrapper.HEAD+remove._bl(l.address+34,l.allocator.address)+wrapper.TAIL
        for at in [0,4,10,20,26,28,34,46,52]:
            bad=bytearray(b);bad[at]^=1
            with self.subTest(at=at),self.assertRaises(ValueError):
                wrapper.bind(bytes(bad),l.address,26,l.allocator,selector=wrapper.SELECTOR)
        with self.assertRaises(ValueError):wrapper.bind(b,l.address,27,l.allocator,selector=wrapper.SELECTOR)

    def test_corrupt_retained_split_and_overlapping_wrapper_refuse(self):
        l=layout();a=l.allocator
        bad=split.Layout(a.address,'0'*64,a.insertion,a.thunk,a.pointer_literal)
        with self.assertRaisesRegex(ValueError,'identity'):wrapper._identity(l.address,bad)
        with self.assertRaisesRegex(ValueError,'overlap'):wrapper._identity(a.address,a)

    def test_zero_size_returns_before_any_heap_or_zero_access(self):
        r=run(0,zero12_receipt=None,observed_zero_target=None)
        self.assertTrue(r['returns_under_witness']);self.assertEqual(r['result_pointer'],0)
        self.assertIsNone(r['allocator_relation']);self.assertEqual(r['changed_cells'],{})
        self.assertEqual([e['operation'] for e in r['memory_events']],['save-entry-LR','restore-entry-LR-into-R1','return-saved-entry-LR'])

    def test_original_nonzero_rounding_to_zero_still_calls_allocator(self):
        for size in [0x40000,0xfffffffd,0xfffffffe,0xffffffff]:
            r=run(size,{2:0,3:0})
            self.assertTrue(r['returns_under_witness'])
            self.assertEqual(r['arithmetic']['allocator_units_u16'],0)
            self.assertFalse(r['arithmetic']['original_zero_shortcut'])
            self.assertIsNotNone(r['allocator_relation'])
            self.assertTrue(any(e['operation']=='ordinary-call' for e in r['memory_events']))

    def test_scheduler_count92_split_and_return_plus12(self):
        r=run(92,heap(40))
        self.assertTrue(r['returns_under_witness'],r['boundary'])
        self.assertEqual(r['arithmetic']['allocator_units_u16'],23)
        self.assertEqual(r['allocator_relation']['summary']['new_block'],232)
        self.assertEqual(r['result_pointer'],['base-plus',140])
        self.assertEqual(r['frame']['maximum_private_bytes'],76)
        self.assertEqual(r['allocator_relation']['frame']['entry_SP_coordinate'],-68)

    def test_new_no_split_remainder_and_returned_allocation_token(self):
        r=run(91,heap(25),zero12_receipt=None,observed_zero_target=None)
        self.assertTrue(r['returns_under_witness'])
        self.assertEqual(r['arithmetic']['rounded_u32'],92)
        self.assertFalse(r['allocator_relation']['summary']['split'])
        self.assertEqual(r['result_pointer'],['base-plus',140])

    def test_nonzero_unit_truncation_does_not_grant_requested_extent(self):
        r=run(262144,heap(10))
        self.assertTrue(r['returns_under_witness'],r['boundary'])
        # Unit0 gives split at selected+12, equal to the wrapper return.
        self.assertEqual(r['allocator_relation']['summary']['new_block'],140)
        self.assertEqual(r['result_pointer'],['base-plus',140])
        self.assertFalse(r['allocation_extent_proved'])
        self.assertFalse(r['arithmetic']['full_requested_extent_preserved'])

    def test_allocator_null_remains_null_without_plus12(self):
        r=run(92,heap(22))
        self.assertTrue(r['returns_under_witness']);self.assertEqual(r['result_pointer'],0)
        self.assertFalse(any(e['operation']=='return-pointer-add' for e in r['memory_events']))

    def test_nested_missing_target_refusal_is_not_discarded(self):
        r=run(92,heap(40),observed_zero_target=None)
        self.assertFalse(r['returns_under_witness']);self.assertIsNone(r['result_pointer'])
        self.assertIn('R2 word',r['boundary']['nested']['reason'])
        self.assertFalse(any(e['operation']=='return-pointer-add' for e in r['memory_events']))

    def test_outer_saved_return_protection_even_zero_size(self):
        r=run(0,protected_spans=((-68,-64),))
        self.assertFalse(r['returns_under_witness']);self.assertIn('saved LR',r['boundary']['reason'])
        self.assertEqual(r['memory_events'],[])

    def test_wrapper_saved_LR_is_added_to_nested_protection(self):
        # IncomingSP140 puts selected physical fields inside wrapper/private
        # storage. It cannot be used as a permissive numeric heap witness.
        r=wrapper.derive(layout(),92,heap(40),140,selector=wrapper.SELECTOR,zero12_receipt=ZERO,observed_zero_target=0x03005e79)
        self.assertFalse(r['returns_under_witness'])
        self.assertEqual(r['frame']['protected_saved_LR'],[136,140])

    def test_limits_and_types_remain_closed(self):
        for size in [-1,True,2**32]:
            with self.subTest(size=size),self.assertRaises(ValueError):run(size)
        for kw in [dict(max_search_transitions=257),dict(max_median_links=257),dict(protected_spans=[(0,4)])]:
            with self.subTest(kw=kw),self.assertRaises(ValueError):run(0,**kw)

    def test_all_actual_permissions_and_heap_origins_remain_unproved(self):
        r=run(92,heap(40))
        for key in ['actual_input_or_heap_proved','actual_size_proved','actual_heap_bytes_proved','allocation_extent_proved',
                    'physical_access_proved','installed_identity_proved','actual_frame_noninterference_proved','source_or_native_admission']:
            self.assertFalse(r[key])
        self.assertTrue(all(o['proved'] is False for o in r['obligations']))
        self.assertIn('no memory/global pointer read',r['incoming_heap_source'])

    def test_complete_wrapper_machine_for16_sizes_and_both_call_results(self):
        sizes=[0,1,2,3,4,5,91,92,93,0x3fffc,0x3fffd,0x40000,0x40001,0xfffffffc,0xfffffffd,0xffffffff]
        l=layout()
        for size in sizes:
            for selected in [0,('base',128)]:
                with self.subTest(size=size,selected=selected):
                    calls,returned,restored=execute_wrapper(l,size,selected)
                    facts=wrapper.arithmetic(size)
                    if size==0:
                        self.assertEqual(calls,[]);self.assertEqual(returned,0)
                    else:
                        self.assertEqual(calls,[(('base',0),facts['allocator_units_u16'],-68)])
                        self.assertEqual(returned,0 if selected==0 else ('base',140))
                    self.assertTrue(restored)


def execute_wrapper(l,size,call_result):
    """Raw Thumb control/arithmetic execution; nested call is an explicit stub."""
    code=wrapper.HEAD+remove._bl(l.address+34,l.allocator.address)+wrapper.TAIL
    regs=[('initial',i) for i in range(16)];original=regs[:]
    regs[0]=('base',0);regs[1]=size;regs[13]=-64
    saved={};pc=l.address;zero=False;calls=[]
    def add(x,y):
        return ('base',x[1]+y) if type(x) is tuple and x[0]=='base' else (x+y)&0xffffffff
    for _ in range(100):
        off=pc-l.address;raw=int.from_bytes(code[off:off+2],'little');nxt=pc+2
        if raw==0xb500:
            regs[13]-=4;saved[regs[13]]=regs[14]
        elif raw==0xbc02:
            regs[1]=saved[regs[13]];regs[13]+=4
        elif raw&0xf800==0xf000:
            second=int.from_bytes(code[off+2:off+4],'little')
            d=((raw&2047)<<12)|((second&2047)<<1)
            if d&(1<<22):d-=1<<23
            assert pc+4+d==l.allocator.address
            calls.append((regs[0],regs[1],regs[13]));regs[0]=call_result
            regs[14]=(pc+4)|1;nxt=pc+4
        elif raw&0xf800==0x2000:regs[(raw>>8)&7]=raw&255
        elif raw&0xf800==0x2800:
            v=regs[(raw>>8)&7];zero=type(v)is int and v==(raw&255)
        elif raw&0xffc0==0x4000:regs[raw&7]&=regs[(raw>>3)&7]
        elif raw&0xffc0==0x4240:regs[raw&7]=(-regs[(raw>>3)&7])&0xffffffff
        elif raw&0xfe00==0x1c00:regs[raw&7]=add(regs[(raw>>3)&7],(raw>>6)&7)
        elif raw&0xf800==0x3000:regs[(raw>>8)&7]=add(regs[(raw>>8)&7],raw&255)
        elif raw&0xf800 in (0,0x0800):
            src=(raw>>3)&7;dst=raw&7;shift=(raw>>6)&31
            regs[dst]=(regs[src]<<shift)&0xffffffff if raw&0xf800==0 else regs[src]>>(shift or 32)
        elif raw&0xf000==0xd000:
            cond=(raw>>8)&15;assert cond in (0,1)
            take=zero if cond==0 else not zero
            d=(raw&255)-(256 if raw&128 else 0)
            if take:nxt=pc+4+2*d
        elif raw&0xf800==0xe000:
            d=(raw&2047)-(2048 if raw&1024 else 0);nxt=pc+4+2*d
        elif raw==0x4708:
            assert regs[1]==original[14]
            return calls,regs[0],regs[13]==-64 and all(regs[i]==original[i] for i in range(4,13))
        else:raise AssertionError(f'unsupported wrapper test instruction{raw:04x}')
        pc=nxt
    raise AssertionError('wrapper test instruction budget exhausted')


if __name__=='__main__':unittest.main()
