"""New composed allocator states; no original workflow or old test replay."""
from pathlib import Path
import copy
import hashlib
import unittest

import allocator_split_relation as split
import allocator_search_relation as search
import allocator_remove_relation as remove
import allocator_insert_relation as insert

ZERO = (Path(__file__).resolve().parents[1]/'inputs/retained-zero12.json').read_bytes()
TARGET = 0x03005e79


def field(cells, at, value):
    cells[at] = value & 255
    cells[at+1] = (value >> 8) & 255


def fixture(size=12, selected=128, physical_next=0):
    cells = {}
    for at, value in [(0, selected//4), (2, selected//4), (4, 1),
                      (selected+2, physical_next//4), (selected+6, size),
                      (selected+8, 0), (selected+10, 0)]:
        field(cells, at, value)
    return cells


def layout(base=0x08004000):
    s=base+0x1000; r=base+0x2000; m=base+0x3000; i=base+0x4000; t=base+0x5000
    sl=search.bind(search.SHAPE,s,87,selector=search.SELECTOR)
    rl=remove.bind(remove.REMOVE_HEAD+remove._bl(r+124,m)+remove.REMOVE_TAIL,r,remove.MEDIAN,m,(66,51),selector=remove.SELECTOR)
    il=insert.bind(insert.HEAD+remove._bl(i+22,s)+insert.MIDDLE+remove._bl(i+138,m)+insert.TAIL,i,73,sl,rl,selector=insert.SELECTOR)
    data=split._encoded(base,il,t,0x08010000)
    return split.bind(data,base,127,il,t,b'\x10\x47',0x08010000,selector=split.SELECTOR)


def run(cells,request=8,sp=-64,**kw):
    kw.setdefault('zero12_receipt',ZERO)
    kw.setdefault('observed_zero_target',TARGET)
    return split.derive(layout(),request,cells,sp,selector=split.SELECTOR,**kw)


def merged(cells,result):
    return dict(cells,**{}) | {int(k):v for k,v in result['changed_cells'].items()}


def word(cells,at):
    return cells[at] | cells[at+1]<<8


class SplitTests(unittest.TestCase):
    def test_complete_partition_literal_and_relocated_owner(self):
        l=layout(0x08018000)
        b=split._encoded(l.address,l.insertion,l.thunk,l.pointer_literal)
        self.assertEqual(len(b),266)
        self.assertEqual(int.from_bytes(b[196:200],'little'),l.pointer_literal)
        self.assertEqual(((l.address+90+4)&~3)+0x68,l.address+196)

    def test_mutated_calls_pool_count_and_thunk_refuse(self):
        l=layout();b=split._encoded(l.address,l.insertion,l.thunk,l.pointer_literal)
        for at in [0,20,38,98,176,196,224,264]:
            changed=bytearray(b);changed[at]^=1
            with self.subTest(at=at),self.assertRaises(ValueError):
                split.bind(bytes(changed),l.address,127,l.insertion,l.thunk,b'\x10\x47',l.pointer_literal,selector=split.SELECTOR)
        for count,thunk in [(126,b'\x10\x47'),(127,b'\x18\x47')]:
            with self.subTest(count=count,thunk=thunk),self.assertRaises(ValueError):
                split.bind(b,l.address,count,l.insertion,l.thunk,thunk,l.pointer_literal,selector=split.SELECTOR)

    def test_forged_dependency_and_overlapping_owner_refuse(self):
        l=layout();il=insert.Layout(l.insertion.address,'0'*64,l.insertion.search,l.insertion.median)
        with self.assertRaisesRegex(ValueError,'identity'):
            split._identity(l.address,il,l.thunk,l.pointer_literal)
        with self.assertRaisesRegex(ValueError,'overlap'):
            split._identity(l.insertion.address,l.insertion,l.thunk,l.pointer_literal)
        with self.assertRaises(ValueError):layout(0x08004002)

    def test_empty_search_returns_null_without_zero_authority(self):
        cells={2:0,3:0};r=run(cells,zero12_receipt=None,observed_zero_target=None)
        self.assertTrue(r['returns_under_witness']);self.assertEqual(r['result_pointer'],0)
        self.assertEqual(set(r['helpers']),{'search'})
        self.assertEqual(set(map(int,r['changed_cells'])),set(range(-96,-88)))

    def test_insufficient_size_returns_null_and_does_not_remove(self):
        r=run(fixture(7))
        self.assertTrue(r['returns_under_witness']);self.assertEqual(r['result_pointer'],0)
        self.assertEqual(set(r['helpers']),{'search'})

    def test_no_split_remainders_zero_through_three(self):
        for remainder in range(4):
            cells=fixture(8+remainder)
            r=run(cells,zero12_receipt=None,observed_zero_target=None)
            self.assertTrue(r['returns_under_witness'],r['boundary'])
            out=merged(cells,r)
            self.assertEqual(word(out,134),11+remainder)
            self.assertEqual([out[132],out[133]],[0x6c,0x61])
            self.assertEqual((word(out,0),word(out,2),word(out,4)),(0,0,0))
            self.assertFalse(r['summary']['split'])

    def test_split_remaining_four_zero_and_reinsert(self):
        cells=fixture(12);r=run(cells);out=merged(cells,r)
        self.assertTrue(r['returns_under_witness'],r['boundary'])
        self.assertEqual(r['summary']['new_block'],172)
        self.assertEqual((word(out,0),word(out,2),word(out,4)),(43,43,1))
        self.assertEqual((word(out,172),word(out,174),word(out,178)),(32,0,1))
        self.assertEqual([out[176],out[177]],[0x70,0x73])
        self.assertEqual(word(out,130),43)
        self.assertEqual(r['result_pointer'],['base-plus',128])

    def test_split_updates_actual_physical_successor(self):
        cells=fixture(20,physical_next=256);r=run(cells);out=merged(cells,r)
        self.assertTrue(r['returns_under_witness'],r['boundary'])
        self.assertEqual((word(out,174),word(out,256)),(64,43))
        self.assertEqual(r['summary']['physical_successor_reload'],64)

    def test_real_physical_alias_to_selected_is_ordered(self):
        cells=fixture(20,physical_next=128);r=run(cells);out=merged(cells,r)
        self.assertTrue(r['returns_under_witness'],r['boundary'])
        self.assertEqual((word(out,128),word(out,174)),(43,32))
        self.assertEqual(r['summary']['physical_successor_reload'],32)

    def test_removal_size_reload_can_underflow_without_sorted_heap_assumption(self):
        cells=fixture(12)
        field(cells,0,31);field(cells,4,2);field(cells,136,31)
        field(cells,130,5);field(cells,132,0)
        # predecessor124.next overlays selected128.size. Removal writes0.
        r=run(cells);out=merged(cells,r)
        # Allocated-size11 then overwrites that same predecessor.next. The
        # subsequent insertion really follows index11 and lacks byte50.
        self.assertFalse(r['returns_under_witness'])
        self.assertIn('coordinate50',r['boundary']['reason'])
        self.assertEqual(r['summary']['size_after_removal'],0)
        self.assertTrue(r['summary']['subtraction_underflow'])
        self.assertEqual(r['summary']['remaining_u16'],65528)
        self.assertEqual(word(out,178),65525)

    def test_request_truncates_to_exact_unsigned16(self):
        cells=fixture(10);r=run(cells,0xabcd0008)
        self.assertTrue(r['returns_under_witness'])
        self.assertEqual(r['summary']['request_u16'],8)
        self.assertEqual(word(merged(cells,r),134),13)

    def test_split_requires_pinned_zero_receipt(self):
        for receipt in [None,ZERO+b' ',b'{}']:
            with self.subTest(receipt=receipt is None):
                r=run(fixture(),zero12_receipt=receipt)
                self.assertFalse(r['returns_under_witness'])
                self.assertIn('certificate',r['boundary']['reason'])
                self.assertEqual(r['boundary']['site'],0x08004062)
                self.assertNotIn('insertion',r['helpers'])

    def test_split_requires_exact_thumb_target_witness(self):
        for target in [None,TARGET&~1,TARGET+4,True]:
            r=run(fixture(),observed_zero_target=target)
            self.assertFalse(r['returns_under_witness']);self.assertIn('R2 word',r['boundary']['reason'])

    def test_missing_size_after_removal_preserves_prior_effects(self):
        # Removal updates next.prev in selected block's own size by alias;
        # here the root size itself is opaque initially, so search stops first.
        cells=fixture();cells[134]=('base-plus-byte',100,0)
        r=run(cells)
        self.assertFalse(r['returns_under_witness']);self.assertIn('search witness',r['boundary']['reason'])
        self.assertEqual(set(map(int,r['changed_cells'])),set(range(-96,-88)))

    def test_search_cycle_retains_refusal_and_no_removal(self):
        cells=fixture(1);field(cells,138,32)
        r=run(cells)
        self.assertFalse(r['returns_under_witness']);self.assertIn('cycle',r['boundary']['reason'])
        self.assertEqual(set(r['helpers']),{'search'})

    def test_protected_caller_save_and_nested_save_refuse(self):
        for span in [(-80,-76),(-110,-106)]:
            r=run(fixture(),protected_spans=(span,))
            self.assertFalse(r['returns_under_witness']);self.assertIn('save/output',r['boundary']['reason'])

    def test_heap_access_into_expired_future_frames_refuses(self):
        # EntrySP196: selected128.size134 lies in full envelope124..196,
        # including save bytes not active until the later insertion call.
        r=run(fixture(),sp=196)
        self.assertFalse(r['returns_under_witness'])
        self.assertIn('search witness',r['boundary']['reason'])
        self.assertEqual(r['frame']['heap_field_exclusion'],[124,196])

    def test_zero_destination_overlap_with_frame_refuses(self):
        r=run(fixture(),sp=236)
        self.assertFalse(r['returns_under_witness'])
        self.assertEqual(r['summary']['new_block'],172)
        self.assertIn('frame envelope',r['boundary']['reason'])
        self.assertFalse(any(e['operation']=='zero-write' for e in r['memory_events']))

    def test_physical_successor_write_protected_refuses(self):
        r=run(fixture(20,physical_next=256),protected_spans=((256,258),))
        self.assertFalse(r['returns_under_witness'])
        self.assertEqual(r['boundary']['site'],0x080040d6)
        self.assertIn('protected',r['boundary']['reason'])
        self.assertNotIn('256',r['changed_cells'])

    def test_known_frame_alias_in_output_read_is_not_admitted_as_heap(self):
        # Header2 is inside the outputword at0 when SP=32. The search may
        # zero it, but a heap-field read still cannot consume stack storage.
        r=run({2:0,3:0},sp=32)
        self.assertFalse(r['returns_under_witness'])
        self.assertIn('frame envelope',r['boundary']['reason'])

    def test_no_hidden_permissions_and_input_unchanged(self):
        cells=fixture();saved=copy.deepcopy(cells);r=run(cells)
        self.assertEqual(cells,saved)
        self.assertTrue(all(o['proved'] is False for o in r['obligations']))
        self.assertFalse(r['physical_access_proved']);self.assertFalse(r['installed_identity_proved'])
        self.assertFalse(r['source_or_native_admission'])
        self.assertEqual(r['frame']['maximum_private_bytes'],72)
        self.assertEqual(r['conditional_preserved_registers'],list(range(4,13)))

    def test_invalid_witness_and_unchanged_helper_limits_refuse(self):
        for kw in [dict(sp=-63),dict(request=True),dict(max_search_transitions=257),dict(max_median_links=257),dict(protected_spans=[(0,4)])]:
            with self.subTest(kw=kw),self.assertRaises(ValueError):run({},**kw)
        with self.assertRaises(ValueError):run({0:('invented',1,0)})

    def test_eight_composed_states_match_linked_thumb_and_retained_zero_effect(self):
        multi=fixture(20,physical_next=320)
        field(multi,0,24);field(multi,4,2);field(multi,136,24)
        for at,value in [(102,4),(104,0),(106,32)]:field(multi,at,value)
        fixtures=[({2:0,3:0},8),(fixture(5),8),(fixture(8),8),(fixture(11),8),
                  (fixture(12),8),(fixture(20,physical_next=256),8),
                  (fixture(20,physical_next=128),8),(multi,8)]
        for cells,request in fixtures:
            with self.subTest(cells=cells):
                r=run(cells,request);self.assertTrue(r['returns_under_witness'],r['boundary'])
                events,memory,returned=execute_machine(cells,request,-64)
                modeled=[]
                for e in r['memory_events']:
                    if e['operation'] in ('read8','write8','read32','write32'):
                        modeled.append((e['site'],e['operation'],e['coordinate'],e['value']))
                    elif e['operation']=='zero-write':
                        modeled.append((e['site'],e['operation'],e['coordinate'],e['width'],e['value']))
                self.assertEqual(modeled,events)
                self.assertEqual(r['result_pointer'],returned)
                self.assertEqual(r['changed_cells'],{str(k):memory[k] for k in map(int,r['changed_cells'])})

    def test_new_size_and_split_index_wrap_match_machine(self):
        cases=[(fixture(65535),65535),(fixture(100,selected=262100),8)]
        for cells,request in cases:
            r=run(cells,request)
            self.assertTrue(r['returns_under_witness'],r['boundary'])
            _,machine,returned=execute_machine(cells,request,-64)
            self.assertEqual(r['result_pointer'],returned)
            self.assertEqual(r['changed_cells'],{str(k):machine[k] for k in map(int,r['changed_cells'])})
            out=merged(cells,r)
            if request==65535:
                self.assertEqual(word(out,134),2)
            else:
                self.assertEqual(r['summary']['new_block'],262144)
                self.assertEqual(r['summary']['split_index'],0)
                self.assertEqual((word(out,0),word(out,2),word(out,4)),(0,0,1))

    def test_changed_request_size_zero_can_alias_split_to_selected(self):
        cells=fixture(65535)
        field(cells,0,31);field(cells,4,3);field(cells,136,31)
        field(cells,138,1);field(cells,130,1);field(cells,132,0)
        # Removal rewrites selected.size to nextindex1, producing remainder4.
        # Requested65533+3 truncates to0, so zero/split operate on selected.
        r=run(cells,65533)
        self.assertEqual(r['summary']['size_after_removal'],1)
        self.assertEqual(r['summary']['new_block'],128)
        self.assertEqual(r['summary']['physical_successor_reload'],32)
        events=r['memory_events']
        next_reads=[e for e in events if e.get('role')=='split physical successor reload after selected writes']
        self.assertEqual([e['value'] for e in next_reads],[32,0])
        self.assertFalse(r['allocation_extent_proved'])

    def test_removal_budget_refusal_preserves_decrement_and_links(self):
        cells=fixture(12);field(cells,0,24);field(cells,4,6);field(cells,136,24)
        field(cells,102,1);field(cells,104,0);field(cells,106,32)
        r=run(cells,max_median_links=0)
        self.assertFalse(r['returns_under_witness'])
        self.assertIn('link-read budget',r['boundary']['reason'])
        out=merged(cells,r)
        self.assertEqual(word(out,4),5)
        self.assertEqual(word(out,106),0)
        self.assertNotIn('new_block',r['summary'])


def execute_machine(cells,request,entry_sp):
    """Raw linked Thumb execution; only installed zero uses its frozen effect.

This is a new composed state, not an original invocation or old proof replay.
"""
    l=layout();a=l.address;s=l.insertion.search.address;m=l.insertion.median.median
    r=l.insertion.median.removal;i=l.insertion.address
    bodies=[(a,split._encoded(a,l.insertion,l.thunk,l.pointer_literal)),(s,search.SHAPE),
            (m,remove.MEDIAN),(r,remove.REMOVE_HEAD+remove._bl(r+124,m)+remove.REMOVE_TAIL),
            (i,insert.HEAD+remove._bl(i+22,s)+insert.MIDDLE+remove._bl(i+138,m)+insert.TAIL),
            (l.thunk,b'\x10\x47')]
    code={address+j:b for address,body in bodies for j,b in enumerate(body)}
    memory=dict(cells);regs=[('entry',i) for i in range(16)];initial=regs[:]
    regs[0]=('base',0);regs[1]=request;regs[13]=('base',entry_sp)
    events=[];pc=a;flags=(False,False,False,False)
    def add(x,y):
        return ('base',x[1]+y) if isinstance(x,tuple) and x[0]=='base' else (x+y)&0xffffffff
    def sub(x,y):
        if isinstance(x,tuple):
            assert x[0]=='base' and isinstance(y,tuple) and y[0]=='base';return (x[1]-y[1])&0xffffffff
        return (x-y)&0xffffffff
    def compare(x,y):
        if isinstance(x,tuple):assert x[0]=='base' and y==0;return False,False,True,False
        z=(x-y)&0xffffffff;return bool(z&0x80000000),z==0,x>=y,bool((x^y)&(x^z)&0x80000000)
    def store_word(at,v):
        if isinstance(v,int):bs=[(v>>(8*i))&255 for i in range(4)]
        elif v[0]=='base':bs=[('base-plus-byte',v[1],i) for i in range(4)]
        else:bs=[('saved-word-byte',v,i) for i in range(4)]
        for i,b in enumerate(bs):memory[at+i]=b
    def load_word(at):
        bs=[memory[at+i] for i in range(4)]
        if all(type(b) is int for b in bs):return sum(b<<(8*i) for i,b in enumerate(bs))
        assert all(type(b) is tuple and b[2]==i and b[:2]==bs[0][:2] for i,b in enumerate(bs))
        return ('base',bs[0][1]) if bs[0][0]=='base-plus-byte' else bs[0][1]
    def visible(v):return ['base-plus',v[1]] if type(v) is tuple and v[0]=='base' else v
    for _ in range(30000):
        if pc==(TARGET&~1):
            # Apply the already frozen zero12 contract, not a rerun of its
            # producer. It returns R0=LR,R1=0,R2=dest+12, preserving3..12.
            assert regs[1]==12 and regs[0][0]=='base'
            dest=regs[0][1]
            for at in range(dest,dest+12):memory[at]=0
            for at in range(dest,dest+12,4):events.append((a+98,'zero-write',at,4,0))
            regs[2]=add(regs[0],12);regs[0]=regs[14];regs[1]=0
            pc=regs[14]&~1;continue
        raw=code[pc]|(code[pc+1]<<8);nxt=pc+2
        if raw&0xf800==0xf000:
            second=code[pc+2]|(code[pc+3]<<8);assert second&0xf800==0xf800
            d=((raw&2047)<<12)|((second&2047)<<1)
            if d&(1<<22):d-=1<<23
            regs[14]=(pc+4)|1;nxt=pc+4+d
        elif raw&0xfe00==0xb400:
            ns=[i for i in range(8) if raw>>i&1]+([14] if raw&256 else [])
            regs[13]=add(regs[13],-4*len(ns))
            for i,reg in enumerate(ns):store_word(regs[13][1]+4*i,regs[reg])
        elif raw&0xfe00==0xbc00:
            ns=[i for i in range(8) if raw>>i&1];assert not raw&256
            for i,reg in enumerate(ns):regs[reg]=load_word(regs[13][1]+4*i)
            regs[13]=add(regs[13],4*len(ns))
        elif raw&0xff00==0xb000:regs[13]=add(regs[13],4*(raw&127)*(-1 if raw&128 else 1))
        elif raw&0xff00==0x4600:regs[(raw&7)|((raw>>4)&8)]=regs[(raw>>3)&15]
        elif raw&0xf800==0xa800:regs[(raw>>8)&7]=add(regs[13],4*(raw&255))
        elif raw&0xf000==0x9000:
            at=regs[13][1]+4*(raw&255);reg=(raw>>8)&7
            if raw&0x800:regs[reg]=load_word(at);events.append((pc,'read32',at,visible(regs[reg])))
            else:store_word(at,regs[reg]);events.append((pc,'write32',at,visible(regs[reg])))
        elif raw&0xf800==0x4800:
            at=((pc+4)&~3)+4*(raw&255)
            regs[(raw>>8)&7]=sum(code[at+j]<<(8*j) for j in range(4))
        elif raw&0xf800==0x2000:regs[(raw>>8)&7]=raw&255
        elif raw&0xf800 in (0,0x0800):
            src=(raw>>3)&7;dst=raw&7;shift=(raw>>6)&31
            regs[dst]=((regs[src]<<shift)&0xffffffff) if raw&0xf800==0 else regs[src]>>(shift or 32)
        elif raw&0xfe00==0x1c00:regs[raw&7]=add(regs[(raw>>3)&7],(raw>>6)&7)
        elif raw&0xfe00==0x1e00:regs[raw&7]=sub(regs[(raw>>3)&7],(raw>>6)&7)
        elif raw&0xfe00==0x1800:regs[raw&7]=add(regs[(raw>>3)&7],regs[(raw>>6)&7])
        elif raw&0xfe00==0x1a00:regs[raw&7]=sub(regs[(raw>>3)&7],regs[(raw>>6)&7])
        elif raw&0xf800==0x3000:regs[(raw>>8)&7]=add(regs[(raw>>8)&7],raw&255)
        elif raw&0xf800==0x3800:regs[(raw>>8)&7]=sub(regs[(raw>>8)&7],raw&255)
        elif raw&0xffc0==0x4000:regs[raw&7]&=regs[(raw>>3)&7]
        elif raw&0xffc0==0x4300:regs[raw&7]|=regs[(raw>>3)&7]
        elif raw&0xf800==0x2800:flags=compare(regs[(raw>>8)&7],raw&255)
        elif raw&0xffc0==0x4280:flags=compare(regs[raw&7],regs[(raw>>3)&7])
        elif raw&0xf800 in (0x7800,0x7000):
            b=regs[(raw>>3)&7];assert b[0]=='base';at=b[1]+((raw>>6)&31)
            if raw&0xf800==0x7800:
                assert type(memory[at]) is int;regs[raw&7]=memory[at];events.append((pc,'read8',at,memory[at]))
            else:memory[at]=regs[raw&7]&255;events.append((pc,'write8',at,memory[at]))
        elif raw&0xf800==0x6800:
            b=regs[(raw>>3)&7];off=4*((raw>>6)&31)
            if type(b) is int:
                assert b+off==l.pointer_literal;regs[raw&7]=TARGET
            else:
                assert b[0]=='base';at=b[1]+off;regs[raw&7]=load_word(at)
                events.append((pc,'read32',at,visible(regs[raw&7])))
        elif raw&0xf800==0x6000:
            b=regs[(raw>>3)&7];assert b[0]=='base';at=b[1]+4*((raw>>6)&31)
            store_word(at,regs[raw&7]);events.append((pc,'write32',at,visible(regs[raw&7])))
        elif raw&0xf000==0xd000:
            n,z,carry,v=flags;cond=(raw>>8)&15
            take={0:z,1:not z,8:carry and not z,9:not carry or z,12:not z and n==v}[cond]
            d=(raw&255)-(256 if raw&128 else 0)
            if take:nxt=pc+4+2*d
        elif raw&0xf800==0xe000:
            d=(raw&2047)-(2048 if raw&1024 else 0);nxt=pc+4+2*d
        elif raw&0xff87==0x4700:
            target=regs[(raw>>3)&15]
            if target==initial[14]:
                assert regs[13]==('base',entry_sp) and all(regs[j]==initial[j] for j in range(4,13))
                return events,memory,visible(regs[0])
            assert type(target) is int and target&1;nxt=target&~1
        else:raise AssertionError(f'unsupported test opcode{raw:04x} at{pc:08x}')
        pc=nxt
    raise AssertionError('test instruction budget exhausted')


if __name__=='__main__':unittest.main()
