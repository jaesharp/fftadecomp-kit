"""Constructed insertion states, pointer-slot aliases and explicit boundaries."""
import copy
import unittest
import allocator_insert_relation as insert
import allocator_search_relation as search
import allocator_remove_relation as median


def field(cells,offset,value):
    cells[offset]=value&255;cells[offset+1]=(value>>8)&255


def heap(head,mid,count,nodes,block,size):
    cells={};field(cells,0,head//4);field(cells,2,mid//4);field(cells,4,count)
    for offset,nsize,prev,nxt in nodes:
        field(cells,offset+6,nsize);field(cells,offset+8,prev//4);field(cells,offset+10,nxt//4)
    field(cells,block+6,size)
    return cells


def layout(base=0x08002000):
    s=base+0x1000;m=base+0x2000;r=base+0x3000
    sl=search.bind(search.SHAPE,s,87,selector=search.SELECTOR)
    rl=median.bind(median.REMOVE_HEAD+median._bl(r+124,m)+median.REMOVE_TAIL,r,median.MEDIAN,m,(66,51),selector=median.SELECTOR)
    data=insert.HEAD+median._bl(base+22,s)+insert.MIDDLE+median._bl(base+138,m)+insert.TAIL
    return insert.bind(data,base,73,sl,rl,selector=insert.SELECTOR)


def run(cells,block,sp=-64,**kw):
    return insert.derive(layout(),cells,block,sp,selector=insert.SELECTOR,**kw)


def word(result,offset):
    cells=result['changed_cells'];return cells[str(offset)]|(cells[str(offset+1)]<<8)


class InsertTests(unittest.TestCase):
    def test_complete_relocated_shape_and_both_calls(self):
        self.assertEqual((len(insert.HEAD),len(insert.MIDDLE),len(insert.TAIL)),(22,112,8))
        self.assertEqual(layout(0x0800a002).address,0x0800a002)

    def test_wrong_call_target_and_instruction_mutation_refuse(self):
        l=layout();data=insert.HEAD+median._bl(l.address+22,l.search.address+2)+insert.MIDDLE+median._bl(l.address+138,l.median.median)+insert.TAIL
        with self.assertRaisesRegex(ValueError,'shape or exact'):
            insert.bind(data,l.address,73,l.search,l.median,selector=insert.SELECTOR)
        data=insert.HEAD+median._bl(l.address+22,l.search.address)+insert.MIDDLE+median._bl(l.address+138,l.median.median)+insert.TAIL
        for offset in [0,44,64,76,98,130,142]:
            changed=bytearray(data);changed[offset]^=1
            with self.subTest(offset=offset),self.assertRaises(ValueError):
                insert.bind(bytes(changed),l.address,73,l.search,l.median,selector=insert.SELECTOR)

    def test_empty_list_insertion_and_expired_output_lifetime(self):
        r=run(heap(0,0,0,[],64,7),64)
        self.assertTrue(r['returns_under_witness'])
        self.assertEqual((word(r,0),word(r,2),word(r,4),word(r,72),word(r,74)),(16,16,1,0,0))
        self.assertEqual(r['output_local_coordinates'],[-84,-76])
        self.assertIn('expired',r['output_local_lifetime']);self.assertFalse(r['nonescape_proved'])

    def test_insert_before_head_updates_successor(self):
        r=run(heap(64,64,2,[(64,5,0,96),(96,10,64,0)],32,3),32)
        self.assertTrue(r['returns_under_witness'])
        self.assertEqual((word(r,0),word(r,72),word(r,40),word(r,42),word(r,4)),(8,8,0,16,3))

    def test_insert_middle_and_all_four_pointer_reloads(self):
        r=run(heap(64,64,2,[(64,5,0,96),(96,10,64,0)],80,7),80)
        self.assertTrue(r['returns_under_witness'])
        self.assertEqual((word(r,74),word(r,104),word(r,88),word(r,90)),(20,20,16,24))
        reads=[e for e in r['memory_events'] if e['operation']=='read32']
        self.assertEqual([e['site']-0x08002000 for e in reads],[44,64,76,98])
        self.assertEqual([e['coordinate'] for e in reads],[-84,-80,-84,-80])

    def test_insert_tail_preserves_null_successor(self):
        r=run(heap(64,64,2,[(64,5,0,96),(96,10,64,0)],128,20),128)
        self.assertTrue(r['returns_under_witness'])
        self.assertEqual((word(r,106),word(r,136),word(r,138)),(32,24,0))
        self.assertFalse(any(e.get('role')=='successor previous link' for e in r['memory_events']))

    def test_encoded_index_wrap_is_not_hidden(self):
        r=run(heap(0,0,0,[],262144,7),262144)
        self.assertTrue(r['returns_under_witness'])
        self.assertEqual(r['summary']['inserted_index'],0)
        self.assertEqual((word(r,0),word(r,2),word(r,4)),(0,0,1))
        self.assertFalse(r['allocation_extent_proved'])

    def test_count_overflow_retains_actual_modulo_behavior(self):
        r=run(heap(0,0,65535,[],64,7),64)
        self.assertTrue(r['returns_under_witness']);self.assertTrue(r['summary']['overflow'])
        self.assertEqual(word(r,4),0)
        self.assertEqual(r['median_relation']['final_counter_u32'],0xffffffff)

    def test_search_cycle_blocks_insertion_continuation(self):
        r=run(heap(64,64,2,[(64,1,0,96),(96,2,64,64)],160,7),160)
        self.assertFalse(r['returns_under_witness'])
        self.assertIn('cycle',r['boundary']['reason'])
        self.assertEqual(set(map(int,r['changed_cells'])),set(range(-84,-76)))
        self.assertFalse(r['actual_termination_proved'])

    def test_search_budget_is_not_relaxed_for_composition(self):
        r=run(heap(64,64,2,[(64,1,0,96),(96,9,64,0)],160,7),160,max_search_transitions=1)
        self.assertFalse(r['returns_under_witness']);self.assertIn('bound',r['boundary']['reason'])

    def test_source_size_opaque_bits_are_not_scalarized(self):
        cells=heap(0,0,0,[],64,7);cells[70]=('base-plus-byte',100,0)
        r=run(cells,64)
        self.assertFalse(r['returns_under_witness']);self.assertEqual(r['boundary']['site'],0x08002008)
        self.assertIn('opaque',r['boundary']['reason'])
        self.assertEqual(r['changed_cells'],{})

    def test_missing_search_field_retains_initial_output_zero_writes(self):
        cells=heap(64,64,1,[],160,7)
        r=run(cells,160)
        self.assertFalse(r['returns_under_witness']);self.assertIn('nested search witness refused',r['boundary']['reason'])
        self.assertEqual([r['changed_cells'][str(i)] for i in range(-84,-76)],[0]*8)
        self.assertTrue(any(e.get('frame_origin_coordinate')==-84 and e['operation']=='save-entry-registers' for e in r['memory_events']))

    def test_first_neighbor_write_can_corrupt_next_output_word(self):
        # Search locals100/104 zero predecessor96's size/next. Search returns
        # previous96,next-null. Updating previous.next changes bytes106/107
        # of that null output to an untrusted nonzero numeric representation.
        cells=heap(96,96,1,[(96,2,0,0)],160,7)
        r=run(cells,160,sp=120)
        self.assertFalse(r['returns_under_witness'])
        self.assertEqual(r['boundary']['site'],0x08002040)
        self.assertIn('intact pointer representation',r['boundary']['reason'])
        self.assertEqual(r['changed_cells']['106'],40)

    def test_block_previous_store_can_corrupt_later_next_reload(self):
        # Insertion block96.prev overlays second output at104. Its size was
        # loaded before search initializes the output words.
        cells=heap(64,64,1,[(64,10,0,0)],96,7)
        r=run(cells,96,sp=120)
        self.assertFalse(r['returns_under_witness'])
        self.assertEqual(r['boundary']['site'],0x08002062)
        self.assertEqual(r['changed_cells']['104'],0)
        self.assertEqual(r['changed_cells']['106'],('base-plus-byte',64,2))

    def test_protected_source_write_refuses_at_exact_store(self):
        cells=heap(0,0,0,[],64,7)
        r=run(cells,64,protected_spans=((0,2),))
        self.assertFalse(r['returns_under_witness'])
        self.assertEqual(r['boundary']['site'],0x0800203a)
        self.assertIn('protected',r['boundary']['reason'])
        self.assertNotIn('0',r['changed_cells'])

    def test_own_saved_frame_cannot_supply_heap_count_bits(self):
        cells=heap(0,0,0,[],64,7)
        r=run(cells,64,sp=28)
        self.assertFalse(r['returns_under_witness'])
        # Search's protected frame contains header2; no stale reaching bits.
        self.assertIn('nested search witness refused',r['boundary']['reason'])
        self.assertFalse(r['actual_frame_noninterference_proved'])

    def test_input_cells_are_preserved_and_no_permission_follows(self):
        cells=heap(0,0,0,[],64,7);before=copy.deepcopy(cells);r=run(cells,64)
        self.assertEqual(cells,before)
        self.assertTrue(all(x['proved'] is False for x in r['obligations']))
        self.assertEqual(r['numeric_frame']['including_search_private_bytes'],40)
        self.assertEqual(r['numeric_frame']['including_median_private_bytes'],28)
        for k in ['physical_access_proved','actual_entry_heap_SP_or_alias_proved','allocation_extent_proved','source_or_native_admission']:
            self.assertFalse(r[k])

    def test_invalid_coordinates_tokens_and_budget_refuse(self):
        for block,sp in [(True,-64),(65,-64),(64,-63)]:
            with self.subTest(block=block,sp=sp),self.assertRaises(ValueError):run({},block,sp=sp)
        with self.assertRaises(ValueError):run({70:('base-plus-byte',1,True)},64)
        with self.assertRaises(ValueError):run({},64,max_median_links=257)

    def test_forged_layout_rejected(self):
        l=layout();bad=insert.Layout('invalid',l.sha256,l.search,l.median)
        with self.assertRaisesRegex(ValueError,'identity'):
            insert.derive(bad,{},64,-64,selector=insert.SELECTOR)


    def test_six_new_insert_states_match_full_thumb_execution(self):
        nodes=[(128,4,0,160),(160,8,128,192),(192,12,160,0)]
        fixtures=[
            (heap(0,0,0,[],320,9),320),
            (heap(128,160,3,nodes,176,10),176),
            (heap(128,160,3,nodes,224,20),224),
            (heap(128,160,3,nodes,96,2),96),
            (heap(0,0,65535,[],512,7),512),
            (heap(0,0,0,[],262148,7),262148),
        ]
        for cells,block in fixtures:
            with self.subTest(block=block):
                r=run(cells,block);self.assertTrue(r['returns_under_witness'])
                events,memory=execute_machine(cells,block,-64)
                modeled=[(e['site'],e['operation'],e['coordinate'],e['value']) for e in r['memory_events'] if e['operation'] in ('read8','write8','read32','write32')]
                self.assertEqual(modeled,events)
                self.assertEqual(r['changed_cells'],{str(k):memory[k] for k in map(int,r['changed_cells'])})


def execute_machine(cells,block,entry_sp):
    """Test-only Thumb machine; no production field/control equations."""
    a=0x08002000;s=a+0x1000;m=a+0x2000
    insertion=insert.HEAD+median._bl(a+22,s)+insert.MIDDLE+median._bl(a+138,m)+insert.TAIL
    code={a+i:b for i,b in enumerate(insertion)};code.update({s+i:b for i,b in enumerate(search.SHAPE)});code.update({m+i:b for i,b in enumerate(median.MEDIAN)})
    memory=dict(cells);regs=[('entry',i) for i in range(16)];initial=regs[:]
    regs[0]=('base',0);regs[1]=('base',block);regs[13]=('base',entry_sp)
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
        elif raw&0xf800==0x2000:regs[(raw>>8)&7]=raw&255
        elif raw&0xf800 in (0,0x0800):
            src=(raw>>3)&7;dst=raw&7;shift=(raw>>6)&31
            regs[dst]=((regs[src]<<shift)&0xffffffff) if raw&0xf800==0 else regs[src]>>(shift or 32)
        elif raw&0xfe00==0x1c00:regs[raw&7]=add(regs[(raw>>3)&7],(raw>>6)&7)
        elif raw&0xfe00==0x1800:regs[raw&7]=add(regs[(raw>>3)&7],regs[(raw>>6)&7])
        elif raw&0xfe00==0x1a00:regs[raw&7]=sub(regs[(raw>>3)&7],regs[(raw>>6)&7])
        elif raw&0xf800==0x3000:regs[(raw>>8)&7]=add(regs[(raw>>8)&7],raw&255)
        elif raw&0xf800==0x3800:regs[(raw>>8)&7]=sub(regs[(raw>>8)&7],raw&255)
        elif raw&0xffc0==0x4300:regs[raw&7]|=regs[(raw>>3)&7]
        elif raw&0xf800==0x2800:flags=compare(regs[(raw>>8)&7],raw&255)
        elif raw&0xffc0==0x4280:flags=compare(regs[raw&7],regs[(raw>>3)&7])
        elif raw&0xf800 in (0x7800,0x7000):
            b=regs[(raw>>3)&7];assert b[0]=='base';at=b[1]+((raw>>6)&31)
            if raw&0xf800==0x7800:
                assert type(memory[at]) is int;regs[raw&7]=memory[at];events.append((pc,'read8',at,memory[at]))
            else:memory[at]=regs[raw&7]&255;events.append((pc,'write8',at,memory[at]))
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
        elif raw==0x4700:
            if regs[0]==initial[14]:
                assert regs[13]==('base',entry_sp) and all(regs[i]==initial[i] for i in range(4,13));return events,memory
            assert type(regs[0]) is int and regs[0]&1;nxt=regs[0]&~1
        else:raise AssertionError(f'unsupported test opcode{raw:04x} at{pc:08x}')
        pc=nxt
    raise AssertionError('test instruction budget exhausted')


if __name__=='__main__':unittest.main()
