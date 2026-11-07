"""Constructed heaps for exact removal and predecremented median effects."""
import copy
import unittest
import allocator_remove_relation as relation


def field(cells,offset,value):
    cells[offset]=value&255;cells[offset+1]=(value>>8)&255


def heap(head,count,nodes,median=0):
    cells={};field(cells,0,head//4);field(cells,2,median//4);field(cells,4,count)
    for offset,previous,following in nodes:
        field(cells,offset+8,previous//4);field(cells,offset+10,following//4)
    return cells


def layout():
    a=0x08002000;m=0x08003000
    code=relation.REMOVE_HEAD+relation._bl(a+124,m)+relation.REMOVE_TAIL
    return relation.bind(code,a,relation.MEDIAN,m,(66,51),selector=relation.SELECTOR)


def median(cells,**kw):return relation.derive_median(layout(),cells,selector=relation.SELECTOR,**kw)
def remove(cells,block,**kw):return relation.derive_removal(layout(),cells,block,selector=relation.SELECTOR,**kw)


def changed_word(result,offset):
    memory=result['changed_bytes'];return memory[str(offset)]|(memory[str(offset+1)]<<8)


class RemoveTests(unittest.TestCase):
    def test_complete_relocatable_shapes_and_direct_call(self):
        self.assertEqual((len(relation.REMOVE_HEAD),len(relation.MEDIAN)),(124,102))
        a=0x08005002;m=0x08004004
        code=relation.REMOVE_HEAD+relation._bl(a+124,m)+relation.REMOVE_TAIL
        r=relation.bind(code,a,relation.MEDIAN,m,(66,51),selector=relation.SELECTOR)
        self.assertEqual((r.removal,r.median),(a,m))

    def test_call_target_and_shape_mutation_refuse(self):
        a=0x08002000;m=0x08003000
        wrong=relation.REMOVE_HEAD+relation._bl(a+124,m+2)+relation.REMOVE_TAIL
        with self.assertRaisesRegex(ValueError,'shape or exact direct'):
            relation.bind(wrong,a,relation.MEDIAN,m,(66,51),selector=relation.SELECTOR)
        code=relation.REMOVE_HEAD+relation._bl(a+124,m)+relation.REMOVE_TAIL
        with self.assertRaisesRegex(ValueError,'shape'):
            relation.bind(code,a,relation.MEDIAN[:-2]+bytes.fromhex('0847'),m,(66,51),selector=relation.SELECTOR)

    def test_bad_count_overlap_and_selector_refuse(self):
        a=0x08002000;m=0x08003000;code=relation.REMOVE_HEAD+relation._bl(a+124,m)+relation.REMOVE_TAIL
        for counts,at,selector in [((67,51),m,relation.SELECTOR),((66,51),a+100,relation.SELECTOR),((66,51),m,'default')]:
            with self.subTest(counts=counts,at=at,selector=selector),self.assertRaises(ValueError):
                relation.bind(code,a,relation.MEDIAN,at,counts,selector=selector)

    def test_empty_head_bypasses_missing_count(self):
        r=median({0:0,1:0})
        self.assertTrue(r['returns_under_witness']);self.assertEqual(changed_word(r,2),0)
        self.assertIsNone(r['summary']['element_count'])
        self.assertEqual([e['coordinate'] for e in r['memory_events'] if e['operation']=='read8'],[0,1])

    def test_counts_zero_through_three_do_not_read_links(self):
        for count in range(4):
            with self.subTest(count=count):
                r=median(heap(32,count,[]))
                self.assertTrue(r['returns_under_witness']);self.assertEqual(changed_word(r,2),8)
                self.assertEqual(r['summary']['completed_link_reads'],0)
                self.assertEqual(r['summary']['final_counter_u32'],0xffffffff if count<2 else 0)

    def test_even_and_odd_counts_use_predecrement(self):
        for count in [4,5]:
            with self.subTest(count=count):
                r=median(heap(32,count,[(32,0,64)]))
                self.assertEqual(changed_word(r,2),16)
                self.assertEqual(r['summary']['completed_link_reads'],1)

    def test_two_link_steps_and_byte_events(self):
        r=median(heap(32,6,[(32,0,64),(64,32,96)]))
        self.assertEqual(changed_word(r,2),24)
        reads=[e['coordinate'] for e in r['memory_events'] if e['operation']=='read8']
        self.assertEqual(reads,[0,1,4,5,42,43,74,75])

    def test_cycle_terminates_by_count_without_list_validity(self):
        r=median(heap(32,8,[(32,32,32)]))
        self.assertTrue(r['returns_under_witness']);self.assertEqual(r['summary']['completed_link_reads'],3)
        self.assertEqual(changed_word(r,2),8)
        self.assertFalse(r['list_sortedness_or_distinct_nodes_assumed'])
        self.assertFalse(r['actual_termination_proved'])

    def test_null_on_last_read_can_produce_zero_median(self):
        r=median(heap(32,4,[(32,0,0)]))
        self.assertTrue(r['returns_under_witness']);self.assertEqual(changed_word(r,2),0)

    def test_null_before_last_read_is_precise_boundary(self):
        r=median(heap(32,6,[(32,0,0)]))
        self.assertFalse(r['returns_under_witness'])
        self.assertIn('absolute0xA/0xB',r['boundary']['reason'])
        self.assertEqual(r['boundary']['site'],0x08003030)
        self.assertEqual(r['boundary']['remaining_link_reads'],1)
        self.assertEqual(r['modified_coordinates'],[])

    def test_budget_is_refusal_not_termination(self):
        r=median(heap(32,65535,[(32,32,32)]),max_link_reads=1)
        self.assertFalse(r['returns_under_witness']);self.assertIn('budget',r['boundary']['reason'])
        self.assertEqual(r['boundary']['remaining_link_reads'],32765)
        self.assertFalse(r['actual_termination_proved'])

    def test_remove_singleton_clears_links_and_head(self):
        r=remove(heap(32,1,[(32,0,0)]),32)
        self.assertTrue(r['returns_under_witness'])
        self.assertEqual((changed_word(r,0),changed_word(r,2),changed_word(r,4)),(0,0,0))
        self.assertTrue(all(r['changed_bytes'][str(i)]==0 for i in range(40,44)))

    def test_remove_head_updates_next_previous_then_median(self):
        r=remove(heap(32,2,[(32,0,64),(64,32,0)]),32)
        self.assertEqual((changed_word(r,0),changed_word(r,72),changed_word(r,2),changed_word(r,4)),(16,0,16,1))
        self.assertEqual(r['summary']['median']['required_link_reads'],0)

    def test_remove_middle_reloads_previous_and_preserves_order(self):
        r=remove(heap(32,3,[(32,0,64),(64,32,96),(96,64,0)]),64)
        self.assertTrue(r['returns_under_witness'])
        self.assertEqual((changed_word(r,42),changed_word(r,104),changed_word(r,4),changed_word(r,2)),(24,8,2,8))
        events=r['memory_events'];writes=[i for i,e in enumerate(events) if e.get('role')=='previous next link']
        reads=[i for i,e in enumerate(events) if e.get('role')=='reload block previous index']
        self.assertLess(max(writes),min(reads))
        clear=[e['coordinate'] for e in events if e.get('role')=='clear removed block links']
        self.assertEqual(clear,[74,75,72,73])

    def test_remove_tail_does_not_invent_next_node_access(self):
        r=remove(heap(32,3,[(32,0,64),(64,32,96),(96,64,0)]),96)
        self.assertEqual(changed_word(r,74),0)
        self.assertFalse(any(e.get('role')=='next previous link' for e in r['memory_events']))

    def test_self_aliases_are_applied_in_instruction_order(self):
        r=remove(heap(32,2,[(32,32,32)]),32)
        self.assertTrue(r['returns_under_witness'])
        self.assertEqual([r['changed_bytes'][str(i)] for i in range(40,44)],[0,0,0,0])
        self.assertEqual(changed_word(r,2),8)
        self.assertFalse(r['list_sortedness_or_distinct_nodes_assumed'])

    def test_count_underflow_retained_before_median_boundary(self):
        r=remove(heap(32,0,[(32,0,64),(64,32,0)]),64,max_link_reads=2)
        self.assertEqual(changed_word(r,4),65535)
        self.assertTrue(r['summary']['underflow'])
        self.assertIn('premature null',r['boundary']['reason'])
        self.assertFalse(r['returns_under_witness'])

    def test_missing_count_keeps_prior_effects(self):
        cells=heap(32,3,[(32,0,64),(64,32,0)]);del cells[4]
        r=remove(cells,64)
        self.assertFalse(r['returns_under_witness'])
        self.assertEqual(r['boundary']['coordinate'],4)
        self.assertEqual(changed_word(r,42),0)
        self.assertEqual(r['changed_bytes']['72'],0)

    def test_witness_not_mutated_or_uninitialized_bytes_invented(self):
        cells=heap(32,1,[(32,0,0)]);before=copy.deepcopy(cells);remove(cells,32)
        self.assertEqual(cells,before)
        r=remove({},32)
        self.assertEqual(r['boundary']['coordinate'],40)
        self.assertEqual(r['changed_bytes'],{})

    def test_no_physical_or_frame_permissions_follow(self):
        r=remove(heap(32,1,[(32,0,0)]),32)
        self.assertTrue(all(o['proved'] is False for o in r['obligations']))
        saves=[e['stack_span'] for e in r['memory_events'] if e['operation']=='save-entry-registers']
        self.assertEqual(saves,[[-16,0],[-24,-16]])
        for key in ['physical_access_proved','allocation_or_object_extent_proved','actual_frame_noninterference_proved','source_or_native_admission']:
            self.assertFalse(r[key])

    def test_invalid_block_byte_budget_and_forged_layout_refuse(self):
        for block in [0,5,True,262144]:
            with self.subTest(block=block),self.assertRaises(ValueError):remove({},block)
        for budget in [-1,257,True]:
            with self.subTest(budget=budget),self.assertRaises(ValueError):median({},max_link_reads=budget)
        with self.assertRaises(ValueError):median({0:256})
        l=layout();bad=relation.Layout(l.removal,l.median,'0'*64,l.median_sha256)
        with self.assertRaisesRegex(ValueError,'identity'):
            relation.derive_median(bad,{0:0,1:0},selector=relation.SELECTOR)


    def test_composed_remove_matches_independent_thumb_machine(self):
        fixtures=[
            (heap(96,6,[(96,0,128),(128,96,160),(160,128,192),(192,160,224),(224,192,256),(256,224,0)]),160),
            (heap(160,3,[(160,0,192),(192,160,224),(224,192,0)]),160),
            (heap(96,7,[(96,0,128),(128,96,160),(160,128,192),(192,160,224),(224,192,256),(256,224,0)]),256),
            (heap(128,4,[(128,0,160),(160,128,128)]),160),
            (heap(0,0,[(160,0,0)]),160),
        ]
        for cells,block in fixtures:
            with self.subTest(block=block,cells=cells):
                r=remove(cells,block);self.assertTrue(r['returns_under_witness'])
                events,memory=execute_machine(cells,block,'removal')
                modeled=[(e['site'],e['operation'],e['coordinate'],e['value']) for e in r['memory_events'] if e['operation'] in ('read8','write8')]
                self.assertEqual(modeled,events)
                self.assertEqual(r['changed_bytes'],{str(k):memory[k] for k in r['modified_coordinates']})

    def test_median_predecrement_matches_independent_thumb_machine(self):
        for cells in [heap(320,0,[]),heap(320,5,[(320,0,352)]),heap(320,8,[(320,320,320)])]:
            with self.subTest(cells=cells):
                r=median(cells);self.assertTrue(r['returns_under_witness'])
                events,memory=execute_machine(cells,None,'median')
                modeled=[(e['site'],e['operation'],e['coordinate'],e['value']) for e in r['memory_events'] if e['operation'] in ('read8','write8')]
                self.assertEqual(modeled,events)
                self.assertEqual(changed_word(r,2),memory[2]|(memory[3]<<8))


def execute_machine(cells,block,entry):
    """Test-only raw Thumb interpreter, independent of field equations."""
    a=0x08002000;m=0x08003000
    removal=relation.REMOVE_HEAD+relation._bl(a+124,m)+relation.REMOVE_TAIL
    code={a+i:b for i,b in enumerate(removal)};code.update({m+i:b for i,b in enumerate(relation.MEDIAN)})
    memory=dict(cells);regs=[('entry',i) for i in range(16)];initial=regs[:]
    regs[0]=('base',0);regs[1]=('base',block) if block is not None else ('entry',1)
    stack=[];events=[];pc=a if entry=='removal' else m;flags=(False,False,False,False)
    def add(x,y):
        return ('base',x[1]+y) if isinstance(x,tuple) and x[0]=='base' else (x+y)&0xffffffff
    def subtract(x,y):
        if isinstance(x,tuple):
            assert x[0]=='base' and isinstance(y,tuple) and y[0]=='base';return (x[1]-y[1])&0xffffffff
        return (x-y)&0xffffffff
    def comparison(x,y):
        if isinstance(x,tuple):
            assert x[0]=='base' and y==0;return False,False,True,False
        z=(x-y)&0xffffffff
        return bool(z&0x80000000),z==0,x>=y,bool((x^y)&(x^z)&0x80000000)
    for _ in range(20000):
        raw=code[pc]|(code[pc+1]<<8);nxt=pc+2
        if raw&0xf800==0xf000:
            second=code[pc+2]|(code[pc+3]<<8);assert second&0xf800==0xf800
            disp=((raw&2047)<<12)|((second&2047)<<1)
            if disp&(1<<22):disp-=1<<23
            regs[14]=(pc+4)|1;nxt=pc+4+disp
        elif raw&0xfe00==0xb400:
            nums=[i for i in range(8) if raw>>i&1]+([14] if raw&256 else []);stack=[regs[i] for i in nums]+stack
        elif raw&0xfe00==0xbc00:
            nums=[i for i in range(8) if raw>>i&1];assert not raw&256
            for i,v in zip(nums,stack):regs[i]=v
            stack=stack[len(nums):]
        elif raw&0xf800==0x2000:regs[(raw>>8)&7]=raw&255
        elif raw&0xf800 in (0,0x0800):
            src=(raw>>3)&7;dst=raw&7;shift=(raw>>6)&31
            regs[dst]=((regs[src]<<shift)&0xffffffff) if raw&0xf800==0 else regs[src]>>(shift or 32)
        elif raw&0xfe00==0x1c00:regs[raw&7]=add(regs[(raw>>3)&7],(raw>>6)&7)
        elif raw&0xfe00==0x1800:regs[raw&7]=add(regs[(raw>>3)&7],regs[(raw>>6)&7])
        elif raw&0xfe00==0x1a00:regs[raw&7]=subtract(regs[(raw>>3)&7],regs[(raw>>6)&7])
        elif raw&0xf800==0x3800:regs[(raw>>8)&7]=subtract(regs[(raw>>8)&7],raw&255)
        elif raw&0xffc0==0x4300:regs[raw&7]|=regs[(raw>>3)&7]
        elif raw&0xf800==0x2800:flags=comparison(regs[(raw>>8)&7],raw&255)
        elif raw&0xf800 in (0x7800,0x7000):
            base=regs[(raw>>3)&7];assert base[0]=='base';at=base[1]+((raw>>6)&31)
            if raw&0xf800==0x7800:
                regs[raw&7]=memory[at];events.append((pc,'read8',at,memory[at]))
            else:
                memory[at]=regs[raw&7]&255;events.append((pc,'write8',at,memory[at]))
        elif raw&0xf000==0xd000:
            n,z,carry,v=flags;cond=(raw>>8)&15;take={0:z,1:not z,12:(not z and n==v)}[cond]
            disp=(raw&255)-(256 if raw&128 else 0)
            if take:nxt=pc+4+2*disp
        elif raw&0xf800==0xe000:
            disp=(raw&2047)-(2048 if raw&1024 else 0);nxt=pc+4+2*disp
        elif raw==0x4700:
            if regs[0]==initial[14]:
                assert not stack and all(regs[i]==initial[i] for i in range(4,13));return events,memory
            assert isinstance(regs[0],int) and regs[0]&1;nxt=regs[0]&~1
        else:raise AssertionError(f'unimplemented opcode{raw:04x} at{pc:08x}')
        pc=nxt
    raise AssertionError('independent machine did not return')


if __name__=='__main__':unittest.main()
