"""Constructed byte witnesses for median search, aliases and refusal bounds."""
import copy
import unittest
import allocator_search_relation as search


def field(cells, offset, value):
    cells[offset] = value & 255
    cells[offset+1] = (value >> 8) & 255


def witness(median, nodes):
    cells = {}
    field(cells, 2, median//4)
    for address, size, previous, following in nodes:
        field(cells, address+6, size)
        field(cells, address+8, previous//4)
        field(cells, address+10, following//4)
    return cells


def derive(cells, request=7, previous=1024, selected=1028, **kw):
    layout = search.bind(search.SHAPE, 0x08002000, 87, selector=search.SELECTOR)
    return search.derive(layout, request, cells, previous, selected, selector=search.SELECTOR, **kw)


def pair(result):
    return result['conditional_output_equations']


class SearchTests(unittest.TestCase):
    def test_relocatable_complete_body_count(self):
        self.assertEqual(len(search.SHAPE), 174)
        layout = search.bind(search.SHAPE, 0x0800a002, 87, selector=search.SELECTOR)
        r = search.derive(layout, 7, witness(0, []), 1024, 1028, selector=search.SELECTOR)
        self.assertEqual(r['memory_events'][1]['site'], 0x0800a010)

    def test_complete_shape_mutations_refuse(self):
        for offset in [0, 14, 28, 110, 164, 172]:
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError, 'complete'):
                changed = bytearray(search.SHAPE); changed[offset] ^= 1
                search.bind(bytes(changed), 0x08002000, 87, selector=search.SELECTOR)

    def test_wrong_count_or_selector_refuse(self):
        for count, selector in [(86, search.SELECTOR), (87, 'default'), (True, search.SELECTOR)]:
            with self.subTest(count=count, selector=selector), self.assertRaises(ValueError):
                search.bind(search.SHAPE, 0x08002000, count, selector=selector)

    def test_empty_median_only_initial_zero_stores(self):
        r = derive(witness(0, []))
        self.assertEqual(pair(r), dict(previous=None, selected=None))
        writes = [e for e in r['memory_events'] if e['operation']=='write32']
        self.assertEqual([e['coordinate'] for e in writes], [1028,1024])
        self.assertEqual(r['conditional_exit_registers']['R2'], ['base-plus',1024])
        self.assertTrue(r['returns_under_witness'])

    def test_backward_null_predecessor_selects_median(self):
        r = derive(witness(64, [(64,10,0,0)]))
        self.assertEqual(pair(r), dict(previous=None, selected=64))
        self.assertEqual([e['coordinate'] for e in r['memory_events'] if e['operation']=='read8'], [2,3,70,71,72,73])

    def test_backward_boundary_pair(self):
        r = derive(witness(96, [(96,10,64,0),(64,5,0,96)]))
        self.assertEqual(pair(r), dict(previous=64, selected=96))
        reads = [e for e in r['memory_events'] if e['operation']=='read8']
        self.assertEqual([e['coordinate'] for e in reads][-4:], [70,71,102,103])

    def test_backward_multiple_qualifying_nodes(self):
        r = derive(witness(96, [(96,10,64,0),(64,8,32,96),(32,7,0,64)]))
        self.assertEqual(pair(r), dict(previous=None, selected=32))
        self.assertFalse(r['sorted_list_assumed'])

    def test_forward_boundary_pair(self):
        r = derive(witness(64, [(64,5,0,96),(96,10,64,0)]))
        self.assertEqual(pair(r), dict(previous=64, selected=96))
        writes = [e for e in r['memory_events'] if e['operation']=='write32']
        self.assertEqual([e['value'] for e in writes[-2:]], [['base-plus',64],['base-plus',96]])

    def test_forward_end_returns_null_selected(self):
        r = derive(witness(64, [(64,5,0,96),(96,6,64,0)]))
        self.assertEqual(pair(r), dict(previous=96, selected=None))
        self.assertEqual(r['conditional_exit_registers']['R2'],0)

    def test_unsorted_links_are_not_silently_repaired(self):
        r = derive(witness(64, [(64,5,0,96),(96,2,0,128),(128,10,0,0)]))
        self.assertEqual(pair(r), dict(previous=96, selected=128))
        self.assertFalse(r['sorted_list_assumed'])

    def test_request_is_unsigned_low_halfword(self):
        r = derive(witness(64, [(64,5,0,96),(96,10,64,0)]), request=0xffff0007)
        self.assertEqual(r['request_u16'],7)
        self.assertEqual(pair(r),dict(previous=64,selected=96))

    def test_byte_order_and_maximum_index(self):
        at=65535*4
        r = derive(witness(at,[(at,0x8102,0,0)]),request=0x8000)
        self.assertEqual(pair(r),dict(previous=None,selected=at))
        self.assertEqual([e['value'] for e in r['memory_events'] if e['operation']=='read8'][:4], [255,255,2,129])
        self.assertFalse(r['numeric_base_or_output_addresses_proved'])

    def test_equal_output_slot_has_last_store_semantics(self):
        r=derive(witness(64,[(64,5,0,96),(96,10,64,0)]),previous=1024,selected=1024)
        out=r['output_snapshots']
        self.assertTrue(out['same_slot'])
        self.assertEqual(out['previous_bytes'],out['selected_bytes'])
        self.assertEqual(out['previous_bytes'],[('base-plus-byte',96,i) for i in range(4)])
        self.assertEqual(pair(r),dict(previous=64,selected=96))

    def test_initial_store_can_zero_median_before_read(self):
        r=derive({},previous=1024,selected=0)
        self.assertEqual(pair(r),dict(previous=None,selected=None))
        reads=[e for e in r['memory_events'] if e['operation']=='read8']
        self.assertEqual([e['value'] for e in reads],[0,0])
        self.assertFalse(r['heap_write_purity_proved'])

    def test_initial_store_can_change_search_direction(self):
        r=derive(witness(64,[(64,20,0,96),(96,10,64,0)]),previous=68)
        self.assertEqual(pair(r),dict(previous=64,selected=96))
        reads=[e for e in r['memory_events'] if e['operation']=='read8' and e['coordinate'] in (70,71)]
        self.assertTrue(reads)
        self.assertTrue(all(e['value']==0 for e in reads))

    def test_input_witness_is_not_mutated(self):
        cells=witness(64,[(64,10,0,0)]);old=copy.deepcopy(cells)
        derive(cells)
        self.assertEqual(cells,old)

    def test_missing_field_bits_are_not_initialized_by_model(self):
        with self.assertRaisesRegex(ValueError,'concrete byte bits'):
            derive({2:16,3:0})

    def test_invalid_byte_and_boolean_request_refuse(self):
        for cells,request in [({2:256,3:0},7),({2:False,3:0},7),({2:0,3:0},True)]:
            with self.subTest(cells=cells,request=request),self.assertRaisesRegex(ValueError,'byte witness'):
                derive(cells,request=request)

    def test_unaligned_or_wrapping_output_coordinates_refuse(self):
        for previous in [1,2**31-2,-2**31-4]:
            with self.subTest(previous=previous),self.assertRaisesRegex(ValueError,'aligned'):
                derive(witness(0,[]),previous=previous)

    def test_forged_layout_identity_refuses(self):
        layout=search.Layout(0x08002000,'0'*64)
        with self.assertRaisesRegex(ValueError,'identity'):
            search.derive(layout,7,witness(0,[]),1024,1028,selector=search.SELECTOR)

    def test_forward_cycle_does_not_return_or_write_final_pair(self):
        r=derive(witness(64,[(64,1,0,96),(96,2,64,64)]))
        self.assertEqual(r['status'],'conditional stable-memory cycle')
        self.assertFalse(r['returns_under_witness'])
        self.assertIsNone(pair(r))
        self.assertEqual(len([e for e in r['memory_events'] if e['operation']=='write32']),2)
        self.assertFalse(r['actual_termination_proved'])

    def test_backward_cycle_does_not_grant_sorted_termination(self):
        r=derive(witness(64,[(64,10,96,0),(96,12,64,0)]))
        self.assertEqual(r['status'],'conditional stable-memory cycle')
        self.assertFalse(r['sorted_list_assumed'])
        self.assertEqual(r['output_snapshots']['selected_bytes'],[0,0,0,0])

    def test_bound_exhaustion_retains_precise_nonreturn_status(self):
        r=derive(witness(64,[(64,1,0,96),(96,2,64,128),(128,9,96,0)]),max_transitions=1)
        self.assertEqual(r['status'],'refused at explicit transition bound')
        self.assertEqual(r['transitions'],1)
        self.assertIsNone(r['conditional_exit_registers'])
        self.assertFalse(r['returns_under_witness'])

    def test_zero_request_still_reads_and_follows_previous_links(self):
        r=derive(witness(64,[(64,0,32,0),(32,0,0,64)]),request=0)
        self.assertEqual(pair(r),dict(previous=None,selected=32))
        self.assertGreater(r['transitions'],1)

    def test_all_physical_frame_and_representation_conditions_remain(self):
        r=derive(witness(0,[]))
        self.assertEqual({e['id'] for e in r['obligations']},{'indexed-owner','entry-bytes-and-coordinates','physical-access','saved-frame','stable-memory','pointer-representation','actual-list-path'})
        self.assertTrue(all(e['proved'] is False for e in r['obligations']))
        for k in ['physical_access_proved','initialization_proved','allocation_extent_proved','source_or_native_admission']:
            self.assertFalse(r[k])


    def test_code_stability_and_saved_frame_are_explicit(self):
        r=derive(witness(0,[]))
        obligations={v['id']:v for v in r['obligations']}
        self.assertIn('executing code remains unchanged',obligations['indexed-owner']['text'])
        self.assertIn('valid Thumb continuation',obligations['saved-frame']['text'])
        self.assertIn('private save also writes20bytes',r['modified_coordinates_scope'])

    def test_new_byte_witnesses_match_independent_thumb_execution(self):
        fixtures=[
            (11, witness(160,[(160,19,128,0),(128,8,0,160)]),2048,2052),
            (0x1000b,witness(160,[(160,2,0,192),(192,6,160,224),(224,12,192,0)]),2048,2052),
            (4,witness(160,[(160,9,128,0),(128,8,96,160),(96,7,0,128)]),2048,2048),
            (9,witness(160,[(160,9,0,192),(192,10,160,0)]),164,2048),
            (13,{},2048,0),
        ]
        for request,cells,p,q in fixtures:
            with self.subTest(request=request,p=p,q=q):
                relation=derive(cells,request=request,previous=p,selected=q)
                machine_events,memory,registers=execute_thumb_fixture(cells,request,p,q)
                relation_events=[(e['site']-0x08002000,e['operation'],e['coordinate'],e['value'])
                    for e in relation['memory_events'] if e['operation'] in ('read8','write32')]
                self.assertEqual(relation_events,machine_events)
                self.assertEqual(relation['output_snapshots']['previous_bytes'],[memory[p+i] for i in range(4)])
                self.assertEqual(relation['output_snapshots']['selected_bytes'],[memory[q+i] for i in range(4)])
                for reg,key in [(2,'R2'),(3,'R3')]:
                    value=registers[reg]
                    encoded=['base-plus',value[1]] if isinstance(value,tuple) and value[0]=='base' else value
                    self.assertEqual(relation['conditional_exit_registers'][key],encoded)


def execute_thumb_fixture(cells,request,p,q):
    """Independent raw-instruction test oracle; no production relation helpers."""
    memory=dict(cells);regs=[('entry',i) for i in range(16)];initial=regs[:]
    regs[:4]=[('base',0),request,('base',p),('base',q)]
    stack=[];events=[];pc=0;equal=greater=None
    def add(a,b):
        if isinstance(a,tuple) and a[0]=='base':return ('base',a[1]+b)
        return (a+b)&0xffffffff
    def compare(a,b):
        if isinstance(a,tuple):
            assert a[0]=='base' and b==0
            return False,True
        return a==b,a>b
    for _ in range(4096):
        raw=int.from_bytes(search.SHAPE[pc:pc+2],'little');next_pc=pc+2
        if raw&0xfe00==0xb400:
            numbers=[i for i in range(8) if raw>>i&1]+([14] if raw&256 else [])
            stack=[regs[i] for i in numbers]+stack
        elif raw&0xfe00==0xbc00:
            numbers=[i for i in range(8) if raw>>i&1];assert not raw&256
            for i,value in zip(numbers,stack):regs[i]=value
            stack=stack[len(numbers):]
        elif raw&0xf800==0x2000:regs[(raw>>8)&7]=raw&255
        elif raw&0xf800 in (0x0000,0x0800):
            src=(raw>>3)&7;dst=raw&7;shift=(raw>>6)&31
            regs[dst]=((regs[src]<<shift)&0xffffffff) if raw&0xf800==0 else (regs[src]>>(shift or 32))
        elif raw&0xfe00==0x1c00:
            regs[raw&7]=add(regs[(raw>>3)&7],(raw>>6)&7)
        elif raw&0xfe00==0x1800:
            regs[raw&7]=add(regs[(raw>>3)&7],regs[(raw>>6)&7])
        elif raw&0xffc0==0x4300:regs[raw&7]|=regs[(raw>>3)&7]
        elif raw&0xf800==0x2800:equal,greater=compare(regs[(raw>>8)&7],raw&255)
        elif raw&0xffc0==0x4280:equal,greater=compare(regs[raw&7],regs[(raw>>3)&7])
        elif raw&0xf800==0x7800:
            base=regs[(raw>>3)&7];assert base[0]=='base';at=base[1]+((raw>>6)&31)
            regs[raw&7]=memory[at];events.append((pc,'read8',at,memory[at]))
        elif raw&0xf800==0x6000:
            base=regs[(raw>>3)&7];assert base[0]=='base';at=base[1]+4*((raw>>6)&31);v=regs[raw&7]
            if isinstance(v,tuple):
                assert v[0]=='base';bs=[('base-plus-byte',v[1],i) for i in range(4)];value=['base-plus',v[1]]
            else:bs=[(v>>(8*i))&255 for i in range(4)];value=v
            for i,x in enumerate(bs):memory[at+i]=x
            events.append((pc,'write32',at,value))
        elif raw&0xf000==0xd000:
            condition=(raw>>8)&15;take={0:equal,1:not equal,8:greater,9:not greater}[condition]
            displacement=(raw&255)-(256 if raw&128 else 0)
            if take:next_pc=pc+4+2*displacement
        elif raw&0xf800==0xe000:
            displacement=(raw&2047)-(2048 if raw&1024 else 0);next_pc=pc+4+2*displacement
        elif raw==0x4700:
            assert regs[0]==initial[14] and not stack
            assert all(regs[i]==initial[i] for i in range(4,13))
            return events,memory,regs
        else:raise AssertionError(f'unimplemented test opcode{raw:04x}')
        pc=next_pc
    raise AssertionError('test execution did not return')


if __name__=='__main__':unittest.main()
