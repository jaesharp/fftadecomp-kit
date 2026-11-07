"""New constructed helper graphs, zero counts and finite-prefix obligations."""
import hashlib
import json
import unittest

import allocator_saved_flow as saved
import scheduler_prefix_relation as prefix
import scheduler_descriptor_lifetime as tail


def bl(site,target):
    d=target-site-4
    return (0xf000|((d>>12)&2047)).to_bytes(2,'little')+(0xf800|((d>>1)&2047)).to_bytes(2,'little')


def body(address,data,count,word=None,alignment=()):
    words=[] if word is None else [dict(address=address+word[0],value=word[1],
        load_sites=[address+word[2]],switch_word=False)]
    return saved.Body(address,data,dict(code_bytes=len(data)-4*len(words)-sum(b-a for a,b in alignment),
        literal_and_table_bytes=4*len(words),alignment_bytes=sum(b-a for a,b in alignment),
        alignment=[list(v) for v in alignment],words=words),count)


def program(base=0x08001000,child_change=None):
    c=base;a=base+0x1000;b=base+0x2000;z=base+0x3000;callback=base+0x4000
    child=(bytes.fromhex('10b5 0448 0268 201c 0c21')+bl(b+10,z)+bytes.fromhex('10bc 01bc 0047')+
           (0x08007000).to_bytes(4,'little'))
    if child_change is not None:child=child_change(child,b)
    allocator=prefix.ALLOC_HEAD+bl(a+34,b)+prefix.ALLOC_TAIL
    root=(tail.CALLEE_HEAD+bl(c+34,a)+prefix.POST_ALLOC+bl(c+48,z)+prefix.LINK_BEFORE_POOL+
          (0x08006000).to_bytes(4,'little')+prefix.LINK_AFTER_POOL+tail.COPY+tail.CALL_SETUP+
          bl(c+180,callback)+tail.CALLEE_RETURN)
    return body(c,root,97,(100,0x08006000,40),[(c+98,c+100)]),(
        body(a,allocator,26),body(b,child,9,(20,0x08007000,2)),body(z,bytes.fromhex('1047'),1)),a,z


def bind(p=None):
    return prefix.bind_prefix(*(program() if p is None else p),selector=prefix.SELECTOR)


def zero_image(changes=None):
    # Byte loop covers all four alignments without relying on word padding.
    words=[0xb500,0x1c02,0x2000,0x2900,0xd004,0x7010,0x3201,0x3901,0x2900,0xd1fa,0xbc01,0x4700]
    for i,v in (changes or {}).items():words[i]=v
    payload=b''.join(w.to_bytes(2,'little') for w in words);d=0x03001000
    authority={'effect_evidence':{'schema':'conditional-installed-thumb-zero-effects-v1',
        'image_sha256':hashlib.sha256(payload).hexdigest(),'destination':d,'entry':d,'count':68,
        'inventory':{'instructions':list(range(d,d+len(payload),2))}}}
    receipt=json.dumps(authority).encode()
    return payload,d,d,receipt,hashlib.sha256(receipt).hexdigest()


def rule(count=92,changes=None):
    return prefix.specialize_zero(*zero_image(changes),count,selector=prefix.SELECTOR)


def relation(**kwargs):
    defaults=dict(wrapper_entry_sp=-52,parent_present=False,chain=(),nested_zero_rules=(rule(12),))
    defaults.update(kwargs)
    return prefix.relate_prefix(bind(),rule(),64,selector=prefix.SELECTOR,**defaults)


class PrefixTests(unittest.TestCase):
    def test_relocated_complete_graph_binds(self):
        p=program(0x08008000);r=bind(p)
        self.assertEqual(r.root,0x08008000)
        self.assertEqual(r.zero_pointer_word,0x08006000)
        self.assertEqual(r.nested_zero_sites[0]['ROM_pointer_word'],0x08007000)

    def test_derived_saves_cover_required_registers_without_ABI_guess(self):
        x=bind();f=next(f for f in x.flows if f.address==x.allocator)
        self.assertTrue(set(range(4,13))<=set(f.preserved))
        self.assertEqual(f.private_peak,4);self.assertEqual(f.nested_peak,16)
        self.assertFalse(f.report()['memory_effect_values_closed'])

    def test_high_register_clobber_is_not_hidden(self):
        # Add MOV R9,R0 before the immediate count; adjust whole child shape.
        p=list(program());b=p[1][1];data=b.data[:8]+bytes.fromhex('8146')+b.data[10:]
        p[1]=(p[1][0],saved.Body(b.address,data,b.partition,b.count),p[1][2])
        with self.assertRaisesRegex(ValueError,'does not restore'):bind(tuple(p))

    def test_missing_callee_body_is_refused(self):
        r,hs,a,z=program()
        with self.assertRaisesRegex(ValueError,'lacks complete'):bind((r,(hs[0],hs[2]),a,z))

    def test_count_mismatch_is_refused(self):
        r,hs,a,z=program();r=saved.Body(r.address,r.data,r.partition,98)
        with self.assertRaisesRegex(ValueError,'count differs'):bind((r,hs,a,z))

    def test_root_list_store_mutation_refused(self):
        r,hs,a,z=program();data=r.data[:150]+bytes.fromhex('4760')+r.data[152:]
        with self.assertRaisesRegex(ValueError,'shape differs'):bind((saved.Body(r.address,data,r.partition,r.count),hs,a,z))

    def test_helper_return_control_is_not_assumed(self):
        p=program(child_change=lambda data,b:data[:18]+bytes.fromhex('0847')+data[20:])
        with self.assertRaisesRegex(ValueError,'saved entry LR'):bind(p)

    def test_helper_saved_stack_mismatch_is_refused(self):
        p=program(child_change=lambda data,b:bytes.fromhex('00b5')+data[2:])
        with self.assertRaisesRegex(ValueError,'POP consumes'):bind(p)

    def test_nested_zero_count_setup_is_bound(self):
        b=bind();self.assertEqual(b.nested_zero_sites[0]['count'],12)
        self.assertEqual(b.nested_zero_sites[0]['destination_register'],4)
        self.assertFalse(b.nested_zero_sites[0]['destination_provenance_proved'])

    def test_nested_zero_unknown_count_refused(self):
        p=program(child_change=lambda data,b:data[:8]+bytes.fromhex('211c')+data[10:])
        with self.assertRaisesRegex(ValueError,'immediate-count'):bind(p)

    def test_nested_zero_interior_entry_refused(self):
        # Replace initial PUSH with BEQ count setup; its alternate path also
        # lacks a frame, so either exact frame/return or setup guard must fail.
        p=program(child_change=lambda data,b:bytes.fromhex('02d0')+data[2:])
        with self.assertRaises(ValueError):bind(p)

    def test_nested_zero_requires_its_own_twelve_byte_rule(self):
        with self.assertRaisesRegex(ValueError,'nested allocator zero counts'):
            relation(nested_zero_rules=())

    def test_wrong_nested_image_rejected(self):
        r=rule(12);bad=prefix.ZeroRule(r.count,'0'*64,r.destination,r.entry,r.retained_pin,r.cases_json)
        with self.assertRaisesRegex(ValueError,'counts/image'):relation(nested_zero_rules=(bad,))

    def test_92_byte_rule_covers_exact_writes_all_alignments(self):
        r=rule().report()
        self.assertEqual(r['zero_write_span'],[0,92]);self.assertEqual(len(r['alignment_cases']),4)
        for case in r['alignment_cases']:
            self.assertEqual([x for x in case['writes'] if x[0]=='destination'],
                             [['destination',i,1] for i in range(92)])
        self.assertFalse(r['installed_identity_proved'])

    def test_zero_rule_preserves_count_cursor_and_saved_frame_contract(self):
        r=rule(12).report()
        self.assertEqual(r['preserved_registers'],list(range(3,13))+[14])
        self.assertEqual(r['private_save_span'],[-4,0])
        self.assertEqual(r['R0'],'incoming ThumbLR')
        self.assertEqual(r['R2'],'destination+count')

    def test_retained68_is_not_replayed_or_admitted_as92(self):
        with self.assertRaisesRegex(ValueError,'unchanged successful'):rule(68)
        old=rule(12)
        with self.assertRaisesRegex(ValueError,'actual scheduler count'):
            prefix.relate_prefix(bind(),old,64,wrapper_entry_sp=-52,parent_present=False,chain=(),
                                 nested_zero_rules=(old,),selector=prefix.SELECTOR)

    def test_zero_source_image_pin_cannot_be_substituted(self):
        args=list(zero_image());args[0]=args[0][:4]+bytes.fromhex('0120')+args[0][6:]
        with self.assertRaisesRegex(ValueError,'identity or structure'):
            prefix.specialize_zero(*args,92,selector=prefix.SELECTOR)

    def test_zero_semantic_mutation_refused_even_with_new_input_pin(self):
        with self.assertRaisesRegex(ValueError,'not exactly observed zero'):rule(92,{2:0x2001})

    def test_zero_bad_cursor_refused(self):
        with self.assertRaisesRegex(ValueError,'bounded destination'):rule(92,{6:0x3202})

    def test_zero_count_bound_and_type_preserved(self):
        for count in [-1,True,257]:
            with self.subTest(count=count),self.assertRaisesRegex(ValueError,'bounded count'):rule(count)

    def test_explicit_selectors_required(self):
        with self.assertRaisesRegex(ValueError,'selector'):
            prefix.specialize_zero(*zero_image(),92,selector='default')

    def test_size64_and_allocator_units_are_exact(self):
        a=prefix.allocation_arithmetic(64)
        self.assertEqual((a['scheduler_count'],a['allocator_rounded_bytes'],a['allocator_units']),(92,92,23))
        self.assertFalse(a['allocation_success_proved'])

    def test_size_truncation_and_allocator_rounding_are_exact(self):
        a=prefix.allocation_arithmetic(0x12340041)
        self.assertEqual((a['scheduler_count'],a['allocator_rounded_bytes'],a['allocator_units']),(93,96,24))

    def test_count_wrap_not_assumed_to_allocate_header(self):
        a=prefix.allocation_arithmetic(0xfff0)
        self.assertEqual((a['scheduler_count'],a['allocator_units']),(12,3))
        self.assertFalse(a['object_extent_proved'])

    def test_empty_root_list_writes_only_root_head(self):
        r=relation();writes=[x for x in r['events'] if x['operation']=='write32']
        self.assertEqual([x['address'] for x in writes],[['allocation',0],['scheduler',4]])
        self.assertEqual(r['conditional_cutpoint_registers']['SP'],-132)
        self.assertEqual(r['conditional_cutpoint_registers']['R2'],'allocation+24')

    def test_empty_parent_list_sets_child_head_and_parent(self):
        r=relation(parent_present=True);writes=[x for x in r['events'] if x['operation']=='write32']
        self.assertEqual([x['address'] for x in writes],[['allocation',0],['parent',16],['allocation',12]])

    def test_nonempty_root_list_appends_and_sets_previous(self):
        r=relation(chain=('first',));writes=[x for x in r['events'] if x['operation']=='write32']
        self.assertEqual([x['address'] for x in writes],[['allocation',0],['node','first',8],['allocation',4]])
        self.assertEqual(writes[-1]['value'],['node','first'])

    def test_nonempty_parent_list_keeps_ordered_reloads(self):
        r=relation(parent_present=True,chain=('first','middle','last'))
        reads=[x for x in r['events'] if x['operation']=='read32' and x['address'][0]=='node']
        self.assertEqual([x['address'][1] for x in reads],['first','first','middle','middle','last'])
        self.assertEqual([x['site']-0x08001000 for x in reads],[72,82,84,82,84])
        self.assertEqual(reads[-1]['value'],0)
        self.assertEqual(r['events'][-1]['address'],['allocation',12])

    def test_root_chain_uses_its_distinct_real_sites(self):
        r=relation(chain=('a','b'));reads=[x for x in r['events'] if x['operation']=='read32' and x['address'][0]=='node']
        self.assertEqual([x['site']-0x08001000 for x in reads],[130,140,142])

    def test_null_allocator_is_a_boundary_not_a_usable_allocation(self):
        r=relation(allocation_case='null')
        self.assertFalse(r['reaches_copy_cutpoint'])
        self.assertEqual(r['boundary']['site'],0x08001030)
        self.assertFalse(any(x['operation'].startswith('write') for x in r['events']))

    def test_cyclic_or_overlong_witness_rejected(self):
        for chain in [('x','x'),tuple(str(i) for i in range(129))]:
            with self.subTest(length=len(chain)),self.assertRaisesRegex(ValueError,'finite chain'):
                relation(chain=chain)

    def test_actual_cutpoint_and_memory_are_not_asserted(self):
        r=relation();json.dumps(r)
        self.assertTrue(r['reaches_copy_cutpoint']);self.assertFalse(r['actual_cutpoint_reached'])
        self.assertEqual(len(r['obligations']),8)
        self.assertTrue(all(x['proved'] is False for x in r['obligations']))
        for name in ['actual_heap_shape_proved','allocator_field_values_closed','actual_memory_or_allocation_proved',
                     'full_prefix_memory_effects_closed','callback_effects_closed','unconditional_termination',
                     'source_or_native_admission']:self.assertFalse(r[name])

    def test_frame_peaks_include_nested_zero_save(self):
        r=relation()
        self.assertEqual(r['frame']['allocator_deepest_SP'],-148)
        self.assertEqual(r['frame']['direct_zero_private_save'],[-136,-132])
        self.assertFalse(r['frame']['physical_permissions'])

    def test_callback_source_and_unknown_aliases_survive_projection(self):
        r=relation()
        self.assertEqual(r['conditional_cutpoint_registers']['R9'],'original caller descriptor')
        self.assertIn('all unknown ordinary output origins',r['ambient_aliases_retained'])

    def test_full_helper_memory_sites_are_retained(self):
        r=relation();sites=[x for f in r['helper_flows'] for x in f['memory_sites']]
        self.assertTrue(any(x.get('operation')=='ldr' and x.get('base_register')==0 for x in sites))
        self.assertTrue(any(x.get('operation')=='PUSH' for x in sites))
        self.assertTrue(all(not f['memory_effect_values_closed'] for f in r['helper_flows']))

    def test_all_retained_zero_physical_premises_survive_adapter(self):
        r=rule().report()
        self.assertEqual(len(r['unproved_premises']),6)
        self.assertTrue(any('little-endian' in s for s in r['unproved_premises']))
        self.assertTrue(any('asynchronous' in s for s in r['unproved_premises']))
        self.assertTrue(any('physically disjoint' in s for s in r['unproved_premises']))

    def test_root_protected_saves_and_unknown_local_allocation_are_enumerated(self):
        r=relation();self.assertEqual([e['operation'] for e in r['events'][:3]],
            ['save-words','save-words','allocate-local'])
        self.assertEqual(r['events'][0]['address'],['stack',-96])
        self.assertEqual(r['events'][1]['address'],['stack',-104])
        self.assertEqual(r['events'][2]['address'],['stack',-132])
        self.assertEqual(r['events'][2]['initial_bytes'],'unproved')

    def test_parent_branch_and_nonzero_chain_nodes_are_explicit_premises(self):
        r=relation(parent_present=True,chain=('x',))
        self.assertEqual(r['branch_preconditions'][0]['expression'],'incoming parent !=0')
        self.assertTrue(all(x['proved'] is False for x in r['branch_preconditions']))
        self.assertIn('nonzero',r['branch_preconditions'][1]['expression'])

    def test_combined_frame_budget_is_not_silently_expanded(self):
        with self.assertRaisesRegex(ValueError,'combined live frame'):relation(wrapper_entry_sp=-944)

    def test_new_high_register_private_frame_restores_through_nested_call(self):
        # Separate constructed graph: save incoming R8 through R7, allocate
        # an output local, call a leaf and restore all original saved values.
        a=0x08009000;b=a+0x100;z=a+0x200
        code=bytes.fromhex('f0b5 4746 80b4 82b0 8046')+bl(a+10,b)+bytes.fromhex(
            '02b0 08bc 9846 f0bc 02bc 0847')
        leaf=bytes.fromhex('10b5 041c 0120 10bc 01bc 0047')
        flows=saved.prove_program((body(a,code,12),body(b,leaf,6),body(z,bytes.fromhex('1047'),1)),
                                   a,z,selector=saved.SELECTOR)
        f=next(f for f in flows if f.address==a)
        self.assertEqual((f.private_peak,f.nested_peak),(32,40))
        self.assertTrue(set(range(4,13))<=set(f.preserved))

    def test_saved_origin_loop_join_does_not_grant_termination(self):
        a=0x0800a000;z=a+0x100
        code=bytes.fromhex('10b5 041c 0138 0028 fcdc 10bc 01bc 0047')
        flows=saved.prove_program((body(a,code,8),body(z,bytes.fromhex('1047'),1)),a,z,selector=saved.SELECTOR)
        f=next(f for f in flows if f.address==a)
        self.assertIn(4,f.preserved);self.assertFalse(f.report()['termination_proved'])


    def test_nested_call_invalidates_possible_output_local_origin(self):
        a=0x0800b000;z=a+0x100
        code=bytes.fromhex('7046 81b0 0090')+bl(a+6,z)+bytes.fromhex('0098 01b0 0047')
        with self.assertRaisesRegex(ValueError,'saved entry LR'):
            saved.prove_program((body(a,code,7),body(z,bytes.fromhex('1047'),1)),a,z,selector=saved.SELECTOR)

    def test_unproved_external_store_invalidates_possible_local_origin(self):
        a=0x0800c000;z=a+0x100
        code=bytes.fromhex('7046 81b0 0090 0860 0098 01b0 0047')
        with self.assertRaisesRegex(ValueError,'saved entry LR'):
            saved.prove_program((body(a,code,7),body(z,bytes.fromhex('1047'),1)),a,z,selector=saved.SELECTOR)

    def test_reestablished_local_after_call_has_exact_saved_origin(self):
        a=0x0800d000;z=a+0x100
        code=bytes.fromhex('10b5 7446 81b0')+bl(a+6,z)+bytes.fromhex('0094 0098 01b0 10bc 02bc 0047')
        flows=saved.prove_program((body(a,code,10),body(z,bytes.fromhex('1047'),1)),a,z,selector=saved.SELECTOR)
        f=next(f for f in flows if f.address==a)
        self.assertIn(4,f.preserved)
        self.assertTrue(any('Protected saved words' in p for p in f.report()['unproved_premises']))


if __name__=='__main__':unittest.main()
