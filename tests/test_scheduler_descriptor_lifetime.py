"""New synthetic scheduler-cutpoint cases; no ROM or original producer calls."""
import hashlib
import json
import unittest

import scheduler_descriptor_lifetime as kernel

W = kernel.Word


def bl(site, target):
    delta = target-site-4
    return ((0xf000 | ((delta >> 12) & 2047)).to_bytes(2,'little') +
            (0xf800 | ((delta >> 1) & 2047)).to_bytes(2,'little'))


def fixture(w=0x08001000, c=0x08002000, prefix=b'\x07\x1c'):
    wrapper = kernel.WRAPPER_HEAD+bl(w+30,c)+kernel.WRAPPER_TAIL+(0x02001000).to_bytes(4,'little')
    head = kernel.CALLEE_HEAD+bl(c+34,0x08004000)+prefix
    before_call = head+kernel.COPY+kernel.CALL_SETUP
    callee = before_call+bl(c+len(before_call),0x08005000)+kernel.CALLEE_RETURN
    wp = dict(code_bytes=56,literal_and_table_bytes=4,alignment_bytes=0,alignment=[],
              words=[dict(address=w+56,value=0x02001000,load_sites=[w+18],switch_word=False)])
    cp = dict(code_bytes=len(callee),literal_and_table_bytes=0,alignment_bytes=0,alignment=[],words=[])
    def authority(data,address,partition,role,count):
        record=dict(address=address,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),
                    instructions=count,partition=partition)
        schema=('conditional-thumb-saved-alias-obligations-v1' if role=='owner'
                else 'complete-thumb-rom-zero-call-interface-v1')
        return dict(evidence=dict(schema=schema,**{role:record}))
    return [wrapper,w,authority(wrapper,w,wp,'owner',27),callee,c,
            authority(callee,c,cp,'caller',len(callee)//2-2)]


def bind(f=None, selector=kernel.SELECTOR):
    if f is None:
        f=fixture()
    wb,w,wr,cb,c,cr=f
    wr=json.dumps(wr).encode(); cr=json.dumps(cr).encode()
    return kernel.bind_layout(wb,w,wr,hashlib.sha256(wr).hexdigest(),cb,c,cr,
                              hashlib.sha256(cr).hexdigest(),selector=selector)


def repin(f, role):
    bi,ri=(0,2) if role=='owner' else (3,5)
    f[ri]['evidence'][role]['sha256']=hashlib.sha256(f[bi]).hexdigest()


def state():
    regs={i:W.unproved(f'entry-r{i}') for i in (*range(13),14)}
    regs.update({0:W.constant(0x08003001),1:W.constant(64),2:W.pointer(-48)})
    words={-44:W.unproved('subject'),-28:W.constant(158+(1<<16))}
    return [[kernel.LOCAL]*16,words,regs]


def derive(s=None,layout=None,**kwargs):
    return kernel.derive(bind() if layout is None else layout,*(state() if s is None else s),
                         selector=kernel.SELECTOR,**kwargs)


class SchedulerDescriptorLifetimeTests(unittest.TestCase):
    def test_complete_relocated_shapes_bind(self):
        x=bind(fixture(w=0x08006000,c=0x08007000))
        self.assertEqual((x.wrapper,x.callee),(0x08006000,0x08007000))
        self.assertEqual(x.prefix_calls,((0x08007022,0x08004000),))

    def test_explicit_selector_required(self):
        with self.assertRaisesRegex(ValueError,'selector'): bind(selector='default')

    def test_authority_pin_required(self):
        f=fixture(); wr=json.dumps(f[2]).encode(); cr=json.dumps(f[5]).encode()
        with self.assertRaisesRegex(ValueError,'pin'):
            kernel.bind_layout(f[0],f[1],wr,'0'*64,f[3],f[4],cr,hashlib.sha256(cr).hexdigest(),
                               selector=kernel.SELECTOR)

    def test_authority_schema_required(self):
        f=fixture(); f[2]['evidence']['schema']='generic-success'
        with self.assertRaisesRegex(ValueError,'schema'): bind(f)

    def test_original_body_identity_is_not_rewritten(self):
        f=fixture(); f[0]=b'\x00\x00'+f[0][2:]
        with self.assertRaisesRegex(ValueError,'identity'): bind(f)

    def test_complete_instruction_count_required(self):
        f=fixture(); f[5]['evidence']['caller']['instructions']+=1
        with self.assertRaisesRegex(ValueError,'count'): bind(f)

    def test_wrapper_saved_register_change_rejected(self):
        f=fixture(); f[0]=b'\x30\xb5'+f[0][2:]; repin(f,'owner')
        with self.assertRaisesRegex(ValueError,'wrapper instruction'): bind(f)

    def test_wrapper_target_must_be_bound_callee(self):
        f=fixture(); f[0]=f[0][:30]+bl(f[1]+30,f[4]+4)+f[0][34:]; repin(f,'owner')
        with self.assertRaisesRegex(ValueError,'wrapper instruction'): bind(f)

    def test_wrapper_literal_extent_and_load_site_checked(self):
        f=fixture(); f[2]['evidence']['owner']['partition']['words'][0]['load_sites']=[f[1]+16]
        with self.assertRaisesRegex(ValueError,'literal binding'): bind(f)

    def test_alignment_is_explicit(self):
        f=fixture(); f[1]+=2
        with self.assertRaisesRegex(ValueError,'authority pin'): bind(f)

    def test_truncated_complete_callee_rejected(self):
        f=fixture(); f[3]=f[3][:-2]; repin(f,'caller')
        with self.assertRaisesRegex(ValueError,'identity'): bind(f)

    def test_copy_reset_store_must_remain_halfword(self):
        f=fixture(); offset=len(kernel.CALLEE_HEAD)+6+20
        f[3]=f[3][:offset]+b'\x08\x60'+f[3][offset+2:]; repin(f,'caller')
        with self.assertRaisesRegex(ValueError,'callee frame'): bind(f)

    def test_prologue_arithmetic_change_rejected(self):
        f=fixture(); f[3]=f[3][:22]+b'\xc0\x20'+f[3][24:]; repin(f,'caller')
        with self.assertRaisesRegex(ValueError,'callee frame'): bind(f)

    def test_suffix_bypass_rejected(self):
        # Conditional B skips the first copy MOV, while fallthrough still
        # reaches every instruction, so reachability alone cannot reject it.
        f=fixture(prefix=b'\x00\xd0')
        with self.assertRaisesRegex(ValueError,'bypasses'): bind(f)

    def test_prefix_reentering_saved_prologue_rejected(self):
        # At c+38, BNE c+0, followed by the copy on its fallthrough edge.
        f=fixture(prefix=(0xd100|((-42//2)&255)).to_bytes(2,'little'))
        with self.assertRaisesRegex(ValueError,'reenters prologue'): bind(f)

    def test_prefix_nontermination_is_not_discharged(self):
        # BNE to itself is permitted only as an open prefix termination fact.
        r=derive(layout=bind(fixture(prefix=b'\xfe\xd1'))).report()
        self.assertFalse(r['unconditional_termination'])
        self.assertFalse(r['prefix_effects_closed'])

    def test_extra_terminal_path_is_rejected(self):
        f=fixture(prefix=b'\x70\x47')
        with self.assertRaisesRegex(ValueError,'reachable CFG'): bind(f)

    def test_twenty_eight_source_bytes_copied_in_order(self):
        s=state(); s[1]={-48+4*i:W.unproved(f'descriptor:{i}') for i in range(7)}
        x=derive(s)
        self.assertEqual(x.reads[:7],tuple(range(-48,-20,4)))
        self.assertEqual(x.writes[:7],tuple(range(-144,-116,4)))
        self.assertEqual(x.callback_words[1:],tuple(s[1][-48+4*i] for i in range(1,7)))

    def test_only_lower_halfword_is_initialized_by_reset(self):
        x=derive(); old=W.unproved('caller-word:-48')
        self.assertEqual(x.callback_words[0].bytes[:2],W.constant(0).bytes[:2])
        self.assertEqual(x.callback_words[0].bytes[2:],old.bytes[2:])
        self.assertEqual(x.scalar_at_callback(0,2),0)
        with self.assertRaisesRegex(ValueError,'unproved'): x.scalar_at_callback(0,4)

    def test_initialized_slices_keep_signedness_and_flags(self):
        s=state(); s[1][-28]=W.constant(0x1234fffe)
        x=derive(s)
        self.assertEqual(x.scalar_at_callback(20,2,signed=True),-2)
        self.assertEqual(x.scalar_at_callback(22,2),0x1234)

    def test_opaque_subject_is_not_scalar(self):
        with self.assertRaisesRegex(ValueError,'unproved'): derive().scalar_at_callback(4,4)

    def test_pointer_subject_keeps_exact_origin(self):
        s=state(); s[1][-44]=W.pointer(-16); x=derive(s)
        self.assertEqual(x.callback_words[1].require_pointer(),-16)
        with self.assertRaisesRegex(ValueError,'pointer bytes'): x.scalar_at_callback(4,4)

    def test_partial_pointer_reset_refused(self):
        s=state(); s[1][-48]=W.pointer(-16)
        with self.assertRaisesRegex(ValueError,'partial overwrite|partial pointer'): derive(s)

    def test_all_opaque_words_are_still_transferred(self):
        s=state(); s[1]={}; x=derive(s)
        self.assertEqual(x.callback_words[6],W.unproved('caller-word:-24'))
        self.assertFalse(x.report()['copy']['initialized_source_bytes_proved'])

    def test_callback_receives_copy_and_ambient_original_pointer(self):
        x=derive(); regs=dict(x.callback_registers)
        self.assertEqual(regs[1],W.pointer(-144))
        self.assertEqual(regs[9],W.pointer(-48))
        self.assertNotEqual(regs[1],regs[9])
        self.assertEqual(regs[2],W.unproved('allocation-plus-24'))
        self.assertEqual(regs[3],state()[2][0])

    def test_scratch_words_remain_exposed_to_callback(self):
        x=derive(); regs=dict(x.callback_registers)
        self.assertEqual(regs[4],W.unproved('caller-word:-32'))
        self.assertEqual(regs[5],W.constant(158+(1<<16)))
        self.assertEqual(set(regs),set(range(15)))

    def test_original_unknown_registers_restore_from_exact_saves(self):
        s=state(); s[2][8]=W.pointer(-4); s[2][9]=W.pointer(-12); x=derive(s)
        regs=dict(x.returned_registers)
        for reg in (4,5,6,7,8,9): self.assertEqual(regs[reg],s[2][reg])
        self.assertEqual(regs[3],s[2][8])
        self.assertEqual(regs[1],s[2][14])

    def test_R2_is_overwritten_but_R10_R11_R12_are_not_assumed_preserved(self):
        x=derive(); regs=dict(x.returned_registers)
        self.assertEqual(regs[2],W.constant(1))
        for reg in (10,11,12):
            self.assertEqual(regs[reg],W.unproved(f'callback-output:{reg}'))
        self.assertIn('R10/R11/R12',' '.join(x.report()['lifetime']['possible_escaped_aliases']))

    def test_exact_nested_saved_slots_and_lifetimes(self):
        s=state(); x=derive(s); saved=dict(x.saved)
        self.assertEqual(saved[-116],s[2][2])
        self.assertEqual(saved[-112],s[2][9])
        self.assertEqual(saved[-92],W.constant(0x08001023))
        self.assertEqual(saved[-84],s[2][8])
        self.assertEqual(len(saved),12)
        self.assertEqual(dict(x.returned_registers)[13],W.pointer(-64))

    def test_callback_copy_is_dead_after_return(self):
        x=derive()
        self.assertEqual(x.scalar_at_callback(0,2),0)
        with self.assertRaisesRegex(ValueError,'lifetime ended'): x.scalar_after_return(0,2)

    def test_callback_local_mutation_does_not_become_post_return_fact(self):
        r=derive().report()['lifetime']
        self.assertEqual(r['retired_local_contents'],'unknown after ordinary callback; no current value assertion')
        self.assertFalse(r['dead_memory_erased'])
        self.assertFalse(r['nonescape_proved'])

    def test_actual_size_specialization_is_92_not_old_68(self):
        x=derive(); self.assertEqual(x.allocation_count,92)
        obligation=next(o for o in x.report()['obligations'] if o['id']=='zero-count')
        self.assertEqual(obligation['count'],92)
        self.assertFalse(obligation['proved'])

    def test_size_truncation_and_addition_wrap_are_not_hidden(self):
        s=state(); s[2][1]=W.constant(0x1234fff0); x=derive(s)
        self.assertEqual(x.allocation_count,12)
        self.assertFalse(x.report()['size']['minimum_header_extent_numeric'])
        self.assertFalse(x.report()['physical_permissions_proved'])

    def test_fresh_post_callback_scheduler_read_is_not_cached(self):
        accesses=derive().report()['conditional_external_accesses']
        self.assertEqual(accesses[2]['operation'],'read32')
        self.assertEqual(accesses[2]['required_value'],'post-callback scheduler pointer')
        self.assertEqual(accesses[4]['value'],'post-callback read16 xor 1')

    def test_all_conditions_remain_open_and_json_serializable(self):
        r=derive().report(); json.dumps(r)
        self.assertEqual(len(r['obligations']),9)
        self.assertTrue(all(o['proved'] is False for o in r['obligations']))
        for key in ('native_admission','source_or_ELF_admission','callback_effects_closed',
                    'full_scheduler_effects_closed','actual_reaching_state_proved',
                    'allocator_or_installed_image_proved'): self.assertIs(r[key],False)

    def test_caller_source_words_are_not_changed_by_copy(self):
        s=state(); x=derive(s)
        self.assertEqual(dict(x.caller_words)[-28],s[1][-28])
        self.assertEqual(dict(x.caller_words)[-48],W.unproved('caller-word:-48'))

    def test_source_requires_live_pointer_provenance(self):
        s=state(); s[2][2]=W.constant(0x03000000)
        with self.assertRaisesRegex(ValueError,'pointer provenance'): derive(s)

    def test_source_extent_must_fit_live_caller(self):
        s=state(); s[2][2]=W.pointer(-24)
        with self.assertRaisesRegex(ValueError,'fit live caller'): derive(s)

    def test_saved_source_slot_rejected(self):
        s=state(); s[0][5]=kernel.SAVED
        with self.assertRaisesRegex(ValueError,'saved/protected'): derive(s)

    def test_protected_source_slot_rejected(self):
        with self.assertRaisesRegex(ValueError,'saved/protected'): derive(protected=(-32,))

    def test_outside_caller_word_rejected(self):
        s=state(); s[1][-68]=W.constant(0)
        with self.assertRaisesRegex(ValueError,'fit the complete'): derive(s)

    def test_dead_pointer_payload_rejected(self):
        s=state(); s[1][-44]=W.pointer(-100)
        with self.assertRaisesRegex(ValueError,'outside live caller'): derive(s)

    def test_missing_ambient_register_rejected(self):
        s=state(); del s[2][12]
        with self.assertRaisesRegex(ValueError,'all incoming register'): derive(s)

    def test_unknown_size_is_not_fabricated(self):
        s=state(); s[2][1]=W.unproved('size')
        with self.assertRaisesRegex(ValueError,'concrete incoming u32'): derive(s)

    def test_frame_total_bound_includes_both_allocations(self):
        s=state(); s[0]=[kernel.LOCAL]*237
        with self.assertRaisesRegex(ValueError,'bounded classified'): derive(s)

    def test_bad_scalar_slice_rejected(self):
        x=derive()
        for offset,width in [(1,2),(26,4),(28,1),(0,3)]:
            with self.subTest(offset=offset,width=width):
                with self.assertRaisesRegex(ValueError,'aligned descriptor'): x.scalar_at_callback(offset,width)

    def test_input_allocation_label_does_not_authenticate_allocator_return(self):
        s=state(); s[1][-44]=W.unproved('allocation'); x=derive(s)
        self.assertEqual(x.callback_words[1],s[1][-44])
        self.assertNotEqual(dict(x.returned_registers)[0],x.callback_words[1])
        self.assertEqual(dict(x.returned_registers)[0],dict(x.callback_registers)[7])

    def test_callback_havoc_label_does_not_forge_preservation(self):
        s=state(); s[2][10]=W.unproved('callback-output:10'); x=derive(s)
        self.assertNotEqual(dict(x.returned_registers)[10],s[2][10])
        self.assertEqual(dict(x.returned_registers)[10],W.unproved('scheduler-1:callback-output:10'))

    def test_missing_caller_word_does_not_unify_with_supplied_origin(self):
        s=state(); s[1][-44]=W.unproved('caller-word:-48'); x=derive(s)
        self.assertNotEqual(dict(x.caller_words)[-48],dict(x.caller_words)[-44])
        self.assertEqual(x.callback_words[0].bytes[2:],dict(x.caller_words)[-48].bytes[2:])

    def test_multiple_origin_namespace_collisions_are_resolved(self):
        s=state(); s[1][-44]=W.unproved('allocation'); s[1][-40]=W.unproved('scheduler-1:allocation')
        x=derive(s)
        self.assertEqual(dict(x.returned_registers)[0],W.unproved('scheduler-2:allocation'))
        self.assertEqual(x.callback_words[1],s[1][-44])
        self.assertEqual(x.callback_words[2],s[1][-40])

    def test_prefix_must_establish_actual_SP_and_preserve_source_before_copy(self):
        obligations={o['id']:o for o in derive().report()['obligations']}
        o=obligations['prefix-reaching-state']
        self.assertIn('exact SP=wrapper_entry_SP-80',o['scope'])
        self.assertIn('source and all saved/caller bytes unchanged',o['scope'])
        self.assertFalse(o['proved'])

    def test_size_arithmetic_does_not_grant_allocator_register_survival(self):
        obligations={o['id']:o for o in derive().report()['obligations']}
        self.assertIn('R4 numeric count must survive the allocator',obligations['zero-count']['scope'])
        self.assertFalse(obligations['zero-count']['proved'])


if __name__=='__main__': unittest.main()
