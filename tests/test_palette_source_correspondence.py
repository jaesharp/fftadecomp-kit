"""Synthetic typed C and independent retained-certificate interface fixtures."""
import copy
import hashlib
from pathlib import Path
import re
import sys
import unittest

sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import palette_source_correspondence as c
import palette_value_composition as ir

SOURCE=b'''typedef unsigned char byte;
typedef unsigned short half;
typedef signed short signedhalf;
typedef unsigned int word;
extern half colors[];
extern byte saved[][12];
extern void *copy_bytes(void *out, const void *in, word length);
void paint(half first, half count, signedhalf red, signedhalf green, signedhalf blue, byte restore) {
 signedhalf channel[3];
 signedhalf *change[3]={&red,&green,&blue};
 half last; half i; half j;
 last=first+count-1;
 if(last>511) last=511;
 if(restore==0) {
  for(i=first;i<=last;i++) {
   channel[0]=colors[i]&31;
   channel[1]=(colors[i]&992)>>5;
   channel[2]=(colors[i]&31744)>>10;
   for(j=0;j<3;j++) {
    saved[i][j]=channel[j];
    if(*change[j]!=0) {
     channel[j]+=*change[j];
     if(channel[j]<0) channel[j]=0;
     else if(channel[j]>31) channel[j]=31;
    }
   }
   colors[i]=(channel[1]<<5)|channel[0]|(channel[2]<<10);
  }
 } else {
  for(i=first;i<=last;i++) {
   for(j=0;j<3;j++) {
    channel[j]=saved[i][j];
    if(*change[j]!=0) {
     channel[j]+=*change[j];
     if(channel[j]<0) channel[j]=0;
     else if(channel[j]>31) channel[j]=31;
    }
   }
   colors[i]=(channel[1]<<5)|channel[0]|(channel[2]<<10);
  }
 }
}'''


def fixture():
    # These are synthetic *premise* certificates, not claims that the fixture
    # bytes are machine-proved. Test the new consumer's relation and guards.
    k=ir.constant;idx=('input','index',9);limit=('input','limit',9)
    first=('low',('input','r0',32),16)
    last=ir.low(ir.add(first,ir.low(('input','r1',32),16),k(-1)),16)
    restore=ir.low(('input','incoming4',32),8)
    palette=ir.add(k(0x02001000),ir.multiply(2,idx))
    rows=[ir.add(k(0x02004000),ir.multiply(12,idx),k(j)) for j in range(3)]
    deltas=[('low',('input',name,32),16) for name in ('r2','r3','incoming0')]
    normal_inputs=[('low',('read',0,2,palette),5),('extract',('read',1,2,palette),5,5),('extract',('read',2,2,palette),10,5)]
    restored_inputs=[('read',j,1,rows[j]) for j in range(3)]
    iterations=[]
    for mode,inputs,header in [('normal',normal_inputs,0x08001040),('restore',restored_inputs,0x08001080)]:
        outputs=[('adjust16',value,delta) for value,delta in zip(inputs,deltas)]
        events=[]
        for j in range(3):
            address,width=(palette,2) if mode=='normal' else (rows[j],1)
            events.append(('external-read',header+2*j,address,width,('read',j,width,address)))
        if mode=='normal':
            for j in range(3):events.append(('external-write',header+8+2*j,rows[j],1,inputs[j]))
        events.append(('external-write',header+20,palette,2,ir.low(ir.bor(outputs[0],ir.multiply(32,outputs[1]),ir.multiply(1024,outputs[2])),16)))
        iterations.append({'mode':mode,'header':header,'events':events,'channel_inputs':inputs,'channel_outputs':outputs,
            'next_index':ir.add(idx,k(1)),'limit':limit,'index_domain':[0,511],
            'non_channel_memory_unchanged':True,'distinct_external_read_tokens_preserved':True})
    paths=[]
    for clamp in (False,True):
        bound=k(511) if clamp else last
        for mode,header in [('normal',0x08001040),('restore',0x08001080)]:
            for enter in (False,True):
                paths.append({'guards':[(('ugt' if clamp else 'ule'),last,k(511)),
                    (('eq' if mode=='normal' else 'ne'),restore,k(0)),(('ule' if enter else 'ugt'),first,bound)],
                    'stop':header if enter else 0x08001100,'last':bound})
    machine={'schema':ir.SELECTOR,'conditional_owner_machine_value_trace':True,'physical_memory_permission':False,
        'source_or_ELF_admission':False,'address':0x08001000,'end':0x08001110,'instructions':100,
        'ROM_sha256':'synthetic-rom','body_sha256':'synthetic-body','iterations':iterations,'prefix_paths':paths,
        'epilogue_from_retained_frame':[0x08001100],'required_unproved_conditions':['synthetic external memory condition']}
    inventory={'schema':'thumb-compiler-local-copy-elf-inventory-v1','inventory_only':True,
        'address':machine['address'],'end':machine['end'],'instructions':100,'ROM_sha256':'synthetic-rom',
        'linked_text_sha256':'synthetic-body','helper_identity':[0x08002000,0x08002004,2,'synthetic-helper'],
        'relocations':[[12,10,'memcpy',0x08002000],[200,2,'colors',0x02001000],[204,2,'saved',0x02004000]]}
    return machine,inventory


def authority(source,machine,inventory):
    return {'independently_established_frozen_certificates':True,'machine_sha256':c.digest(machine),
        'inventory_sha256':c.digest(inventory),'original_source_sha256':hashlib.sha256(source).hexdigest(),
        'original_source_and_object_lineage_authenticated':True}


class PaletteSourceTests(unittest.TestCase):
    def reject(self,source):
        with self.assertRaises(ValueError):c.close_source(source)

    def test_synthetic_complete_source_ast_closes(self):
        model=c.close_source(SOURCE)
        self.assertEqual(model['parameter_types'],['u16','u16','s16','s16','s16','u8'])
        self.assertEqual(model['pointer_initializer_order'],['red','green','blue'])
        self.assertEqual(model['history_stride'],12);self.assertEqual(model['external_calls_in_C_body'],0)

    def test_alpha_renaming_function_data_and_local_roles(self):
        original=c.close_source(SOURCE);names=['paint','colors','saved','first','count','red','green','blue','restore','channel','change','last','i','j']
        rename={name:'renamed_'+name for name in names}
        changed=re.sub(rb'\b[A-Za-z_][A-Za-z_0-9]*\b',lambda m:rename.get(m.group().decode(),m.group().decode()).encode(),SOURCE)
        model=c.close_source(changed)
        self.assertEqual(model['function'],'renamed_paint');self.assertNotEqual(model['AST_sha256'],original['AST_sha256'])

    def test_comments_hex_literals_and_redundant_parentheses(self):
        changed=SOURCE.replace(b'last=first+count-1;',b'last=((first+count)-1); /* no operation */').replace(b'&31;',b'&0x1f;').replace(b'>>5',b'>>0x5')
        self.assertEqual(c.close_source(changed)['body_AST_sha256'],c.close_source(SOURCE)['body_AST_sha256'])

    def test_C_precedence_is_structural_not_textual(self):
        parser=c.Parser(b'a+b*c<<5|d');actual=parser.expression()
        expected=c.binary('|',c.binary('<<',c.binary('+',c.ident('a'),c.binary('*',c.ident('b'),c.ident('c'))),c.integer(5)),c.ident('d'))
        self.assertEqual(actual,expected)

    def test_unsigned_short_signature_and_signed_channel_types_required(self):
        self.reject(SOURCE.replace(b'half first',b'signedhalf first'))
        self.reject(SOURCE.replace(b'signedhalf channel[3]',b'half channel[3]'))

    def test_incoming_argument_order_cannot_change_initializer_relation(self):
        self.reject(SOURCE.replace(b'{&red,&green,&blue}',b'{&blue,&green,&red}'))

    def test_sixth_argument_must_remain_unsigned_byte(self):
        self.reject(SOURCE.replace(b'byte restore',b'half restore'))

    def test_extra_argument_or_return_value_refuses(self):
        self.reject(SOURCE.replace(b'byte restore)',b'byte restore, word extra)'))
        self.reject(SOURCE.replace(b'void paint',b'word paint'))

    def test_last_assignment_conversion_cannot_move_or_disappear(self):
        self.reject(SOURCE.replace(b'half last;',b'word last;'))
        self.reject(SOURCE.replace(b'last=first+count-1;',b'last=first+count;'))

    def test_clamp_and_entry_guard_exact(self):
        self.reject(SOURCE.replace(b'last>511',b'last>=511'))
        self.reject(SOURCE.replace(b'i<=last',b'i<last'))

    def test_restore_branch_polarity_exact(self):
        self.reject(SOURCE.replace(b'restore==0',b'restore!=0'))

    def test_local_channel_array_and_pointer_types_exact(self):
        self.reject(SOURCE.replace(b'channel[3];',b'channel[4];'))
        self.reject(SOURCE.replace(b'signedhalf *change',b'half *change'))

    def test_inner_loop_bounds_and_increment_exact(self):
        self.reject(SOURCE.replace(b'j<3',b'j<=3'))
        self.reject(SOURCE.replace(b'j++)',b'i++)'))

    def test_channel_extract_masks_and_shift_exact(self):
        self.reject(SOURCE.replace(b'&992',b'&993'))
        self.reject(SOURCE.replace(b'>>10',b'>>9'))

    def test_history_stride_or_element_type_cannot_be_assumed(self):
        self.reject(SOURCE.replace(b'saved[][12]',b'saved[][3]'))
        self.reject(SOURCE.replace(b'extern byte saved',b'extern half saved'))

    def test_history_read_and_write_order_retained(self):
        self.reject(SOURCE.replace(b'saved[i][j]=channel[j];',b'saved[i][j]=channel[0];'))
        self.reject(SOURCE.replace(b'channel[j]=saved[i][j];',b'channel[j]=saved[j][i];'))

    def test_compound_assignment_and_signed_clamp_cannot_change(self):
        self.reject(SOURCE.replace(b'channel[j]+=*change[j];',b'channel[j]=*change[j];'))
        self.reject(SOURCE.replace(b'channel[j]<0',b'channel[j]>0'))

    def test_zero_delta_must_preserve_original_restored_byte(self):
        self.reject(SOURCE.replace(b'if(*change[j]!=0)',b'if(*change[j]==0)'))

    def test_final_channel_order_and_operator_are_closed(self):
        self.reject(SOURCE.replace(b'(channel[1]<<5)|channel[0]',b'(channel[0]<<5)|channel[1]'))
        self.reject(SOURCE.replace(b'|channel[0]|',b'+channel[0]+'))

    def test_extra_statements_calls_or_storage_refuse(self):
        self.reject(SOURCE.replace(b'last=first+count-1;',b'last=first+count-1; restore=0;'))
        self.reject(SOURCE.replace(b'last=first+count-1;',b'copy_bytes(channel,change,12); last=first+count-1;'))
        self.reject(SOURCE+b'\nword global;')

    def test_preprocessing_splices_and_trigraphs_refuse(self):
        for prefix in (b'#define first second\n',b'// hidden\\\n',b'??=define first second\n'):
            self.reject(prefix+SOURCE)

    def test_qualifiers_and_identifier_shadowing_refuse(self):
        self.reject(SOURCE.replace(b'half i;',b'const half i;'))
        self.reject(SOURCE.replace(b'half i;',b'half first;'))
        self.reject(SOURCE.replace(b'half i;',b'half break;'))

    def test_lexical_invalid_or_ambiguous_literals_refuse(self):
        self.reject(SOURCE.replace(b'511',b'0777'))
        self.reject(SOURCE+b'\x00')
        self.reject(SOURCE.replace(b'511',b'511u'))

    def test_bounded_parser_refuses_deep_expression(self):
        self.reject(SOURCE.replace(b'first+count-1',b'('*70+b'first'+b')'*70))

    def test_complete_synthetic_source_machine_relation(self):
        machine,inventory=fixture()
        proof=c.verify(SOURCE,machine,inventory,selector=c.SELECTOR,reuse_authority=authority(SOURCE,machine,inventory))
        self.assertTrue(proof['conditional_C_AST_value_access_correspondence'])
        self.assertFalse(proof['source_or_ELF_admission']);self.assertFalse(proof['physical_memory_permission'])
        self.assertEqual([row['machine_bits'] for row in proof['entry_argument_transport']][-2:],['incoming word at entrySP+0','incoming word at entrySP+4'])
        self.assertEqual(proof['relation']['normal_external_events'],7)

    def test_machine_reusing_one_read_for_three_channels_refuses(self):
        machine,inventory=fixture();machine['iterations'][0]['events'][1]=machine['iterations'][0]['events'][0]
        with self.assertRaisesRegex(ValueError,'ordered accesses'):c.correlate(machine,inventory,c.close_source(SOURCE))

    def test_machine_swapped_delta_pairing_refuses(self):
        machine,inventory=fixture();outputs=machine['iterations'][1]['channel_outputs'];outputs[0],outputs[2]=outputs[2],outputs[0]
        with self.assertRaisesRegex(ValueError,'values'):c.correlate(machine,inventory,c.close_source(SOURCE))

    def test_machine_history_effect_reordering_refuses(self):
        machine,inventory=fixture();events=machine['iterations'][0]['events'];events[3],events[4]=events[4],events[3]
        with self.assertRaisesRegex(ValueError,'ordered accesses'):c.correlate(machine,inventory,c.close_source(SOURCE))

    def test_machine_entry_guard_or_last_expression_change_refuses(self):
        machine,inventory=fixture();machine['prefix_paths'][0]['last']=ir.constant(0)
        with self.assertRaisesRegex(ValueError,'wrapped min'):c.correlate(machine,inventory,c.close_source(SOURCE))

    def test_machine_successor_or_frame_claim_change_refuses(self):
        for changed in ('next_index','non_channel_memory_unchanged'):
            machine,inventory=fixture();machine['iterations'][0][changed]=ir.constant(0) if changed=='next_index' else False
            with self.assertRaises(ValueError):c.correlate(machine,inventory,c.close_source(SOURCE))

    def test_different_ROM_body_or_extent_refuses(self):
        for key in ('ROM_sha256','linked_text_sha256','end'):
            machine,inventory=fixture();inventory[key]='changed'
            with self.assertRaises(ValueError):c.correlate(machine,inventory,c.close_source(SOURCE))

    def test_unknown_or_inconsistent_original_data_binding_refuses(self):
        machine,inventory=fixture();inventory['relocations'].append([208,2,'colors',0x02003000])
        with self.assertRaisesRegex(ValueError,'inconsistent'):c.correlate(machine,inventory,c.close_source(SOURCE))

    def test_original_copy_symbol_or_helper_target_change_refuses(self):
        for index,value in ((2,'user_copy'),(3,0x08003000)):
            machine,inventory=fixture();inventory['relocations'][0][index]=value
            with self.assertRaisesRegex(ValueError,'genuine original'):c.correlate(machine,inventory,c.close_source(SOURCE))

    def test_source_object_lineage_and_certificate_pins_required(self):
        machine,inventory=fixture();base=authority(SOURCE,machine,inventory)
        for key,value in (('machine_sha256','changed'),('inventory_sha256','changed'),('original_source_sha256','changed'),('original_source_and_object_lineage_authenticated',False)):
            changed=dict(base);changed[key]=value
            with self.assertRaisesRegex(ValueError,'identity differs'):c.verify(SOURCE,machine,inventory,selector=c.SELECTOR,reuse_authority=changed)

    def test_explicit_selector_required(self):
        machine,inventory=fixture()
        with self.assertRaisesRegex(ValueError,'explicit selector'):c.verify(SOURCE,machine,inventory,selector='default',reuse_authority=authority(SOURCE,machine,inventory))

    def test_numeric_definedness_bounds_are_independent_of_memory_permission(self):
        machine,inventory=fixture();proof=c.verify(SOURCE,machine,inventory,selector=c.SELECTOR,reuse_authority=authority(SOURCE,machine,inventory))
        defined=proof['C_definedness']
        self.assertEqual(defined['first_plus_count_minus_one_signed_int_range'],[-1,131069])
        self.assertEqual(defined['promoted_channel_plus_delta_range'],[-32768,33022])
        self.assertEqual(defined['maximum_packed_int'],262143)
        self.assertFalse(defined['external_first_dimension_extent_established'])
        self.assertTrue(any('without raising a signal' in condition for condition in proof['required_unproved_conditions']))

    def test_prototype_parameter_cannot_hide_typedef_used_later(self):
        self.reject(SOURCE.replace(b'void *out, const void *in, word length',b'void *word, const void *in, word length'))

    def test_new_prototype_scope_guard_accepts_disjoint_names(self):
        parsed=c.Parser(SOURCE).parse()
        self.assertIsNone(c.check_prototype_scope(parsed))


if __name__=='__main__':unittest.main()
