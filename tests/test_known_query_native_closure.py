"""Synthetic certificate transport and complete-owner routing, without compilers."""
from contextlib import ExitStack
import copy
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import known_query_native_closure_profile as query
import named_data_buffer_profile as named
import owner_admission_profile as owner

A,T,C,H=0x0809D640,0x08099840,0x0809C9E8,0x08001000

def bl(site,target):
    value=(target-site-4)&0x7fffff
    return struct.pack('<HH',0xf000|(value>>12),0xf800|((value>>1)&2047))

class Fixture:
    def __init__(self):
        self.frozen=json.loads(query.FROZEN_CERTIFICATE)
        root=bytes.fromhex('00b582b0021c00290cd00091002001900349101c6a46')
        root+=bl(A+22,T)+bytes.fromhex('019803e00000')+struct.pack('<I',C|1)
        root+=bytes.fromhex('002002b002bc0847')
        bodies={A:root,T:bytes.fromhex('7047'),C:bytes.fromhex('7047'),H:bytes.fromhex('3047')}
        rom=bytearray(A+len(root)-0x08000000)
        self.rows=[];self.dependencies=[]
        for address,body in bodies.items():
            rom[address-0x08000000:address-0x08000000+len(body)]=body
            count=18 if address==A else 1
            self.rows.append(dict(rom=f'0x{address:08X}',end=f'0x{address+len(body):08X}',mode='thumb',instrs=count))
            self.dependencies.append(dict(address=address,end=address+len(body),instructions=count,body_sha256=query.sha(body)))
        rom[H-0x08000000+2:H-0x08000000+4]=bytes.fromhex('c046')
        self.args=dict(data=root,address=A,rom=bytes(rom),mapping=json.dumps(self.rows).encode(),
                       index=self.index(self.rows),selector=query.SELECTOR)
        self.frozen.update(address=A,end=A+44,body_sha256=query.sha(root),ROM_sha256=query.sha(bytes(rom)))
        self.thunks=(dict(address=H,padding_end=H+4,complete_sha256=query.sha(bytes(rom[H-0x08000000:H-0x08000000+4]))),)

    @staticmethod
    def index(rows):
        return ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} {int(row["end"],16)-int(row["rom"],16)} {row["instrs"]}\n'for row in rows).encode()

    def authority(self):
        raw=json.dumps(self.frozen).encode()
        stack=ExitStack()
        for key,value in dict(FROZEN_CERTIFICATE=raw,CERTIFICATE_SHA256=query.sha(raw),
                              DEPENDENCIES=tuple(self.dependencies),THUNKS=self.thunks).items():
            stack.enter_context(patch.object(query,key,value))
        return stack

    def bindings(self):
        return dict(calls=[[22,'func_08099840']],data=[],functions=[[32,'func_0809C9E8']],switches=[])

    def prove(self):
        with self.authority():return query.prove(**self.args)

    def native(self,bindings=None,**kwargs):
        with self.authority():return owner.verify(**self.args,objects=b'{}',bindings=self.bindings()if bindings is None else bindings,**kwargs)

class QueryNativeTests(unittest.TestCase):
    def setUp(self):self.f=Fixture()

    def test_preserves_complete_conditional_certificate_and_outward_aliases(self):
        result=self.f.prove()
        self.assertEqual(result['frozen_conditional_query_effects'],self.f.frozen)
        self.assertFalse(result['frozen_conditional_query_effects']['stale_alias_transport']['outward_aliases_erased'])
        self.assertEqual(result['explicit_conditions'],self.f.frozen['explicit_conditions'])
        for key in ('source_or_ELF_admission','native_admission','physical_memory_permission',
                    'actual_C_function_compatibility_proved','termination_proved'):
            self.assertIs(result[key],False)

    def test_uses_no_old_callback_or_owner_producer(self):
        import known_query_callback_effects as old
        with patch.object(old,'prove',side_effect=AssertionError('old producer replay')),patch.object(old,'effects',side_effect=AssertionError('old effect replay')):
            self.assertEqual(self.f.prove()['old_effect_or_owner_producer_executions'],0)

    def test_current_complete_owner_and_typed_bindings(self):
        manifest,instructions=self.f.native()
        self.assertEqual(manifest['profile'],query.SCHEMA)
        self.assertEqual(len(instructions),18)
        self.assertEqual(manifest['bindings'],self.f.bindings())

    def test_report_round_trip_selector_and_original_elf_fingerprint(self):
        manifest,ins=self.f.native();v=self.f.args
        result=(v['data'],manifest,'a'*64,v['mapping'],v['index'],b'{}',v['rom'],len(ins),b'original-ELF')
        report=owner.render(A,result)
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report),query.SELECTOR)
        self.assertIn('* owner runtime: '+query.SELECTOR,report)
        self.assertIn(query.CONTROL_FLOW,report)
        with self.assertRaisesRegex(ValueError,'original ELF identity'):
            owner.fingerprint(A,v['data'],manifest,'a'*64,v['mapping'],v['index'],b'{}',v['rom'])

    def test_explicit_selector_required(self):
        self.f.args['selector']='ordinary'
        with self.assertRaisesRegex(ValueError,'explicit'):self.f.prove()

    def test_mutable_input_refuses(self):
        self.f.args['data']=bytearray(self.f.args['data'])
        with self.assertRaisesRegex(ValueError,'immutable'):self.f.prove()

    def test_wrong_root_address_refuses(self):
        self.f.args['address']+=2
        with self.assertRaisesRegex(ValueError,'root'):self.f.prove()

    def test_changed_complete_root_refuses(self):
        self.f.args['data']=bytes.fromhex('c046')+self.f.args['data'][2:]
        with self.assertRaisesRegex(ValueError,'root'):self.f.prove()

    def test_truncated_root_refuses(self):
        self.f.args['data']=self.f.args['data'][:-2]
        with self.assertRaisesRegex(ValueError,'root'):self.f.prove()

    def test_changed_unrelated_full_rom_refuses(self):
        rom=bytearray(self.f.args['rom']);rom[20]=1;self.f.args['rom']=bytes(rom)
        with self.assertRaisesRegex(ValueError,'full ROM'):self.f.prove()

    def test_corrupted_certificate_refuses(self):
        with self.f.authority(),patch.object(query,'FROZEN_CERTIFICATE',b'{}'):
            with self.assertRaisesRegex(ValueError,'authority'):query.prove(**self.f.args)

    def test_mutable_certificate_refuses(self):
        with self.f.authority(),patch.object(query,'FROZEN_CERTIFICATE',bytearray(b'{}')):
            with self.assertRaisesRegex(ValueError,'authority'):query.prove(**self.f.args)

    def test_json_instruction_count_refuses(self):
        self.f.rows[1]['instrs']=2;self.f.args['mapping']=json.dumps(self.f.rows).encode()
        with self.assertRaises(ValueError):self.f.prove()

    def test_text_instruction_count_refuses(self):
        self.f.args['index']=self.f.args['index'].replace(b' 18\n',b' 22\n')
        with self.assertRaises(ValueError):self.f.prove()

    def test_consistent_but_wrong_dependency_count_refuses(self):
        self.f.rows[1]['instrs']=2
        self.f.args.update(mapping=json.dumps(self.f.rows).encode(),index=self.f.index(self.f.rows))
        with self.assertRaisesRegex(ValueError,'dependency'):self.f.prove()

    def test_missing_dependency_refuses(self):
        self.f.args.update(mapping=json.dumps(self.f.rows[:-1]).encode(),index=self.f.index(self.f.rows[:-1]))
        with self.assertRaises(ValueError):self.f.prove()

    def test_duplicate_json_owner_refuses(self):
        self.f.args['mapping']=json.dumps(self.f.rows+[self.f.rows[1]]).encode()
        with self.assertRaises(ValueError):self.f.prove()

    def test_duplicate_text_owner_refuses(self):
        self.f.args['index']+=self.f.index(self.f.rows[1:2])
        with self.assertRaises(ValueError):self.f.prove()

    def test_arm_dependency_refuses(self):
        self.f.rows[1]['mode']='arm';self.f.args['mapping']=json.dumps(self.f.rows).encode()
        with self.assertRaises(ValueError):self.f.prove()

    def test_dependency_body_refuses_after_rom_authority_changed(self):
        rom=bytearray(self.f.args['rom']);rom[T-0x08000000]=0
        self.f.args['rom']=bytes(rom);self.f.frozen['ROM_sha256']=query.sha(bytes(rom))
        with self.assertRaisesRegex(ValueError,'dependency'):self.f.prove()

    def test_overlapping_dependency_owner_refuses(self):
        self.f.rows.append(dict(rom=f'0x{A+2:08X}',end=f'0x{A+4:08X}',mode='thumb',instrs=1))
        self.f.args['mapping']=json.dumps(self.f.rows).encode()
        with self.assertRaises(ValueError):self.f.prove()

    def test_thunk_padding_cannot_become_function(self):
        self.f.rows.append(dict(rom=f'0x{H+2:08X}',end=f'0x{H+4:08X}',mode='thumb',instrs=1))
        self.f.args.update(mapping=json.dumps(self.f.rows).encode(),index=self.f.index(self.f.rows))
        with self.assertRaisesRegex(ValueError,'padding'):self.f.prove()

    def test_unrelated_count_context_can_change(self):
        self.f.rows.append(dict(rom='0x08002000',end='0x08002002',mode='thumb',instrs=1))
        self.f.args.update(mapping=json.dumps(self.f.rows).encode(),index=self.f.index(self.f.rows))
        self.assertEqual(self.f.prove()['mapping_sha256'],query.sha(self.f.args['mapping']))

    def test_wrong_genuine_call_binding_refuses(self):
        bindings=self.f.bindings();bindings['calls'][0][1]='func_08099844'
        with self.assertRaisesRegex(ValueError,'typed bindings'):self.f.native(bindings)

    def test_wrong_function_literal_binding_refuses(self):
        bindings=self.f.bindings();bindings['functions'][0][0]=28
        with self.assertRaisesRegex(ValueError,'typed bindings'):self.f.native(bindings)

    def test_extra_data_binding_refuses(self):
        bindings=self.f.bindings();bindings['data']=[[32,'g_state',0]]
        with self.assertRaisesRegex(ValueError,'typed bindings'):self.f.native(bindings)

    def test_stale_expected_manifest_refuses(self):
        manifest,_=self.f.native();manifest=copy.deepcopy(manifest)
        manifest['proof']['frozen_conditional_query_effects']['native_admission']=True
        with self.assertRaisesRegex(ValueError,'manifest differs'):self.f.native(manifest=manifest)

    def test_default_and_old_policies_do_not_gain_permission(self):
        for selector in (owner.SELECTOR,named.DATAFREE_SELECTOR):
            with self.subTest(selector=selector):
                self.f.args['selector']=selector
                with self.assertRaises(ValueError):self.f.native()

    def test_mixed_report_verification_refuses(self):
        report='* verification: `'+query.SCHEMA+'`\n* verification: `ordinary`\n'
        with self.assertRaisesRegex(ValueError,'mixed'):owner.selected(report)

    def test_environment_binds_this_profile_and_owner_sources(self):
        value=query.environment_fingerprint()
        for name in ('known_query_native_closure_profile.py','owner_admission_profile.py','match.py'):
            self.assertEqual(value['sources'][name],query.sha((Path(query.__file__).parent/name).read_bytes()))

if __name__=='__main__':unittest.main()
