"""Synthetic typed-literal callback closures, pinned state callback and routing."""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import owner_admission_profile as owner
import named_data_buffer_profile as named
import function_thunk_profile as thunk
import two_word_callback_closure_profile as previous
import literal_callback_closure_profile as closure

A,C,G,X=0x08001000,0x08003000,0x08004000,0x08005000
W,S=closure.ITERATOR,0x0809AC20
ROOTS={  # form: (owner-load halfword, callback)
    'private-state':(0x6900,S),'entry-object':(0x6910,X),'null':(0x6900,X)}


def bl(site,target):
    delta=target-site-4
    return struct.pack('<HH',0xF000|((delta>>12)&0x7FF),0xF800|((delta>>1)&0x7FF))


def root(form,callback):
    shape=closure.FORMS[form];code=shape['code']
    load=ROOTS[form][0]
    body=bytearray(bytes.fromhex(code.replace('xx','00')))
    struct.pack_into('<H',body,shape['owner'],load)
    body[shape['call']:shape['call']+4]=bl(A+shape['call'],W)
    return bytes(body)+struct.pack('<II',callback+1,C+1)


def fixture(form='private-state',changes=None,callback=None):
    callback=ROOTS[form][1] if callback is None else callback
    worker=bytes.fromhex('70b50e1c151c446800e0a468002c05d0201c291c')+bl(W+20,thunk.ALIASES['_call_via_r6'])+bytes.fromhex('0028f6d170bc01bc0047')
    adapter=bytes.fromhex('10b50c1c')+bl(C+4,G)+bytes.fromhex('21686268')+bl(C+12,thunk.ALIASES['_call_via_r2'])+bytes.fromhex('10bc02bc0847')
    bodies={A:root(form,callback),W:worker,C:adapter,G:bytes.fromhex('00687047'),
            S:bytes.fromhex(closure.STATE_CALLBACKS[S][1]),X:bytes.fromhex('01207047')}
    counts={A:closure.FORMS[form]['count'],W:16,C:9,G:2,S:8,X:2}
    rom=bytearray(thunk.END-match.ROM_BASE)
    for number,target in enumerate(thunk.ALIASES.values()):
        struct.pack_into('<HH',rom,target-match.ROM_BASE,0x4700+(number<<3),0x46C0)
    for target in (thunk.ALIASES['_call_via_r6'],thunk.ALIASES['_call_via_r2']):
        bodies[target]=bytes(rom[target-match.ROM_BASE:target-match.ROM_BASE+2]);counts[target]=1
    for (target,offset),value in (changes or {}).items():
        code=bytearray(bodies[target]);struct.pack_into('<H',code,offset,value);bodies[target]=bytes(code)
    rows=[]
    for target,body in bodies.items():
        rom[target-match.ROM_BASE:target-match.ROM_BASE+len(body)]=body
        rows.append(dict(rom=f'0x{target:08X}',end=f'0x{target+len(body):08X}',mode='thumb',instrs=counts[target]))
    index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} {int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'for row in rows).encode()
    shape=closure.FORMS[form]
    return dict(data=bodies[A],address=A,rom=bytes(rom),mapping=json.dumps(rows).encode(),index=index,objects=b'{}',selector=closure.SELECTOR,
        bindings=dict(calls=[[shape['call'],f'func_{W:08X}']],data=[],
                      functions=[[shape['callback'],f'func_{callback:08X}'],[shape['adapter'],f'func_{C:08X}']],switches=[]))


class LiteralClosureTests(unittest.TestCase):
    def test_private_state_callback_effects_and_result(self):
        manifest,ins=owner.verify(**fixture())
        self.assertEqual(manifest['profile'],closure.SCHEMA);self.assertEqual(len(ins),17)
        proof=manifest['proof']['literal_callback_closure']
        self.assertEqual(proof['form'],'private-state')
        self.assertEqual(proof['private_state']['offset'],-20)
        self.assertEqual(proof['private_state']['result'],dict(site=A+28,offset=0,width=4,register=0,
            relation='zero plus one per returning callback invocation, modulo 2**32'))
        effects=proof['callback']
        self.assertEqual([row[1] for row in effects['state_reads']],[4,0])
        self.assertEqual([row[1] for row in effects['state_writes']],[0,4])
        self.assertEqual([row[1:] for row in effects['external_writes']],[['state word 4 on entry',0,4,'object']])
        self.assertTrue(effects['private_provenance_passed'])
        self.assertEqual(proof['root_descriptor']['actual_buffer_checks'][0]['pointer_slots'],[[-12,-20]])
        conditions=' '.join(proof['explicit_conditions'])
        self.assertNotIn('Loaded input words carry no tracked private-frame',conditions)
        self.assertIn('not asserted satisfied',conditions)
        for key in ('physical_memory_permission','numeric_nonalias_proved','actual_callback_ABI_established','termination_proved'):
            self.assertIs(proof[key],False)
        self.assertFalse(proof['iterator']['iteration_bound_assumed'])

    def test_opaque_forms_keep_existing_premises(self):
        for form in ('entry-object','null'):
            with self.subTest(form=form):
                manifest,ins=owner.verify(**fixture(form))
                proof=manifest['proof']['literal_callback_closure']
                self.assertEqual(proof['form'],form);self.assertIsNone(proof['private_state'])
                self.assertEqual(proof['callback']['effects'],'opaque')
                self.assertFalse(proof['callback']['private_provenance_passed'])
                self.assertIn('Loaded input words carry no tracked private-frame or saved-return provenance; ordinary memory noninterference remains a premise.',
                              proof['explicit_conditions'])
                self.assertEqual(proof['root_descriptor']['actual_buffer_checks'][0]['pointer_slots'],[])

    def test_native_report_selector_and_replay(self):
        values=fixture();manifest,ins=owner.verify(**values)
        result=(values['data'],manifest,'a'*64,values['mapping'],values['index'],values['objects'],values['rom'],len(ins),b'synthetic-original-ELF')
        report=owner.render(A,result)
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report),closure.SELECTOR)
        self.assertIn('* owner runtime: '+closure.SELECTOR,report)
        self.assertIn('* control flow: '+closure.CONTROL_FLOW,report)

    def test_tampered_manifest_refuses(self):
        values=fixture();report,_=owner.verify(**values)
        for path in (('private_state','result','relation'),('callback','private_provenance_passed'),('termination_proved',)):
            changed=copy.deepcopy(report);target=changed['proof']['literal_callback_closure']
            for key in path[:-1]:target=target[key]
            target[path[-1]]='zero' if path[-1]=='relation' else not target[path[-1]]
            with self.subTest(path=path),self.assertRaisesRegex(ValueError,'manifest differs'):
                owner.verify(**values,manifest=changed)

    def test_existing_and_default_selectors_do_not_gain_permission(self):
        for form in closure.FORMS:
            for selector in (owner.SELECTOR,previous.SELECTOR,named.TREE_CALLBACK_SELECTOR,named.DATAFREE_SELECTOR):
                values=fixture(form);values['selector']=selector
                with self.subTest(form=form,selector=selector),self.assertRaises(ValueError):owner.verify(**values)

    def test_existing_28_byte_root_is_not_a_literal_form(self):
        data=bytes.fromhex('00b582b000920191006903496a46')+bl(A+14,W)+bytes.fromhex('02b001bc0047')+struct.pack('<I',C+1)
        with self.assertRaisesRegex(ValueError,'natural root form'):closure.form_of(data)

    def test_templates_match_independent_genuine_roots(self):
        genuine={'private-state':'00b584b000220092019106496a46029202aa5160006904492df0e4ff009804b002bc084721ac0908e9ab0908',
                 'entry-object':'00b582b0011c80310a68054900900191106904496a462ef02ff902b001bc00476dad0908e9ab0908',
                 'null':'00b582b0054a002100910192006904496a462df0dffa02b001bc0047b5ac0908e9ab0908'}
        for form,raw in genuine.items():
            with self.subTest(form=form):self.assertEqual(closure.form_of(bytes.fromhex(raw)),form)

    def test_call_to_other_iterator_refuses(self):
        values=fixture();body=bytearray(values['data']);body[24:28]=bl(A+24,G)
        values['data']=bytes(body);rom=bytearray(values['rom']);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body
        values['rom']=bytes(rom);values['bindings']['calls']=[[24,f'func_{G:08X}']]
        with self.assertRaisesRegex(ValueError,'exact iterator call'):closure.prove(**{k:v for k,v in values.items() if k not in ('objects','bindings')})

    def test_callback_cannot_be_another_dependency(self):
        for target in (C,G,W):
            with self.subTest(target=hex(target)),self.assertRaisesRegex(ValueError,'distinct complete dependency owners'):
                owner.verify(**fixture('null',callback=target))

    def test_wrong_root_bytes_refuse(self):
        # Initializing stores, descriptor address, result read-back and frame size.
        for offset,value in ((6,0x46C0),(14,0x9201),(16,0xAA01),(28,0x9801),(2,0xB083),(30,0xB003)):
            with self.subTest(offset=offset),self.assertRaisesRegex(ValueError,'natural root form'):
                owner.verify(**fixture(changes={(A,offset):value}))

    def test_owner_load_must_be_aligned_word_from_entry_object(self):
        for value in (0x6901,0x6908,0x8A00,0x5800):
            with self.subTest(value=hex(value)),self.assertRaisesRegex(ValueError,'aligned incoming object word load'):
                owner.verify(**fixture(changes={(A,20):value}))

    def test_state_callback_body_changes_refuse(self):
        # Wrong state offset, store of the state address, extra state word,
        # wrong increment and wrong return value.
        for offset,value in ((0,0x688A),(4,0x6809),(6,0x3002),(8,0x6088),(12,0x2000)):
            with self.subTest(offset=offset),self.assertRaises(ValueError):
                owner.verify(**fixture(changes={(S,offset):value}))
        raw=bytearray.fromhex(closure.STATE_CALLBACKS[S][1]);raw[8:10]=bytes.fromhex('0960')
        with self.assertRaisesRegex(ValueError,'pinned state callback body differs'):
            closure.state_callback_effects(bytes(raw),S)

    def test_interpreter_refuses_state_escape_even_if_pinned(self):
        raw=bytes.fromhex('4a6801c20868013008604a6001207047')
        for edit,error in (((8,'0960'),'stores the private state address'),((2,'08c2'),'getter word'),
                           ((0,'8a68'),'leaves the private two-word state'),((6,'0230'),'effect relation')):
            changed=bytearray(raw);changed[edit[0]:edit[0]+2]=bytes.fromhex(edit[1])
            with self.subTest(edit=edit),self.assertRaisesRegex(ValueError,error),\
                    patch.dict(closure.STATE_CALLBACKS,{S:(8,changed.hex())}):
                closure.state_callback_effects(bytes(changed),S)

    def test_private_state_requires_pinned_callback(self):
        with self.assertRaisesRegex(ValueError,'pinned state callback'):
            owner.verify(**fixture(callback=X))

    def test_pinned_state_callback_refuses_without_private_state(self):
        for form in ('entry-object','null'):
            with self.subTest(form=form),self.assertRaisesRegex(ValueError,'private-state root form'):
                owner.verify(**fixture(form,callback=S))

    def test_state_form_requires_adapter_return_through_R1(self):
        with self.assertRaisesRegex(ValueError,'adapter return through R1'):owner.verify(**fixture(changes={(C,18):0xBC04,(C,20):0x4710}))

    def test_inexact_bindings_refuse(self):
        for change in (lambda b:b['functions'].reverse(),lambda b:b['functions'].pop(),
                       lambda b:b['data'].append([0,'fake',0]),lambda b:b['functions'][0].__setitem__(1,f'func_{X:08X}')):
            values=fixture();change(values['bindings'])
            with self.assertRaisesRegex(ValueError,'exact typed callback and adapter bindings'):owner.verify(**values)

    def test_iterator_and_dependency_changes_refuse(self):
        for target,offset,value in ((W,10,0x60A4),(W,12,0x2C01),(C,8,0x4621),(G,0,0x6840)):
            with self.subTest(target=hex(target),offset=offset),self.assertRaises(ValueError):
                owner.verify(**fixture(changes={(target,offset):value}))
        for target in (W,C,G,S,thunk.ALIASES['_call_via_r6']):
            values=fixture();rows=json.loads(values['mapping'])
            next(row for row in rows if int(row['rom'],16)==target)['instrs']+=1
            values['mapping']=json.dumps(rows).encode()
            with self.subTest(target=hex(target)),self.assertRaises(ValueError):owner.verify(**values)

    def test_even_literal_refuses(self):
        values=fixture();body=bytearray(values['data']);struct.pack_into('<I',body,36,S);values['data']=bytes(body)
        rom=bytearray(values['rom']);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body;values['rom']=bytes(rom)
        with self.assertRaises(ValueError):owner.verify(**values)

    def test_exact_policy_and_immutable_input_contract(self):
        values=fixture()
        for key in('objects','bindings'):values.pop(key)
        for key,value in(('selector',previous.SELECTOR),('address',True),('data',bytearray(values['data']))):
            changed=dict(values);changed[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):closure.prove(**changed)


if __name__=='__main__':
    unittest.main()
