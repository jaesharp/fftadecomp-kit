"""Instruction-sensitive path and signed-conversion checks without a solver."""
import copy
import hashlib
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import halfword_channel_arithmetic as arithmetic

A = 0x08001000


def fixture(restore=False, changes=None):
    if restore:
        items = [('unsigned',0x8805),('zero_index',0x2700),('signed',0x5fc0),('zero_test',0x2800),('skip',('eq','exit')),
            ('sum',0x1948),('narrow_store',0x8030),('left',0x0400),('right',0x1400),('negative_test',0x2800),('nonnegative',('ge','upper')),
            ('zero',0x4650),('zero_jump',('b','store')),('upper',0x281f),('within',('le','exit')),
            ('maximum',0x201f),('store',0x8030),('exit',0x46c0)]
        bindings = {0:'adjustment_pointer',6:'channel_pointer',1:'channel_value',10:0}
    else:
        items = [('unsigned',0x8801),('zero_index',0x2700),('signed',0x5fc0),('zero_test',0x2800),('skip',('eq','exit')),
            ('channel_load',0x882f),('sum',0x19c8),('narrow_store',0x8028),('left',0x0400),('right',0x1400),
            ('negative_test',0x2800),('nonnegative',('ge','upper')),('zero',0x2000),('zero_store',0x8028),('zero_jump',('b','exit')),
            ('upper',0x281f),('within',('le','exit')),('maximum',0x211f),('store',0x8029),('exit',0x46c0)]
        bindings = {0:'adjustment_pointer',5:'channel_pointer'}
    labels = {name:A+2*i for i,(name,_) in enumerate(items)}
    words=[]
    for name, word in items:
        word=(changes or {}).get(name,word)
        if isinstance(word,tuple):
            kind,target=word;delta=(labels[target]-labels[name]-4)//2
            word=(0xe000|(delta&2047)) if kind=='b' else ({'eq':0xd000,'ge':0xda00,'le':0xdd00}[kind]|(delta&255))
        words.append(word)
    return b''.join(struct.pack('<H',word) for word in words),labels,bindings


def prove(selected=None, **overrides):
    data,labels,bindings=selected or fixture()
    args=dict(selector=arithmetic.SELECTOR)
    args.update(overrides)
    return arithmetic.region(data,A,A,labels['exit'],bindings,set(labels.values()),**args)


def composition_fixture(restore=False, changes=None):
    data,labels,bindings=fixture(restore,changes)
    data=data[:-2]+struct.pack('<H',0x4770)
    address=A
    sites=set(labels.values())
    records=[['local-read',A,-24,2]]
    access={0:A}
    preloaded={}
    if restore:
        address=A-4;data=struct.pack('<HH',0x7801,0x8031)+data
        sites.update((A-4,A-2));preloaded={1:A-2};access[6]=labels['narrow_store']
        records += [['local-write',A-2,-32,2],['local-write',labels['narrow_store'],-32,2]]
    else:
        access[5]=labels['channel_load'];records.append(['local-read',labels['channel_load'],-32,2])
    common={'address':address,'end':address+len(data),'body_sha256':hashlib.sha256(data).hexdigest(),
            'ROM_sha256':'0'*64,'partition':{'synthetic_complete_owner':True}}
    frame=dict(common,continuation={'continuation_sites':sorted(sites),'records':records,
        'local_reads_have_definite_prior_machine_byte_writes':True},required_unproved_conditions=['Synthetic independently established local-frame premise.'])
    ranges=[[0,0xffffffff] for _ in range(13)]
    if restore:ranges[10]=[0,0]
    numeric=dict(common,fixed_point_states=[{'site':A,'ranges':ranges}])
    return dict(data=data,address=address,entry=A,exit_site=labels['exit'],bindings=bindings,
                pointer_access_sites=access,preloaded_stores=preloaded,
                frame_certificate=frame,numeric_certificate=numeric,selector=arithmetic.SELECTOR)


def compose(selected):
    selected=copy.deepcopy(selected)
    selected['reuse_authority']={'independently_established_frozen_certificates':True,
        'frame_sha256':arithmetic.certificate_digest(selected['frame_certificate']),
        'numeric_sha256':arithmetic.certificate_digest(selected['numeric_certificate'])}
    return arithmetic.compose(**selected)


class HalfwordArithmeticTests(unittest.TestCase):
    def test_normal_four_exact_symbolic_paths(self):
        report=prove()
        self.assertEqual(len(report['paths']),4)
        self.assertTrue(report['signed_sum_narrowing_precedes_clamp'])
        self.assertFalse(report['source_or_ELF_admission'])

    def test_restore_register_zero_and_preloaded_channel(self):
        report=prove(fixture(True))
        self.assertEqual(len(report['paths']),4)
        self.assertIn((10,0),report['entry_bindings'])

    def test_unsigned_threshold_is_not_signed_clamp(self):
        with self.assertRaisesRegex(ValueError,'supported signed condition'):
            prove(fixture(changes={'nonnegative':0xd200}))

    def test_wrong_narrowing_shift_refuses(self):
        with self.assertRaisesRegex(ValueError,'differ from wrapped'):
            prove(fixture(changes={'left':0x03c0}))

    def test_logical_right_shift_cannot_replace_sign_extension(self):
        with self.assertRaisesRegex(ValueError,'unsupported'):
            prove(fixture(changes={'right':0x0c00}))

    def test_nonzero_signed_load_index_refuses(self):
        with self.assertRaisesRegex(ValueError,'zero index'):
            prove(fixture(changes={'zero_index':0x2702}))

    def test_wrong_saturation_maximum_refuses(self):
        with self.assertRaisesRegex(ValueError,'differ from wrapped'):
            prove(fixture(changes={'maximum':0x2120}))

    def test_wrong_restore_zero_register_refuses(self):
        data,labels,bindings=fixture(True);bindings[10]=1
        with self.assertRaisesRegex(ValueError,'differ from wrapped'):
            prove((data,labels,bindings))

    def test_missing_middle_store_refuses(self):
        with self.assertRaisesRegex(ValueError,'differ from wrapped'):
            prove(fixture(changes={'narrow_store':0x4600}))

    def test_adjustment_store_refuses(self):
        with self.assertRaisesRegex(ValueError,'overwrites adjustment'):
            prove(fixture(changes={'unsigned':0x8001}))

    def test_cell_offset_cannot_expand_memory_contract(self):
        with self.assertRaisesRegex(ValueError,'two local cells'):
            prove(fixture(changes={'channel_load':0x886f}))

    def test_scalar_does_not_become_pointer(self):
        data,labels,bindings=fixture();bindings[6]=0
        with self.assertRaisesRegex(ValueError,'two local cells'):
            prove((fixture(changes={'channel_load':0x8837})[0],labels,bindings))

    def test_preloaded_channel_relation_is_required(self):
        data,labels,bindings=fixture(True);bindings[1]=0
        with self.assertRaisesRegex(ValueError,'differ from wrapped'):
            prove((data,labels,bindings))

    def test_flags_clobber_cannot_reuse_comparison(self):
        with self.assertRaisesRegex(ValueError,'CMP flags'):
            prove(fixture(changes={'negative_test':0x2000}))

    def test_cycle_refuses_without_assumed_termination(self):
        with self.assertRaisesRegex(ValueError,'cycle'):
            prove(fixture(changes={'zero_jump':('b','unsigned')}))

    def test_missing_owner_boundary_refuses(self):
        data,labels,bindings=fixture()
        with self.assertRaisesRegex(ValueError,'retained owner'):
            arithmetic.region(data,A,A,labels['exit'],bindings,set(labels.values())-{labels['upper']},selector=arithmetic.SELECTOR)

    def test_unbound_source_register_refuses(self):
        with self.assertRaisesRegex(ValueError,'unbound'):
            prove(fixture(changes={'channel_load':0x8837}))

    def test_selector_is_explicit(self):
        with self.assertRaisesRegex(ValueError,'typed selector'):
            prove(selector=None)

    def test_manifest_rejects_changed_relation(self):
        # This is a new manifest-negative case, not a replay of an actual owner.
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            prove(manifest={'relation':'clamp the unwrapped mathematical sum'})

    def test_step_budget_refuses(self):
        with patch.object(arithmetic,'MAX_PATH_STEPS',4),self.assertRaisesRegex(ValueError,'step bound'):
            prove()

    def test_all_signed_halfword_load_encodings(self):
        expression=arithmetic.sext16(arithmetic.ADJUSTMENT)
        for value in range(65536):
            expected=int.from_bytes(value.to_bytes(2,'little'),'little',signed=True)&0xffffffff
            self.assertEqual(arithmetic.evaluate(expression,0,value),expected)

    def test_every_promoted_sum_in_actual_channel_domains(self):
        # Independent byte decoding checks the LSL16/ASR16 normalization over
        # every possible promoted sum for channel0..255 and signed16 delta.
        for total in range(-32768,33023):
            expression=arithmetic.shift(arithmetic.shift(arithmetic.const(total),16),16,True)
            expected=int.from_bytes((total&65535).to_bytes(2,'little'),'little',signed=True)&0xffffffff
            self.assertEqual(arithmetic.evaluate(expression,0,0),expected)

    def test_wrap_boundaries_and_zero_restore_preserve_value(self):
        cases=arithmetic.expected_cases()
        for channel in (0,1,30,31,32,127,255):
            for adjustment in (0,1,31,32766,32767,32768,32769,65505,65534,65535):
                selected=[output for guards,output in cases if all(arithmetic.predicate_value(g,channel,adjustment) for g in guards)]
                self.assertEqual(len(selected),1)
                signed_delta=int.from_bytes(adjustment.to_bytes(2,'little'),'little',signed=True)
                total=int.from_bytes(((channel+signed_delta)&65535).to_bytes(2,'little'),'little',signed=True)
                expected=channel if signed_delta==0 else min(max(total,0),31)
                self.assertEqual(arithmetic.evaluate(selected[0],channel,adjustment),expected)
        self.assertEqual(arithmetic.evaluate(next(value for guards,value in cases if all(arithmetic.predicate_value(g,255,0) for g in guards)),255,0),255)

    def test_composed_normal_local_roles_are_disjoint(self):
        report=compose(composition_fixture())
        self.assertEqual(report['authenticated_entry_evidence']['local_role_offsets'],
                         {'channel_pointer':[-32],'adjustment_pointer':[-24]})

    def test_composed_restore_authenticates_preload_and_zero(self):
        report=compose(composition_fixture(True))
        evidence=report['authenticated_entry_evidence']
        self.assertEqual(evidence['preloaded_registers'][0]['load_width'],1)
        self.assertEqual(evidence['constants'],[(10,0)])

    def test_composition_requires_independent_authority(self):
        with self.assertRaisesRegex(ValueError,'independent certificate authority'):
            arithmetic.compose(**composition_fixture(),reuse_authority={})

    def test_composition_zero_constant_requires_numeric_evidence(self):
        selected=composition_fixture(True)
        selected['numeric_certificate']['fixed_point_states'][0]['ranges'][10]=[0,1]
        with self.assertRaisesRegex(ValueError,'authenticated singleton'):
            compose(selected)

    def test_composition_rejects_overlapping_local_roles(self):
        selected=composition_fixture()
        selected['frame_certificate']['continuation']['records'][0][2]=-32
        with self.assertRaisesRegex(ValueError,'alternatives overlap'):
            compose(selected)

    def test_preloaded_register_requires_zero_extending_load(self):
        selected=composition_fixture(True)
        selected['data']=struct.pack('<H',0x6801)+selected['data'][2:]
        for key in ('frame_certificate','numeric_certificate'):
            selected[key]['body_sha256']=hashlib.sha256(selected['data']).hexdigest()
        with self.assertRaisesRegex(ValueError,'zero-extending load'):
            compose(selected)

    def test_preloaded_register_rejects_alternative_entry_path(self):
        with self.assertRaisesRegex(ValueError,'alternative predecessor'):
            compose(composition_fixture(True,{'zero_jump':('b','unsigned')}))

    def test_composition_requires_definite_local_writes(self):
        selected=composition_fixture()
        selected['frame_certificate']['continuation']['local_reads_have_definite_prior_machine_byte_writes']=False
        with self.assertRaisesRegex(ValueError,'definite initialized'):
            compose(selected)

    def test_pointer_first_use_guard_accepts_witnessed_access(self):
        selected=composition_fixture()
        report=compose(selected)
        self.assertEqual({row['register'] for row in report['authenticated_entry_evidence']['pointer_first_uses']},{0,5})

    def test_later_access_does_not_justify_earlier_pointer_read(self):
        data,labels,bindings=fixture()
        paths=[{'trace':(A,labels['signed'])}]
        with self.assertRaisesRegex(ValueError,'before its witnessed access'):
            arithmetic.authenticate_entry_pointer_uses(data,A,paths,bindings,{0:labels['signed'],5:labels['channel_load']})

    def test_pointer_overwrite_before_witness_refuses(self):
        data,labels,_=fixture()
        data=struct.pack('<H',0x4625)+data[2:]
        paths=[{'trace':(A,labels['channel_load'])}]
        with self.assertRaisesRegex(ValueError,'before its witnessed access'):
            arithmetic.authenticate_entry_pointer_uses(data,A,paths,{5:'channel_pointer'},{5:labels['channel_load']})


if __name__ == '__main__':
    unittest.main()
