"""The descriptor+8 interface preserves the existing private payload limits."""
from pathlib import Path
import hashlib
import struct
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import conditional_local_buffer_profile as local
import owner_admission_profile as owner
from test_conditional_local_buffers import proof, LOCAL, SAVED, PINNED, SCHEDULER_BODY, ALLOCATOR_BODY

R0=match.ARM_REG_R0
BASE=0x08001000
CALLEE=0x08005B6C


def body(*, store=0x6090, middle=()):
    # Complete synthetic ARMv4T caller, not C or ROM-derived source.
    # push {r4,lr}; sub sp,44; add r0,sp,28; add r2,sp,0;
    # str r0,[r2,8]; clear r0; BL; restore private/saved frame; return.
    data=struct.pack('<'+'H'*(6+len(middle)),
                     0xB510,0xB08B,0xA807,0xAA00,store,*middle,0x2000)
    site=BASE+len(data);disp=CALLEE-site-4
    data+=struct.pack('<HH',0xF000|((disp>>12)&0x7FF),0xF800|((disp>>1)&0x7FF))
    data+=struct.pack('<HHHH',0xB00B,0xBC10,0xBC02,0x4708)
    return data,{site:CALLEE}


def context(calls, policy=local.SCHEDULER_PAYLOAD8):
    p=proof(policy,calls)
    p.stack_arguments=True
    return p


class Payload8Tests(unittest.TestCase):
    def test_trailing_payload_records_field_and_keeps_all_effects_conditional(self):
        p=context({100:CALLEE})
        p.check_call(CALLEE,{R0+2:-52,R0+4:-24},[LOCAL]*11+[SAVED]*2,{-44:-24},site=100)
        m=p.contract_manifest();o=m['observations'][0]
        self.assertEqual((o['payload_pointer_word_offset'],o['payload_offset'],o['payload_frame_bytes']),(8,-24,16))
        self.assertEqual(o['aliases'],[(R0+2,-52),(R0+4,-24)])
        self.assertFalse(m['actual_callback_effects_proved'])
        self.assertFalse(m['nonescape_proved'])
        self.assertIn('descriptor+8',' '.join(m['assumptions']))
        self.assertNotIn('descriptor+4',' '.join(m['assumptions']))

    def test_leading_payload_uses_same_exact_start_rule(self):
        p=context({100:CALLEE})
        p.check_call(CALLEE,{R0+2:-36},[LOCAL]*11+[SAVED]*2,{-28:-52},site=100)
        o=p.contract_manifest()['observations'][0]
        self.assertEqual((o['local_offset'],o['payload_offset'],o['payload_frame_bytes']),(-36,-52,16))

    def test_field4_and_other_descriptor_words_are_not_field8(self):
        for field in (0,4,12,16,20,24,28):
            with self.subTest(field=field),self.assertRaisesRegex(ValueError,r'descriptor\+8'):
                context({100:CALLEE}).check_call(CALLEE,{R0+2:-52},[LOCAL]*11+[SAVED]*2,{-52+field:-24},site=100)

    def test_missing_extra_and_interior_pointer_values_refused(self):
        for slots in ({}, {-44:-20}, {-44:-52}, {-44:-8}, {-44:0}, {-44:-24,-48:-24}):
            with self.subTest(slots=slots),self.assertRaises(ValueError):
                context({100:CALLEE}).check_call(CALLEE,{R0+2:-52},[LOCAL]*11+[SAVED]*2,slots,site=100)

    def test_extra_outgoing_aliases_refused(self):
        for reg in (R0,R0+1,R0+3):
            with self.subTest(reg=reg),self.assertRaisesRegex(ValueError,'additional register aliases'):
                context({100:CALLEE}).check_call(CALLEE,{R0+2:-52,reg:-24},[LOCAL]*11+[SAVED]*2,{-44:-24},site=100)

    def test_saved_word_gap_or_empty_payload_is_not_private_frame(self):
        cases=(({-44:-24},[LOCAL]*10+[SAVED,LOCAL,SAVED],-52),
               ({-28:-8},[LOCAL]*7+[SAVED]*2,-36),
               ({-40:-24},[LOCAL]*11+[SAVED]*2,-48),
               ({-42:-24},[LOCAL]*11+[SAVED]*2,-50))
        for slots,stack,offset in cases:
            with self.subTest(slots=slots),self.assertRaises(ValueError):
                context({100:CALLEE}).check_call(CALLEE,{R0+2:offset},stack,slots,site=100)

    def test_scalar_or_opaque_word_facts_cannot_replace_pointer_tracking(self):
        with self.assertRaisesRegex(ValueError,'authenticated interface'):
            context({100:CALLEE}).check_call(CALLEE,{R0+2:-52},[LOCAL]*11+[SAVED]*2,{-44:-24},site=100,words={R0:'opaque'})

    def test_unknown_call_or_missing_observation_refused(self):
        p=context({100:CALLEE})
        with self.assertRaises(ValueError):p.contract_manifest()
        with self.assertRaises(ValueError):p.check_call(CALLEE,{R0+2:-52},[LOCAL]*11+[SAVED]*2,{-44:-24},site=102)
        with self.assertRaises(ValueError):p.check_call(CALLEE+2,{R0+2:-52},[LOCAL]*11+[SAVED]*2,{-44:-24},site=100)

    def test_native_frame_records_alias_addressed_full_word_store(self):
        data,calls=body();p=context(calls)
        match.verify_leaf_instructions(data,BASE,True,calls,buffer_proof=p)
        self.assertEqual(p.contract_manifest()['observations'][0]['pointer_words'],[(-44,-24)])

    def test_native_old_payload_profile_still_refuses_field8(self):
        data,calls=body()
        with self.assertRaisesRegex(ValueError,r'descriptor\+4'):
            match.verify_leaf_instructions(data,BASE,True,calls,buffer_proof=context(calls,local.SCHEDULER_PAYLOAD))

    def test_native_new_profile_refuses_field4(self):
        data,calls=body(store=0x6050)
        with self.assertRaisesRegex(ValueError,r'descriptor\+8'):
            match.verify_leaf_instructions(data,BASE,True,calls,buffer_proof=context(calls))

    def test_native_pointer_reload_remains_an_extra_outgoing_alias(self):
        data,calls=body(middle=(0x6891,))
        with self.assertRaisesRegex(ValueError,'additional register aliases'):
            match.verify_leaf_instructions(data,BASE,True,calls,buffer_proof=context(calls))

    def test_native_second_pointer_word_is_not_forgotten(self):
        data,calls=body(middle=(0x60D0,))
        with self.assertRaisesRegex(ValueError,r'descriptor\+8'):
            match.verify_leaf_instructions(data,BASE,True,calls,buffer_proof=context(calls))

    def test_native_partial_pointer_store_remains_refused(self):
        data,calls=body(store=0x8110)  # strh r0,[r2,8]
        with self.assertRaisesRegex(ValueError,'stored or spilled'):
            match.verify_leaf_instructions(data,BASE,True,calls,buffer_proof=context(calls))

    def test_direct_pointer_store_rejects_saved_value_or_return_provenance(self):
        for source,returns in ((-8,()),(-23,()),(-24,(R0,))):
            with self.subTest(source=source,returns=returns),self.assertRaises(ValueError):
                match.stack_alias_store([LOCAL]*11+[SAVED]*2,{}, {R0:source},set(returns),-44,4,R0,pointer_proof=context({}))

    def test_old_payload_observation_and_assumptions_keep_field4(self):
        p=context({100:CALLEE},local.SCHEDULER_PAYLOAD)
        p.check_call(CALLEE,{R0+2:-52},[LOCAL]*11+[SAVED]*2,{-48:-24},site=100)
        m=p.contract_manifest()
        self.assertNotIn('payload_pointer_word_offset',m['observations'][0])
        self.assertIn('descriptor+4',' '.join(m['assumptions']))
        self.assertNotIn('descriptor+8',' '.join(m['assumptions']))

    def test_one_call_root_authenticates_both_existing_complete_bodies(self):
        calls={100:CALLEE};p=context(calls)
        p.rom,p.mapping,p.index,p.entries=b'',b'',b'',[]
        p.dependencies,p.records,p.identities={},{},{}
        bodies={CALLEE:SCHEDULER_BODY,0x08005954:ALLOCATOR_BODY}
        p.span=lambda address:bodies.get(address,b'\x00\x00')
        with mock.patch.dict(local.DEPENDENCIES,PINNED), \
                mock.patch.object(local.named,'validate_owner'), \
                mock.patch.object(local.graph,'graph',return_value=({},None,{},calls,{})), \
                mock.patch.object(local.thunk,'dependencies',return_value=[]), \
                mock.patch.object(owner,'refine'), \
                mock.patch('known_query_native_closure_profile.environment_fingerprint',return_value={}):
            p.bind_root(b'',BASE,calls)
        self.assertEqual(set(p.records),{CALLEE,0x08005954})

    def test_new_interface_does_not_admit_guard_or_multiple_calls(self):
        for calls in ({100:CALLEE,120:CALLEE},{100:0x080DD494,120:CALLEE},{}):
            p=context(calls);p.rom,p.mapping,p.index=b'',b'',b''
            with self.subTest(calls=calls),mock.patch.object(local.named,'validate_owner'), \
                    mock.patch.object(local.graph,'graph',return_value=({},None,{},calls,{})), \
                    mock.patch.object(owner,'refine'), \
                    mock.patch('known_query_native_closure_profile.environment_fingerprint',return_value={}), \
                    self.assertRaisesRegex(ValueError,'one actual scheduler call'):
                p.bind_root(b'',BASE,calls)

if __name__=='__main__':unittest.main()
