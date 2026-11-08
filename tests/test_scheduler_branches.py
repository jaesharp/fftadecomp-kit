"""Bounded conditional call composition keeps all paths and local aliases."""
import hashlib
import json
from pathlib import Path
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import conditional_local_buffer_profile as local
import scheduler_branch_profile as branch
import scheduler_predicate_profile as predicates
from test_scheduler_predicates import fixture,half,bl,A,B,C,R0,LOCAL,SAVED

S=branch.SCHEDULER


def caller(*,early_alias=False,both_on_path=False):
    data=half(0xB510,0xB087)
    if early_alias:data+=half(0xAC00)
    first=A+len(data);data+=bl(first,B)+half(0x2800,0xD003,0xAA00)
    second=A+len(data);data+=bl(second,S)+half(0x2100 if both_on_path else 0xE002,0xAA00)
    third=A+len(data);data+=bl(third,S)+half(0x2000,0xB007,0xBC10,0xBC02,0x4708)
    return data,{first:B,second:S,third:S}


def bound(data,calls):
    # Only the old pinned scheduler/allocator bodies and runtime byte transport
    # are synthetic stubs. Caller CFG/frame and ordinary body authentication run.
    bodies={S:bytes(60),0x08005954:bytes(206)}
    p=fixture({A:data,B:half(0x6008,0x4770),**bodies},policy=local.SCHEDULER_BRANCH)
    original_span=p.span
    runtime=set(match.function_thunk.ALIASES.values())
    p.span=lambda address: half(0x4710) if address in runtime else original_span(address)
    pins={address:(len(body),hashlib.sha256(body).hexdigest()) for address,body in bodies.items()}
    with mock.patch.dict(local.DEPENDENCIES,pins),mock.patch.object(local.thunk,'dependencies',return_value=[]):
        p.bind_root(data,A,calls)
    return p


def context(calls):
    p=fixture({B:half(0x6008,0x4770)},policy=local.SCHEDULER_BRANCH)
    p.calls,p.environment,p.runtime_dependencies=calls,{},[]
    p.branch_calls={'ordinary_targets':[B]}
    return p


class BranchGraphTests(unittest.TestCase):
    def test_two_scheduler_sites_on_distinct_paths(self):
        result=branch.phases({0:(2,),2:(4,6),4:(8,),6:(8,),8:()}, {0:B,4:S,6:S})
        self.assertEqual(result['scheduler_sites'],[4,6])
        self.assertEqual(result['maximum_scheduler_calls_per_path'],1)
        self.assertFalse(result['ordinary_calls_after_scheduler'])

    def test_no_scheduler_execution_on_one_return_path_is_allowed(self):
        branch.phases({0:(2,4),2:(),4:()}, {2:B,4:S})

    def test_cfg_order_not_numerical_address_order(self):
        branch.phases({0:(60,),60:(20,40),20:(),40:()}, {60:B,20:S,40:S})

    def test_second_scheduler_on_same_path_is_refused(self):
        with self.assertRaisesRegex(ValueError,'after a scheduler'):
            branch.phases({0:(2,),2:(4,),4:()}, {0:B,2:S,4:S})

    def test_ordinary_call_after_scheduler_on_one_join_arm_is_refused(self):
        with self.assertRaisesRegex(ValueError,'after a scheduler'):
            branch.phases({0:(2,4),2:(4,),4:()}, {2:S,4:B})

    def test_cfg_cycles_and_unknown_edges_are_refused(self):
        for edges in ({0:(2,),2:(0,)},{0:(2,),2:(4,)}):
            with self.subTest(edges=edges),self.assertRaises(ValueError):
                branch.phases(edges,{0:B,2:S})

    def test_missing_or_too_many_scheduler_sites_refused(self):
        for calls in ({0:B},{0:B,1:S,2:S,3:S},{0:S}):
            with self.subTest(calls=calls),self.assertRaisesRegex(ValueError,'bounds'):
                branch.phases({site:() for site in calls},calls)

    def test_unique_helper_and_call_site_budgets(self):
        cases=({0:S,**{i:B+2*i for i in range(1,6)}},
               {0:S,**{i:B for i in range(1,9)}})
        for calls in cases:
            with self.subTest(calls=calls),self.assertRaisesRegex(ValueError,'bounds'):
                branch.phases({site:() for site in calls},calls)

    def test_call_site_must_be_in_authenticated_graph(self):
        with self.assertRaises(ValueError):branch.phases({0:()},{0:B,2:S})


class BranchBindingTests(unittest.TestCase):
    def test_writing_helper_identity_does_not_claim_readonly_or_effect_proof(self):
        p=fixture({B:half(0x6008,0x4770)},policy=local.SCHEDULER_BRANCH)
        m=branch.bind(p,{0:(2,),2:()},{0:B,2:S})
        record=p.records[B]
        self.assertEqual(record['body_sha256'],hashlib.sha256(half(0x6008,0x4770)).hexdigest())
        self.assertFalse(record['structure']['callee_effects_proved'])
        self.assertFalse(m['ordinary_callee_effects_proved'])
        self.assertFalse(m['nested_execution_proved'])
        self.assertIn('existing returning ARM ABI',m['ordinary_call_contract'])
        self.assertEqual(p.dependencies[B],half(0x6008,0x4770))

    def test_missing_indexed_owner_refused(self):
        p=fixture({C:half(0x4770)},policy=local.SCHEDULER_BRANCH)
        with self.assertRaises(ValueError):branch.bind(p,{0:(2,),2:()},{0:B,2:S})

    def test_overlapping_helper_index_refused(self):
        p=fixture({B:half(0x2000,0x4770),B+2:half(0x4770)},policy=local.SCHEDULER_BRANCH)
        with self.assertRaises(ValueError):branch.bind(p,{0:(2,),2:()},{0:B,2:S})

    def test_wrong_index_extent_and_count_refused(self):
        for index in (b'08001200 08001204 4 100 return\n', b'08001200 08001206 6 0 return\n'):
            p=fixture({B:half(0x2000,0x4770)},policy=local.SCHEDULER_BRANCH);p.index=index
            with self.subTest(index=index),self.assertRaises(ValueError):
                branch.bind(p,{0:(2,),2:()},{0:B,2:S})

    def test_runtime_thunk_is_not_an_ordinary_target(self):
        p=fixture({B:half(0x4770)},policy=local.SCHEDULER_BRANCH)
        with self.assertRaisesRegex(ValueError,'ordinary indexed Thumb'):
            branch.bind(p,{0:(2,),2:()},{0:match.function_thunk.ALIASES['_call_via_r2'],2:S})

    def test_complete_raw_caller_binds_and_observes_all_three_sites(self):
        data,calls=caller();p=bound(data,calls)
        match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p)
        report=p.contract_manifest()
        self.assertEqual(len(report['observations']),3)
        self.assertEqual([o['bytes'] for o in report['observations'] if 'bytes' in o],[28,28])
        self.assertEqual(report['branch_calls']['maximum_scheduler_calls_per_path'],1)
        self.assertFalse(report['actual_callback_effects_proved'])
        self.assertFalse(report['branch_calls']['ordinary_callee_effects_proved'])
        self.assertEqual(set(p.dependencies),{B,S,0x08005954})

    def test_complete_raw_caller_with_two_scheduler_calls_on_one_path_refused(self):
        data,calls=caller(both_on_path=True)
        with self.assertRaisesRegex(ValueError,'after a scheduler'):bound(data,calls)

    def test_complete_native_replay_keeps_callee_saved_alias_at_ordinary_call(self):
        data,calls=caller(early_alias=True);p=bound(data,calls)
        with self.assertRaisesRegex(ValueError,'every live local alias'):
            match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p)

    def test_ordinary_call_must_have_no_aliases_in_any_register(self):
        for reg in (R0,R0+1,R0+2,R0+3,R0+4,R0+9):
            with self.subTest(reg=reg),self.assertRaisesRegex(ValueError,'every live local alias'):
                context({100:B}).check_call(B,{reg:-36},[LOCAL]*7+[SAVED]*2,site=100)

    def test_pointer_slots_and_word_facts_are_not_discarded_at_ordinary_call(self):
        for slots,words in (({-36:-32},{}),({},{R0:'opaque'})):
            with self.subTest(slots=slots),self.assertRaises(ValueError):
                context({100:B}).check_call(B,{},[LOCAL]*7+[SAVED]*2,slots,site=100,words=words)

    def test_complete_descriptor_and_preserved_alias_at_each_scheduler(self):
        p=context({100:S,200:S})
        p.check_call(S,{R0+2:-64,R0+4:-64},[LOCAL]*14+[SAVED]*2,site=100)
        p.check_call(S,{R0+2:-36},[LOCAL]*14+[SAVED]*2,site=200)
        self.assertEqual([o['local_offset'] for o in p.contract_manifest()['observations']],[-64,-36])

    def test_short_descriptor_saved_word_and_extra_pointer_refused(self):
        for offset,slots in ((-32,{}),(-36,{-32:-36}),(-40,{})):
            with self.subTest(offset=offset,slots=slots),self.assertRaises(ValueError):
                context({100:S}).check_call(S,{R0+2:offset},[LOCAL]*7+[SAVED]*2,slots,site=100)

    def test_unknown_target_and_unobserved_ordinary_site_refused(self):
        p=context({100:B,200:S})
        p.check_call(S,{R0+2:-36},[LOCAL]*7+[SAVED]*2,site=200)
        with self.assertRaises(ValueError):p.contract_manifest()
        with self.assertRaises(ValueError):p.check_call(C,{},[],site=100)

    def test_frame_difference_at_scheduler_site_refused(self):
        p=context({100:S})
        p.check_call(S,{R0+2:-36},[LOCAL]*7+[SAVED]*2,site=100)
        with self.assertRaisesRegex(ValueError,'differs across incoming paths'):
            p.check_call(S,{R0+2:-40},[LOCAL]*8+[SAVED]*2,site=100)

    def test_old_predicate_profile_still_refuses_writing_helper(self):
        p=fixture({B:half(0x6008,0x4770)})
        with self.assertRaisesRegex(ValueError,'memory-writing'):
            predicates.close(p,[B])

    def test_no_payload_store_permission_added(self):
        stack=[LOCAL]*8+[SAVED]*2
        with self.assertRaisesRegex(ValueError,'stored or spilled'):
            match.stack_alias_store(stack,{}, {R0:-40},set(),-32,4,R0,pointer_proof=context({}))

if __name__=='__main__':unittest.main()
