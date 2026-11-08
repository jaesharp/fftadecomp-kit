"""Complete synthetic Thumb helpers exercise guarded scheduler composition."""
import json
import hashlib
from pathlib import Path
import struct
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import named_data_buffer_profile as named
import conditional_local_buffer_profile as local
import scheduler_predicate_profile as predicates

A, B, C = 0x08001000, 0x08001200, 0x08001400
R0 = match.ARM_REG_R0
LOCAL, SAVED = (False, False, True), (False, True, False)


def half(*values):
    return struct.pack('<'+'H'*len(values), *values)


def bl(site, target):
    displacement = target-site-4
    return half(0xF000 | (displacement >> 12 & 0x7FF),
                0xF800 | (displacement >> 1 & 0x7FF))


def fixture(bodies, *, policy=local.SCHEDULER_GUARDED):
    rom = bytearray(max(address+len(body) for address, body in bodies.items())-match.ROM_BASE)
    rows = []
    for address, body in sorted(bodies.items()):
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(body)] = body
        rows.append(dict(rom=f'0x{address:08X}', end=f'0x{address+len(body):08X}',
                         mode='thumb', instrs=0))
    mapping = json.dumps(rows).encode()
    index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                    f'{int(row["end"],16)-int(row["rom"],16)} 0 return\n'
                    for row in rows).encode()
    return local.ConditionalLocalBufferProof(bytes(rom), mapping, index, b'{}', policy=policy)


def call_body(address, target):
    return half(0xB510, 0x1C04)+bl(address+4, target)+half(0xBC10, 0xBC02, 0x4708)


def root_body(*, early_alias=False):
    data = half(0xB510, 0xB087)
    if early_alias:
        data += half(0xAC00)  # r4 = sp, still live at guard
    first = A+len(data)
    data += bl(first, B)+half(0xAA00)
    second = A+len(data)
    data += bl(second, predicates.SCHEDULER)+half(0xB007, 0xBC10, 0xBC02, 0x4708)
    return data, {first:B, second:predicates.SCHEDULER}


def replay_proof(calls):
    p = fixture({B:half(0x6800, 0x4770)})
    p.predicates = predicates.close(p, [B])
    p.calls, p.environment, p.runtime_dependencies = calls, {}, []
    return p


class PredicateClosureTests(unittest.TestCase):
    def test_readonly_scalar_leaf_complete_frame(self):
        p = fixture({A:half(0x8840, 0x2108, 0x4008, 0x4770)})
        result = predicates.close(p, [A])
        self.assertEqual(result['helpers'], [A])
        self.assertEqual(p.records[A]['structure']['instructions'], 4)
        self.assertFalse(result['actual_memory_readability_proved'])
        self.assertFalse(result['actual_predicate_values_proved'])

    def test_nested_shared_helper_closes_once_with_saved_r4(self):
        p = fixture({A:call_body(A,C), B:call_body(B,C), C:half(0x4770)})
        self.assertEqual(predicates.close(p, [A,B])['helpers'], [A,B,C])
        self.assertEqual(len(p.dependencies), 3)

    def test_frame_must_restore_callee_saved_register(self):
        p = fixture({A:half(0x2401,0x4770)})
        with self.assertRaisesRegex(ValueError, 'restore SP, r4-r11'):
            predicates.close(p,[A])

    def test_return_must_be_original_entry_lr(self):
        p = fixture({A:half(0xB500,0xBC01,0x4708)})
        with self.assertRaises(ValueError):
            predicates.close(p,[A])

    def test_memory_store_encodings_refused(self):
        for encoding in (0x6001,0x7001,0x8001,0x5001,0x5201,0x5401,0xC002):
            with self.subTest(encoding=hex(encoding)), self.assertRaises(ValueError):
                predicates.close(fixture({A:half(encoding,0x4770)}),[A])

    def test_stack_address_materialization_and_swi_refused(self):
        for encoding in (0x4668,0xA800,0x9000,0xDF0B):
            with self.subTest(encoding=hex(encoding)), self.assertRaises(ValueError):
                predicates.close(fixture({A:half(encoding,0x4770)}),[A])

    def test_unclosed_indirect_transfer_refused(self):
        with self.assertRaises(ValueError):
            predicates.close(fixture({A:half(0x4700)}),[A])

    def test_missing_nested_owner_refused(self):
        with self.assertRaises(ValueError):
            predicates.close(fixture({A:call_body(A,B)}),[A])

    def test_call_cycle_refused(self):
        p=fixture({A:call_body(A,B), B:call_body(B,A)})
        with self.assertRaisesRegex(ValueError, 'call cycle'):
            predicates.close(p,[A])

    def test_cfg_cycle_with_reachable_exit_refused(self):
        # cmp r0,0; beq self; bx lr: every node can reach return, still cyclic.
        with self.assertRaisesRegex(ValueError, 'CFG cycles'):
            predicates.close(fixture({A:half(0x2800,0xD0FE,0x4770)}),[A])

    def test_complete_owner_rejects_unowned_tail(self):
        with self.assertRaises(ValueError):
            predicates.close(fixture({A:half(0x4770,0x1234)}),[A])

    def test_helper_budget_and_size_are_explicit(self):
        bodies={A+0x400*i:half(0x4770) for i in range(9)}
        with self.assertRaisesRegex(ValueError, 'helper budget'):
            predicates.close(fixture(bodies),bodies)
        with self.assertRaisesRegex(ValueError, 'byte budget'):
            predicates.close(fixture({A:half(*([0x2000]*256),0x4770)}),[A])

    def test_overlap_and_instruction_count_not_bypassed(self):
        p=fixture({A:half(0x4770)})
        rows=json.loads(p.mapping)
        rows[0]['instrs']=2
        p.mapping=json.dumps(rows).encode()
        with self.assertRaises(ValueError):
            predicates.close(p,[A])
        p=fixture({A:half(0x2000,0x4770), A+2:half(0x4770)})
        with self.assertRaises(ValueError):
            predicates.close(p,[A])

    def test_runtime_target_is_not_a_predicate(self):
        target=match.function_thunk.ALIASES['_call_via_r2']
        p=fixture({A:half(0x4770)})
        with self.assertRaisesRegex(ValueError, 'runtime and indirect'):
            predicates.close(p,[target])


class GuardedCompositionTests(unittest.TestCase):
    def test_bind_root_then_native_replay_composes_complete_synthetic_caller(self):
        data, calls = root_body()
        bodies = {0x08005B6C:bytes(60), 0x08005954:bytes(206)}
        p = fixture({A:data, B:half(0x6800,0x4770), **bodies})
        original_span = p.span
        runtime = set(match.function_thunk.ALIASES.values())
        p.span = lambda address: (bodies[address] if address in bodies else
                                 half(0x4710) if address in runtime else original_span(address))
        pins = {address:(len(body), hashlib.sha256(body).hexdigest())
                for address,body in bodies.items()}
        with mock.patch.dict(local.DEPENDENCIES,pins), \
                mock.patch.object(local.thunk,'dependencies',return_value=[]):
            p.bind_root(data,A,calls)
        match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p)
        self.assertEqual(set(p.records),{B,0x08005B6C,0x08005954})
        self.assertEqual(p.contract_manifest()['schema'],local.SCHEMAS[local.SCHEDULER_GUARDED])
        with self.assertRaisesRegex(ValueError,'single use'):
            p.bind_root(data,A,calls)

    def test_phase_checks_cfg_not_numerical_address_order(self):
        # Guard at high address, scheduler at low address: legal execution order.
        predicates.phases({40:(60,),60:(20,),20:()}, {60:B,20:predicates.SCHEDULER})

    def test_guard_after_scheduler_on_either_join_arm_refused(self):
        with self.assertRaisesRegex(ValueError, 'after scheduler'):
            predicates.phases({0:(2,4),2:(4,),4:()}, {2:predicates.SCHEDULER,4:B})

    def test_missing_or_multiple_scheduler_and_cycles_refused(self):
        for edges,calls in (({0:()}, {0:B}),
                            ({0:(2,),2:(4,),4:()}, {0:B,2:predicates.SCHEDULER,4:predicates.SCHEDULER}),
                            ({0:(2,),2:(0,)}, {0:B,2:predicates.SCHEDULER})):
            with self.subTest(edges=edges), self.assertRaises(ValueError):
                predicates.phases(edges,calls)

    def test_native_replay_observes_alias_free_predicate_and_descriptor(self):
        data,calls=root_body()
        p=replay_proof(calls)
        match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p)
        report=p.contract_manifest()
        self.assertEqual(len(report['observations']),2)
        self.assertEqual(report['observations'][1]['bytes'],28)
        self.assertFalse(report['actual_callback_effects_proved'])
        self.assertIn('premises',report['predicates']['conditional_memory'])

    def test_native_replay_retains_callee_saved_local_alias_at_guard(self):
        data,calls=root_body(early_alias=True)
        with self.assertRaisesRegex(ValueError,'every live local alias'):
            match.verify_leaf_instructions(data,A,True,calls,buffer_proof=replay_proof(calls))

    def test_all_alias_registers_and_pointer_words_refused_at_guard(self):
        p=replay_proof({100:B})
        for aliases,slots,words in (({R0:-36},{},{}),({R0+4:-36},{},{}),
                                    ({R0+9:-36},{},{}),({}, {-36:-32},{}),
                                    ({},{},{R0:'opaque'})):
            with self.subTest(aliases=aliases,slots=slots),self.assertRaises(ValueError):
                p.check_call(B,aliases,[LOCAL]*7+[SAVED]*2,slots,site=100,words=words)

    def test_no_new_payload_pointer_permission(self):
        p=replay_proof({100:predicates.SCHEDULER})
        with self.assertRaises(ValueError):
            p.check_call(predicates.SCHEDULER,{R0+2:-36},[LOCAL]*7+[SAVED]*2,{-32:-36},site=100)

    def test_unobserved_guard_and_unknown_site_refused(self):
        p=replay_proof({100:B,102:predicates.SCHEDULER})
        p.check_call(predicates.SCHEDULER,{R0+2:-36},[LOCAL]*7+[SAVED]*2,site=102)
        with self.assertRaises(ValueError): p.contract_manifest()
        with self.assertRaises(ValueError): p.check_call(B,{},[],site=104)

    def test_new_dependency_budget_does_not_change_defaults(self):
        self.assertEqual(fixture({A:half(0x4770)}).dependency_budget,12)
        self.assertEqual(fixture({A:half(0x4770)},policy=local.SCHEDULER).dependency_budget,8)
        self.assertFalse(match._ordinary_call_replay(fixture({A:half(0x4770)},policy=local.SCHEDULER),B))

if __name__=='__main__':
    unittest.main()
