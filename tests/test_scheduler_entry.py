"""Pinned pool-wrapper and direct scheduler entries for 28-byte descriptors."""
import hashlib
from pathlib import Path
import struct
import subprocess
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import conditional_local_buffer_profile as local
import scheduler_entry_profile as profile
import owner_admission_profile as owner
from test_scheduler_predicates import half, bl, fixture, A, R0, LOCAL, SAVED

POOL, DIRECT = profile.POOL, profile.DIRECT
MANAGER = 0x0200F430


def pool_caller(*, register=2, extra=False):
    # push {lr}; sub sp,#28; add rN,sp,#0; movs r1,#8; [movs r3,#0]; bl; add sp,#28; pop {r1}; bx r1
    data = half(0xB500, 0xB087, 0xA800 | register << 8, 0x2108)
    if register != 3:
        data += half(0x2300)
    if extra:
        data += half(0x1C10 | 3)  # r3 = r2, a second outgoing alias
    site = A+len(data)
    return data+bl(site, POOL)+half(0xB007, 0xBC02, 0x4708), {site: POOL}


def direct_caller(*, descriptor=1, deref=0x6800, parent=0x9200, join=False):
    # push {lr}; sub sp,#32; add r3,sp,#4*descriptor; ldr r0,[pc,#16]; ldr r0,[r0];
    # str r2,[sp]; movs r2,#40; bl; add sp,#32; pop {r1}; bx r1; .word MANAGER
    if join:
        # ldr r0,[pc]; cmp r1,#0; beq L; ldr r0,[r0]; L: the dereference is
        # skipped on one path, so it is not the only reaching manager write.
        data = half(0xB500, 0xB088, 0xAB00+descriptor, 0x4805, 0x2900, 0xD000, 0x6800,
                    parent, 0x2228)
    else:
        data = half(0xB500, 0xB088, 0xAB00+descriptor, 0x4804, deref, parent, 0x2228)
    site = A+len(data)
    data += bl(site, DIRECT)+half(0xB008, 0xBC02, 0x4708)
    data += b'\0\0'*((-len(data)) % 4 // 2)
    return data+struct.pack('<I', MANAGER), {site: DIRECT}


def bound(data, calls, policy=profile.SELECTOR, pins=None):
    bodies = {A: data, POOL: bytes(44), DIRECT: bytes(206)}
    p = fixture(bodies, policy=policy)
    span = p.span
    runtimes = set(match.function_thunk.ALIASES.values())
    p.span = lambda a: half(0x4710) if a in runtimes else span(a)
    pins = pins or {a: (len(b), hashlib.sha256(b).hexdigest()) for a, b in bodies.items() if a != A}
    with mock.patch.dict(local.DEPENDENCIES, pins), mock.patch.object(local.thunk, 'dependencies', return_value=[]):
        p.bind_root(data, A, calls)
    return p


def verified(data, calls, **kw):
    p = bound(data, calls, **kw)
    match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)
    return p


class SchedulerEntryTests(unittest.TestCase):
    def test_pool_wrapper_caller_records_entry_and_descriptor(self):
        data, calls = pool_caller()
        p = verified(data, calls)
        report = p.contract_manifest()
        self.assertEqual(report['schema'], profile.SCHEMA)
        self.assertEqual(report['entry']['address'], POOL)
        self.assertEqual(report['entry']['kind'], 'pool-manager-wrapper')
        observation, = report['observations']
        self.assertEqual((observation['scheduler_entry'], observation['local_offset'], observation['bytes']),
                         ('pool-manager-wrapper', -32, 28))
        self.assertEqual(sorted(p.dependencies), [DIRECT, POOL])

    def test_direct_caller_records_manager_literal_and_outgoing_word(self):
        data, calls = direct_caller()
        p = verified(data, calls)
        report = p.contract_manifest()
        self.assertEqual(report['entry']['manager'], dict(literal_offset=24, load_site=A+6, dereference_site=A+8))
        observation, = report['observations']
        self.assertEqual((observation['local_offset'], observation['outgoing_argument_word']), (-32, -36))
        self.assertEqual(sorted(p.dependencies), [DIRECT])

    def test_existing_scheduler_selectors_still_refuse_both_entries(self):
        for data, calls in (pool_caller(), direct_caller()):
            for policy in (local.SCHEDULER, local.SCHEDULER_PAYLOAD):
                with self.subTest(policy=policy, target=calls), self.assertRaises(ValueError):
                    bound(data, calls, policy=policy)

    def test_08005B6C_wrong_and_extra_targets_refused(self):
        data, calls = pool_caller()
        site = next(iter(calls))
        for alternate in ({site: 0x08005B6C}, {site: POOL+2}, {**calls, A: DIRECT}):
            with self.subTest(alternate=alternate), self.assertRaises(ValueError):
                bound(data, alternate)
        # The closed entry table itself refuses func_08005B6C and extra calls.
        for alternate in ({site: 0x08005B6C}, {site: POOL, A: DIRECT}, {}):
            with self.subTest(table=alternate), self.assertRaisesRegex(ValueError, 'one actual pinned entry'):
                profile.bind(data, A, {}, {}, alternate)

    def test_entry_body_identity_differs_refused(self):
        data, calls = pool_caller()
        pins = {POOL: (44, '0'*64), DIRECT: (206, hashlib.sha256(bytes(206)).hexdigest())}
        with self.assertRaisesRegex(ValueError, 'dependency identity differs'):
            bound(data, calls, pins=pins)

    def test_pool_descriptor_in_wrong_register_or_extra_alias_refused(self):
        for data, calls in (pool_caller(register=3), pool_caller(extra=True)):
            with self.subTest(data=data.hex()), self.assertRaisesRegex(ValueError, 'additional register or pointer-word'):
                verified(data, calls)

    def test_direct_descriptor_overlapping_outgoing_word_refused(self):
        data, calls = direct_caller(descriptor=0)
        with self.assertRaisesRegex(ValueError, 'overlaps the outgoing argument word'):
            verified(data, calls)

    def test_direct_local_pointer_as_parent_refused(self):
        data, calls = direct_caller(parent=0x9300)  # str r3,[sp]: parent is the descriptor address
        with self.assertRaises(ValueError):
            verified(data, calls)

    def test_direct_manager_not_one_named_data_load_refused(self):
        for deref in (0x2000, 0x6840, 0x6808):  # movs r0,#0; ldr r0,[r0,#4]; ldr r0,[r1]
            data, calls = direct_caller(deref=deref)
            with self.subTest(deref=hex(deref)), self.assertRaisesRegex(ValueError, 'named data load'):
                bound(data, calls)

    def test_direct_manager_load_across_branch_join_refused(self):
        data, calls = direct_caller(join=True)
        with self.assertRaisesRegex(ValueError, 'straight-line named data load'):
            bound(data, calls)

    def test_manager_literal_requires_one_typed_zero_addend_data_binding(self):
        data, calls = direct_caller()
        report = verified(data, calls).contract_manifest()
        profile.check_bindings(report, dict(data=[[24, 'data_0200F430', 0]]))
        for rows in ([], [[24, 'data_0200F430', 4]], [[28, 'data_0200F430', 0]],
                     [[24, 'data_0200F430', 0], [24, 'data_0200F434', 0]]):
            with self.subTest(rows=rows), self.assertRaisesRegex(ValueError, 'typed named data relocation'):
                profile.check_bindings(report, dict(data=rows))
        pool = verified(*pool_caller()).contract_manifest()
        profile.check_bindings(pool, dict(data=[]))

    def test_tampered_manifest_entry_refused_by_binding_check(self):
        data, calls = direct_caller()
        report = verified(data, calls).contract_manifest()
        report['entry']['manager']['literal_offset'] = 28
        with self.assertRaises(ValueError):
            profile.check_bindings(report, dict(data=[[24, 'data_0200F430', 0]]))

    def test_changed_path_state_refused_and_manifest_requires_observation(self):
        data, calls = pool_caller()
        p = bound(data, calls)
        with self.assertRaises(ValueError):
            p.contract_manifest()
        site, stack = next(iter(calls)), [LOCAL]*7+[SAVED]
        p.check_call(POOL, {R0+2: -32}, stack, {}, site=site)
        p.check_call(POOL, {R0+2: -32}, stack, {}, site=site)
        with self.assertRaises(ValueError):
            p.check_call(POOL, {R0+2: -32, R0+4: -28}, stack, {}, site=site)
        with self.assertRaises(ValueError):
            p.check_call(POOL, {R0+2: -32}, stack, {}, site=site+2)

    def test_manifest_retains_conditional_premises(self):
        for data, calls, word in ((*pool_caller(), 'data_020159CC'), (*direct_caller(), 'ldr r6,[sp,#0x38]')):
            report = verified(data, calls).contract_manifest()
            text = ' '.join(report['assumptions'])
            for flag in ('actual_callback_effects_proved', 'nonescape_proved', 'termination_proved'):
                self.assertFalse(report[flag])
            for phrase in ('ambient original R9', 'separate from all caller stack words', word):
                self.assertIn(phrase, text)

    def test_pinned_entry_table_and_CLI_registration(self):
        self.assertEqual(local.DEPENDENCIES[POOL],
                         (44, '6646f8955088430fdcc363b15cb3555c12a6ae52ec775c4a4aba44e43a7e292f'))
        self.assertNotIn(0x08005B6C, profile.ENTRIES)
        self.assertIn(profile.SELECTOR, owner.named_buffer.SELECTORS)
        self.assertEqual(owner.selector_for_report('* verification: `'+profile.SCHEMA+'`'), profile.SELECTOR)
        run = subprocess.run([sys.executable, '-B', str(Path(match.__file__)), '--owner-runtime-profile',
                              profile.SELECTOR, '--help'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)


if __name__ == '__main__':
    unittest.main()
