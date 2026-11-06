"""A guarded callee switch must retain the existing bounded alias checks."""
import copy
import hashlib
import json
from pathlib import Path
import struct
import unittest

from test_buffer_discarded_return_scratch import (
    A, B, C, DiscardedReturnScratchTests, buffers, owner)


class GuardedSwitchBufferTests(unittest.TestCase):
    setUp = DiscardedReturnScratchTests.setUp
    fixture = DiscardedReturnScratchTests.fixture

    def switch_fixture(self, *, constants=False, store='str r0, [r4, #4]',
                       prefix='', guard='bhi default', case='case1', after=''):
        loads = 'ldr r1, constant0\nldr r2, constant1\n' if constants else ''
        words = 'constant0: .word 0x25a\nconstant1: .word 0x25b\n' if constants else ''
        callee = ('push {r4, lr}\nadds r4, r3, #0\nmovs r3, #0\n' + prefix + '\n' + loads +
            'bl child\ncmp r0, #1\n' + guard + '\n'
            'lsls r0, r0, #2\nldr r1, pointer\nadds r0, r0, r1\n'
            'ldr r0, [r0]\nmov pc, r0\n.balign 4, 0\n' + words +
            'pointer: .word table\ntable: .word case0, ' + case + '\n'
            'case0: movs r0, #7\nstr r0, [r4]\nb done\n'
            'case1: movs r0, #8\n' + store + '\nb done\n'
            'default: movs r0, #0\ndone: pop {r4}\npop {r1}\nbx r1')
        return dict(self.fixture(callee=callee, after=after), selector=buffers.GUARDED_SWITCH_SELECTOR)

    def check_switch(self, constants):
        manifest, _ = owner.verify(**self.switch_fixture(constants=constants))
        self.assertEqual(manifest['profile'], buffers.GUARDED_SWITCH_SCHEMA)
        proof = manifest['proof']['buffers']['guarded_switches']
        self.assertIn('switch_constants_profile.py', proof['source_sha256'])
        record, = proof['observations']
        self.assertEqual(record['address'], B)
        self.assertEqual(record['structure']['switch']['bound'], 1)
        self.assertEqual(len(record['structure']['successors']), 2)
        self.assertEqual(record['structure']['partition']['literal_and_table_bytes'],
                         20 if constants else 12)

    def test_plain_switch_composes_calls_and_bounds(self):
        self.check_switch(False)

    def test_two_constant_switch_composes_calls_and_bounds(self):
        self.check_switch(True)

    def test_every_case_preserves_buffer_bounds_and_nonescape(self):
        for store in ('str r0, [r4, #8]', 'str r4, [r1]'):
            with self.subTest(store=store), self.assertRaises(ValueError):
                owner.verify(**self.switch_fixture(store=store))

    def test_returned_alias_remains_tracked_through_nested_calls(self):
        # An identity child and a returned local pointer are supported. Their
        # provenance must reach the caller, where storing the pointer escapes.
        for store in ('adds r0, r4, #0\nbl child', 'adds r0, r4, #0'):
            with self.subTest(store=store), self.assertRaisesRegex(ValueError, 'alias use or escape'):
                owner.verify(**self.switch_fixture(store=store, after='str r0, [r1]'))

    def test_two_constant_layout_keeps_guard_bounds_and_frame_restrictions(self):
        for change in (dict(guard='bhs default'), dict(case='child'),
                       dict(store='str r0, [r4, #8]'),
                       dict(prefix='sub sp, #4\nmov r1, sp\nadd sp, #4')):
            with self.subTest(change=change), self.assertRaises(ValueError):
                owner.verify(**self.switch_fixture(constants=True, **change))

    def test_unsigned_guard_exact_targets_and_owner_partition_required(self):
        for change in (dict(guard='bhs default'), dict(case='case1+1'),
                       dict(case='child'), dict(prefix='b skip\nnop\nskip:')):
            with self.subTest(change=change), self.assertRaises(ValueError):
                owner.verify(**self.switch_fixture(**change))

    def test_callee_identity_mode_mapping_and_table_bytes_are_bound(self):
        for change in ('duplicate', 'arm', 'outside', 'table'):
            f = self.switch_fixture()
            if change == 'table':
                image = bytearray(f['rom'])
                manifest, _ = owner.verify(**f)
                row = manifest['proof']['buffers']['guarded_switches']['observations'][0]
                offset = row['structure']['switch']['table'] + B - 0x08000000
                struct.pack_into('<I', image, offset, C)
                f['rom'] = bytes(image)
            else:
                rows = json.loads(f['mapping'])
                if change == 'duplicate':
                    rows.append(copy.deepcopy(rows[1]))
                elif change == 'arm':
                    rows[1]['mode'] = 'arm'
                else:
                    rows[1]['end'] = f'0x{B+2:08X}'
                f['mapping'] = json.dumps(rows).encode()
            with self.subTest(change=change), self.assertRaises(ValueError):
                owner.verify(**f)

    def test_old_policies_and_absent_switch_are_separate(self):
        f = self.switch_fixture(constants=True)
        for selector in (buffers.SELECTOR, buffers.SCRATCH_SELECTOR, buffers.BIOS_SQRT_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                owner.verify(**dict(f, selector=selector))
        with self.assertRaisesRegex(ValueError, 'actual inspected switch'):
            owner.verify(**dict(self.fixture(callee='str r0, [r3]\nmovs r3, #0\nbx lr'),
                                selector=buffers.GUARDED_SWITCH_SELECTOR))

    def test_fresh_manifest_report_selection_and_original_elf_required(self):
        f = self.switch_fixture(constants=True)
        manifest, _ = owner.verify(**f)
        proof = manifest['proof']['buffers']['guarded_switches']
        module = Path(buffers.__file__).with_name('switch_constants_profile.py')
        self.assertEqual(proof['source_sha256']['switch_constants_profile.py'],
                         hashlib.sha256(module.read_bytes()).hexdigest())
        for field in ('successors', 'transfer', 'table_words_sha256'):
            altered = copy.deepcopy(manifest)
            altered['proof']['buffers']['guarded_switches']['observations'][0]['structure'][field] = None
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'manifest differs'):
                owner.verify(**dict(f, manifest=altered))
        marker = f'* verification: `{buffers.GUARDED_SWITCH_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker), buffers.GUARDED_SWITCH_SELECTOR)
        with self.assertRaises(ValueError):
            owner.selected(marker*2)
        with self.assertRaisesRegex(ValueError, 'original ELF identity'):
            owner.fingerprint(A, f['data'], manifest, 'source', f['mapping'],
                              f['index'], f['objects'], f['rom'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
