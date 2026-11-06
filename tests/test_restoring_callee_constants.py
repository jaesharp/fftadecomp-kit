"""Joint native preservation and actual alias effects, including hostile contexts."""
import json
from pathlib import Path
import struct
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import function_thunk_profile as thunk
import owner_admission_profile as owner
import descriptor_callee_constant_profile as policy

A, B, C = 0x08010000, 0x08011000, 0x08012000
R0, R1, R2, R4, R6 = [match.ARM_REG_R0+n for n in (0, 1, 2, 4, 6)]


def words(*values):
    return struct.pack('<'+'H'*len(values), *values)


def call(site, target):
    delta = target-site-4
    return words(0xF000 | ((delta >> 12) & 0x7FF),
                 0xF800 | ((delta >> 1) & 0x7FF))


def fixture(*, prefix=None, suffix=None, target=C, consumer=None, callee=None):
    # The entry R4 value is privately saved and overwritten before the call.
    prefix = words(0xB510, 0x2400, 0x7004) if prefix is None else prefix
    suffix = words(0xBC10, 0xBC01, 0x4700) if suffix is None else suffix
    body = prefix+call(B+len(prefix), target)+suffix if callee is None else callee
    consumer = words(0xB500)+call(A+2, B)+words(0xBC02, 0x4708) if consumer is None else consumer
    leaf = words(0x2001, 0x4770)
    rom = bytearray(thunk.END-match.ROM_BASE)
    for register in range(13):
        struct.pack_into('<HH', rom, thunk.START-match.ROM_BASE+4*register,
                         0x4700+(register << 3), 0x46C0)
    rows = []
    for address, data in ((A, consumer), (B, body), (C, leaf)):
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(data)] = data
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        rows.append(dict(rom=f'0x{address:08X}', end=f'0x{address+len(data):08X}',
                         mode='thumb', instrs=len(list(decoder.disasm(data, address)))))
    rows += [dict(rom=f'0x{address:08X}', end=f'0x{address+2:08X}',
                  mode='thumb', instrs=1) for address in thunk.ALIASES.values()]
    mapping = json.dumps(rows).encode()
    index = ''.join(f"{int(row['rom'],16):08X} {int(row['end'],16):08X} "
                    f"{int(row['end'],16)-int(row['rom'],16)} {row['instrs']} return\n"
                    for row in rows).encode()
    return bytes(rom), mapping, index


def proof(**changes):
    return policy.DescriptorRestoringCalleeConstantProof(*fixture(**changes), b'{}')


def replay(instance, *, arguments=None, watched=(R4,), constants=None):
    return instance.check_arguments(B, {R0:-4} if arguments is None else arguments,
        [(False, False, True)], {}, frozenset(),
        constants={R6:C+1} if constants is None else constants,
        site=A+2, words={}, frame_base=-4, root_frame=A, watched=watched)


class RestoringConstantTests(unittest.TestCase):
    def test_actual_restoration_effects_and_native_constants_complete_together(self):
        instance = proof()
        result = replay(instance)
        self.assertEqual(instance.preserved_frames[B]['frame']['preserved'],
                         'r4-r11,sp,entry-lr')
        receipt = instance.restoring_leaf_manifest()
        self.assertEqual(receipt['observations'][0]['restoration']['registers'], [4])
        self.assertIn('descriptor_callee_constant_profile.py', receipt['source_sha256'])
        constants = {R6:C+1, R1:123}
        instance.finish_call_constants(constants, result, site=A+2, target=B)
        self.assertEqual(constants, {R6:C+1})

    def test_same_body_different_alias_offset_cannot_reuse_safe_effects(self):
        instance = proof()
        replay(instance)
        before = instance.native_frames[B]
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            replay(instance, arguments={R0:-8})
        self.assertEqual(instance.native_frames[B], before)

    def test_explicit_pointer_argument_cannot_be_relaxed(self):
        instance = proof()
        with self.assertRaisesRegex(ValueError, 'explicit pointer argument'):
            replay(instance, arguments={R0:-4, R4:-4})
        self.assertFalse(instance.leaf_restorations)

    def test_observed_opaque_entry_alias_refuses_before_export(self):
        instance = proof(prefix=words(0xB510, 0x1C22, 0x2400, 0x7004))
        with self.assertRaisesRegex(ValueError, 'observes an opaque live entry alias'):
            replay(instance)
        self.assertNotIn(B, instance.preserved_frames)
        self.assertFalse(instance.leaf_restorations)

    def test_saved_word_write_and_wrong_restore_refuse(self):
        variants = [dict(prefix=words(0xB510, 0x2400, 0x9400)),
                    dict(suffix=words(0xBC20, 0xBC01, 0x4700))]
        for variant in variants:
            instance = proof(**variant)
            with self.subTest(variant=variant), self.assertRaises(ValueError):
                replay(instance)
            self.assertNotIn(B, instance.preserved_frames)

    def test_unknown_callback_and_changed_canonical_thunk_refuse(self):
        target = thunk.START+4*6
        instance = proof(target=target)
        with self.assertRaisesRegex(ValueError, 'exact Thumb'):
            replay(instance, constants={})
        rom, mapping, index = fixture(target=target)
        changed = bytearray(rom)
        changed[target-match.ROM_BASE:target-match.ROM_BASE+2] = words(0x4728)
        instance = policy.DescriptorRestoringCalleeConstantProof(bytes(changed), mapping, index, b'{}')
        with self.assertRaises(ValueError):
            replay(instance)
        self.assertNotIn(B, instance.preserved_frames)

    def test_exact_canonical_target_has_its_own_native_certificate(self):
        target = thunk.START+4*6
        instance = proof(target=target)
        replay(instance)
        calls = instance.preserved_frames[B]['calls']
        self.assertEqual(calls[0]['proofs'][0]['target'], target)
        self.assertEqual(calls[0]['proofs'][0]['resolved_address'], C)
        self.assertEqual(instance.native_frames[C], 1)

    def test_dead_return_scratch_requires_actual_consumer_continuation(self):
        callee = words(0xB500, 0x1C02, 0x2000, 0xBC02, 0x4708)
        instance = proof(callee=callee)
        replay(instance)
        receipt = instance.scratch_manifest()['observations']
        self.assertEqual(receipt[0]['projected'], [[2, -4]])
        consumer = words(0xB500)+call(A+2, B)+words(0x1C10, 0xBC02, 0x4708)
        instance = proof(callee=callee, consumer=consumer)
        with self.assertRaisesRegex(ValueError, 'consumer observes discarded return scratch'):
            replay(instance)
        self.assertNotIn(B, instance.preserved_frames)
        local = words(0xB500, 0xB081, 0x466A, 0x2000, 0xB001, 0xBC02, 0x4708)
        instance = proof(callee=local)
        with self.assertRaisesRegex(ValueError, 'local stack pointer escapes'):
            replay(instance)
        self.assertNotIn(B, instance.preserved_frames)

    def test_distinct_schema_and_mixed_markers_remain_strict(self):
        for selector, schema in policy.PROFILES.items():
            marker = f'* verification: `{schema}`\n'
            self.assertEqual(owner.selector_for_report(marker), selector)
            with self.assertRaises(ValueError):
                owner.selected(marker+marker)
        mixed = ''.join(f'* verification: `{schema}`\n' for schema in policy.PROFILES.values())
        with self.assertRaises(ValueError):
            owner.selected(mixed)
        with self.assertRaises(ValueError):
            policy.proof_type('descriptor-restoring-callee-constant-v2')


if __name__ == '__main__':
    unittest.main(verbosity=2)
