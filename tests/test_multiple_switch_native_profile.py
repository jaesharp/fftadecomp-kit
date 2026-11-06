"""Source-profile binding, report replay and isolation around real ELF fixtures."""
import argparse
import copy
import hashlib
import json
import unittest
from unittest.mock import patch

import test_multiple_switch_owner_prerequisite as fixtures
import multiple_switch_native_profile as native
import owner_admission_profile as owner


class MultipleSwitchNativeTests(unittest.TestCase):
    def setUp(self):
        self.fixture = fixtures.fixture()
        self.inputs = fixtures.inputs(self.fixture)
        self.bindings = dict(calls=self.fixture[4]['calls'], data=[], functions=[],
                             switches=[list(row) for row in sorted(self.fixture[2].items())])

    def verify(self, **changes):
        return native.verify_original(*self.inputs, changes.pop('bindings', self.bindings), **changes)

    def result(self):
        manifest, count = self.verify()
        original, linked, address, rom, mapping, index = self.inputs
        return (bytes(self.fixture[0]), manifest, 'a'*64, mapping, index, b'{}', rom, count, original)

    def test_actual_original_roles_and_conditional_owner_receipt(self):
        manifest, count = self.verify()
        self.assertEqual(manifest['profile'], native.SCHEMA)
        self.assertEqual(manifest['bindings'], self.bindings)
        self.assertEqual(count, self.fixture[5][0]['instrs'])
        self.assertEqual(manifest['prerequisite']['original_ET_REL_sha256'],
                         hashlib.sha256(self.inputs[0]).hexdigest())
        self.assertEqual(len(manifest['prerequisite']['switches']), 2)
        self.assertFalse(manifest['prerequisite']['ordinary_callee_effects_proved'])
        self.assertFalse(manifest['prerequisite']['memory_safety_claim'])

    def test_binding_roles_cannot_be_omitted_or_extended(self):
        for name in ('calls', 'switches', 'data', 'functions'):
            bindings = copy.deepcopy(self.bindings)
            bindings[name] = [] if bindings[name] else [[0, 'invented']]
            with self.subTest(role=name), self.assertRaisesRegex(ValueError, 'actual original ELF roles'):
                self.verify(bindings=bindings)

    def test_expected_manifest_is_replayed_exactly(self):
        manifest, _ = self.verify()
        manifest['contract'] = 'invented unconditional memory theorem'
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.verify(manifest=manifest)

    def test_linked_bytes_cannot_substitute_for_original_ET_REL(self):
        inputs = list(self.inputs)
        inputs[0] = inputs[1]
        with self.assertRaises(ValueError):
            native.verify_original(*inputs, self.bindings)

    def test_data_only_owner_API_cannot_select_source_admission(self):
        _, _, address, rom, mapping, index = self.inputs
        with self.assertRaisesRegex(ValueError, 'unknown complete-owner selector'):
            owner.verify(bytes(self.fixture[0]), address, rom, mapping, index, b'{}',
                         bindings=self.bindings, selector=native.SELECTOR)

    def test_native_report_selects_original_bound_status_replay(self):
        result = self.result()
        report = owner.render(fixtures.BASE, result)
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), native.SELECTOR)
        self.assertIn(f'* control flow: {native.CONTROL_FLOW}', report)
        evidence = json.loads(next(line for line in report.splitlines()
                              if line.startswith('* owner runtime evidence:')).split('`')[1])
        self.assertEqual(evidence['original_elf_sha256'], hashlib.sha256(self.inputs[0]).hexdigest())
        with patch.object(owner, 'build', return_value=result) as build:
            self.assertTrue(owner.report_matches(report, '.', fixtures.BASE))
            self.assertEqual(build.call_args.kwargs['selector'], native.SELECTOR)
            self.assertEqual(owner.text(build.call_args.kwargs['expected']), owner.text(result[1]))

    def test_status_replay_refusal_and_report_tampering_fail_closed(self):
        report = owner.render(fixtures.BASE, self.result())
        with patch.object(owner, 'build', side_effect=ValueError('changed actual source/object')):
            self.assertFalse(owner.report_matches(report, '.', fixtures.BASE))
        tampered = report.replace('* source plausibility: plausible', '* source plausibility: ignored')
        with patch.object(owner, 'build', return_value=self.result()):
            self.assertFalse(owner.report_matches(tampered, '.', fixtures.BASE))

    def test_fingerprint_requires_and_binds_actual_original_object(self):
        data, manifest, source, mapping, index, objects, rom, _, original = self.result()
        with self.assertRaisesRegex(ValueError, 'original ELF identity'):
            owner.fingerprint(fixtures.BASE, data, manifest, source, mapping, index, objects, rom)
        first = owner.fingerprint(fixtures.BASE, data, manifest, source, mapping, index, objects, rom, original)
        second = owner.fingerprint(fixtures.BASE, data, manifest, source, mapping, index, objects, rom, original+b'x')
        self.assertNotEqual(first, second)

    def test_source_selector_refuses_mixed_runtime_policies_before_compilation(self):
        import match
        options = dict(mode='thumb', control_flow_profile='ordinary', software_double_profile=None,
            software_double_remainder_profile=None, function_address_profile=None, switch_profile=None,
            label=None, wsl='Ubuntu', wsl_path=match.DEFAULT_WSL_PATH, owner_runtime_profile=native.SELECTOR,
            signed_quotient_profile=None, signed_runtime_profile=None, unsigned_runtime_profile=None,
            addressed_signed_runtime_profile=None, switch_data_profile=None)
        for flag in ('signed_quotient_profile', 'signed_runtime_profile', 'unsigned_runtime_profile',
                     'addressed_signed_runtime_profile', 'switch_data_profile'):
            args = argparse.Namespace(**dict(options, **{flag: 'mixed'}))
            with self.subTest(flag=flag), patch.object(owner, 'build') as build:
                with self.assertRaisesRegex(ValueError, 'excludes mixed'):
                    owner.issue('.', fixtures.BASE, args)
                build.assert_not_called()


if __name__ == '__main__':
    unittest.main()
