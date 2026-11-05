"""Compose independently checked scalar control and typed function literals."""
from contextlib import redirect_stdout
import io
import sys
import unittest
from unittest.mock import patch

import test_bios_function_literals as functions

profile, match, A = functions.profile, functions.match, functions.A


class BiosScalarFunctionLiteralTests(unittest.TestCase):
    setUp = functions.BiosFunctionLiteralTests.setUp

    def fixture(self, control=0x05000010):
        original = self.base.fixture
        with patch.object(self.base,'fixture',side_effect=lambda **kw: original(**kw,control=control)):
            f = functions.BiosFunctionLiteralTests.fixture(self)
        f['selector'] = profile.BIOS_SCALAR_FUNCTION_DATA_SELECTOR
        return f

    def test_actual_scalar_and_function_roles_are_distinct_and_authenticated(self):
        f = self.fixture()
        manifest,_ = profile.verify(**f)
        controls = manifest['bios_scalar_control']['words']
        self.assertEqual(len(controls),1)
        self.assertEqual(controls[0][1],0x05000010)
        self.assertNotIn(controls[0][0],{row[0] for row in manifest['data_bindings']})
        self.assertEqual(manifest['function_literal_bindings'],[f['data_bindings'][-1][:2]])
        self.assertEqual(manifest['native_buffers']['bios_fill']['sites'][0][2],4)
        self.assertEqual(manifest['runtime_numeric_return_facts'],[])
        self.assertFalse(manifest['original_formal_type_certainty'])

    def test_dual_control_identity_missing_boundary_and_old_selectors_stay_refused(self):
        f = self.fixture()
        manifest,_ = profile.verify(**f)
        offset = manifest['bios_scalar_control']['words'][0][0]
        with self.assertRaises(ValueError):
            profile.verify(**dict(f,data_bindings=sorted(f['data_bindings']+[[offset,'destination',0]])))
        for selector in (profile.BIOS_SCALAR_DATA_SELECTOR,profile.BIOS_FUNCTION_DATA_SELECTOR):
            with self.subTest(selector=selector),self.assertRaises(ValueError):
                profile.verify(**dict(f,selector=selector))
        for control in (None,0x04000010):
            with self.subTest(control=control),self.assertRaises(ValueError):
                profile.verify(**self.fixture(control))
        with self.assertRaises(ValueError):
            profile.verify(**f,manifest=dict(manifest,bios_scalar_control={}))

    def test_cli_report_replay_preserves_both_roles_and_source_runtime_guards(self):
        f = self.fixture()
        with self.base.base.build_boundary(f) as (root,_,_),patch.object(
                profile,'toolchain_fingerprint',return_value=[['synthetic','1'*64]]):
            with patch.object(sys,'argv',['match.py','--root',str(root),
                    '--addressed-runtime-profile',f['selector'],f'{A:08X}']),redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(),0)
            report = (root/'docs/match/08010000.md').read_text()
            evidence = functions.fill.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report,root,A))
            with patch.object(profile,'runtime_fingerprint',return_value={'changed':True}):
                self.assertFalse(evidence.report_matches(report,root,A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report,root,A))


if __name__ == '__main__':
    unittest.main()
