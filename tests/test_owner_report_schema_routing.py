"""Nested proof schemas do not select the enclosing report's native profile."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import owner_admission_profile as owner
import private_float_pack_admission_profile as private


class OwnerReportSchemaRoutingTests(unittest.TestCase):
    def test_private_scalar_report_with_nested_owner_proof_stays_private(self):
        report = (f'* verification: `{private.SCALAR_DIVISION_LOCALS_SCHEMA}`\n'
                  f'* private float pack: `{private.SCALAR_DIVISION_LOCALS_SELECTOR}`\n'
                  f'* private float pack evidence: `{{"native_closure":{{"schema":"{owner.dynamic_div.SCHEMA}"}}}}`\n')
        self.assertEqual(private.selector_for_report(report), private.SCALAR_DIVISION_LOCALS_SELECTOR)
        self.assertFalse(owner.selected(report))
        with self.assertRaises(ValueError):
            owner.selector_for_report(report)

    def test_top_level_owner_schema_and_malformed_owner_markers_remain_strict(self):
        valid = f'* verification: `{owner.SCHEMA}`\n'
        self.assertTrue(owner.selected(valid))
        self.assertEqual(owner.selector_for_report(valid), owner.SELECTOR)
        for report in (valid+valid,
                       valid+f'* verification: `{private.SCALAR_DIVISION_LOCALS_SCHEMA}`\n',
                       '* verification: `unknown`\n* owner runtime: `unknown`\n',
                       f'* verification: `{private.SCALAR_DIVISION_LOCALS_SCHEMA}`\n* owner runtime: `unknown`\n'):
            with self.subTest(report=report), self.assertRaises(ValueError):
                owner.selected(report)


if __name__ == '__main__':
    unittest.main(verbosity=2)
