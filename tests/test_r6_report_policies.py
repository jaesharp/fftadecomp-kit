"""Published R6 policy reports retain strict, complete dispatch selection."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))

import owner_admission_profile as owner
import static_callback_r6_frame_profile as policy


class ReportPolicyTests(unittest.TestCase):
    def test_every_declared_schema_selects_its_exact_policy(self):
        for selector, (schema, _) in policy.PROFILES.items():
            with self.subTest(selector=selector):
                report = f'* verification: `{schema}`\n'
                self.assertTrue(owner.selected(report))
                self.assertEqual(owner.selector_for_report(report), selector)

    def test_duplicate_and_mixed_schemas_stay_refused(self):
        for schema in policy.SCHEMAS:
            report = f'* verification: `{schema}`\n'
            for extra in (report, f'* verification: `{owner.SCHEMA}`\n',
                          '* buffer calls: `unsupported`\n'):
                with self.subTest(schema=schema, extra=extra), \
                        self.assertRaisesRegex(ValueError, 'mixed or malformed'):
                    owner.selected(report + extra)

    def test_unknown_and_noncanonical_owner_reports_stay_refused(self):
        for line in ('* verification: `unknown-r6-policy`',
                     f'* verification: `{policy.COMPACT_CLOSURE_SCHEMA}` extra'):
            with self.subTest(line=line), \
                    self.assertRaisesRegex(ValueError, 'mixed or malformed'):
                owner.selected(line + '\n* owner runtime: `claimed`\n')


if __name__ == '__main__':
    unittest.main(verbosity=2)
