"""New coexistence checks for the independently tested query and palette routes."""
from pathlib import Path
import runpy
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import owner_admission_profile as owner
import known_query_native_closure_profile as query
import palette_source_admission_profile as palette
from test_palette_source_admission_profile import PaletteSourceTests, A

class CombinedDispatchTests(unittest.TestCase):
    def setUp(self):
        self.fixture=PaletteSourceTests()
        self.fixture.setUp()

    def test_query_cli_keeps_existing_owner_route(self):
        with self.fixture.project() as root:
            argv=[str(Path(match.__file__)),'--root',str(root),f'{A:08X}',
                  '--owner-runtime-profile',query.SELECTOR,'--no-write']
            with patch.object(sys,'argv',argv),patch.object(owner,'issue',return_value=17)as issue,patch.object(palette,'issue',side_effect=AssertionError('palette route')):
                with self.assertRaises(SystemExit)as result:
                    runpy.run_path(str(Path(match.__file__)),run_name='__main__')
                self.assertEqual(result.exception.code,17)
                self.assertEqual(issue.call_args.args[2].owner_runtime_profile,query.SELECTOR)

    def test_query_cannot_consume_palette_certificate_option(self):
        with self.fixture.project()as root:
            argv=[str(Path(match.__file__)),'--root',str(root),f'{A:08X}',
                  '--owner-runtime-profile',query.SELECTOR,'--palette-closure-bundle','bundle.json']
            with patch.object(sys,'argv',argv),patch.object(owner,'issue',side_effect=AssertionError('unexpected owner dispatch')),patch.object(palette,'issue',side_effect=AssertionError('unexpected palette dispatch')):
                with self.assertRaisesRegex(SystemExit,'requires the isolated'):
                    runpy.run_path(str(Path(match.__file__)),run_name='__main__')

    def test_report_selectors_keep_both_families_distinct(self):
        query_report='* verification: `'+query.SCHEMA+'`\n'
        palette_report='* verification: `'+palette.SCHEMA+'`\n* palette source: `'+palette.SELECTOR+'`\n'
        self.assertEqual(owner.selector_for_report(query_report),query.SELECTOR)
        self.assertIsNone(palette.selector_for_report(query_report))
        self.assertEqual(palette.selector_for_report(palette_report),palette.SELECTOR)
        self.assertFalse(owner.selected(palette_report))

if __name__=='__main__':unittest.main()
