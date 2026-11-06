"""Every explicit R6 owner policy reaches the native CLI dispatcher."""
import contextlib
import io
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))

import match
import owner_admission_profile as owner
import static_callback_r6_frame_profile as policy


class CliPolicyTests(unittest.TestCase):
    def test_all_declared_r6_policies_dispatch_without_compiling(self):
        root = Path.cwd()
        for selector in policy.PROFILES:
            with self.subTest(selector=selector), \
                    patch.object(sys, 'argv', ['match.py', '0x08008000',
                        '--root', str(root), '--owner-runtime-profile', selector]), \
                    patch.object(match, 'repo_root', return_value=str(root)), \
                    patch.object(owner, 'issue', return_value=17) as issue:
                self.assertEqual(match.main(), 17)
                self.assertEqual(issue.call_args.args[2].owner_runtime_profile, selector)

    def test_undeclared_policy_stays_refused_before_dispatch(self):
        with patch.object(sys, 'argv', ['match.py', '0x08008000',
                '--owner-runtime-profile', 'static-callback-restoring-r6-unknown-v1']), \
                patch.object(owner, 'issue') as issue, \
                contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as stopped:
            match.main()
        self.assertEqual(stopped.exception.code, 2)
        issue.assert_not_called()


if __name__ == '__main__':
    unittest.main(verbosity=2)
