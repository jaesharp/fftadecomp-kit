"""Fresh-interpreter regression for owner policy dependency initialization."""
import os
from pathlib import Path
import subprocess
import sys
import unittest


class ImportOrderTests(unittest.TestCase):
    def test_callback_dependency_before_owner_dispatch(self):
        tools = str(Path(__file__).resolve().parents[1] / 'tools')
        code = "import sys; sys.path.insert(0, sys.argv[1]); import two_word_callback_closure_profile; import owner_admission_profile; import tree_two_word_callback_closure_profile; assert callable(tree_two_word_callback_closure_profile.prove)"
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
        result = subprocess.run([sys.executable, '-B', '-c', code, tools],
                                capture_output=True, text=True, env=env)
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == '__main__':
    unittest.main()
