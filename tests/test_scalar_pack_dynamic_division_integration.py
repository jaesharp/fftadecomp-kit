"""CLI routing after combining independent scalar and output-buffer policies."""
import sys
import unittest
from unittest.mock import patch

import dynamic_division_buffer_profile as dynamic
import match
import owner_admission_profile as owner
import private_float_pack_admission_profile as private
import three_halfword_output_buffer_profile as three


class CombinedPolicyRoutingTests(unittest.TestCase):
    def test_combined_explicit_policies_keep_their_distinct_dispatch(self):
        for selector, endpoint in (
            (private.DOUBLE_SCALAR_PACK_SELECTOR, private),
            (three.SELECTOR, owner),
            (dynamic.SELECTOR, owner),
        ):
            with self.subTest(selector=selector), \
                    patch.object(private, 'issue', return_value=301) as scalar, \
                    patch.object(owner, 'issue', return_value=302) as buffer, \
                    patch.object(sys, 'argv', ['match.py', '08000100',
                        '--owner-runtime-profile', selector]):
                self.assertEqual(match.main(), 301 if endpoint is private else 302)
                selected = scalar if endpoint is private else buffer
                other = buffer if endpoint is private else scalar
                self.assertEqual(selected.call_args.args[2].owner_runtime_profile, selector)
                selected.assert_called_once()
                other.assert_not_called()


if __name__ == '__main__':
    unittest.main(verbosity=2)
