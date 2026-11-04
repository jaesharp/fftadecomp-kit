"""Real literal-policy regression; no original ROM or compiler is used."""
import hashlib
import os
from pathlib import Path
import sys
import unittest

OVERLAY = Path(__file__).resolve().parents[1]
PRODUCTION = Path(os.environ.get('FFTA_TEST_PRODUCTION_KIT', OVERLAY))
sys.path[:0] = [str(OVERLAY / 'tools'), str(PRODUCTION / 'tools'),
               str(PRODUCTION / 'tests')]

import unsigned_divmod_profile as profile
import modsi3_profile as classifier
import test_unsigned_divmod_profile as fixtures


class UnsignedDivmodLiteralTests(unittest.TestCase):
    # Reuse only existing synthetic fixture helpers, never their test methods.
    setUp = fixtures.UnsignedDivmodCompositionTests.setUp
    runtime_closure = fixtures.UnsignedDivmodCompositionTests.runtime_closure
    fixture = fixtures.UnsignedDivmodCompositionTests.fixture

    def literal_fixture(self, value):
        # The reached LDR at +26 references the aligned numeric pool at +36.
        tokens = (fixtures.DEFAULT[:-3] + (0x4A02,) + fixtures.DEFAULT[-3:] +
                  (0x0000, value & 0xFFFF, value >> 16))
        return self.fixture(tokens)

    def test_scalar_pool_executes_real_classifier_and_binds_its_source(self):
        self.assertIs(profile.address_literal, classifier.address_literal)
        value = 0xFFFFD01E
        manifest, instructions = profile.verify(**self.literal_fixture(value))
        self.assertEqual([row['value'] for row in
                          manifest['unsigned_runtime_inventory']['partition']['words']],
                         [value])
        self.assertEqual(len(manifest['divisors']), 2)
        self.assertTrue(all(divisor == 10 for _, divisor in manifest['divisors']))
        self.assertIn('ldr', [instruction.mnemonic for instruction in instructions])
        self.assertEqual(manifest['producer_source_sha256']['modsi3_profile.py'],
                         hashlib.sha256(Path(classifier.__file__).read_bytes()).hexdigest())

    def test_untyped_address_like_pool_words_fail_at_real_literal_guard(self):
        self.assertIs(profile.address_literal, classifier.address_literal)
        for value in (0x02000000, 0x06000020, 0x0839144E, 0x0FFFFFFF):
            with self.subTest(value=hex(value)):
                with self.assertRaisesRegex(
                        ValueError, 'unsigned divmod excludes unbound address literals'):
                    profile.verify(**self.literal_fixture(value))


if __name__ == '__main__':
    unittest.main()
