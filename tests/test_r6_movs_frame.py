"""Native R6 frame address formation uses only existing reaching MOVS facts."""
import copy
import unittest

from test_r6_local_return_scratch import fixture as local_fixture
import static_callback_r6_frame_profile as policy
import owner_admission_profile as owner


def fixture(body='00b581b001206844021c002001b002bc0847'):
    values = local_fixture(bytes.fromhex(body))
    values['selector'] = policy.MOVS_FRAME_SELECTOR
    return values


class MovsFrameTests(unittest.TestCase):
    def test_native_sp_add_uses_exact_reaching_movs_and_binds_its_producer(self):
        values = fixture()
        manifest, _ = owner.verify(**values)
        evidence = manifest['proof']['buffers']['r6_restoration']
        self.assertEqual(evidence['policy']['frame_small_constants']['values'], [1, 2, 3])
        self.assertTrue(evidence['policy']['frame_small_constants']['producer_sha256'])
        self.assertTrue(any(row['frame']['local_aliases']['assignments'] for row in evidence['observations']))
        with self.assertRaisesRegex(ValueError, 'stack-address materialization'):
            owner.verify(**dict(values, selector=policy.QUARANTINE_SELECTOR))

    def test_unknown_or_outside_domain_offsets_do_not_gain_provenance(self):
        for body in ('00b581b0181c6844021c002001b002bc0847',
                     '00b581b007206844021c002001b002bc0847'):
            with self.subTest(body=body), self.assertRaises(ValueError):
                owner.verify(**fixture(body))

    def test_proved_constant_does_not_permit_an_unaligned_or_saved_word_store(self):
        for body in ('00b581b00120684401210160002001b002bc0847',
                     '00b581b00320684401214160002001b002bc0847'):
            with self.subTest(body=body), self.assertRaises(ValueError):
                owner.verify(**fixture(body))

    def test_changed_constant_policy_manifest_is_refused(self):
        values = fixture()
        manifest, _ = owner.verify(**values)
        changed = copy.deepcopy(manifest)
        changed['proof']['buffers']['r6_restoration']['policy']['frame_small_constants']['values'].append(7)
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**values, manifest=changed)


if __name__ == '__main__':
    unittest.main(verbosity=2)
