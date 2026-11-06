"""An optional local return alias needs its explicit unobserving exit policy."""
import copy
import unittest

from test_r6_local_return_scratch import fixture as local_fixture
import static_callback_r6_frame_profile as policy
import owner_admission_profile as owner


OPTIONAL = '00b581b0002801d06a4600e00022002001b002bc0847'


def fixture(body=OPTIONAL, continuation='0022'):
    values = local_fixture(bytes.fromhex(body), continuation)
    values['selector'] = policy.OPTIONAL_LOCAL_FRAME_SELECTOR
    return values


class OptionalLocalFrameTests(unittest.TestCase):
    def test_optional_exact_local_alias_is_bound_and_old_policy_stays_closed(self):
        values = fixture()
        manifest, _ = owner.verify(**values)
        evidence = manifest['proof']['buffers']['r6_restoration']
        self.assertEqual(evidence['policy']['optional_local_exit_scratch']['exact_local_offsets'], 1)
        residuals = [item for row in evidence['observations']
                     for item in row['frame'].get('discarded_exit_scratch', {}).get('residual_aliases', [])]
        self.assertTrue(any(item[2:] == [0, False] for item in residuals))
        self.assertTrue(any(item[2] < 0 for item in residuals))
        with self.assertRaisesRegex(ValueError, 'exact local-offset provenance'):
            owner.verify(**dict(values, selector=policy.MOVS_FRAME_SELECTOR))

    def test_two_distinct_local_offsets_are_not_an_optional_single_offset(self):
        body = '00b581b0002802d06a46013200e06a46002001b002bc0847'
        with self.assertRaises(ValueError):
            owner.verify(**fixture(body))

    def test_consumer_must_still_kill_every_return_alias_before_read(self):
        with self.assertRaisesRegex(ValueError, 'consumer observes'):
            owner.verify(**fixture(continuation='111c'))

    def test_optional_join_does_not_authorize_an_ambiguous_memory_read(self):
        body = '00b581b0002801d06a4600e000221178002001b002bc0847'
        with self.assertRaises(ValueError):
            owner.verify(**fixture(body))

    def test_unallocated_pointer_and_result_alias_escape_remain_refused(self):
        for body in ('00b581b06a46083201b002bc0847',
                     '00b581b0684601b002bc0847'):
            with self.subTest(body=body), self.assertRaises(ValueError):
                owner.verify(**fixture(body))

    def test_manifest_cannot_enlarge_the_offset_or_register_policy(self):
        values = fixture()
        manifest, _ = owner.verify(**values)
        changed = copy.deepcopy(manifest)
        changed['proof']['buffers']['r6_restoration']['policy']['optional_local_exit_scratch']['exact_local_offsets'] = 2
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**values, manifest=changed)


if __name__ == '__main__':
    unittest.main(verbosity=2)
