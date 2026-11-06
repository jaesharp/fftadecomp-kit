"""Guarded inventory must preserve live native return aliases and all bounds."""
import argparse
import copy
import unittest
from unittest.mock import patch

from test_buffer_discarded_return_scratch import DiscardedReturnScratchTests, buffers, owner

match = buffers.match


class GuardedCalleeReturnAliasTests(unittest.TestCase):
    setUp = DiscardedReturnScratchTests.setUp
    fixture = DiscardedReturnScratchTests.fixture

    def live_fixture(self, *, store='str r0, [r4, #4]', guard='bhi default',
                     after='movs r0, #9\nstr r0, [r3]\nmovs r3, #0'):
        callee = ('push {r4, lr}\nadds r4, r3, #0\nmovs r3, #0\nbl child\n'
            'cmp r0, #1\n' + guard + '\nlsls r0, r0, #2\nldr r1, pointer\n'
            'adds r0, r0, r1\nldr r0, [r0]\nmov pc, r0\n.balign 4, 0\n'
            'pointer: .word table\ntable: .word case0, case1\n'
            'case0: movs r0, #7\nstr r0, [r4]\nb done\n'
            'case1: movs r0, #8\n' + store + '\nb done\n'
            'default: movs r0, #0\ndone: adds r3, r4, #0\n'
            'pop {r4}\npop {r1}\nbx r1')
        return dict(self.fixture(callee=callee, after=after),
                    selector=buffers.GUARDED_ALIAS_SELECTOR)

    def test_live_return_alias_is_consumed_with_ordinary_bounds(self):
        f = self.live_fixture()
        manifest, _ = owner.verify(**f)
        self.assertEqual(manifest['profile'], buffers.GUARDED_ALIAS_SCHEMA)
        self.assertTrue(manifest['proof']['buffers']['guarded_switches']['observations'])
        self.assertNotIn('normal_return_scratch', manifest['proof']['buffers'])
        replay, _ = owner.verify(**f, manifest=manifest)
        self.assertEqual(replay, manifest)

    def test_old_discarded_scratch_selector_still_rejects_actual_observation(self):
        with self.assertRaisesRegex(ValueError, 'observes discarded return scratch'):
            owner.verify(**dict(self.live_fixture(), selector=buffers.GUARDED_SWITCH_SELECTOR))

    def test_every_switch_case_and_returned_alias_keep_bounds_and_nonescape(self):
        for change in (dict(store='str r0, [r4, #8]'),
                       dict(after='str r0, [r3, #8]\nmovs r3, #0'),
                       dict(after='ldr r0, [r3, #8]\nmovs r3, #0'),
                       dict(after='str r3, [r1]\nmovs r3, #0'),
                       dict(guard='bhs default')):
            with self.subTest(change=change), self.assertRaises(ValueError):
                owner.verify(**self.live_fixture(**change))

    def test_no_projection_and_no_uninspected_switch_admission(self):
        f = self.live_fixture()
        proof = buffers.GuardedAliasBufferProof(f['rom'], f['mapping'], f['index'], f['objects'])
        aliases = {match.ARM_REG_R0+2:-8, match.ARM_REG_R0+3:-4}
        self.assertEqual(proof.normal_return_aliases(0, 0, aliases), aliases)
        with self.assertRaisesRegex(ValueError, 'actual inspected switch'):
            owner.verify(**dict(self.fixture(callee='str r0, [r3]\nmovs r3, #0\nbx lr'),
                                selector=buffers.GUARDED_ALIAS_SELECTOR))

    def test_returned_alias_multiaccess_excludes_saved_words(self):
        for access in ('stm r3!, {r0}', 'ldm r3!, {r0}'):
            with self.subTest(access=access):
                owner.verify(**self.live_fixture(after='adds r3, #4\n'+access+'\nmovs r3, #0'))
                with self.assertRaises(ValueError):
                    owner.verify(**self.live_fixture(after='adds r3, #8\n'+access+'\nmovs r3, #0'))

    def test_explicit_finite_dependency_budget_is_enforced(self):
        self.assertEqual(buffers.NamedDataBufferProof.dependency_budget, 8)
        self.assertEqual(buffers.GuardedAliasBufferProof.dependency_budget, 32)
        manifest, _ = owner.verify(**self.live_fixture())
        self.assertEqual(manifest['proof']['buffers']['dependency_budget'], 32)
        with patch.object(buffers.GuardedAliasBufferProof, 'dependency_budget', 0):
            with self.assertRaisesRegex(ValueError, 'dependency budget exceeded'):
                owner.verify(**self.live_fixture())

    def prefix_fixture(self, body):
        f = self.fixture(callee=body)
        return buffers.GuardedAliasBufferProof(f['rom'], f['mapping'], f['index'], f['objects'])

    def test_entry_scratch_kill_requires_actual_writes_before_every_read_and_call(self):
        r3 = match.ARM_REG_R0 + 3
        for body in ('movs r3, #0\nbx lr',
                     'push {lr}\nsub sp, #8\nadds r3, r1, #0\nmov r1, sp\nbl child\nadd sp, #8\npop {r0}\nbx r0',
                     'cmp r0, #0\nbeq kill\nmovs r3, #0\nb done\nkill: movs r3, #1\ndone: bx lr'):
            with self.subTest(body=body):
                proof = self.prefix_fixture(body)
                result = proof.check_arguments(0x08010100, {r3:-4}, [(False,False,True)], {}, frozenset())
                self.assertEqual(result, {})
                self.assertTrue(proof.entry_kill_manifest()['observations'])
        for body in ('cmp r3, #0\nmovs r3, #0\nbx lr',
                     'str r3, [r1]\nmovs r3, #0\nbx lr',
                     'bl child\nmovs r3, #0\nbx lr', 'bx lr',
                     'cmp r0, #0\nbeq done\nmovs r3, #0\ndone: bx lr',
                     'loop: b loop'):
            with self.subTest(body=body):
                self.assertIsNone(self.prefix_fixture(body).prefix_kills(0x08010100, {r3}))

    def test_entry_kill_never_discards_unwritten_aliases_or_nonlocal_inputs(self):
        r2, r3 = match.ARM_REG_R0+2, match.ARM_REG_R0+3
        proof = self.prefix_fixture('movs r3, #0\nbx lr')
        self.assertIsNone(proof.prefix_kills(0x08010100, {r2,r3}))
        self.assertIsNone(proof.prefix_kills(0x08010100, {match.ARM_REG_R0}))
        with self.assertRaisesRegex(ValueError, 'outside allocated'):
            proof.check_arguments(0x08010100, {r3:0}, [(False,False,True)], {}, frozenset())

    def test_exact_manifest_and_report_selection_remain_required(self):
        f = self.live_fixture()
        manifest, _ = owner.verify(**f)
        forged = copy.deepcopy(manifest)
        forged['proof']['buffers']['guarded_switches']['observations'] = []
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**f, manifest=forged)
        marker = f'* verification: `{buffers.GUARDED_ALIAS_SCHEMA}`\n'
        self.assertTrue(owner.selected(marker))
        self.assertEqual(owner.selector_for_report(marker), buffers.GUARDED_ALIAS_SELECTOR)
        with self.assertRaises(ValueError):
            owner.selected(marker*2)

    def test_cli_accepts_selector_before_any_execution(self):
        original = argparse.ArgumentParser.parse_args
        class Parsed(Exception):
            pass
        def capture(parser, *args, **kwargs):
            parsed = original(parser, ['0x08010000', '--owner-runtime-profile', buffers.GUARDED_ALIAS_SELECTOR])
            self.assertEqual(parsed.owner_runtime_profile, buffers.GUARDED_ALIAS_SELECTOR)
            raise Parsed
        with patch.object(argparse.ArgumentParser, 'parse_args', capture), self.assertRaises(Parsed):
            match.main()


if __name__ == '__main__':
    unittest.main(verbosity=2)
