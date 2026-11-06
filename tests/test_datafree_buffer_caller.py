"""Data-free callers use ordinary buffer effects without broadening named callers."""
import argparse
import copy
import unittest
from unittest.mock import patch

import test_buffer_discarded_return_scratch as fixtures

buffers, owner = fixtures.buffers, fixtures.owner


class DatafreeBufferCallerTests(unittest.TestCase):
    setUp = fixtures.DiscardedReturnScratchTests.setUp
    fixture = fixtures.DiscardedReturnScratchTests.fixture

    def plain(self, **changes):
        changes.setdefault('callee', 'strh r0, [r3]\nmovs r3, #0\nbx lr')
        return dict(self.fixture(**changes), selector=buffers.DATAFREE_SELECTOR)

    def test_complete_datafree_caller_and_fresh_manifest(self):
        f = self.plain()
        manifest, _ = owner.verify(**f)
        self.assertEqual(manifest['profile'], buffers.DATAFREE_SCHEMA)
        self.assertEqual(manifest['proof']['schema'], buffers.DATAFREE_SCHEMA)
        self.assertTrue(manifest['proof']['buffers']['dependencies'])
        self.assertNotIn('normal_return_scratch', manifest['proof']['buffers'])
        self.assertEqual(owner.verify(**f, manifest=manifest)[0], manifest)

    def test_named_profile_retains_its_required_data_relocation(self):
        f = self.plain()
        with self.assertRaisesRegex(ValueError, 'require actual named object'):
            owner.verify(**dict(f, selector=buffers.SELECTOR))

    def test_data_function_and_switch_bindings_are_excluded(self):
        f = self.plain()
        for field, value in (('data', [[0, 'invented', 0]]),
                             ('functions', [[0, 'func_08010100']]),
                             ('switches', [[0, 4]])):
            bindings = copy.deepcopy(f['bindings'])
            bindings[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'data-free caller'):
                owner.verify(**dict(f, bindings=bindings))

    def test_bounds_escape_and_observed_return_alias_remain_checked(self):
        for changes in (dict(callee='ldr r0, [r3, #8]\nmovs r3, #0\nbx lr'),
                        dict(callee='str r3, [r1]\nmovs r3, #0\nbx lr'),
                        dict(callee='strh r0, [r3]\nbx lr', after='str r3, [r1]'),
                        dict(release='add sp, #4')):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                owner.verify(**self.plain(**changes))

    def test_manifest_and_original_elf_identity_are_required(self):
        f = self.plain()
        manifest, _ = owner.verify(**f)
        altered = copy.deepcopy(manifest)
        altered['proof']['buffers']['dependencies'][0]['body_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**f, manifest=altered)
        with self.assertRaisesRegex(ValueError, 'original ELF identity'):
            owner.fingerprint(f['address'], f['data'], manifest, 'source', f['mapping'],
                              f['index'], f['objects'], f['rom'])

    def test_selector_report_rejects_mixed_markers(self):
        marker = f'* verification: `{buffers.DATAFREE_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker), buffers.DATAFREE_SELECTOR)
        for report in (marker * 2, marker + f'* verification: `{buffers.SCHEMA}`\n',
                       marker + '* buffer calls: legacy\n'):
            with self.subTest(report=report), self.assertRaises(ValueError):
                owner.selected(report)

    def test_render_preserves_selected_policy_and_original_identity(self):
        f = self.plain()
        manifest, instructions = owner.verify(**f)
        report = owner.render(f['address'], (f['data'], manifest, 'source', f['mapping'],
            f['index'], f['objects'], f['rom'], len(instructions), b'original ELF identity'))
        self.assertIn(f'* owner runtime: {buffers.DATAFREE_SELECTOR}', report)
        self.assertIn(f'* control flow: {buffers.DATAFREE_CONTROL_FLOW}', report)
        self.assertEqual(owner.selector_for_report(report), buffers.DATAFREE_SELECTOR)
        self.assertIn('original_elf_sha256', report)

    def test_cli_selects_profile_before_any_execution(self):
        parse = argparse.ArgumentParser.parse_args
        class Parsed(Exception):
            pass
        def capture(parser, *args, **kwargs):
            parsed = parse(parser, ['0x08010000', '--owner-runtime-profile',
                                    buffers.DATAFREE_SELECTOR])
            self.assertEqual(parsed.owner_runtime_profile, buffers.DATAFREE_SELECTOR)
            raise Parsed
        with patch.object(argparse.ArgumentParser, 'parse_args', capture), self.assertRaises(Parsed):
            buffers.match.main()
