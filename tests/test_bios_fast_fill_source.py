"""CpuFastSet source-word proof stays separate from CpuSet and old owners."""
import copy
import json
import struct
import unittest

import bios_fast_fill_source_profile as fast
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import test_bios_cpuset_fill_profile as fixtures


class FastFillSourceTests(unittest.TestCase):
    def setUp(self):
        self.base = fixtures.BiosCpuSetFillTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, **changes):
        f = self.base.fixture(**changes)
        data = bytearray(f['data'])
        calls = {}
        for site, address in f['calls'].items():
            self.assertEqual(address, fixtures.bios.ADDRESS)
            data[site-fixtures.A:site-fixtures.A+4] = fixtures.fixtures.fixtures.bl(site, fast.ADDRESS)
            calls[site] = fast.ADDRESS
        rows = json.loads(f['mapping'])
        rows[-1].update(rom=f'0x{fast.ADDRESS:08X}', end=f'0x{fast.ADDRESS+4:08X}')
        mapping, index = fixtures.fixtures.fixtures.indexes(rows)
        rom = bytearray(f['rom'])
        rom[fixtures.A-fixtures.match.ROM_BASE:fixtures.A-fixtures.match.ROM_BASE+len(data)] = data
        rom[fast.ADDRESS-fixtures.match.ROM_BASE:fast.ADDRESS-fixtures.match.ROM_BASE+4] = fast.WRAPPER
        return dict(data=bytes(data), address=fixtures.A, rom=bytes(rom), mapping=mapping,
            index=index, objects=b'{}', selector=buffers.FAST_FILL_SELECTOR,
            bindings=dict(calls=[[site-fixtures.A, f'func_{target:08X}']
                for site, target in sorted(calls.items())], data=[], functions=[], switches=[]))

    def test_word_source_known_and_unknown_count_with_explicit_selector(self):
        for prefix in ((0x2280, 0x0452), (0x2080, 0x0440, 0x4302)):
            with self.subTest(prefix=prefix):
                f = self.fixture(prefix=prefix)
                manifest, _ = owner.verify(**f)
                self.assertEqual(manifest['profile'], buffers.FAST_FILL_SCHEMA)
                fill = manifest['proof']['buffers']['bios_fast_fill']
                self.assertEqual(fill['sites'][0][2], 4)
                self.assertEqual(fill['dependency'][:2], [fast.ADDRESS, 4])
                self.assertIn('conditional returning', fill['contract'])
                self.assertIn('bios_fast_fill_source_profile.py', fill['producer_sha256'])
        self.assertEqual(owner.selector_for_report(f'* verification: `{buffers.FAST_FILL_SCHEMA}`\n'), buffers.FAST_FILL_SELECTOR)

    def test_unproved_mode_source_destination_and_control_flow_fail_closed(self):
        for changes in (dict(prefix=()), dict(prefix=(0x2200,)),
                        dict(prefix=(0x2280, 0x0452, 0x6812)),
                        dict(prefix=(0x2B00, 0xD001, 0x2280, 0x0452)),
                        dict(source=0xA801), dict(source=0x2000),
                        dict(destination=0x4669)):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                owner.verify(**self.fixture(**changes))

    def test_exact_wrapper_both_indexes_and_missing_actual_calls_fail_closed(self):
        f = self.fixture()
        for wrapper in (bytes.fromhex('0bdf7047'), bytes.fromhex('0cdf0047')):
            rom = bytearray(f['rom'])
            offset = fast.ADDRESS-fixtures.match.ROM_BASE
            rom[offset:offset+4] = wrapper
            with self.subTest(wrapper=wrapper.hex()), self.assertRaises(ValueError):
                owner.verify(**dict(f, rom=bytes(rom)))
        for change in ('missing', 'end', 'duplicate', 'text'):
            rows = json.loads(f['mapping'])
            if change == 'missing': rows.pop()
            elif change == 'end': rows[-1]['end'] = f'0x{fast.ADDRESS+2:08X}'
            elif change == 'duplicate': rows.append(dict(rows[-1]))
            mapping, index = fixtures.fixtures.fixtures.indexes(rows)
            if change == 'text': index = index.replace(b'0814186C', b'0814186E')
            with self.subTest(change=change), self.assertRaises(ValueError):
                owner.verify(**dict(f, mapping=mapping, index=index))
        with self.assertRaises(ValueError): owner.verify(**dict(f, bindings=dict(calls=[], data=[], functions=[], switches=[])))

    def test_save_word_pointer_slots_and_stale_manifest_are_rejected(self):
        f = self.fixture()
        manifest, _ = owner.verify(**f)
        changed = copy.deepcopy(manifest)
        changed['proof']['buffers']['bios_fast_fill']['sites'][0][2] = 2
        with self.assertRaises(ValueError): owner.verify(**f, manifest=changed)
        p = fast.FastFillSourceProof(f['rom'], f['mapping'], f['index'], f['objects'])
        site = fixtures.A + f['bindings']['calls'][0][0]
        p.bind_root(f['data'], fixtures.A, {site: fast.ADDRESS})
        with self.assertRaises(ValueError): p.check_call(fast.ADDRESS, {fixtures.match.ARM_REG_R0:-4}, [(False, True, False)], site=site)
        with self.assertRaises(ValueError): p.check_call(fast.ADDRESS, {fixtures.match.ARM_REG_R0:-8}, [(False,False,True),(False,True,False)], slots={-8:-8}, site=site)
        with self.assertRaises(ValueError): p.bind_root(f['data'], fixtures.A, {site: fast.ADDRESS})

    def test_old_selectors_and_cli_remain_explicit(self):
        f = self.fixture()
        for selector in (buffers.BIOS_FILL_SELECTOR, buffers.DATAFREE_SELECTOR, owner.ACYCLIC_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError): owner.verify(**dict(f, selector=selector))
        import match
        import argparse
        from unittest.mock import patch
        captured = {}
        def capture(parser, *args, **kwargs):
            captured['choices'] = next(action.choices for action in parser._actions
                                      if action.dest == 'owner_runtime_profile')
            raise RuntimeError('parser captured')
        with patch.object(argparse.ArgumentParser, 'parse_args', capture):
            with self.assertRaisesRegex(RuntimeError, 'parser captured'):
                match.main()
        self.assertIn(buffers.FAST_FILL_SELECTOR, captured['choices'])



if __name__ == '__main__': unittest.main(verbosity=2)
