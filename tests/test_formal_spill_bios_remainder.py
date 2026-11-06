"""The scalar exception boundary preserves existing formal-output obligations."""
import unittest
from unittest.mock import patch

import test_ordinary_formal_output_spill as fixtures

profile, match = fixtures.profile, fixtures.match


class BiosRemainderTests(unittest.TestCase):
    def direct(self, wrapper=None, helper=None):
        helper = helper or fixtures.PREFIX + bytes.fromhex('0021') + fixtures.bl(fixtures.H+14, fixtures.N) + fixtures.SUFFIX
        wrapper = profile.BiosRemainderSpillProof.wrapper_bytes if wrapper is None else wrapper
        data, rom, mapping, index = fixtures.fixture(helper, wrapper)
        with patch.object(profile.BiosRemainderSpillProof, 'wrapper_address', fixtures.N):
            proof = profile.BiosRemainderSpillProof(rom,mapping,index,b'{}')
            match.verify_leaf_instructions(data,fixtures.A,True,{fixtures.A+10:fixtures.H},buffer_proof=proof)
            return proof

    def test_actual_nested_scalar_wrapper_retains_formal_spill_and_output(self):
        proof = self.direct()
        self.assertTrue(proof.spill_manifest()['writes'])
        self.assertEqual(proof.bios_manifest()['observations'][0]['unknown_results'],[0,1,2,3,12])
        self.assertEqual(set(proof.dependencies),{fixtures.H,fixtures.N})

    def test_changed_service_transport_and_extent_remain_rejected(self):
        expected = profile.BiosRemainderSpillProof.wrapper_bytes
        for wrapper in (b'\x07\xdf'+expected[2:], expected[:2]+b'\x00\x1c'+expected[4:],
                        expected+b'\xc0\x46'):
            with self.subTest(wrapper=wrapper.hex()), self.assertRaises(ValueError):
                self.direct(wrapper=wrapper)

    def test_live_pointer_argument_cannot_become_scalar(self):
        helper = fixtures.PREFIX + fixtures.bl(fixtures.H+12,fixtures.N) + fixtures.SUFFIX
        with self.assertRaises(ValueError):
            self.direct(helper=helper)

    def test_missing_output_store_is_not_discharged_by_bios(self):
        helper = fixtures.PREFIX[:10]+b'\xc0\x46'+bytes.fromhex('0021')+fixtures.bl(fixtures.H+14,fixtures.N)+fixtures.SUFFIX
        with self.assertRaises(ValueError):
            self.direct(helper=helper)

    def test_complete_owner_requires_explicit_selector_and_authentic_manifest(self):
        helper = fixtures.PREFIX + bytes.fromhex('0021') + fixtures.bl(fixtures.H+14,fixtures.N) + fixtures.SUFFIX
        data,rom,mapping,index = fixtures.fixture(helper,profile.BiosRemainderSpillProof.wrapper_bytes)
        bindings = dict(calls=[[10,f'func_{fixtures.H:08X}']],data=[],functions=[],switches=[])
        with patch.object(profile.BiosRemainderSpillProof,'wrapper_address',fixtures.N):
            manifest,_ = fixtures.owner.verify(data,fixtures.A,rom,mapping,index,b'{}',
                bindings=bindings,selector=profile.BIOS_SELECTOR)
            self.assertEqual(manifest['profile'],profile.BIOS_SCHEMA)
            self.assertTrue(manifest['proof']['buffers']['bios_remainder']['observations'])
            forged = fixtures.copy.deepcopy(manifest)
            forged['proof']['buffers']['bios_remainder']['observations']=[]
            with self.assertRaisesRegex(ValueError,'manifest differs'):
                fixtures.owner.verify(data,fixtures.A,rom,mapping,index,b'{}',forged,
                    bindings=bindings,selector=profile.BIOS_SELECTOR)
            with self.assertRaises(ValueError):
                fixtures.owner.verify(data,fixtures.A,rom,mapping,index,b'{}',
                    bindings=bindings,selector=profile.SELECTOR)
        report = f'* verification: `{profile.BIOS_SCHEMA}`\n* owner runtime: {profile.BIOS_SELECTOR}\n'
        self.assertTrue(fixtures.owner.selected(report))
        self.assertEqual(fixtures.owner.selector_for_report(report),profile.BIOS_SELECTOR)


if __name__ == '__main__':
    unittest.main(verbosity=2)
