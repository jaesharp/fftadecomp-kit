"""Named-data owners compose only exact BIOS fill source accesses."""
import copy
import json
import unittest
import test_bios_cpuset_fill_profile as fixtures
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
match,bios,A=fixtures.match,fixtures.bios,fixtures.A

class NamedBiosFillTests(unittest.TestCase):
    def setUp(self):
        self.base=fixtures.BiosCpuSetFillTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self,control=0x01000010,**changes):
        f=self.base.fixture(data=True,control=control,**changes)
        return dict(data=f['data'],address=A,rom=f['rom'],mapping=f['mapping'],index=f['index'],
            objects=f['data_mapping'],selector=buffers.BIOS_FILL_SELECTOR,
            bindings=dict(calls=[[site-A,f'func_{target:08X}']for site,target in sorted(f['calls'].items())],
                data=f['data_bindings'],functions=[],switches=[]))

    def test_source_width_modes_and_explicit_report_selector(self):
        for control,width in [(0x01000010,2),(0x05000010,4)]:
            with self.subTest(width=width):
                f=self.fixture(control);manifest,_=owner.verify(**f)
                self.assertEqual(manifest['profile'],buffers.BIOS_FILL_SCHEMA)
                fill=manifest['proof']['buffers']['bios_fill']
                self.assertEqual(fill['sites'][0][2],width)
                self.assertEqual(fill['dependency'][0],bios.ADDRESS)
                self.assertIn('source span',fill['contract'])
                self.assertIn('bios_cpuset_fill_profile.py',fill['producer_sha256'])
                self.assertEqual(owner.selector_for_report(f'* verification: `{buffers.BIOS_FILL_SCHEMA}`\n'),buffers.BIOS_FILL_SELECTOR)

    def test_mode_source_destination_and_wrapper_fail_closed(self):
        for changes in [dict(control=0),dict(control=0x04000010),dict(source=0xA801),
                        dict(source=0x2000),dict(destination=0x4669)]:
            with self.subTest(changes=changes),self.assertRaises(ValueError):owner.verify(**self.fixture(**changes))
        for body in [b'\x0c\xdf\x70\x47',b'\x0b\xdf\x00\x47']:
            f=self.fixture();rom=bytearray(f['rom']);off=bios.ADDRESS-match.ROM_BASE;rom[off:off+4]=body
            with self.subTest(wrapper=body.hex()),self.assertRaises(ValueError):owner.verify(**dict(f,rom=bytes(rom)))

    def test_typed_objects_indexes_manifest_and_old_policy_remain_strict(self):
        f=self.fixture();manifest,_=owner.verify(**f)
        changed=copy.deepcopy(manifest);changed['proof']['buffers']['bios_fill']['sites'][0][2]=1
        with self.assertRaises(ValueError):owner.verify(**f,manifest=changed)
        for kind in ['missing-data','missing-wrapper','bad-index','old-selector']:
            altered=copy.deepcopy(f)
            if kind=='missing-data':altered['bindings']['data']=[]
            elif kind=='missing-wrapper':altered['mapping']=json.dumps([r for r in json.loads(f['mapping'])if int(r['rom'],16)!=bios.ADDRESS]).encode()
            elif kind=='bad-index':altered['index']=f['index'].replace(b'08141870',b'08141872')
            else:altered['selector']=buffers.SELECTOR
            with self.subTest(kind=kind),self.assertRaises(ValueError):owner.verify(**altered)

if __name__=='__main__':unittest.main(verbosity=2)
