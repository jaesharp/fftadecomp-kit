"""Original cyclic switch owners keep typed words and exact frame restoration."""
import copy
import json
import unittest
from pathlib import Path
import test_restoring_original_alignment as aligned
from test_switch_constants import assemble,fixture_assembly,ordinary_link,fixed_args
match,owner,A=aligned.match,aligned.owner,aligned.A

class CyclicSwitchWordTests(unittest.TestCase):
    def setUp(self):
        aligned.RestoringAlignmentTests.setUp(self)

    def fixture(self, broken=None):
        assembly=fixture_assembly(call=True,prefix='sub sp,#8',first='',second='')
        assembly=assembly.replace('.Lconstant0:\n.word 0xFF00FF00\n.Lconstant1:\n.word 0x0F0F0F0F\n','')
        loop='.Lagain:\ncmp r0,#0\nbne .Lagain\n'
        assembly=assembly.replace('bl func_08001000\npop {r1}',loop+
            'ldr r0,.Lfunctionword\nb .Lafterword\n.balign 4,0\n.Lfunctionword:\n.word func_08001000\n.Lafterword:\nmovs r3,#0\nstr r3,[sp]\nbl func_08001000\nadd sp,#8\npop {r1}')
        if broken=='growing-loop':assembly=assembly.replace('.Lagain:\n','.Lagain:\nsub sp,#4\n')
        if broken=='restore':assembly=assembly.replace('add sp,#8\n','movs r0,r0\n')
        assembly=assembly.replace('func_08000000','func_08010000')+'\n.balign 4\n'
        original=assemble(self.root,assembly)
        linked,data=ordinary_link(self.root,original,A)
        rows=[dict(rom=f'0x{A:08X}',end=f'0x{A+len(data):08X}',mode='thumb',instrs=0),
              dict(rom='0x08001000',end='0x08001002',mode='thumb',instrs=1)]
        rows[0]['instrs']=owner.refine(data,A,json.dumps(rows).encode())['instrs']
        mapping=json.dumps(rows).encode()
        index=''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
            f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'for r in rows).encode()
        rom=bytearray(A-match.ROM_BASE+len(data));rom[A-match.ROM_BASE:]=data
        rom[0x1000:0x1002]=b'\x70\x47'
        inputs=dict(data=data,address=A,rom=bytes(rom),mapping=mapping,index=index,
            objects=b'{}',selector=owner.CYCLIC_SELECTOR)
        bindings,_=owner.original_bindings(match.elf_image(original),A,inputs['rom'],mapping,
            b'{}',selector=owner.CYCLIC_SELECTOR,index=index)
        return original,linked,inputs,bindings

    def test_actual_original_link_report_and_partial_correctness(self):
        original,linked,f,bindings=self.fixture()
        manifest,ins=owner.verify(**f,bindings=bindings)
        self.assertEqual(manifest['profile'],owner.CYCLIC_SCHEMA)
        inventory=manifest['proof']['ordinary_switch_inventory']
        self.assertTrue(inventory['local_CFG_cycles'])
        self.assertFalse(inventory['termination_claim'])
        self.assertFalse(inventory['source_or_ELF_admission'])
        self.assertEqual(manifest['proof']['typed_function_words'],bindings['functions'])
        report=owner.render(A,(f['data'],manifest,'synthetic-source',f['mapping'],f['index'],f['objects'],f['rom'],len(ins),original))
        self.assertIn(owner.CYCLIC_CONTROL_FLOW,report)
        self.assertEqual(owner.selector_for_report(report),owner.CYCLIC_SELECTOR)
        self.assertIn('original_elf_sha256',report)
        runner=match.Runner(match.DEFAULT_CC,root=self.root,timeout=120)
        with runner.workspace() as workspace:
            Path(workspace+'/f.o').write_bytes(original)
            runner.write_text(workspace+'/f.i','')
            data,actual=owner.object_bytes(runner,workspace,fixed_args(),match.elf_image(original),
                A,f['rom'],f['mapping'],f['objects'],selector=owner.CYCLIC_SELECTOR,index=f['index'])
            self.assertEqual(data,f['data']);self.assertEqual(actual,bindings)
            self.assertEqual(match.elf_image(runner.read_binary(workspace+'/f.elf'))['text'],match.elf_image(linked)['text'])

    def test_wrong_or_missing_function_words_and_old_policy_reject(self):
        _,_,f,bindings=self.fixture()
        for kind in ('missing','wrong-name','duplicate'):
            altered=copy.deepcopy(bindings)
            if kind=='missing':altered['functions']=[]
            elif kind=='wrong-name':altered['functions'][0][1]='func_08001002'
            else:altered['functions']*=2
            with self.subTest(kind=kind),self.assertRaises(ValueError):owner.verify(**f,bindings=altered)
        with self.assertRaises(ValueError):owner.verify(**dict(f,selector=owner.ALIGNED_SELECTOR),bindings=bindings)
        import framed_switch_inventory as scalar
        calls={A+offset:int(name[5:],16)for offset,name in bindings['calls']}
        with self.assertRaisesRegex(ValueError,'cycles'):
            scalar.verify(f['data'],A,f['rom'],f['mapping'],f['index'],calls,
                {site:f'func_{target:08X}'for site,target in calls.items()},selector=scalar.SELECTOR)

    def test_growing_loop_and_missing_stack_restoration_reject(self):
        for broken in ('growing-loop','restore'):
            _,_,f,bindings=self.fixture(broken)
            with self.subTest(broken=broken),self.assertRaises(ValueError):owner.verify(**f,bindings=bindings)

if __name__=='__main__':unittest.main(verbosity=2)
