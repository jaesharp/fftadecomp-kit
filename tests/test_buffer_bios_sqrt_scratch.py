"""Only an exact scalar wrapper and wholly killed caller scratch may compose."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import named_data_buffer_profile as buffers
import owner_admission_profile as owner

A, B, C = 0x08010000, 0x08010100, 0x08010200
KILL = 'movs r1, #0\nmovs r2, #0\nmovs r3, #0'


class BiosSqrtScratchTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ['FFTA_TEST_SCRATCH'])
        scratch.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix='bios_sqrt_', dir=scratch)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def fixture(self, after=KILL, before='', wrapper='svc #8\nbx lr', nested=False):
        caller = ('push {r4, lr}\nsub sp, #8\nmov r3, sp\n' + before +
                  '\nbl callee\n' + after +
                  '\nadd sp, #8\npop {r4}\npop {r0}\nbx r0')
        callee = ('push {lr}\nbl child\n' + KILL + '\npop {r0}\nbx r0') if nested else wrapper
        assembly = self.root/'fixture.s'
        assembly.write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n'
            '.global caller, caller_end, callee, callee_end, child, child_end\n'
            f'caller:\n{caller}\ncaller_end:\n.org 0x100\n'
            f'callee:\n{callee}\ncallee_end:\n.org 0x200\n'
            f'child:\n{wrapper if nested else "bx lr"}\nchild_end:\n')
        for command in (
            ['arm-none-eabi-as', '-mthumb-interwork', str(assembly), '-o', str(self.root/'f.o')],
            ['arm-none-eabi-ld', '-Ttext=0x08010000', '-e', 'caller', str(self.root/'f.o'), '-o', str(self.root/'f.elf')],
            ['arm-none-eabi-objcopy', '-O', 'binary', '--only-section=.text', str(self.root/'f.elf'), str(self.root/'rom.bin')],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root/'f.elf').read_bytes())
        symbols = {symbol['name']: symbol['value'] for symbol in image['symbols']}
        rows = [dict(rom=f'0x{symbols[name]:08X}', end=f'0x{symbols[name+"_end"]:08X}',
                     mode='thumb', instrs=0) for name in ('caller', 'callee', 'child')]
        binary = (self.root/'rom.bin').read_bytes()
        body = binary[:symbols['caller_end']-A]
        mapping = json.dumps(rows).encode()
        index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                        f'{int(row["end"],16)-int(row["rom"],16)} 0 return\n' for row in rows).encode()
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        calls = [[i.address-A, f'func_{i.operands[0].imm:08X}']
                 for i in decoder.disasm(body, A) if i.mnemonic == 'bl']
        return dict(data=body, address=A, rom=b'\0'*(A-match.ROM_BASE)+binary,
                    mapping=mapping, index=index, objects=b'{}\n',
                    bindings=dict(calls=calls, data=[], functions=[], switches=[]),
                    selector=buffers.BIOS_SQRT_SELECTOR)

    def test_exact_direct_and_nested_wrapper(self):
        for nested in (False, True):
            with self.subTest(nested=nested):
                manifest, _ = owner.verify(**self.fixture(nested=nested))
                self.assertEqual(manifest['profile'], buffers.BIOS_SQRT_SCHEMA)
                bios = manifest['proof']['buffers']['bios_sqrt']
                self.assertEqual(bios['wrapper_hex'], '08df7047')
                self.assertEqual(bios['observations'][0]['address'], C if nested else B)
                self.assertEqual(bios['observations'][0]['consumer'], B if nested else A)
                self.assertEqual(bios['observations'][0]['killed_registers'], [1, 2, 3])
                self.assertIn('no numerical', bios['contract'])
                self.assertIn('named_data_buffer_profile.py', bios['source_sha256'])

    def test_wrapper_mutation_and_other_service_are_refused(self):
        for wrapper in ('svc #9\nbx lr', 'svc #8\nmovs r0, #0\nbx lr',
                        'svc #8\nbx r0', 'movs r0, #8\nbx lr'):
            with self.subTest(wrapper=wrapper), self.assertRaises(ValueError):
                owner.verify(**self.fixture(wrapper=wrapper))

    def test_every_scratch_register_is_killed_before_read_call_or_return(self):
        for register in (1, 2, 3):
            for observed in (f'str r{register}, [r0]\n'+KILL,
                             f'adds r0, r{register}, #0\n'+KILL,
                             '\n'.join(f'movs r{n}, #0' for n in (1, 2, 3) if n != register)):
                with self.subTest(register=register, observed=observed), self.assertRaisesRegex(
                        ValueError, 'scratch.*before a killing write'):
                    owner.verify(**self.fixture(after=observed))
        with self.assertRaisesRegex(ValueError, 'observes BIOS Sqrt scratch'):
            owner.verify(**self.fixture(after='bl child\n'+KILL))
        with self.assertRaisesRegex(ValueError, 'observes BIOS Sqrt scratch'):
            owner.verify(**self.fixture(after='cmp r0, #0\nbeq read\n'+KILL+
                '\nread:\nadds r0, r1, #0'))

    def test_input_r0_bounds_and_unknown_result_remain_checked(self):
        with self.assertRaisesRegex(ValueError, 'scalar R0'):
            owner.verify(**self.fixture(before='mov r0, sp'))
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            owner.verify(**self.fixture(before='add r3, sp, #8'))
        with self.assertRaises(ValueError):
            owner.verify(**self.fixture(after=KILL+'\nmov r3, sp\nldr r0, [r3, r0]'))

    def test_exact_mapping_and_actual_call_site_are_required(self):
        f = self.fixture()
        rows = json.loads(f['mapping'])
        for kind in ('missing', 'duplicate', 'overlap', 'mode'):
            changed = copy.deepcopy(rows)
            if kind == 'missing':
                changed.pop(1)
            elif kind == 'duplicate':
                changed.append(changed[1].copy())
            elif kind == 'overlap':
                changed[2]['rom'] = f'0x{B+2:08X}'
            else:
                changed[1]['mode'] = 'arm'
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                owner.verify(**dict(f, mapping=json.dumps(changed).encode()))
        proof = buffers.BiosSqrtScratchProof(f['rom'], f['mapping'], f['index'], f['objects'])
        stack = [(False, False, True)]*4
        for site in (None, A, C):
            with self.subTest(site=site), self.assertRaises(ValueError):
                proof.check_arguments(B, {match.ARM_REG_R3: -8}, stack, {}, frozenset(), site=site)

    def test_old_selectors_and_absent_actual_wrapper_remain_separate(self):
        f = self.fixture()
        for selector in (owner.ACYCLIC_SELECTOR, buffers.SELECTOR, buffers.SCRATCH_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                owner.verify(**dict(f, selector=selector))
        marker = f'* verification: `{buffers.BIOS_SQRT_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker), buffers.BIOS_SQRT_SELECTOR)
        for malformed in (marker*2, marker+f'* verification: `{buffers.SCRATCH_SCHEMA}`\n'):
            with self.assertRaises(ValueError):
                owner.selected(malformed)

    def test_incoming_slots_remain_untouched_without_pointer_or_word_escape(self):
        f = self.fixture()
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        site = next(i.address for i in decoder.disasm(f['data'], A) if i.mnemonic == 'bl')
        proof = buffers.BiosSqrtScratchProof(f['rom'], f['mapping'], f['index'], f['objects'])
        stack = [(False, False, True)]*4
        result = proof.check_arguments(B, {match.ARM_REG_R3: -8}, stack,
            {0: -12}, frozenset({-16}), site=site)
        self.assertEqual(result, {})
        observation = proof.bios_manifest()['observations'][0]
        self.assertEqual(observation['untouched_incoming_slots'], [(0, -12)])
        self.assertEqual(observation['protected_slots'], [-16])
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            proof.check_arguments(B, {}, stack, {0: -20}, frozenset(), site=site)
        with self.assertRaisesRegex(ValueError, 'word-provenance'):
            proof.check_arguments(B, {}, stack, {}, frozenset(), site=site, words={-8: 'pointer'})
        with self.assertRaisesRegex(ValueError, 'scalar R0'):
            proof.check_arguments(B, {match.ARM_REG_R0: -8}, stack,
                {0: -12}, frozenset(), site=site)

    def test_fresh_manifest_binds_wrapper_consumer_policy_and_source(self):
        f = self.fixture()
        manifest, _ = owner.verify(**f)
        for field in ('consumer_sha256', 'call_site', 'incoming_aliases'):
            changed = copy.deepcopy(manifest)
            row = changed['proof']['buffers']['bios_sqrt']['observations'][0]
            row[field] = [] if field == 'incoming_aliases' else 0
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'manifest differs'):
                owner.verify(**dict(f, manifest=changed))
        changed = copy.deepcopy(manifest)
        changed['proof']['buffers']['bios_sqrt']['source_sha256']['match.py'] = '0'*64
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**dict(f, manifest=changed))
        with self.assertRaisesRegex(ValueError, 'original ELF identity'):
            owner.fingerprint(A, f['data'], manifest, 'source', f['mapping'],
                              f['index'], f['objects'], f['rom'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
