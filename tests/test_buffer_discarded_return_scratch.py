"""Discarded ABI scratch requires complete consumer non-observation."""
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


class DiscardedReturnScratchTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ['FFTA_TEST_SCRATCH'])
        scratch.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix='scratch_consumer_', dir=scratch)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def fixture(self, after='', callee='strh r0, [r3]\nbx lr', before='',
                release='add sp, #8', return_register='r0'):
        caller = ('push {r4, lr}\nsub sp, #8\nmov r3, sp\n' + before +
                  'bl callee\n' + after + '\n' + release +
                  '\npop {r4}\n' + f'pop {{{return_register}}}\nbx {return_register}')
        assembly = self.root/'fixture.s'
        assembly.write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n'
            '.global caller, caller_end, callee, callee_end, child, child_end\n'
            f'caller:\n{caller}\ncaller_end:\n.org 0x100\n'
            f'callee:\n{callee}\ncallee_end:\n.org 0x200\n'
            'child:\nbx lr\nchild_end:\n')
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
        rom = b'\0' * (A-match.ROM_BASE) + binary
        body = binary[:symbols['caller_end']-A]
        mapping = json.dumps(rows).encode()
        index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                        f'{int(row["end"],16)-int(row["rom"],16)} 0 return\n' for row in rows).encode()
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        calls = [[i.address-A, f'func_{i.operands[0].imm:08X}']
                 for i in decoder.disasm(body, A) if i.mnemonic == 'bl']
        return dict(data=body, address=A, rom=rom, mapping=mapping, index=index, objects=b'{}\n',
                    bindings=dict(calls=calls, data=[], functions=[], switches=[]),
                    selector=buffers.SCRATCH_SELECTOR)

    def test_exact_unobserved_return_and_killing_write(self):
        for after in ('', 'movs r3, #0\nstr r3, [r1]',
                      'cmp r0, #0\nbeq done\nmovs r3, #0\ndone:'):
            with self.subTest(after=after):
                f = self.fixture(after)
                manifest, _ = owner.verify(**f)
                proof = manifest['proof']['buffers']['normal_return_scratch']
                self.assertEqual(manifest['profile'], buffers.SCRATCH_SCHEMA)
                self.assertEqual(proof['registers'], [2, 3])
                self.assertEqual(proof['observations'][0]['projected'], [[3, -16]])
                self.assertEqual(proof['observations'][0]['consumer'], A)
                self.assertIn('named_data_buffer_profile.py', proof['source_sha256'])

    def test_consumer_reads_stores_and_calls_are_not_discarded(self):
        for after in ('ldr r0, [r3]', 'str r3, [r1]', 'adds r2, r3, #0',
                      'bl child', 'cmp r0, #0\nbeq read\nmovs r3, #0\nread:\nldr r0, [r3]'):
            with self.subTest(after=after), self.assertRaisesRegex(ValueError, 'consumer observes'):
                owner.verify(**self.fixture(after))

    def test_result_registers_and_callee_memory_bounds_stay_checked(self):
        for register in ('r0', 'r1'):
            with self.subTest(register=register), self.assertRaisesRegex(ValueError, 'escapes through a return register'):
                owner.verify(**self.fixture(callee=f'adds {register}, r3, #0\nbx lr',
                                             return_register='r1' if register == 'r0' else 'r0'))
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            owner.verify(**self.fixture(callee='ldr r0, [r3, #8]\nbx lr'))
        with self.assertRaisesRegex(ValueError, 'buffer pointer use or escape'):
            owner.verify(**self.fixture(callee='str r3, [r1]\nbx lr'))

    def test_old_profiles_and_absent_projection_remain_separate(self):
        f = self.fixture()
        for selector in (owner.ACYCLIC_SELECTOR, buffers.SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                owner.verify(**dict(f, selector=selector))
        with self.assertRaisesRegex(ValueError, 'actual checked projections'):
            owner.verify(**self.fixture(callee='strh r0, [r3]\nmovs r3, #0\nbx lr'))
        with self.assertRaises(ValueError):
            owner.verify(**self.fixture(release='add sp, #4'))

    def test_fresh_manifest_binds_policy_consumer_and_callee(self):
        f = self.fixture()
        manifest, _ = owner.verify(**f)
        for field in ('consumer_sha256', 'call_site', 'projected'):
            changed = copy.deepcopy(manifest)
            row = changed['proof']['buffers']['normal_return_scratch']['observations'][0]
            row[field] = [] if field == 'projected' else 0
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'manifest differs'):
                owner.verify(**dict(f, manifest=changed))
        changed = bytearray(f['rom'])
        changed[B-A] ^= 1
        with self.assertRaises(ValueError):
            owner.verify(**dict(f, rom=bytes(changed), manifest=manifest))

    def test_separate_report_selection_and_original_elf_binding(self):
        marker = f'* verification: `{buffers.SCRATCH_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker), buffers.SCRATCH_SELECTOR)
        for report in (marker*2, marker+f'* verification: `{buffers.SCHEMA}`\n',
                       marker+'* buffer calls: legacy\n'):
            with self.subTest(report=report), self.assertRaises(ValueError):
                owner.selected(report)
        f = self.fixture()
        manifest, _ = owner.verify(**f)
        with self.assertRaisesRegex(ValueError, 'original ELF identity'):
            owner.fingerprint(A, f['data'], manifest, 'source', f['mapping'],
                              f['index'], f['objects'], f['rom'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
