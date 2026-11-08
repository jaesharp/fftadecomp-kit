"""Conditional indirect ABI never supplies local buffer or callback effects."""
import copy
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import function_thunk_profile as thunk

A, B, T = 0x08010000, 0x08011000, thunk.ALIASES['_call_via_r4']


def bl(site, target):
    displacement = target-site-4
    return struct.pack('<HH', 0xF000 | ((displacement >> 12) & 0x7FF),
                       0xF800 | ((displacement >> 1) & 0x7FF))


def fixture(extra=(), leaf=(0x2101, 0x7001, 0x2000, 0x4770), function_word=False):
    tokens = [0xB510, 0xB082, 0x4668, B, 'literal', 0x6824, *extra,
              T, *(['function'] if function_word else []), 0xB002, 0xBC10, 0xBC02, 0x4708]
    data, calls, loads, function_loads = bytearray(), [], [], []
    for token in tokens:
        if token == 'literal':
            loads.append(len(data))
            data += b'\0\0'
        elif token == 'function':
            function_loads.append(len(data))
            data += b'\0\0'
        elif token in (B, T):
            site = A+len(data)
            calls.append([len(data), '_call_via_r4' if token == T else f'func_{B:08X}'])
            data += bl(site, token)
        else:
            data += struct.pack('<H', token)
    if len(data) % 4:
        data += b'\0\0'
    pool = len(data)
    for load in loads:
        struct.pack_into('<H', data, load, 0x4C00 | ((pool-((load+4)&~3))//4))
    data += struct.pack('<I', 0x02000020)
    functions = []
    if function_loads:
        function_pool = len(data)
        for load in function_loads:
            struct.pack_into('<H', data, load, 0x4800 | ((function_pool-((load+4)&~3))//4))
        data += struct.pack('<I', B|1)
        functions.append([function_pool,f'func_{B:08X}'])
    leaf = struct.pack('<'+'H'*len(leaf), *leaf)
    rows = [dict(rom=f'0x{start:08X}', end=f'0x{start+length:08X}', mode='thumb', instrs=count)
            for start,length,count in ((A,len(data),len(tokens)), (B,len(leaf),len(leaf)//2), (T,2,1))]
    mapping = json.dumps(rows).encode()
    index = ''.join(f'{r["rom"][2:]} {r["end"][2:]} '
                    f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'
                    for r in rows).encode()
    rom = bytearray(T-match.ROM_BASE+4)
    rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
    rom[B-match.ROM_BASE:B-match.ROM_BASE+len(leaf)] = leaf
    struct.pack_into('<HH', rom, T-match.ROM_BASE, 0x4720, 0x46C0)
    return dict(data=bytes(data), address=A, rom=bytes(rom), mapping=mapping, index=index,
        objects=b'{"callback_slot":"0x02000020"}', selector=buffers.THUNK_SELECTOR,
        bindings=dict(calls=calls, data=[[pool,'callback_slot',0]], functions=functions, switches=[]))


class ConditionalThunkBufferTests(unittest.TestCase):
    def test_actual_buffer_and_canonical_indirect_call_have_separate_evidence(self):
        f = fixture()
        manifest, _ = owner.verify(**f)
        evidence = manifest['proof']['buffers']
        self.assertEqual([r['address'] for r in evidence['dependencies']], [B])
        conditional = evidence['conditional_thunks']
        self.assertEqual(conditional['ABI'], thunk.ABI)
        self.assertEqual(conditional['dependencies'][0][:3], ['_call_via_r4',T,T+4])
        self.assertEqual(conditional['observations'][0]['local_argument_aliases'], [])
        self.assertIn('no callback body identity', conditional['contract'])
        self.assertEqual(owner.selector_for_report(f'* verification: `{buffers.THUNK_SCHEMA}`\n'),
                         buffers.THUNK_SELECTOR)
        rendered = owner.render(A, (f['data'],manifest,'synthetic',f['mapping'],f['index'],
                                    f['objects'],f['rom'],len(manifest['proof']['calls']),b'synthetic'))
        self.assertIn('* owner runtime: '+buffers.THUNK_SELECTOR, rendered)
        self.assertIn('* control flow: '+buffers.THUNK_CONTROL_FLOW, rendered)

    def test_local_arguments_slots_target_and_saved_return_target_are_rejected(self):
        for extra in ((0x4668,), (0x466C,), (0x4668,0x9000,0x2000)):
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                owner.verify(**fixture(extra=extra))

    def test_ordinary_buffer_bounds_and_return_pointer_rules_remain(self):
        for leaf in ((0x2101,0x7201,0x2000,0x4770), (0x2101,0x7001,0x4770)):
            with self.subTest(leaf=leaf), self.assertRaises(ValueError):
                owner.verify(**fixture(leaf=leaf))
        with self.assertRaises(ValueError):
            owner.verify(**dict(fixture(), selector=buffers.SELECTOR))

    def test_canonical_bytes_complete_indexes_site_and_manifest_are_authenticated(self):
        f = fixture()
        manifest, _ = owner.verify(**f)
        for part in ('body','padding','index','missing-entry','data-role','manifest'):
            changed = copy.deepcopy(f)
            if part in ('body','padding'):
                rom = bytearray(changed['rom'])
                rom[T-match.ROM_BASE+(2 if part == 'padding' else 0)] ^= 1
                changed['rom'] = bytes(rom)
            elif part == 'index':
                changed['index'] = changed['index'].replace(b'08142256',b'08142258')
            elif part == 'missing-entry':
                changed['mapping'] = json.dumps(json.loads(changed['mapping'])[:-1]).encode()
            elif part == 'data-role':
                changed['bindings']['data'] = []
            else:
                altered = copy.deepcopy(manifest)
                altered['proof']['buffers']['conditional_thunks']['observations'][0]['target_register'] = 3
                changed['manifest'] = altered
            with self.subTest(part=part), self.assertRaises(ValueError):
                owner.verify(**changed)
        proof = buffers.ConditionalThunkBufferProof(f['rom'],f['mapping'],f['index'],f['objects'])
        calls = {A+offset:T if name == '_call_via_r4' else B for offset,name in f['bindings']['calls']}
        proof.bind_root(f['data'],A,calls)
        site = next(site for site,target in calls.items() if target == T)
        for returns in ({match.ARM_REG_R0+4}, {match.ARM_REG_R0}):
            with self.subTest(returns=returns), self.assertRaises(ValueError):
                proof.check_indirect_target(T,{},returns,site=site)
        with self.assertRaises(ValueError):
            proof.check_indirect_target(T,{},(),site=A)
        with self.assertRaises(ValueError):
            proof.thunk_manifest()
        with self.assertRaises(ValueError):
            proof.bind_root(f['data'],A,calls)

    def test_only_canonical_calls_gain_forced_replay_for_the_exact_opt_in_type(self):
        class Unselected(buffers.ConditionalThunkBufferProof):
            pass
        f = fixture()
        args = (f['rom'],f['mapping'],f['index'],f['objects'])
        self.assertTrue(match._ordinary_call_replay(buffers.ConditionalThunkBufferProof(*args),T))
        self.assertFalse(match._ordinary_call_replay(buffers.ConditionalThunkBufferProof(*args),B))
        self.assertFalse(match._ordinary_call_replay(Unselected(*args),T))
        self.assertFalse(match._ordinary_call_replay(buffers.NamedDataBufferProof(*args),T))

    def test_returned_function_words_require_exact_indexed_typed_provenance(self):
        f = fixture(function_word=True)
        manifest, _ = owner.verify(**f)
        self.assertEqual(manifest['bindings']['functions'],f['bindings']['functions'])
        changed = copy.deepcopy(f)
        changed['bindings']['functions'] = []
        with self.assertRaises(ValueError):
            owner.verify(**changed)
        changed = copy.deepcopy(f)
        offset,name = changed['bindings']['functions'].pop()
        changed['objects'] = b'{"callback_slot":"0x02000020","code_as_data":"0x08011001"}'
        changed['bindings']['data'].append([offset,'code_as_data',0])
        with self.assertRaisesRegex(ValueError,'function entries as data|canonical function provenance'):
            owner.verify(**changed)

    @unittest.skipUnless(shutil.which('arm-none-eabi-as'), 'fixed assembler required')
    def test_original_elf_requires_actual_canonical_undefined_call_relocations(self):
        scratch = Path(os.environ.get('TMPDIR', Path(__file__).resolve().parents[1]/'build'))
        scratch.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='conditional_thunk_elf_',dir=scratch) as directory:
            root = Path(directory)
            source = root/'fixture.s'
            source.write_text('''.syntax unified
.arch armv4t
.thumb
.text
.global func_08010000
.type func_08010000, %function
.thumb_func
func_08010000:
push {r4,lr}
sub sp,#8
mov r0,sp
bl func_08011000
ldr r4,callback
ldr r4,[r4]
bl _call_via_r4
add sp,#8
pop {r4}
pop {r1}
bx r1
.balign 4,0
callback:
.word callback_slot
.size func_08010000, .-func_08010000
''')
            output = root/'fixture.o'
            subprocess.run(['arm-none-eabi-as','-mthumb-interwork',str(source),'-o',str(output)],
                           check=True,capture_output=True,timeout=30)
            original = match.elf_image(output.read_bytes())
        f = fixture()
        bindings, targets = owner.original_bindings(original,A,f['rom'],f['mapping'],
            f['objects'],selector=buffers.THUNK_SELECTOR,index=f['index'])
        self.assertEqual(bindings,f['bindings'])
        self.assertEqual(targets['_call_via_r4'],(T,False))
        for name in (f'func_{T:08X}','_call_via_r3'):
            altered = copy.deepcopy(original)
            next(s for s in altered['symbols'] if s['name']=='_call_via_r4')['name'] = name
            with self.subTest(name=name), self.assertRaises(ValueError):
                owner.original_bindings(altered,A,f['rom'],f['mapping'],f['objects'],
                    selector=buffers.THUNK_SELECTOR,index=f['index'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
