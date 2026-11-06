"""Direct outputs require exact incoming transport and live caller bounds."""
import copy
import hashlib
import json
import subprocess
import unittest
from unittest.mock import patch

import test_formal_entry_word_halfword_effects as fixtures
import direct_halfword_output_buffer_profile as direct

match, owner = fixtures.match, fixtures.owner
A, B = 0x08010000, 0x08010100


class DirectOutputTests(unittest.TestCase):
    setUp = fixtures.FormalEntryWordEffectsTests.setUp

    def fixture(self, **changes):
        leaf = fixtures.FormalEntryWordEffectsTests.fixture(self, **changes)
        raw = leaf['data']
        mapping = json.dumps([dict(rom=hex(A), end=hex(A+len(raw)), mode='thumb', instrs=51)]).encode()
        inputs = dict(rom=b'\0'*(A-match.ROM_BASE)+raw, mapping=mapping,
            index=f'{A:08X} {A+len(raw):08X} {len(raw)} 51 return\n'.encode(),
            objects=leaf['data_mapping'])
        identity = (A, len(raw), hashlib.sha256(raw).hexdigest())
        return inputs, identity

    def proof(self, **changes):
        inputs, identity = self.fixture(**changes)
        context = patch.object(direct, 'LEAF', identity)
        context.start()
        self.addCleanup(context.stop)
        return direct.DirectOutputBufferProof(**inputs)

    @staticmethod
    def stack():
        return [(False, False, True)]*8

    def call(self, proof, **changes):
        arguments = dict(aliases={match.ARM_REG_R0+3:-8}, stack=self.stack(),
                         slots={-32:-6}, site=B)
        arguments.update(changes)
        return proof.check_call(A, **arguments)

    def test_outputs_and_actual_returned_entry_aliases(self):
        proof = self.proof()
        r0 = match.ARM_REG_R0
        result = self.call(proof, aliases={r0+3:-8, r0+8:-4, r0+12:-2})
        self.assertEqual(result, {r0+3:-4, r0+12:-2})
        manifest = proof.direct_manifest()
        self.assertEqual(manifest['calls'][0]['writes_entry_SP_offsets'], [[-8, 2], [-6, 2]])
        self.assertEqual(manifest['calls'][0]['outgoing_pointer_word'], [-32, -6])
        self.assertEqual(set(proof.dependencies), {A})
        self.assertFalse(manifest['physical_nonalias_claim'])

    def test_pointer_word_requires_live_initialized_slot_zero(self):
        proof = self.proof()
        for slots in (None, {}, {-28:-6}, {-32:-6, -28:-4}):
            with self.subTest(slots=slots), self.assertRaises(ValueError):
                self.call(proof, slots=slots)
        stack = self.stack()
        stack[0] = (False, True, False)
        with self.assertRaises(ValueError):
            self.call(proof, stack=stack)

    def test_each_halfword_requires_aligned_live_local_bytes(self):
        proof = self.proof()
        r3 = match.ARM_REG_R0+3
        for changes in (dict(aliases={r3:-7}), dict(slots={-32:-5}),
                        dict(aliases={r3:-34}), dict(slots={-32:0}),
                        dict(stack=[(False, True, False)]*8)):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                self.call(proof, **changes)

    def test_outputs_cannot_corrupt_outgoing_pointer_transport(self):
        proof = self.proof()
        for changes in (dict(aliases={match.ARM_REG_R0+3:-32}),
                        dict(slots={-32:-30})):
            with self.subTest(changes=changes), self.assertRaisesRegex(ValueError, 'outgoing pointer word'):
                self.call(proof, **changes)

    def test_scalar_inputs_cannot_carry_hidden_local_aliases(self):
        proof = self.proof()
        for register in (match.ARM_REG_R0, match.ARM_REG_R0+1, match.ARM_REG_R0+2, match.ARM_REG_LR):
            with self.subTest(register=register), self.assertRaises(ValueError):
                self.call(proof, aliases={match.ARM_REG_R0+3:-8, register:-4})
        with self.assertRaises(ValueError):
            self.call(proof, aliases={})
        with self.assertRaises(ValueError):
            self.call(proof, words={-32:('pointer', -6)})

    def test_actual_leaf_effects_and_named_read_premise_cannot_be_substituted(self):
        for changes in (dict(incoming='ldr r7, [sp, #40]'), dict(output='strh r1, [r7, #2]'),
                        dict(restore='mov r8, r4')):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                self.call(self.proof(**changes))
        inputs, identity = self.fixture()
        with patch.object(direct, 'LEAF', identity):
            with self.assertRaises(ValueError):
                self.call(direct.DirectOutputBufferProof(**dict(inputs, objects=b'{}')))
            changed = bytearray(inputs['rom'])
            changed[-1] ^= 1
            with self.assertRaises(ValueError):
                self.call(direct.DirectOutputBufferProof(**dict(inputs, rom=bytes(changed))))

    def owner_fixture(self, *, after='', return_register='r0'):
        inputs, identity = self.fixture()
        (self.root/'leaf.bin').write_bytes(inputs['rom'][A-match.ROM_BASE:])
        source = self.root/'caller.s'
        source.write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n'
            '.thumb_func\nleaf:\n.incbin "'+str(self.root/'leaf.bin')+'"\n.org 0x100\n'
            '.global caller, caller_end\n.thumb_func\ncaller:\npush {lr}\nsub sp, #12\n'
            'add r3, sp, #4\nadd r2, sp, #8\nstr r2, [sp]\nmovs r2, #0\n'
            'movs r0, #0\nmovs r1, #0\nbl leaf\n'+after+'\nadd sp, #12\n'
            f'pop {{{return_register}}}\nbx {return_register}\ncaller_end:\n')
        for command in (
            ['arm-none-eabi-as', '-mthumb-interwork', str(source), '-o', str(self.root/'caller.o')],
            ['arm-none-eabi-ld', f'-Ttext=0x{A:08X}', '-e', 'caller', str(self.root/'caller.o'), '-o', str(self.root/'caller.elf')],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root/'caller.elf').read_bytes())
        end = next(row['value'] for row in image['symbols'] if row['name']=='caller_end')
        raw = image['text'][B-A:end-A]
        rom = b'\0'*(A-match.ROM_BASE)+image['text']
        mapping = json.dumps(json.loads(inputs['mapping'])+[
            dict(rom=hex(B), end=hex(end), mode='thumb', instrs=12)]).encode()
        index = inputs['index']+f'{B:08X} {end:08X} {len(raw)} 12 return\n'.encode()
        bindings = dict(calls=[[16, 'func_08010000']], data=[], functions=[], switches=[])
        arguments = dict(bindings=bindings, selector=direct.SELECTOR)
        return inputs, identity, raw, rom, mapping, index, arguments

    def test_explicit_profile_roundtrip_and_manifest_tampering(self):
        inputs, identity, raw, rom, mapping, index, arguments = self.owner_fixture()
        bindings = arguments['bindings']
        with patch.object(direct, 'LEAF', identity):
            manifest, instructions = owner.verify(raw, B, rom, mapping, index, inputs['objects'], **arguments)
            self.assertEqual(manifest['profile'], direct.SCHEMA)
            forged = copy.deepcopy(manifest)
            forged['proof']['buffers']['direct_halfword_outputs']['calls'][0]['outgoing_pointer_word'] = []
            with self.assertRaisesRegex(ValueError, 'manifest differs'):
                owner.verify(raw, B, rom, mapping, index, inputs['objects'], forged, **arguments)
            with self.assertRaises(ValueError):
                owner.verify(raw, B, rom, mapping, index, inputs['objects'],
                             bindings=bindings, selector=direct.nested.SELECTOR)
            report = owner.render(B, (raw, manifest, 'synthetic-source', mapping, index,
                inputs['objects'], rom, len(instructions), (self.root/'caller.o').read_bytes()))
            self.assertTrue(owner.selected(report))
            self.assertEqual(owner.selector_for_report(report), direct.SELECTOR)

    def test_root_scratch_projection_is_explicit_and_only_at_normal_return(self):
        inputs, identity, raw, rom, mapping, index, arguments = self.owner_fixture(after='mov r2, sp')
        with patch.object(direct, 'LEAF', identity):
            manifest, _ = owner.verify(raw, B, rom, mapping, index, inputs['objects'], **arguments)
        scratch = manifest['proof']['buffers']['direct_halfword_outputs']['root_return_scratch']
        self.assertEqual(scratch['registers'], [2, 3])
        self.assertEqual(scratch['observations'][0][1:], [2, -16])

    def test_root_result_register_aliases_remain_rejected(self):
        for register, return_register in (('r0', 'r1'), ('r1', 'r0')):
            inputs, identity, raw, rom, mapping, index, arguments = self.owner_fixture(
                after=f'mov {register}, sp', return_register=return_register)
            with self.subTest(register=register), patch.object(direct, 'LEAF', identity):
                with self.assertRaisesRegex(ValueError, 'escapes through a return register'):
                    owner.verify(raw, B, rom, mapping, index, inputs['objects'], **arguments)

    def test_return_projection_cannot_be_reused_for_nested_or_changed_contexts(self):
        proof = self.proof()
        aliases = {match.ARM_REG_R0+2:-8}
        with self.assertRaises(ValueError):
            direct.root_return_aliases(proof, b'body', B, B+2, aliases)
        proof._root = (B, b'body', frozenset({B+2}))
        for body, address, site in ((b'changed', B, B+2), (b'body', A, B+2), (b'body', B, B)):
            with self.subTest(body=body, address=address, site=site), self.assertRaises(ValueError):
                direct.root_return_aliases(proof, body, address, site, aliases)
        proof.active.add(A)
        with self.assertRaises(ValueError):
            direct.root_return_aliases(proof, b'body', B, B+2, aliases)
        class OtherProof(direct.DirectOutputBufferProof):
            pass
        inputs, _ = self.fixture()
        self.assertEqual(direct.root_return_aliases(OtherProof(**inputs), b'body', B, B+2, aliases), aliases)


if __name__ == '__main__':
    unittest.main(verbosity=2)
