"""Nested outputs require native transport, live bounds and retained aliases."""
import hashlib
import copy
import json
import subprocess
import unittest
from unittest.mock import patch

import test_formal_entry_word_halfword_effects as leaf_fixtures
import nested_formal_output_buffer_profile as nested

match = leaf_fixtures.match
A, B = 0x08010000, 0x08010100


class NestedOutputTests(unittest.TestCase):
    setUp = leaf_fixtures.FormalEntryWordEffectsTests.setUp

    def fixture(self, *, store='str r2, [sp]', arg='adds r3, r1, #0', terminal='bx r0'):
        leaf = leaf_fixtures.FormalEntryWordEffectsTests.fixture(self)
        (self.root / 'leaf.bin').write_bytes(leaf['data'])
        source = self.root / 'wrapper.s'
        source.write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n'
            '.thumb_func\nleaf:\n.incbin "' + str(self.root/'leaf.bin') + '"\n.org 0x100\n'
            '.global wrapper, wrapper_end\n.thumb_func\nwrapper:\n'
            'push {r4, r5, r6, lr}\nsub sp, #4\n' + arg + '\n'
            'movs r1, #8\nldrsh r4, [r0, r1]\nmovs r5, #10\n'
            'ldrsh r1, [r0, r5]\nmovs r6, #12\nldrsh r5, [r0, r6]\n'
            + store + '\nadds r0, r4, #0\nadds r2, r5, #0\nbl leaf\n'
            'add sp, #4\npop {r4, r5, r6}\npop {r0}\n' + terminal + '\nwrapper_end:\n')
        for command in (
            ['arm-none-eabi-as', '-mthumb-interwork', str(source), '-o', str(self.root/'wrapper.o')],
            ['arm-none-eabi-ld', f'-Ttext=0x{A:08X}', '-e', 'wrapper',
             str(self.root/'wrapper.o'), '-o', str(self.root/'wrapper.elf')],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root/'wrapper.elf').read_bytes())
        end = next(row['value'] for row in image['symbols'] if row['name'] == 'wrapper_end')
        wrapper = image['text'][B-A:end-A]
        leaf_data = leaf['data']
        rom = b'\0' * (A-match.ROM_BASE) + leaf_data + b'\0' * (B-A-len(leaf_data)) + wrapper
        rows = [dict(rom=f'0x{start:08X}', end=f'0x{start+len(raw):08X}', mode='thumb', instrs=count)
                for start, raw, count in ((A, leaf_data, 51), (B, wrapper, 17))]
        mapping = json.dumps(rows).encode()
        index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                        f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
                        for row in rows).encode()
        identities = dict(LEAF=(A, len(leaf_data), hashlib.sha256(leaf_data).hexdigest()),
                          WRAPPER=(B, len(wrapper), hashlib.sha256(wrapper).hexdigest()))
        return dict(rom=rom, mapping=mapping, index=index, objects=leaf['data_mapping']), identities

    def proof(self, fixture):
        inputs, identities = fixture
        context = patch.multiple(nested, **identities)
        context.start()
        self.addCleanup(context.stop)
        return nested.NestedOutputBufferProof(**inputs)

    @staticmethod
    def stack():
        return [(False, False, True)] * 8

    def test_actual_pointer_word_outputs_and_entry_alias_returns(self):
        proof = self.proof(self.fixture())
        r0 = match.ARM_REG_R0
        aliases = {r0+1:-8, r0+2:-6, r0+3:-10, r0+8:-4, r0+12:-2}
        result = proof.check_call(B, aliases, self.stack(), site=0x08010200)
        self.assertEqual(result, {r0+3:-4, r0+12:-2})
        manifest = proof.nested_manifest()
        self.assertEqual(manifest['calls'][0]['writes_entry_SP_offsets'], [[-8, 2], [-6, 2]])
        wrapper = manifest['native_helpers']['wrapper']['structure']['effects']
        self.assertTrue(wrapper['child_argument_transport'][0]['incoming_word_initialized'])
        self.assertEqual(wrapper['preserved'], 'r4-r11,sp,entry-lr')
        self.assertEqual(set(proof.dependencies), {A, B})

    def test_caller_alignment_allocation_and_protected_words_remain_closed(self):
        proof = self.proof(self.fixture())
        r0 = match.ARM_REG_R0
        valid = {r0+1:-8, r0+2:-6}
        for change in (dict(aliases={r0+1:-8}), dict(aliases=valid | {r0:-12}),
                       dict(aliases={r0+1:-8, r0+2:-1}), dict(aliases={r0+1:-34, r0+2:-6}),
                       dict(slots={-4:-8}), dict(words={-4:('pointer', -8)}),
                       dict(stack=[(False, True, False)]*8)):
            with self.subTest(change=change), self.assertRaises(ValueError):
                arguments = dict(aliases=valid, stack=self.stack(), site=0x08010200)
                arguments.update(change)
                proof.check_call(B, **arguments)

    def test_outgoing_pointer_word_must_be_initialized_in_own_live_local(self):
        for store in ('movs r2, #0', 'str r2, [sp, #4]'):
            with self.subTest(store=store), self.assertRaises(ValueError):
                self.proof(self.fixture(store=store))._prove()

    def test_child_formals_and_terminal_return_cannot_be_forged(self):
        for change in (dict(arg='adds r3, r2, #0'), dict(terminal='bx r2')):
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.proof(self.fixture(**change))._prove()

    def test_changed_complete_body_and_named_binding_are_rejected(self):
        inputs, identities = self.fixture()
        changed = bytearray(inputs['rom'])
        changed[B-match.ROM_BASE] ^= 1
        for replacement in (dict(rom=bytes(changed)), dict(objects=b'{}')):
            with self.subTest(replacement=list(replacement)), self.assertRaises(ValueError):
                self.proof((dict(inputs, **replacement), identities))._prove()

    def test_no_unused_native_composition_manifest(self):
        with self.assertRaisesRegex(ValueError, 'actual bounded caller'):
            self.proof(self.fixture()).nested_manifest()

    def test_complete_owner_selector_report_and_manifest_replay(self):
        inputs, identities = self.fixture()
        self.proof((inputs, identities))
        owner = leaf_fixtures.fixtures.owner
        caller = 0x08010200
        (self.root/'helpers.bin').write_bytes(inputs['rom'][A-match.ROM_BASE:])
        (self.root/'caller.s').write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n'
            '.incbin "' + str(self.root/'helpers.bin') + '"\n.org 0x200\n'
            '.global func_08010200, caller_end\n.thumb_func\nfunc_08010200:\n'
            'push {lr}\nsub sp, #8\nmov r1, sp\nadd r2, sp, #4\n'
            'bl wrapper\nadd sp, #8\npop {r0}\nbx r0\ncaller_end:\n'
            '.thumb_set wrapper, func_08010200-0x100\n')
        for command in (
            ['arm-none-eabi-as', '-mthumb-interwork', str(self.root/'caller.s'), '-o', str(self.root/'caller.o')],
            ['arm-none-eabi-ld', f'-Ttext=0x{A:08X}', '-e', 'func_08010200',
             str(self.root/'caller.o'), '-o', str(self.root/'caller.elf')],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root/'caller.elf').read_bytes())
        end = next(row['value'] for row in image['symbols'] if row['name'] == 'caller_end')
        raw = image['text'][caller-A:end-A]
        rom = b'\0'*(A-match.ROM_BASE) + image['text']
        rows = json.loads(inputs['mapping']) + [dict(rom=hex(caller), end=hex(end), mode='thumb', instrs=8)]
        mapping = json.dumps(rows).encode()
        index = inputs['index'] + f'{caller:08X} {end:08X} {len(raw)} 8 return\n'.encode()
        bindings = dict(calls=[[8, 'func_08010100']], data=[], functions=[], switches=[])
        arguments = dict(bindings=bindings, selector=nested.SELECTOR)
        manifest, instructions = owner.verify(raw, caller, rom, mapping, index, inputs['objects'], **arguments)
        self.assertEqual(manifest['profile'], nested.SCHEMA)
        replay, _ = owner.verify(raw, caller, rom, mapping, index, inputs['objects'], manifest, **arguments)
        self.assertEqual(replay, manifest)
        forged = copy.deepcopy(manifest)
        forged['proof']['buffers']['nested_halfword_outputs']['calls'][0]['writes_entry_SP_offsets'] = []
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(raw, caller, rom, mapping, index, inputs['objects'], forged, **arguments)
        with self.assertRaises(ValueError):
            owner.verify(raw, caller, rom, mapping, index, inputs['objects'],
                         bindings=bindings, selector=nested.named.SCRATCH_SELECTOR)
        report = owner.render(caller, (raw, manifest, 'synthetic-source', mapping, index,
            inputs['objects'], rom, len(instructions), (self.root/'caller.o').read_bytes()))
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), nested.SELECTOR)


if __name__ == '__main__':
    unittest.main(verbosity=2)
