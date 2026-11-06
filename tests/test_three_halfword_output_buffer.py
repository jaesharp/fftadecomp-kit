"""Three outputs retain actual pointer origins and all caller-frame bounds."""
import copy
import hashlib
import json
import subprocess
import unittest
from unittest.mock import patch

import test_buffer_discarded_return_scratch as fixtures
import three_halfword_output_buffer_profile as three

match, owner = fixtures.match, fixtures.owner
A, B, C = 0x08010000, 0x08010100, 0x08010200


class ThreeOutputTests(unittest.TestCase):
    setUp = fixtures.DiscardedReturnScratchTests.setUp

    def fixture(self, *, incoming='ldr r5, [sp, #16]', leaf_store='strh r2, [r5]',
                second_word='str r3, [sp, #4]', first_output='adds r3, r6, #0',
                wrapper_return='bx r0', input_offset=12, caller_after='movs r3, #0'):
        source = self.root/'fixture.s'
        source.write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n'
            '.global leaf, leaf_end, wrapper, wrapper_end, func_08010200, caller_end\n'
            '.thumb_func\nleaf:\npush {r4, r5, lr}\nldr r4, [sp, #12]\n' + incoming + '\n'
            'lsls r0, r0, #16\nasrs r0, r0, #21\nstrh r0, [r3]\n'
            'lsls r1, r1, #16\nasrs r1, r1, #20\nstrh r1, [r4]\n'
            'lsls r2, r2, #16\nasrs r2, r2, #21\n' + leaf_store + '\n'
            'pop {r4, r5}\npop {r0}\nbx r0\nleaf_end:\n.org 0x100\n'
            '.thumb_func\nwrapper:\npush {r4, r5, r6, r7, lr}\nsub sp, #8\n'
            'adds r6, r1, #0\nmovs r1, #8\nldrsh r4, [r0, r1]\n'
            'movs r5, #10\nldrsh r1, [r0, r5]\nmovs r7, #' + str(input_offset) + '\n'
            'ldrsh r5, [r0, r7]\nstr r2, [sp]\n' + second_word + '\n'
            'adds r0, r4, #0\nadds r2, r5, #0\n' + first_output + '\nbl leaf\n'
            'add sp, #8\npop {r4, r5, r6, r7}\npop {r0}\n' + wrapper_return + '\n'
            'wrapper_end:\n.org 0x200\n.thumb_func\nfunc_08010200:\n'
            'push {lr}\nsub sp, #8\nmov r1, sp\nadd r2, sp, #4\n'
            'movs r3, #6\nadd r3, sp\nbl wrapper\n' + caller_after + '\n'
            'add sp, #8\npop {r0}\nbx r0\ncaller_end:\n')
        for command in (
            ['arm-none-eabi-as', '-mthumb-interwork', str(source), '-o', str(self.root/'f.o')],
            ['arm-none-eabi-ld', f'-Ttext=0x{A:08X}', '-e', 'func_08010200',
             str(self.root/'f.o'), '-o', str(self.root/'f.elf')],
        ):
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
        image = match.elf_image((self.root/'f.elf').read_bytes())
        symbols = {row['name']: row['value'] for row in image['symbols']}
        rows, bodies = [], {}
        for name, start, end in (('leaf', A, symbols['leaf_end']),
                                 ('wrapper', B, symbols['wrapper_end']),
                                 ('caller', C, symbols['caller_end'])):
            raw = image['text'][start-A:end-A]
            bodies[name] = raw
            rows.append(dict(rom=hex(start), end=hex(end), mode='thumb', instrs=0))
        identities = dict(LEAF=(A, len(bodies['leaf']), hashlib.sha256(bodies['leaf']).hexdigest()),
            WRAPPER=(B, len(bodies['wrapper']), hashlib.sha256(bodies['wrapper']).hexdigest()))
        inputs = dict(rom=b'\0'*(A-match.ROM_BASE)+image['text'],
            mapping=json.dumps(rows).encode(),
            index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                f'{int(row["end"],16)-int(row["rom"],16)} 0 return\n' for row in rows).encode(),
            objects=b'{}\n')
        context = patch.multiple(three, **identities)
        context.start()
        self.addCleanup(context.stop)
        return inputs, bodies

    @staticmethod
    def stack():
        return [(False, False, True)]*8

    def test_three_actual_outputs_and_retained_first_output_alias(self):
        inputs, _ = self.fixture()
        proof = three.ThreeOutputBufferProof(**inputs)
        r0 = match.ARM_REG_R0
        aliases = {r0+1:-8, r0+2:-6, r0+3:-4, r0+12:-2}
        result = proof.check_call(B, aliases, self.stack(), site=C+10)
        self.assertEqual(result, {r0+3:-8, r0+12:-2})
        manifest = proof.nested_manifest()
        self.assertEqual(manifest['calls'][0]['writes_entry_SP_offsets'], [[-8, 2], [-6, 2], [-4, 2]])
        effects = manifest['native_helpers']['wrapper']['structure']['effects']
        self.assertEqual(effects['return_entry_origins'], [[3, 1], [12, 12]])
        self.assertTrue(effects['child_argument_transport'][0]['incoming_words_initialized'])
        self.assertFalse(manifest['physical_nonalias_claim'])
        self.assertEqual(set(proof.dependencies), {A, B})

    def test_all_outputs_require_live_aligned_unprotected_local_halfwords(self):
        inputs, _ = self.fixture()
        r0 = match.ARM_REG_R0
        valid = {r0+1:-8, r0+2:-6, r0+3:-4}
        for change in (dict(aliases={r0+1:-8, r0+2:-6}), dict(aliases=valid|{r0:-12}),
                       dict(aliases=valid|{r0+3:-1}), dict(aliases=valid|{r0+3:-34}),
                       dict(stack=[(False, True, False)]*8), dict(slots={-4:-8}),
                       dict(words={-4:('pointer', -8)}), dict(site=True)):
            with self.subTest(change=change), self.assertRaises(ValueError):
                arguments = dict(aliases=valid, stack=self.stack(), site=C+10)
                arguments.update(change)
                three.ThreeOutputBufferProof(**inputs).check_call(B, **arguments)

    def test_two_outgoing_words_must_be_initialized_and_private(self):
        for second_word in ('movs r3, #0', 'str r3, [sp, #8]', 'str r2, [sp, #4]'):
            with self.subTest(second_word=second_word), self.assertRaises(ValueError):
                inputs, _ = self.fixture(second_word=second_word)
                three.ThreeOutputBufferProof(**inputs)._prove()

    def test_leaf_cannot_read_extra_words_or_store_a_pointer(self):
        for change in (dict(incoming='ldr r5, [sp, #20]'),
                       dict(leaf_store='strh r3, [r5]'), dict(leaf_store='strh r2, [r5, #2]')):
            with self.subTest(change=change), self.assertRaises(ValueError):
                inputs, _ = self.fixture(**change)
                three.ThreeOutputBufferProof(**inputs)._prove()

    def test_wrapper_transport_input_offsets_and_control_restore_remain_exact(self):
        for change in (dict(first_output='adds r3, r5, #0'),
                       dict(wrapper_return='bx lr'), dict(input_offset=14)):
            with self.subTest(change=change), self.assertRaises(ValueError):
                inputs, _ = self.fixture(**change)
                three.ThreeOutputBufferProof(**inputs)._prove()

    def test_complete_body_and_unused_composition_are_rejected(self):
        inputs, _ = self.fixture()
        changed = bytearray(inputs['rom'])
        changed[B-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            three.ThreeOutputBufferProof(**dict(inputs, rom=bytes(changed)))._prove()
        with self.assertRaisesRegex(ValueError, 'actual bounded caller'):
            three.ThreeOutputBufferProof(**inputs).nested_manifest()

    def test_explicit_selector_report_and_manifest_replay(self):
        inputs, bodies = self.fixture()
        arguments = dict(bindings=dict(calls=[[12, 'func_08010100']],
            data=[], functions=[], switches=[]), selector=three.SELECTOR)
        manifest, ins = owner.verify(bodies['caller'], C, **inputs, **arguments)
        self.assertEqual(manifest['profile'], three.SCHEMA)
        replay, _ = owner.verify(bodies['caller'], C, **inputs, manifest=manifest, **arguments)
        self.assertEqual(manifest, replay)
        forged = copy.deepcopy(manifest)
        forged['proof']['buffers']['three_halfword_outputs']['calls'][0]['writes_entry_SP_offsets'] = []
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(bodies['caller'], C, **inputs, manifest=forged, **arguments)
        with self.assertRaises(ValueError):
            owner.verify(bodies['caller'], C, **inputs,
                **dict(arguments, selector=three.named.SCRATCH_SELECTOR))
        report = owner.render(C, (bodies['caller'], manifest, 'synthetic-source',
            inputs['mapping'], inputs['index'], inputs['objects'], inputs['rom'],
            len(ins), (self.root/'f.o').read_bytes()))
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), three.SELECTOR)
        escaping, bodies = self.fixture(caller_after='')
        with self.assertRaisesRegex(ValueError, 'escapes through a return register'):
            owner.verify(bodies['caller'], C, **escaping, **arguments)


if __name__ == '__main__':
    unittest.main(verbosity=2)
