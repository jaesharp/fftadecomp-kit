"""Formal output effects retain entry aliases and reject invented access rights."""
import json
import subprocess
import unittest

import test_buffer_discarded_return_scratch as fixtures
import formal_entry_word_halfword_effects as effects

match, owner = fixtures.match, fixtures.owner


class FormalEntryWordEffectsTests(unittest.TestCase):
    setUp = fixtures.DiscardedReturnScratchTests.setUp

    def fixture(self, *, first_store='strh r4, [r6]', incoming='ldr r7, [sp, #36]',
                output='strh r1, [r7]', restore='mov r8, r3', named='ldrh r7, [r5, #32]'):
        source = self.root / 'fixture.s'
        source.write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n'
            '.global helper, helper_end\nhelper:\n'
            'push {r4, r5, r6, r7, lr}\nmov r7, r9\nmov r6, r8\npush {r6, r7}\n'
            'sub sp, #8\nmov r6, sp\nmovs r4, #2\nadd r4, sp\nmov r8, r4\n'
            'add r7, sp, #4\nmov r9, r7\nlsls r0, r0, #16\nasrs r0, r0, #16\n'
            'lsls r2, r2, #16\nasrs r2, r2, #16\nsubs r4, r0, r2\nldr r5, literal\n'
            'asrs r4, r4, #1\n' + named + '\nadds r4, r4, r7\n' + first_store + '\n'
            'adds r0, r0, r2\nasrs r2, r0, #2\nlsls r1, r1, #16\nasrs r1, r1, #17\n'
            'subs r2, r2, r1\nldrh r1, [r5, #34]\nadds r2, r2, r1\n'
            'mov r4, r8\nstrh r2, [r4]\nmov r7, r9\nstrh r0, [r7]\n'
            'mov r0, sp\nmovs r2, #0\nldrsh r1, [r4, r2]\nldrh r2, [r5, #36]\n'
            'movs r4, #0\nldrsh r0, [r0, r4]\nsubs r0, r0, r2\nstrh r0, [r3]\n'
            'ldrh r0, [r5, #38]\nsubs r1, r1, r0\n' + incoming + '\n' + output + '\n'
            'add sp, #8\npop {r3, r4}\n' + restore + '\nmov r9, r4\n'
            'pop {r4, r5, r6, r7}\npop {r0}\nbx r0\n.balign 4, 0\nliteral: .word 0x02007F40\nhelper_end:\n')
        for command in (
            ['arm-none-eabi-as', '-mthumb-interwork', str(source), '-o', str(self.root/'f.o')],
            ['arm-none-eabi-ld', '-Ttext=0x08010000', '-e', 'helper', str(self.root/'f.o'), '-o', str(self.root/'f.elf')],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root/'f.elf').read_bytes())
        end = next(row['value'] for row in image['symbols'] if row['name'] == 'helper_end')
        address = 0x08010000
        data = image['text'][:end-address]
        mapping = json.dumps([dict(rom=hex(address), end=hex(end), mode='thumb', instrs=0)]).encode()
        refinement = owner.refine(data, address, mapping)
        ins, edges, branches, calls, words = owner.graph.graph(data, address, refinement)
        self.assertFalse(branches or calls or words)
        partition = owner.graph.partition(data, address, refinement, ins, words)
        return dict(instructions=ins, edges=edges, address=address, data=data, partition=partition,
            data_mapping=json.dumps({effects.NAME: f'0x{effects.GLOBAL:08X}'}).encode(), policy=effects.named_policy())

    def test_initialized_local_reads_and_both_outputs_retain_entry_r8(self):
        proof = effects.prove_origins(**self.fixture())
        self.assertEqual([r[1:] for r in proof['formal_writes']],
                         [[['formal', 3], 0, 2], [['incoming', 0], 0, 2]])
        self.assertEqual(proof['return_entry_origins'], [[3, 8]])
        self.assertEqual(len(proof['local_halfword_reads']), 2)
        self.assertFalse(proof['caller_bounds_proved'])

    def test_readable_initialized_named_premise_is_distinct_and_exact(self):
        fixture = self.fixture()
        for change in (dict(policy=None), dict(policy=dict(effects.named_policy(), initialized=False)),
                       dict(policy=dict(effects.named_policy(), initialized=1)),
                       dict(policy=dict(effects.named_policy(), reads=[[32, 2], [34, 2]])),
                       dict(data_mapping=b'{}')):
            with self.subTest(change=change), self.assertRaises(ValueError):
                effects.prove_origins(**dict(fixture, **change))

    def test_uninitialized_local_read_and_pointer_spill_are_rejected(self):
        for first_store in ('movs r4, #0', 'strh r3, [r6]'):
            with self.subTest(first_store=first_store), self.assertRaises(ValueError):
                effects.prove_origins(**self.fixture(first_store=first_store))

    def test_entry_word_and_output_domains_cannot_be_widened(self):
        for change in (dict(incoming='ldr r7, [sp, #40]'), dict(incoming='adds r7, r6, #0'),
                       dict(output='strh r1, [r7, #2]'), dict(named='ldrh r7, [r5, #40]')):
            with self.subTest(change=change), self.assertRaises(ValueError):
                effects.prove_origins(**self.fixture(**change))

    def test_preserved_entry_origin_cannot_be_replaced_by_scalar(self):
        with self.assertRaisesRegex(ValueError, 'restore'):
            effects.prove_origins(**self.fixture(restore='mov r8, r0'))

    def test_instruction_bytes_and_complete_edges_are_bound(self):
        fixture = self.fixture()
        edges = dict(fixture['edges'])
        edges[fixture['address']] = ()
        for change in (dict(data=b'\0\0' + fixture['data'][2:]), dict(edges=edges)):
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'exact narrow'):
                effects.prove_origins(**dict(fixture, **change))


if __name__ == '__main__':
    unittest.main(verbosity=2)
