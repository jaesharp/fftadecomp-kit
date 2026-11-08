"""New synthetic cases for the CA78-style scalar/output-origin adapter."""
from pathlib import Path
import struct
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import three_halfword_output_buffer_profile as outputs

A = 0x08006000


def body(*, extra=None, add0=7, add1=9, add2=16):
    words = [0xb530, 0x9c03, 0x9d04, 0x0400, 0x12c0,
             0x3000 | add0, 0x8018, 0x0109, 0x3100 | add1,
             0x8021, 0x0412, 0x12d2, 0x3200 | add2, 0x802a,
             0xbc30, 0xbc01, 0x4700]
    if extra is not None:
        words.insert(5, extra)
    return struct.pack('<' + 'H' * len(words), *words)


def prove(data, *, flag=True, base=A, edit_edges=None):
    cs = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    cs.detail = True
    ins = {i.address: i for i in cs.disasm(data, base)}
    edges = {s: (() if i.mnemonic == 'bx' else (s + i.size,)) for s, i in ins.items()}
    if edit_edges:
        edit_edges(edges)
    return outputs.prove_leaf_origins(ins, edges, base, data, scalar_immediate_add=flag)


class ScalarOutputAdditionTests(unittest.TestCase):
    def test_three_scalar_additions_preserve_exact_effects_and_return_aliases(self):
        result = prove(body())
        self.assertEqual([x[1:] for x in result['formal_writes']],
            [[['formal', 3], 0, 2], [['incoming', 0], 0, 2], [['incoming', 4], 0, 2]])
        self.assertEqual(result['return_entry_origins'], [[3, 3], [12, 12]])
        self.assertEqual([x[1:] for x in result['scalar_immediate_additions']],
                         [[0, 7], [1, 9], [2, 16]])

    def test_default_policy_keeps_scalar_addition_refusal(self):
        with self.assertRaisesRegex(ValueError, 'unsupported'):
            prove(body(), flag=False)

    def test_opt_in_rejects_non_boolean_values(self):
        for flag in (0, 1, None, 'yes'):
            with self.subTest(flag=flag), self.assertRaisesRegex(ValueError, 'Boolean'):
                prove(body(), flag=flag)

    def test_formal_pointer_arithmetic_rejected(self):
        with self.assertRaisesRegex(ValueError, 'pointer or saved origin'):
            prove(body(extra=0x3301))

    def test_incoming_pointer_arithmetic_rejected(self):
        for word in (0x3401, 0x3501):
            with self.subTest(word=word), self.assertRaisesRegex(ValueError, 'pointer or saved origin'):
                prove(body(extra=word))

    def test_opaque_saved_register_arithmetic_rejected(self):
        with self.assertRaisesRegex(ValueError, 'pointer or saved origin'):
            prove(body(extra=0x3601))

    def test_immediate_range_does_not_change_formal_write_extent(self):
        for addend in (0, 1, 127, 128, 255):
            with self.subTest(addend=addend):
                result = prove(body(add0=addend, add1=addend, add2=addend))
                self.assertEqual([x[-1] for x in result['formal_writes']], [2, 2, 2])
                self.assertFalse(result['numeric_equivalence_claim'])

    def test_nonzero_output_offset_still_rejected(self):
        data = bytearray(body())
        struct.pack_into('<H', data, 12, 0x8058)
        with self.assertRaisesRegex(ValueError, 'formal halfword bound'):
            prove(bytes(data))

    def test_wrong_incoming_stack_word_still_rejected(self):
        data = bytearray(body())
        struct.pack_into('<H', data, 4, 0x9d05)
        with self.assertRaisesRegex(ValueError, 'two incoming pointer words'):
            prove(bytes(data))

    def test_missing_save_restoration_still_rejected(self):
        data = bytearray(body())
        struct.pack_into('<H', data, 28, 0xbc10)
        with self.assertRaisesRegex(ValueError, 'restoration'):
            prove(bytes(data))

    def test_alternate_cfg_edge_still_rejected(self):
        with self.assertRaisesRegex(ValueError, 'complete edges'):
            prove(body(), edit_edges=lambda edges: edges.update({A + 10: (A + 14,)}))

    def test_relocated_leaf_is_not_an_address_whitelist(self):
        result = prove(body(), base=A + 0x400)
        self.assertEqual(result['scalar_immediate_additions'][0][0], A + 0x40a)

    def test_no_physical_capacity_or_numeric_claim_is_added(self):
        result = prove(body())
        for flag in ('caller_bounds_proved', 'numeric_equivalence_claim', 'physical_nonalias_claim'):
            self.assertFalse(result[flag])


if __name__ == '__main__':
    unittest.main()
