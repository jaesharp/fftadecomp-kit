"""Double-to-float closure: complete native effects and strict ELF admission."""
from contextlib import contextmanager
import copy
import hashlib
import struct
import sys
from pathlib import Path
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import private_double_truncation_effects_inventory as inventory
import private_float_pack_admission_profile as admission
import software_float_profile as runtime
import test_private_float_pack_effects_inventory as base
import test_private_double_pack as double

A, U, P, C = base.ADDRESS, base.UNPACK, base.PACK, 0x08000380
words, call = base.words, base.call


def fixture(*, pointer=5, outside_pack=False, saved_store=False):
    unpack = words(0x6802, 0x6843, 0x600A, 0x604A, 0x608A,
                   0x60CA, 0x610A, 0x688A, 0x4770)
    pack = words(0x6801, 0x6841, 0x6881, 0x6900 if outside_pack else 0x68C0, 0x4770)
    constructor = words(0xB500, 0xB084, 0x9000, 0x9101, 0x9202,
                        0x9304 if saved_store else 0x9303, 0x4668)
    constructor += call(C+14, P)+words(0xB004, 0xBC02, 0x4708)
    caller = words(0xB500, 0xB087, 0x9005, 0x9106, 0xA800|pointer, 0x4669)
    caller += call(A+12, U)+words(0x9800, 0x9901, 0x9A02, 0x9B03)
    caller += call(A+24, C)+words(0xB007, 0xBC02, 0x4708)
    parts = {A: caller, U: unpack, P: pack, C: constructor}
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    counts = {start: len(list(decoder.disasm(body, start))) for start, body in parts.items()}
    rom, rows, mapping, index = base.image(parts, counts)
    helpers = tuple((role, (start, start+len(parts[start]), counts[start],
        hashlib.sha256(parts[start]).hexdigest()), bounds)
        for (role, _, bounds), start in zip(inventory.HELPERS, (U,P,C)))
    return caller, rom, rows, mapping, index, helpers


def elf_pair(body):
    original, linked = double.elf_pair(body)
    original['symbols'][2]['name'] = linked['symbols'][2]['name'] = f'func_{C:08X}'
    linked['symbols'][2]['value'] = C|1
    raw = bytearray(body)
    for site in (12,24): raw[site:site+4] = call(A+site,A+site)
    rels = b''.join(struct.pack('<II', site, number<<8|10)for site,number in((12,1),(24,2)))
    original.update(text=bytes(raw),section_data=[b'',bytes(raw),rels])
    return original, linked


class DoubleTruncationTests(unittest.TestCase):
    @contextmanager
    def closure(self, selected=None, *, edges=((C+14,P),), helpers=None):
        selected = fixture() if selected is None else selected
        with patch.object(inventory,'HELPERS',selected[-1]if helpers is None else helpers), \
                patch.object(runtime,'ROM_SHA256',hashlib.sha256(selected[1]).hexdigest()), \
                patch.object(runtime,'EDGES',edges):
            yield selected

    def verify(self, selected=None, **options):
        with self.closure(selected,**options)as(body,rom,_,mapping,index,_):
            return inventory.verify(body,A,rom,mapping,index,selector=inventory.SELECTOR)

    def test_complete_nested_effects_and_unknown_result(self):
        proof,_=self.verify()
        self.assertEqual(proof['external_reads'],[])
        self.assertEqual(proof['external_writes'],[])
        self.assertEqual(proof['helper_closure'][0]['native_proof']['argument_effects']['writes'],
                         [[1,offset,4]for offset in range(0,20,4)])
        self.assertEqual(proof['helper_closure'][1]['native_proof']['argument_effects']['reads'],
                         [[0,offset,4]for offset in range(0,16,4)])
        self.assertEqual(proof['helper_closure'][-1]['native_proof']['stack_reads'],[])
        self.assertFalse(proof['physical_memory_claim'])
        self.assertEqual(proof['numeric_return_facts'],[])

    def test_second_input_word_cannot_read_saved_or_incoming_words(self):
        for pointer in(6,7,8):
            with self.subTest(pointer=pointer),self.assertRaises(ValueError):self.verify(fixture(pointer=pointer))

    def test_float_packer_cannot_read_a_fifth_word(self):
        with self.assertRaisesRegex(ValueError,'external read'):self.verify(fixture(outside_pack=True))

    def test_constructor_cannot_store_into_saved_return(self):
        with self.assertRaises(ValueError):self.verify(fixture(saved_store=True))

    def test_only_completed_dependency_may_be_called(self):
        with self.assertRaisesRegex(ValueError,'completed native dependency'):
            self.verify(edges=((C+14,P+2),))

    def test_each_reached_unpack_or_pack_effect_requires_its_bound(self):
        selected=fixture()
        for helper in(0,1):
            specs=copy.deepcopy(selected[-1]);specs[helper][2]['reads'].pop()
            with self.subTest(helper=helper),self.assertRaises(ValueError):self.verify(selected,helpers=specs)

    def test_genuine_original_bindings_preserve_full_symbol(self):
        with self.closure()as(body,rom,_,mapping,index,_):
            original,linked=elf_pair(body);before=copy.deepcopy(original)
            calls,targets=admission.original_bindings(original,A,rom,mapping,index,
                selector=admission.DOUBLE_TRUNCATION_SELECTOR)
            self.assertEqual(calls,[[12,f'func_{U:08X}'],[24,f'func_{C:08X}']])
            self.assertEqual(admission.linked_bytes(original,linked,A,calls,targets,
                selector=admission.DOUBLE_TRUNCATION_SELECTOR),body)
            self.assertEqual(original,before)
            manifest,_=admission.verify(body,A,rom,mapping,index,calls,
                selector=admission.DOUBLE_TRUNCATION_SELECTOR)
            self.assertEqual(manifest['selector'],admission.DOUBLE_TRUNCATION_SELECTOR)
            changed=copy.deepcopy(original);changed['symbols'][2]['name']='__truncdfsf2'
            with self.assertRaises(ValueError):admission.original_bindings(changed,A,rom,mapping,index,
                selector=admission.DOUBLE_TRUNCATION_SELECTOR)
            with self.assertRaises(ValueError):admission.original_bindings(original,A,rom,mapping,index)

    def test_explicit_selector_manifest_and_dual_indices_are_required(self):
        with self.closure()as(body,rom,_,mapping,index,_):
            for selector,manifest in(('default',None),(inventory.SELECTOR,{})):
                with self.subTest(selector=selector),self.assertRaises(ValueError):
                    inventory.verify(body,A,rom,mapping,index,selector=selector,manifest=manifest)
            changed=index.replace(b'08000380 08000398 24 11',b'08000380 08000398 24 10')
            self.assertNotEqual(changed,index)
            with self.assertRaises(ValueError):inventory.verify(body,A,rom,mapping,changed,selector=inventory.SELECTOR)

    def test_report_and_cli_keep_the_distinct_profile(self):
        marker=f'* verification: `{admission.DOUBLE_TRUNCATION_SCHEMA}`\n* private float pack: `{admission.DOUBLE_TRUNCATION_SELECTOR}`\n'
        self.assertEqual(admission.selector_for_report(marker),admission.DOUBLE_TRUNCATION_SELECTOR)
        with self.assertRaises(ValueError):admission.selector_for_report(marker+marker)
        with patch.object(admission,'issue',return_value=123)as issue, \
                patch.object(sys,'argv',['match.py','08000100','--owner-runtime-profile',admission.DOUBLE_TRUNCATION_SELECTOR]):
            self.assertEqual(match.main(),123)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile,admission.DOUBLE_TRUNCATION_SELECTOR)


if __name__=='__main__':unittest.main(verbosity=2)
