"""Original ELF authentication with exactly three conditional incoming words."""
import hashlib
import importlib
import json
import argparse
import subprocess
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import canonical_integer_native_profile as strict
import match
import owner_admission_profile as owner
from test_canonical_integer_native_profile import BASE, fixture, symbol_change


def incoming(prefix=(0xB500, 0x9801, 0x9902, 0x9A03), suffix=(0xBC02, 0x4708), family='__modsi3'):
    return fixture(family, prefix=prefix, suffix=suffix)


class ThreeIncomingWordsTests(unittest.TestCase):
    def setUp(self):
        self.closure = patch.object(strict.scalar, 'prove_called_closures', return_value=({}, {}, []))
        self.prove = self.closure.start()
        self.addCleanup(self.closure.stop)

    def profile(self):
        native = importlib.import_module('canonical_integer_three_words_native_profile')
        environment = patch.object(native, 'environment_fingerprint', return_value={'synthetic': True})
        environment.start()
        self.addCleanup(environment.stop)
        return native

    def test_exact_three_incoming_words_are_unknown_conditional_ABI_values(self):
        native = self.profile()
        result, count = native.verify_original(*incoming())
        self.assertEqual(count, 7)
        proof = result['prerequisite']
        self.assertEqual(proof['entry_stack_policy']['words'], [0, 1, 2])
        self.assertEqual({row[1] for row in proof['frame']['entry_stack']['reads']}, {0, 4, 8})
        self.assertEqual(proof['entry_loaded_value_facts'], [])
        self.assertFalse(proof['physical_caller_stack_nonalias_proof'])
        self.assertFalse(proof['arithmetic_C_equivalence'])
        self.assertEqual(proof['numeric_operand_preconditions'], [])

    def test_every_real_integer_alias_uses_the_same_three_word_contract(self):
        native = self.profile()
        for family in strict.scalar.OPERATIONS:
            with self.subTest(family=family):
                result, count = native.verify_original(*incoming(family=family))
                self.assertEqual(count, 7)
                self.assertEqual(result['prerequisite']['runtime_families'], [family])

    def test_default_scalar_selector_still_refuses_incoming_words(self):
        with patch.object(strict, 'environment_fingerprint', return_value={'synthetic': True}):
            with self.assertRaisesRegex(ValueError, 'established frame'):
                strict.verify_original(*incoming())
        self.prove.assert_not_called()

    def test_missing_third_reached_read_refuses(self):
        native = self.profile()
        with self.assertRaisesRegex(ValueError, 'exactly every declared'):
            native.verify_original(*incoming(prefix=(0xB500, 0x9801, 0x9902)))
        self.prove.assert_not_called()

    def test_fourth_incoming_word_is_outside_the_contract(self):
        native = self.profile()
        with self.assertRaisesRegex(ValueError, 'declared incoming'):
            native.verify_original(*incoming(prefix=(0xB500, 0x9801, 0x9902, 0x9A03, 0x9B04)))
        self.prove.assert_not_called()

    def test_incoming_store_does_not_get_readability_permission(self):
        native = self.profile()
        with self.assertRaisesRegex(ValueError, 'exact direct aligned'):
            native.verify_original(*incoming(prefix=(0xB500, 0x9801, 0x9902, 0x9A03, 0x9001)))
        self.prove.assert_not_called()

    def test_forming_an_SP_address_does_not_get_alias_permission(self):
        native = self.profile()
        with self.assertRaisesRegex(ValueError, 'SP addresses'):
            native.verify_original(*incoming(prefix=(0xB500, 0x9801, 0x9902, 0x9A03, 0xA801)))
        self.prove.assert_not_called()

    def test_return_must_restore_the_real_entry_LR(self):
        native = self.profile()
        with self.assertRaises(ValueError):
            native.verify_original(*incoming(suffix=(0xBC02, 0x4770)))
        self.prove.assert_not_called()

    def test_linked_nonrelocation_mutation_refuses(self):
        native = self.profile(); values = incoming(); raw = bytearray(values[1])
        image = match.elf_image(raw); section = image['sections'][image['text_index']]
        raw[section[4]+2] ^= 1; values[1] = bytes(raw)
        with self.assertRaisesRegex(ValueError, 'outside original call'):
            native.verify_original(*values)
        self.prove.assert_not_called()

    def test_original_undefined_symbol_must_keep_zero_size(self):
        native = self.profile(); values = incoming()
        values[0] = symbol_change(values[0], '__modsi3', 'size', 4)
        with self.assertRaisesRegex(ValueError, 'zero-sized'):
            native.verify_original(*values)
        self.prove.assert_not_called()

    def test_original_object_and_full_manifest_are_bound(self):
        native = self.profile(); values = incoming()
        result, _ = native.verify_original(*values)
        self.assertEqual(result['original_ET_REL_sha256'], hashlib.sha256(values[0]).hexdigest())
        self.assertEqual(result['linked_ELF_sha256'], hashlib.sha256(values[1]).hexdigest())
        self.assertEqual(result['profile'], native.SCHEMA)
        self.assertEqual(result['selector'], native.SELECTOR)

    def test_manifest_cannot_change_the_number_of_incoming_words(self):
        native = self.profile(); values = incoming()
        result, _ = native.verify_original(*values)
        result['prerequisite']['entry_stack_policy']['words'].append(3)
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            native.verify_original(*values, manifest=result)

    def test_report_routes_only_the_new_closed_selector(self):
        native = self.profile(); values = incoming(); result, count = native.verify_original(*values)
        image = match.elf_image(values[1]); body = image['text']
        report = owner.render(BASE, (body, result, 'synthetic-source', values[4], values[5], b'{}', values[3], count, values[0]))
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), native.SELECTOR)
        self.assertIn(native.CONTROL_FLOW, report)
        evidence = json.loads(next(line for line in report.splitlines() if line.startswith('* owner runtime evidence: `')).split(': `', 1)[1][:-1])
        self.assertEqual(evidence['original_elf_sha256'], hashlib.sha256(values[0]).hexdigest())
        with self.assertRaisesRegex(ValueError, 'original ELF identity'):
            owner.fingerprint(BASE, body, result, 'synthetic-source', values[4], values[5], b'{}', values[3])

    def test_new_original_binding_selector_keeps_exact_scalar_roles(self):
        native = self.profile(); values = incoming(); image = match.elf_image(values[0])
        actual = owner.original_bindings(image, BASE, values[3], values[4], b'{}',
                                        selector=native.SELECTOR, index=values[5])
        strict_roles = owner.original_bindings(image, BASE, values[3], values[4], b'{}',
                                              selector=strict.SELECTOR, index=values[5])
        self.assertEqual(actual, strict_roles)
        self.assertEqual(actual[0], values[6])
        with self.assertRaises(ValueError):
            owner.original_bindings(image, BASE, values[3], values[4], b'{}', selector='undeclared')

    def test_source_cannot_declare_reserved_integer_helpers(self):
        native = self.profile(); values = incoming()
        runner = type('SourceOnly', (), {'read_binary': lambda self, path: b'extern int __modsi3(int, int);'})()
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        with self.assertRaisesRegex(ValueError, 'reserved for compiler emission'):
            owner.object_bytes(runner, 'unexecuted', args, match.elf_image(values[0]), BASE,
                               values[3], values[4], b'{}', selector=native.SELECTOR, index=values[5])

    def test_native_CLI_exposes_the_explicit_closed_selector(self):
        native = self.profile()
        run = subprocess.run([sys.executable, '-B', str(Path(match.__file__)), '--help'],
                             capture_output=True, text=True, check=True)
        self.assertIn(native.SELECTOR, run.stdout)
