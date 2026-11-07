"""Fresh synthetic authority and live ELF transport guards, without old verifiers."""
import base64
import copy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import palette_certificate_authority as authority
import palette_original_transport as transport
import palette_native_closure as closure
from test_palette_native_closure import Fixture, A, H, DATA, elf, symbol, pin


class TransportTests(unittest.TestCase):
    def setUp(self):
        self.f = Fixture()
        prior = dict(address=A, end=A+len(self.f.body), instructions=9,
            source_sha256=closure.sha(self.f.source), ROM_sha256=closure.sha(self.f.rom),
            body_sha256=closure.sha(self.f.body), conditional_full_owner_closure=True,
            environment=closure.environment_fingerprint(),
            bindings=closure.bindings_for(self.f.c['inventory']),
            dependency_context=dict(helper=[H, H+2, 1, closure.sha(b'\x70\x47')]),
            native_admission=False, source_or_ELF_admission=False, physical_memory_permission=False,
            unconditional_termination=False,
            required_unproved_conditions=['synthetic explicit target ABI and memory conditions'])
        self.artifacts = dict(original=self.f.original, linked=self.f.linked,
                              closure=json.dumps(prior, sort_keys=True).encode())
        self.guard = patch.object(authority, 'TRUSTED_PINS', {k: pin(v) for k, v in self.artifacts.items()})
        self.guard.start(); self.addCleanup(self.guard.stop)
        self.bundle = authority.encode(self.artifacts)

    def args(self):
        return dict(original=self.f.original, linked=self.f.linked, address=A, rom=self.f.rom,
                    mapping=self.f.mapping, index=self.f.index, objects=self.f.objects,
                    source=self.f.source, bundle=self.bundle, selector=transport.SELECTOR)

    def verify(self, **changes):
        args=self.args(); args.update(changes)
        return transport.verify_original(**args)

    def test_conditional_transport_keeps_complete_frozen_conditions(self):
        result, count = self.verify()
        self.assertEqual(count, 9)
        self.assertEqual(result['transported_conditional_closure']['required_unproved_conditions'],
                         ['synthetic explicit target ABI and memory conditions'])
        self.assertTrue(result['fresh_fixed_compiler_source_replay_required'])
        for key in ('native_admission','source_or_ELF_admission','physical_memory_permission','unconditional_termination'):
            self.assertIs(result[key], False)

    def test_self_selected_artifact_digest_cannot_change_authority(self):
        forged = dict(self.artifacts, original=b'forged ELF')
        with self.assertRaisesRegex(ValueError, 'authority'): authority.encode(forged)

    def test_exact_artifact_keys_required(self):
        with self.assertRaisesRegex(ValueError, 'exact'): authority.encode(dict(self.artifacts, extra=b'x'))

    def test_mutable_artifact_refused(self):
        with self.assertRaises(ValueError): authority.encode(dict(self.artifacts, original=bytearray(self.f.original)))

    def test_bundle_roundtrip_is_canonical(self):
        self.assertEqual(authority.decode(self.bundle), self.artifacts)

    def test_noncanonical_bundle_refused(self):
        with self.assertRaisesRegex(ValueError, 'canonical'): authority.decode(b' '+self.bundle)

    def test_duplicate_bundle_member_refused(self):
        with self.assertRaisesRegex(ValueError, 'duplicate'): authority.decode(b'{"original":"AA==","original":"AA=="}')

    def test_malformed_base64_refused(self):
        values=json.loads(self.bundle); values['original']='!'
        with self.assertRaises(ValueError): authority.decode(json.dumps(values).encode())

    def test_bundle_bound_and_immutable_type(self):
        for raw in (bytearray(self.bundle), b' '*(authority.MAX_BUNDLE_BYTES+1)):
            with self.subTest(kind=type(raw).__name__),self.assertRaisesRegex(ValueError,'bounded'):
                authority.decode(raw)

    def test_nonfinite_bundle_refused(self):
        with self.assertRaisesRegex(ValueError,'nonfinite'): authority.decode(b'{"original":NaN}')

    def test_source_change_refused(self):
        with self.assertRaisesRegex(ValueError, 'premise differs'): self.verify(source=self.f.source+b' ')

    def test_selector_is_exact_and_explicit(self):
        with self.assertRaisesRegex(ValueError, 'explicit'): self.verify(selector=closure.SELECTOR)

    def test_rom_change_refused(self):
        with self.assertRaisesRegex(ValueError, 'premise differs'): self.verify(rom=self.f.rom+b'\0')

    def test_current_compiler_must_match_authenticated_lineage(self):
        changed=closure.environment_fingerprint(); changed['toolchain']=[['compiler','0'*64]]
        with patch.object(closure,'environment_fingerprint',return_value=changed),self.assertRaisesRegex(ValueError,'compiler differs'):
            self.verify()

    def test_changed_original_text_refused(self):
        text=bytearray(self.f.original_text); text[0]^=1
        original=elf(bytes(text),self.f.original_symbols,self.f.relocations)
        with self.assertRaisesRegex(ValueError, 'compiler text'): self.verify(original=original)

    def test_changed_original_relocation_identity_refused(self):
        symbols=copy.deepcopy(self.f.original_symbols); symbols[2]['name']='impostor'
        original=elf(bytes(self.f.original_text),symbols,self.f.relocations)
        with self.assertRaisesRegex(ValueError, 'relocation differs'): self.verify(original=original)

    def test_extra_original_unresolved_symbol_refused(self):
        symbols=self.f.original_symbols+[symbol('foreign',0,0)]
        with self.assertRaisesRegex(ValueError, 'unresolved'): self.verify(original=elf(bytes(self.f.original_text),symbols,self.f.relocations))

    def test_nonallocated_file_metadata_can_differ(self):
        symbols=self.f.original_symbols+[symbol('fresh-source-file.c',4,0xfff1,bind=0)]
        result,_=self.verify(original=elf(bytes(self.f.original_text),symbols,self.f.relocations))
        self.assertTrue(result['conditional_original_ELF_transport'])

    def test_foreign_allocated_section_refused(self):
        with self.assertRaises(ValueError): self.verify(original=elf(bytes(self.f.original_text),self.f.original_symbols,self.f.relocations,extra_allocated=True))

    def test_changed_complete_func_extent_refused(self):
        symbols=copy.deepcopy(self.f.original_symbols); symbols[1]['size']-=2
        with self.assertRaises(ValueError): self.verify(original=elf(bytes(self.f.original_text),symbols,self.f.relocations))

    def test_changed_linked_body_refused(self):
        body=bytearray(self.f.body); body[0]^=1
        with self.assertRaisesRegex(ValueError,'linked body'): self.verify(linked=elf(bytes(body),self.f.linked_symbols,[],linked=True))

    def test_changed_linked_typed_identity_refused(self):
        symbols=copy.deepcopy(self.f.linked_symbols); symbols[2]['type']=1
        with self.assertRaisesRegex(ValueError,'typed linked'): self.verify(linked=elf(self.f.body,symbols,[],linked=True))

    def test_changed_named_object_map_refused(self):
        values={name:f'0x{point+4:08X}'for name,point in DATA.items()}
        with self.assertRaisesRegex(ValueError,'typed linked'): self.verify(objects=json.dumps(values).encode())

    def test_changed_owner_count_refused(self):
        rows=json.loads(self.f.mapping); rows[0]['instrs']+=1
        with self.assertRaises(ValueError): self.verify(mapping=json.dumps(rows).encode())

    def test_changed_helper_count_refused(self):
        rows=json.loads(self.f.mapping); rows[1]['instrs']+=1
        with self.assertRaises(ValueError): self.verify(mapping=json.dumps(rows).encode())

    def test_old_complete_closure_is_never_invoked(self):
        with patch.object(closure,'verify_original',side_effect=AssertionError('old complete closure replay')):
            result,_=self.verify()
        self.assertEqual(result['old_complete_closure_executions'],0)

    def test_manifest_tampering_refused_without_replaying_success(self):
        with self.assertRaisesRegex(ValueError,'manifest differs'): self.verify(manifest={'forged':True})


if __name__ == '__main__':
    unittest.main()
