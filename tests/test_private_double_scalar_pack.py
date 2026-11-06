"""A single double packer may access only its caller's live local record."""
from contextlib import contextmanager
import copy
import hashlib
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import private_double_scalar_pack_effects_inventory as inventory
import private_float_pack_admission_profile as admission
import software_float_profile as runtime
import test_private_float_pack_effects_inventory as base

A, P = base.ADDRESS, base.PACK
words, call = base.words, base.call
SELECTOR = admission.DOUBLE_SCALAR_PACK_SELECTOR


def fixture(*, pointer=0, pack=None, target=P):
    if pack is None:
        pack = words(0x6801,0x6841,0x6881,0x68C1,0x6900,0x4770)
    body = words(0xB500,0xB085,0xA800|pointer)
    body += call(A+6,target)+words(0xB005,0xBC02,0x4708)
    parts = {A:body,P:pack}
    decoder = match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB)
    counts = {a:len(list(decoder.disasm(data,a))) for a,data in parts.items()}
    rom,rows,mapping,index = base.image(parts,counts)
    role,_,bounds = inventory.HELPERS[-1]
    helpers = ((role,(P,P+len(pack),counts[P],hashlib.sha256(pack).hexdigest()),bounds),)
    return body,rom,rows,mapping,index,helpers


def elf_pair(body):
    symbols = [dict(name=f'func_{A:08X}',type=2,bind=1,section=1,value=1,size=len(body)),
               dict(name=f'func_{P:08X}',type=2,bind=1,section=0,value=0,size=0)]
    original = body[:6]+call(A+6,A+6)+body[10:]
    rels = struct.pack('<II',6,1<<8|10)
    image = dict(type=1,text_index=1,text=original,symbols=symbols,
        sections=[(0,)*10,(0,1,6,0,0,len(body),0,0,4,0),
                  (0,9,0,0,0,len(rels),3,1,4,8)],
        symbol_tables={3:symbols},relocations=[2],section_data=[b'',original,rels])
    linked = copy.deepcopy(image)
    linked.update(type=2,text=body,relocations=[])
    linked['sections'][1] = (0,1,6,A,0,len(body),0,0,4,0)
    linked['symbols'][0]['value'] = A|1
    linked['symbols'][1].update(value=P|1,section=0xFFF1)
    return image,linked


class DoubleScalarPackTests(unittest.TestCase):
    @contextmanager
    def closure(self, selected=None, *, helpers=None, edges=()):
        selected = fixture() if selected is None else selected
        with patch.object(inventory,'HELPERS',selected[-1] if helpers is None else helpers), \
                patch.object(runtime,'ROM_SHA256',hashlib.sha256(selected[1]).hexdigest()), \
                patch.object(runtime,'EDGES',edges):
            yield selected

    def verify(self, selected=None, **options):
        with self.closure(selected,**options) as (body,rom,_,mapping,index,_):
            return inventory.verify(body,A,rom,mapping,index,selector=inventory.SELECTOR)

    def test_twenty_byte_reads_are_discharged_into_live_local_record(self):
        proof,_ = self.verify()
        self.assertEqual(proof['helper_closure'][0]['native_proof']['argument_effects']['reads'],
                         [[0,offset,4] for offset in range(0,20,4)])
        self.assertEqual(proof['external_reads'],[])
        self.assertEqual(proof['external_writes'],[])
        self.assertTrue(all(v[-1][:2]==['stack',0] for v in proof['caller']['argument_accesses']))
        self.assertEqual(proof['numeric_input_preconditions'],[])
        self.assertEqual(proof['numeric_return_facts'],[])
        self.assertFalse(proof['source_or_ELF_admission'])
        self.assertFalse(proof['physical_memory_claim'])

    def test_complete_shift_dependency_is_proved_before_the_packer(self):
        wide = base.UNPACK
        helper = words(0x2000,0x2100,0x4770)
        pack = words(0xB510,0x1C04,0x6820,0x6861,0x68A2,0x68E3,0x6920)
        pack += call(P+14,wide)+words(0xBC10,0xBC02,0x4708)
        body,_,_,_,_,specs = fixture(pack=pack)
        parts = {A:body,wide:helper,P:pack}
        decoder = match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB)
        counts = {a:len(list(decoder.disasm(data,a))) for a,data in parts.items()}
        rom,rows,mapping,index = base.image(parts,counts)
        wide_spec = ('private-wide-shift',(wide,wide+len(helper),counts[wide],
            hashlib.sha256(helper).hexdigest()),inventory.policy())
        selected = body,rom,rows,mapping,index,(wide_spec,specs[0])
        proof,_ = self.verify(selected,edges=((P+14,wide),))
        self.assertEqual(proof['helper_closure'][-1]['calls'],[(P+14,wide)])
        with self.assertRaisesRegex(ValueError,'completed native dependency'):
            self.verify(selected,helpers=(specs[0],),edges=((P+14,wide),))

    def test_record_may_not_cross_saved_or_incoming_words(self):
        for pointer in (1,2,6):
            with self.subTest(pointer=pointer),self.assertRaises(ValueError):
                self.verify(fixture(pointer=pointer))

    def test_every_actual_read_requires_its_own_bound(self):
        selected = fixture()
        for n in range(5):
            helpers = copy.deepcopy(selected[-1]);helpers[0][2]['reads'].pop(n)
            with self.subTest(read=n),self.assertRaises(ValueError):
                self.verify(selected,helpers=helpers)

    def test_packer_cannot_write_external_record_or_add_hidden_dependency(self):
        with self.assertRaises(ValueError):self.verify(fixture(pack=words(0x6001,0x4770)))
        with self.assertRaisesRegex(ValueError,'completed native dependency'):
            self.verify(edges=((P,P+0x80),))
        with self.assertRaisesRegex(ValueError,'structural inventory is not closed'):
            self.verify(fixture(target=P+2))

    def test_exact_helper_identity_and_dual_index_are_required(self):
        selected = fixture();helpers = list(selected[-1]);role,(start,end,count,digest),bounds=helpers[0]
        helpers[0] = role,(start,end,count+1,digest),bounds
        with self.assertRaises(ValueError):self.verify(selected,helpers=helpers)
        with self.closure() as (body,rom,rows,mapping,index,_):
            rows[-1]['instrs'] += 1
            with self.assertRaises(ValueError):
                inventory.verify(body,A,rom,json.dumps(rows).encode(),index,selector=inventory.SELECTOR)
            for selector,manifest in [('default',None),(inventory.SELECTOR,{})]:
                with self.subTest(selector=selector),self.assertRaises(ValueError):
                    inventory.verify(body,A,rom,mapping,index,selector=selector,manifest=manifest)

    def test_genuine_original_binding_and_complete_symbol_are_preserved(self):
        with self.closure() as (body,rom,_,mapping,index,_):
            original,linked = elf_pair(body);before=copy.deepcopy(original)
            calls,targets = admission.original_bindings(original,A,rom,mapping,index,selector=SELECTOR)
            self.assertEqual(calls,[[6,f'func_{P:08X}']])
            self.assertEqual(admission.linked_bytes(original,linked,A,calls,targets,selector=SELECTOR),body)
            self.assertEqual(original,before)
            manifest,_ = admission.verify(body,A,rom,mapping,index,calls,selector=SELECTOR)
            self.assertEqual(manifest['selector'],SELECTOR)
            bad=copy.deepcopy(linked);bad['symbols'][0]['size']-=2
            with self.assertRaises(ValueError):
                admission.linked_bytes(original,bad,A,calls,targets,selector=SELECTOR)

    def test_other_alias_definitions_and_nonzero_addends_cannot_enter(self):
        with self.closure() as (body,rom,_,mapping,index,_):
            original,_=elf_pair(body)
            for kind in ('name','definition','addend'):
                bad=copy.deepcopy(original)
                if kind=='name':bad['symbols'][1]['name']='__floatsidf'
                elif kind=='definition':bad['symbols'][1]['section']=0xFFF1
                else:bad['text']=bad['text'][:6]+call(A+6,A+8)+bad['text'][10:]
                with self.subTest(kind=kind),self.assertRaises(ValueError):
                    admission.original_bindings(bad,A,rom,mapping,index,selector=SELECTOR)
            with self.assertRaises(ValueError):admission.original_bindings(original,A,rom,mapping,index)

    def test_report_and_cli_require_the_distinct_selector(self):
        marker=f'* verification: `{admission.DOUBLE_SCALAR_PACK_SCHEMA}`\n* private float pack: `{SELECTOR}`\n'
        self.assertEqual(admission.selector_for_report(marker),SELECTOR)
        with self.assertRaises(ValueError):admission.selector_for_report(marker+marker)
        with patch.object(admission,'issue',return_value=321) as issue, \
                patch.object(sys,'argv',['match.py','08000100','--owner-runtime-profile',SELECTOR]):
            self.assertEqual(match.main(),321)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile,SELECTOR)


if __name__=='__main__':unittest.main(verbosity=2)
