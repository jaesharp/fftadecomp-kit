import json
from pathlib import Path
import struct
import sys
import unittest
W=Path(__file__).resolve().parents[1]
sys.dont_write_bytecode=True
sys.path.insert(0,str(W/'tools'))
from test_local_shadow_halfword_matrix import fixture
import local_shadow_matrix_elf_binding as binding
import match

def bl(site,target):
    delta=target-site-4
    return struct.pack('<HH',0xf000|((delta>>12)&2047),0xf800|((delta>>1)&2047))

def original_elf(env, helper_type=2, data_type=1, addend=0):
    raw_text=bytearray(env['data'])
    raw_text[66:70]=bl(env['root']+66,env['root']+66)
    struct.pack_into('<I',raw_text,92,addend)
    rows=[('',0,0,0,0),(f'func_{env["root"]:08X}',1,96,0x12,1),
          ('memcpy',0,0,0x10|helper_type,0),
          ('shadow_state',0,0,0x10|data_type,0)]
    strings=bytearray(b'\0');symbols=bytearray()
    for name,value,size,info,section in rows:
        offset=len(strings);strings+=name.encode()+b'\0'
        symbols+=struct.pack('<IIIBBH',offset,value,size,info,0,section)
    rel=struct.pack('<IIII',66,(2<<8)|10,92,(3<<8)|2)
    names=b'\0.text\0.symtab\0.strtab\0.rel.text\0.shstrtab\0'
    raw=bytearray(52);offsets=[]
    for part in (raw_text,symbols,strings,rel,names):
        while len(raw)%4:raw+=b'\0'
        offsets.append(len(raw));raw+=part
    sections=[(0,0,0,0,0,0,0,0,0,0),
        (1,1,6,0,offsets[0],96,0,0,4,0),
        (7,2,0,0,offsets[1],len(symbols),3,1,4,16),
        (15,3,0,0,offsets[2],len(strings),0,0,1,0),
        (23,9,0,0,offsets[3],len(rel),2,1,4,8),
        (33,3,0,0,offsets[4],len(names),0,0,1,0)]
    while len(raw)%4:raw+=b'\0'
    shoff=len(raw);raw+=b''.join(struct.pack('<10I',*row) for row in sections)
    raw[:16]=b'\x7fELF\x01\x01\x01'+b'\0'*9
    struct.pack_into('<HHIIIIIHHHHHH',raw,16,1,40,1,0,0,shoff,0,52,0,0,40,6,5)
    return bytes(raw)

def plan(env,raw=None):
    return binding.binding_plan(original_elf(env) if raw is None else raw,env['root'],env['rom'],
        env['mapping'],env['index'],env['objects'])

class BindingTests(unittest.TestCase):
    def test_genuine_function_and_object_bindings(self):
        env=fixture();result=plan(env)
        self.assertEqual(result['targets'],{'memcpy':(env['helper']|1,2),'shadow_state':(env['source'],1)})
        self.assertFalse(result['source_or_native_admission'])
        self.assertFalse(result['physical_access_granted'])

    def test_compiler_undefined_notype_is_transportable(self):
        env=fixture();self.assertEqual(plan(env,original_elf(env,0,0))['bindings'],
            dict(calls=[[66,'memcpy']],data=[[92,'shadow_state',0]],functions=[],switches=[]))

    def test_function_object_type_confusion_refused(self):
        env=fixture()
        for ft,dt in ((1,1),(2,2),(3,1),(2,3)):
            with self.assertRaises(ValueError):plan(env,original_elf(env,ft,dt))

    def test_nonzero_literal_addend_refused(self):
        env=fixture()
        for addend in (4,0xffffffff):
            with self.assertRaises(ValueError):plan(env,original_elf(env,addend=addend))

    def test_nonzero_call_addend_refused(self):
        env=fixture();raw=bytearray(original_elf(env));image=match.elf_image(raw)
        text=image['sections'][image['text_index']][4]
        raw[text+66:text+70]=bl(env['root']+66,env['root']+68)
        with self.assertRaises(ValueError):plan(env,bytes(raw))

    def test_unknown_original_identity_refused(self):
        env=fixture();raw=original_elf(env).replace(b'memcpy\0',b'memcpz\0')
        with self.assertRaises(ValueError):plan(env,raw)

    def test_defined_or_nonzero_external_symbol_refused(self):
        env=fixture();original=original_elf(env);image=match.elf_image(original)
        sym=next(section for section in image['sections'] if section[1]==2)[4]
        for field,fmt,value in ((4,'I',1),(14,'H',0xfff1)):
            raw=bytearray(original);struct.pack_into('<'+fmt,raw,sym+2*16+field,value)
            with self.assertRaises(ValueError):plan(env,bytes(raw))

    def test_duplicate_or_shifted_relocation_refused(self):
        env=fixture();original=original_elf(env);image=match.elf_image(original)
        rel=next(section for section in image['sections'] if section[1]==9)[4]
        for site in (66,90,88):
            raw=bytearray(original);struct.pack_into('<I',raw,rel+8,site)
            with self.assertRaises(ValueError):plan(env,bytes(raw))

    def test_original_instruction_change_refused(self):
        env=fixture();raw=bytearray(original_elf(env));image=match.elf_image(raw)
        raw[image['sections'][image['text_index']][4]+64]^=1
        with self.assertRaises(ValueError):plan(env,bytes(raw))

    def test_helper_and_canonical_data_point_authenticated(self):
        env=fixture();rom=bytearray(env['rom']);rom[env['helper']-0x08000000+26]^=1;env['rom']=bytes(rom)
        with self.assertRaises(ValueError):plan(env)
        env=fixture();env['objects']=json.dumps({'shadow_state':hex(env['source']),'alias':hex(env['source'])}).encode()
        with self.assertRaises(ValueError):plan(env)

if __name__=='__main__':
    unittest.main(verbosity=2)

