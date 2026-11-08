"""New matrix/copy16 cases, compared with an independent raw Thumb executor."""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest

W = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0,str(W/'tools'))
import local_shadow_halfword_matrix as matrix

ROOT, HELPER, SOURCE = 0x08000200,0x08000400,0x03002000
ROM_BASE = 0x08000000

def fixture(root=ROOT,helper=HELPER,source=SOURCE):
    words=[0xb530,0xb088,0x1c05,0x1c0c,0x062d,0x0e2d,0x0624,0x0e24,
        0x4b12,0x8958,0xa904,0x8008,0x899a,0x4668,0x3012,0x8002,
        0xaa05,0x89d8,0x8010,0x8a18,0x8050,0xaa06,0x8a58,0x8010,
        0x8a98,0x8050,0xaa07,0x8ad8,0x8010,0x8b18,0x8050,0x4668,
        0x2210,0,0,0x0064,0x00ad,0x1964,0x4669,0x1908,0x2100,0x5e40,
        0xb008,0xbc30,0xbc02,0x4708,0,0]
    data=bytearray(struct.pack('<48H',*words));delta=helper-(root+66)-4
    struct.pack_into('<HH',data,66,0xf000|((delta>>12)&2047),0xf800|((delta>>1)&2047))
    struct.pack_into('<I',data,92,source)
    copy_words=[0xb530,0x1c05,0x1c2c,0x1c0b,0x2a0f,0xd919,
        0x1c18,0x4328,0x2103,0x4008,0x2800,0xd113,0x1c29,
        0xcb01,0xc101,0xcb01,0xc101,0xcb01,0xc101,0xcb01,0xc101,
        0x3a10,0x2a0f,0xd8f4,0x2a03,0xd904,0xcb01,0xc101,
        0x3a04,0x2a03,0xd8fa,0x1c0c,0x3a01,0x2001,0x4240,
        0x4282,0xd007,0x1c01,0x7818,0x7020,0x3301,0x3401,
        0x3a01,0x428a,0xd1f8,0x1c28,0xbc30,0xbc02,0x4708]
    helper_body=struct.pack('<49H',*copy_words)
    rom=bytearray(max(root+96,helper+98)-ROM_BASE)
    for a,b in ((root,data),(helper,helper_body)):
        rom[a-ROM_BASE:a-ROM_BASE+len(b)]=b
    rows=[dict(rom=f'0x{a:08X}',end=f'0x{a+n:08X}',mode='thumb',instrs=c)
          for a,n,c in ((root,96,45),(helper,98,49))]
    return dict(root=root,helper=helper,source=source,data=bytes(data),rom=bytes(rom),
        mapping=json.dumps(rows).encode(),
        index=''.join(f'{a:08X} {a+n:08X} {n} {c} bx\n'
            for a,n,c in ((root,96,45),(helper,98,49))).encode(),
        objects=json.dumps({'shadow_state':f'0x{source:08X}'}).encode())

def prove(env):
    return matrix.prove(env['data'],env['root'],env['rom'],env['mapping'],env['index'],env['objects'])

def raw_run(env, row, column, sp, saved4, saved5, values):
    """Decode raw opcodes, perform concrete accesses, reject every unknown op.

    No production recognizer, transition, constants, graph or relation is used.
    """
    memory = {ROM_BASE+i:b for i,b in enumerate(env['rom'])}
    initial = [0x17395101+i*0x010101 for i in range(16)]
    memory.update({env['source']+10+i:b for i,b in enumerate(values)})
    initial[0], initial[1], initial[4], initial[5], initial[13], initial[14] = row,column,saved4,saved5,sp,0x09123457
    registers = list(initial)
    pc, zero, carry, writes, trace = env['root'],False,False,[],[]

    def read(address, size):
        return sum(memory[address+i] << (8*i) for i in range(size))

    def write(address, value, size):
        for i in range(size):
            memory[address+i] = (value >> (8*i)) & 255
            writes.append((address+i, memory[address+i]))

    def cmp(a,b):
        return a == b, a >= b

    def sign(value,bits):
        return value - (1 << bits) if value & (1 << (bits-1)) else value

    for _ in range(256):
        trace.append(pc)
        instruction = read(pc,2)
        next_pc = pc+2
        if instruction & 0xfe00 == 0xb400:
            regs = [r for r in range(8) if instruction & (1 << r)]
            if instruction & 256: regs.append(14)
            registers[13] -= 4*len(regs)
            for n,r in enumerate(regs):write(registers[13]+4*n,registers[r],4)
        elif instruction & 0xfe00 == 0xbc00:
            assert not instruction & 256
            for r in range(8):
                if instruction & (1 << r):
                    registers[r]=read(registers[13],4);registers[13]+=4
        elif instruction & 0xff00 == 0xb000:
            registers[13] += (-1 if instruction & 128 else 1)*4*(instruction & 127)
        elif instruction & 0xf800 == 0xf000:
            low = read(pc+2,2);assert low & 0xf800 == 0xf800
            delta = sign(((instruction & 2047) << 12) | ((low & 2047) << 1),23)
            registers[14]=pc+5;next_pc=pc+4+delta
        elif instruction & 0xff87 == 0x4700:
            value=registers[(instruction >> 3) & 15]
            assert value & 1
            if value == initial[14]:
                return dict(registers=registers,initial=initial,memory=memory,writes=writes,trace=trace)
            next_pc=value & ~1
        elif instruction & 0xff00 == 0x4600:
            destination=(instruction & 7) | ((instruction >> 4) & 8)
            registers[destination]=registers[(instruction >> 3) & 15]
        elif instruction & 0xf800 in (0x0000,0x0800):
            destination, source, shift = instruction & 7,(instruction >> 3) & 7,(instruction >> 6) & 31
            registers[destination] = ((registers[source] << shift) & 0xffffffff
                if instruction & 0xf800 == 0 else registers[source] >> (shift or 32))
        elif instruction & 0xf800 == 0x1800:
            destination, left = instruction & 7,(instruction >> 3) & 7
            right=(instruction >> 6) & 7
            value=right if instruction & 1024 else registers[right]
            registers[destination]=(registers[left]+(-value if instruction & 512 else value)) & 0xffffffff
        elif instruction & 0xf800 == 0x2000:
            registers[(instruction >> 8) & 7] = instruction & 255
        elif instruction & 0xf800 in (0x3000,0x3800):
            destination=(instruction >> 8) & 7
            registers[destination]=(registers[destination]+(-1 if instruction & 0x800 else 1)*(instruction & 255)) & 0xffffffff
        elif instruction & 0xf800 == 0x2800:
            zero,carry=cmp(registers[(instruction >> 8) & 7],instruction & 255)
        elif instruction & 0xffc0 == 0x4280:
            zero,carry=cmp(registers[instruction & 7],registers[(instruction >> 3) & 7])
        elif instruction & 0xffc0 == 0x4240:
            registers[instruction & 7]=(-registers[(instruction >> 3) & 7]) & 0xffffffff
        elif instruction & 0xf000 == 0xd000:
            condition=(instruction >> 8) & 15
            take={0:zero,1:not zero,8:(carry and not zero),9:(not carry or zero)}[condition]
            if take: next_pc=pc+4+sign(instruction & 255,8)*2
        elif instruction & 0xf800 == 0x4800:
            registers[(instruction >> 8) & 7]=read(((pc+4)&~3)+4*(instruction & 255),4)
        elif instruction & 0xf800 in (0x7800,0x8800):
            size=1 if instruction & 0xf800 == 0x7800 else 2
            address=registers[(instruction >> 3) & 7]+size*((instruction >> 6)&31)
            registers[instruction & 7]=read(address,size)
        elif instruction & 0xf800 == 0x8000:
            write(registers[(instruction >> 3)&7]+2*((instruction >> 6)&31),registers[instruction&7],2)
        elif instruction & 0xf800 == 0xa800:
            registers[(instruction >> 8)&7] = registers[13]+4*(instruction&255)
        elif instruction & 0xfe00 == 0x5e00:
            address=registers[(instruction>>3)&7]+registers[(instruction>>6)&7]
            registers[instruction&7]=sign(read(address,2),16)&0xffffffff
        elif instruction & 0xffc0 in (0x4000,0x4300):
            dest=instruction&7;right=registers[(instruction>>3)&7]
            registers[dest] = registers[dest]&right if instruction&0xffc0==0x4000 else registers[dest]|right
        elif instruction & 0xf800 in (0xc000,0xc800):
            base=(instruction>>8)&7
            assert not instruction&(1<<base)
            for register in range(8):
                if instruction&(1<<register):
                    if instruction&0xf800==0xc800:registers[register]=read(registers[base],4)
                    else:write(registers[base],registers[register],4)
                    registers[base]+=4
        elif instruction & 0xf800 == 0x7000:
            write(registers[(instruction >> 3)&7]+((instruction >> 6)&31),registers[instruction&7],1)
        else:
            raise AssertionError(f'unsupported raw opcode {instruction:04X} at {pc:08X}')
        pc=next_pc
    raise AssertionError('raw execution exceeded closed instruction bound')

class MatrixTests(unittest.TestCase):
    def test_complete_conditional_partition(self):
        result=prove(fixture())
        self.assertEqual(result['instructions'],45)
        self.assertEqual(result['helper_instructions'],49)
        self.assertEqual(len(result['cases']),8)
        self.assertFalse(result['physical_access_proved'])
        self.assertFalse(result['source_or_ELF_admission'])
        self.assertFalse(result['source_bytes_known'])

    def test_relocated_owner_helper_and_named_point(self):
        result=prove(fixture(0x08001000,0x08000800,0x02003102))
        self.assertEqual(result['helper'],0x08000800)
        self.assertEqual(result['shadow_point'],0x02003102)

    def test_opaque_halfwords_stay_opaque(self):
        values=tuple(f'unknown_byte_{i}' for i in range(16))
        for row in range(4):
            for col in range(2):
                result=matrix.relation(values,row,col)
                self.assertEqual(result['result']['little_endian_bytes'],list(values[4*row+2*col:4*row+2*col+2]))
                self.assertNotIn('u32',result['result'])
                self.assertEqual(result['copy_words'],4)

    def test_raw_oracle_all_indices_sign_boundaries_and_saves(self):
        env=fixture()
        for values in (struct.pack('<8H',0,1,0x7fff,0x8000,0xffff,0x1234,0x5678,0xabcd),bytes(range(16))):
            for sp in (0x02001000,0x03003000):
                for row in range(4):
                    for col in range(2):
                        raw=raw_run(env,0xaabbcc00|row,0x12345600|col,sp,0xdeadbeef,0x1234abcd,values)
                        effect=matrix.relation(values,row,col,saved=dict(R4=0xdeadbeef,R5=0x1234abcd,LR=0x09123457,BL=env['root']+71))
                        self.assertEqual(raw['registers'][0],effect['result']['u32'])
                        self.assertEqual(raw['registers'][1],effect['final_R1'])
                        self.assertEqual(raw['registers'][2],0xffffffff)
                        self.assertEqual(raw['registers'][3],sp-12)
                        self.assertEqual(raw['registers'][4:6],[0xdeadbeef,0x1234abcd])
                        self.assertEqual(raw['registers'][13],sp)
                        self.assertEqual(raw['writes'],[(sp+off,value) for phase,off,value in effect['writes']])
                        self.assertEqual(sum(pc in [env['helper']+x for x in (26,30,34,38)] for pc in raw['trace']),4)
                        self.assertNotIn(env['helper']+76,raw['trace'])

    def test_expired_pointer_is_not_erased(self):
        result=matrix.relation(bytes(16),0,0)
        self.assertEqual(result['final_R3'],dict(kind='entry_SP_relative_pointer',offset=-12,lifetime='expired',dereference_permission=False))

    def test_each_owner_instruction_mutation_refused(self):
        for offset in range(0,92,2):
            env=fixture();data=bytearray(env['data']);data[offset]^=1;env['data']=bytes(data)
            rom=bytearray(env['rom']);rom[ROOT-ROM_BASE:ROOT-ROM_BASE+96]=data;env['rom']=bytes(rom)
            with self.assertRaises(ValueError,msg=str(offset)):prove(env)

    def test_each_helper_halfword_mutation_refused(self):
        for offset in range(0,98,2):
            env=fixture();rom=bytearray(env['rom']);rom[HELPER-ROM_BASE+offset]^=1;env['rom']=bytes(rom)
            with self.assertRaises(ValueError,msg=str(offset)):prove(env)

    def test_both_counts_must_be_exact(self):
        for which,count in ((0,44),(0,48),(1,48),(1,50)):
            env=fixture();rows=json.loads(env['mapping']);rows[which]['instrs']=count;env['mapping']=json.dumps(rows).encode()
            with self.assertRaises(ValueError):prove(env)
        env=fixture();env['index']=env['index'].replace(b'96 45 ',b'96 48 ')
        with self.assertRaises(ValueError):prove(env)

    def test_named_point_requires_unique_identity(self):
        for objects in ({},{'a':hex(SOURCE),'b':hex(SOURCE)},{'a':hex(SOURCE+2)}):
            env=fixture();env['objects']=json.dumps(objects).encode()
            with self.assertRaises(ValueError):prove(env)

    def test_complete_root_extent_and_current_rom(self):
        env=fixture();env['data']=env['data'][:-2]
        with self.assertRaises(ValueError):prove(env)
        env=fixture();rom=bytearray(env['rom']);rom[ROOT-ROM_BASE+18]^=1;env['rom']=bytes(rom)
        with self.assertRaises(ValueError):prove(env)

    def test_independent_index_domains(self):
        for row,col in ((4,0),(0,2),(-1,0),(0,-1),(True,0),(0,False)):
            with self.assertRaises(ValueError):matrix.relation(bytes(16),row,col)

    def test_numeric_domain_has_no_access_grant(self):
        result=matrix.concrete_domain(0x02001000,0x123403,0xffff01,SOURCE,ROOT,HELPER)
        self.assertEqual((result['row'],result['column']),(3,1))
        self.assertFalse(result['physical_access_granted'])
        self.assertFalse(result['initialized_values_assumed'])

    def test_frame_alignment_wrap_and_overlap_refused(self):
        for sp,shadow in ((0,SOURCE),(55,SOURCE),(0x02001002,SOURCE),(SOURCE+26,SOURCE),
                          (0x02001000,0x02000fea),(ROOT+40,SOURCE),(HELPER+40,SOURCE),
                          (0x02001000,0xfffffff0),(0x02001000,SOURCE+1)):
            with self.assertRaises(ValueError):matrix.concrete_domain(sp,0,0,shadow,ROOT,HELPER)

    def test_short_unknown_and_invalid_byte_vectors_refused(self):
        for value in (b'',bytes(15),bytes(17),list(range(16)),tuple([None]*16),tuple([-1]*16)):
            with self.assertRaises(ValueError):matrix.relation(value,0,0)

    def test_protected_save_identity_required(self):
        for saved in ({},{'R4':0,'R5':0,'LR':0,'BL':-1},{'R4':False,'R5':0,'LR':0,'BL':0}):
            with self.assertRaises(ValueError):matrix.relation(bytes(16),0,0,saved=saved)

if __name__=='__main__':
    unittest.main(verbosity=2)
