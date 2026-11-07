"""Exhaustive independent dispatch execution and opaque-byte regressions."""
from dataclasses import replace
import unittest

import scheduler_callback_dispatch as dispatch
from descriptor_partial_word_prerequisite import Word


def fixture(address=0x08001000):
    body=bytearray(658)
    words='b5f0 b084 1c06 1c0f 1c15 8839 2080 0040 4281 d044 4281 dc04 2900 d00d 2901 d03b e132 4804 4281 d100 e0ea 3001 4281 d100 e10a e129'
    body[:52]=b''.join(int(v,16).to_bytes(2,'little')for v in words.split())
    body[52:56]=(257).to_bytes(4,'little')
    body[648:]=bytes.fromhex('0020 04b0 f0bc 02bc 0847')
    return bytes(body),address


def registers():return {r:Word.unproved(f'entry-r{r}')for r in (*range(13),14)}
def bind():return dispatch.bind(*fixture(),selector=dispatch.SELECTOR)
def derive(phase=None,**changes):
    args=dict(binding=bind(),phase_word=Word.unproved('post-save-phase')if phase is None else phase,
              registers=registers(),entry_sp=-132,selector=dispatch.SELECTOR)
    args.update(changes)
    return dispatch.derive(**args)


def execute(body,address,phase):
    """Independent raw-halfword execution through dispatch/default return only."""
    regs={r:0x12340000+4*r for r in range(16)}
    regs.update({0:0x6000,1:0x2000,2:0x3000,13:0x10000,14:0x09000001})
    initial=dict(regs);memory={};pc=address;comparison=None;trace=[]
    stops={address+offset for offset in(56,152,158,512,584)}
    for _ in range(32):
        if pc in stops:return pc,trace,regs,initial
        trace.append(pc);offset=pc-address;op=int.from_bytes(body[offset:offset+2],'little');next_pc=pc+2
        if op&0xfe00==0xb400:
            selected=[r for r in range(8)if op>>r&1]+([14]if op&256 else [])
            regs[13]-=4*len(selected)
            for i,r in enumerate(selected):memory[regs[13]+4*i]=regs[r]
        elif op&0xfe00==0xbc00:
            selected=[r for r in range(8)if op>>r&1]
            for i,r in enumerate(selected):regs[r]=memory[regs[13]+4*i]
            regs[13]+=4*len(selected)
        elif op&0xff00==0xb000:regs[13]+=4*(op&127)*(-1 if op&128 else 1)
        elif op&0xffc0==0x1c00:regs[op&7]=regs[(op>>3)&7]
        elif op&0xf800==0x8800:
            if regs[(op>>3)&7]+2*((op>>6)&31)!=0x2000:raise AssertionError('unexpected data read')
            regs[op&7]=phase
        elif op&0xf800==0x2000:regs[(op>>8)&7]=op&255
        elif op&0xf800==0:regs[op&7]=(regs[(op>>3)&7]<<((op>>6)&31))&0xffffffff
        elif op&0xffc0==0x4280:comparison=(regs[op&7],regs[(op>>3)&7])
        elif op&0xf800==0x2800:comparison=(regs[(op>>8)&7],op&255)
        elif op&0xf000==0xd000:
            left,right=comparison;condition=(op>>8)&15
            signed=lambda v:v if v<0x80000000 else v-0x100000000
            if {0:left==right,1:left!=right,12:signed(left)>signed(right)}[condition]:
                next_pc=pc+4+2*((op&255)-256 if op&128 else op&255)
        elif op&0xf800==0xe000:
            immediate=op&2047;next_pc=pc+4+2*(immediate-2048 if immediate&1024 else immediate)
        elif op&0xf800==0x4800:
            literal=((pc+4)&~3)+4*(op&255)-address
            regs[(op>>8)&7]=int.from_bytes(body[literal:literal+4],'little')
        elif op&0xf800==0x3000:regs[(op>>8)&7]=(regs[(op>>8)&7]+(op&255))&0xffffffff
        elif op&0xff87==0x4700:
            if regs[(op>>3)&15]!=initial[14]:raise AssertionError('return origin changed')
            return None,trace,regs,initial
        else:raise AssertionError(f'unmodeled {pc:08X}:{op:04X}')
        pc=next_pc
    raise AssertionError('dispatch execution exceeded finite budget')


class DispatchTests(unittest.TestCase):
    def test_all65536_observed_phases_match_independent_raw_thumb(self):
        body,address=fixture();cases=derive()['cases'];counts={c['case']:0 for c in cases}
        for phase in range(65536):
            matching=[c for c in cases if c['guard'].get('equals')==phase or
                      ('inclusive_range'in c['guard']and c['guard']['inclusive_range'][0]<=phase<=c['guard']['inclusive_range'][1])]
            self.assertEqual(len(matching),1);case=matching[0];counts[case['case']]+=1
            stop,trace,regs,initial=execute(body,address,phase)
            self.assertEqual((stop,trace),(case['stop_before'],case['trace']))
            if stop is None:
                self.assertEqual(regs[0],0);self.assertEqual(regs[13],initial[13])
                self.assertEqual([regs[r]for r in range(4,13)],[initial[r]for r in range(4,13)])
        self.assertEqual(counts,{c['case']:c['compatible_phase_values']for c in cases})

    def test_opaque_phase_has_seven_disjoint_cases_without_initialization(self):
        r=derive();self.assertEqual(r['possible_phase_values'],65536);self.assertEqual(len(r['cases']),7)
        self.assertEqual(sum(c['compatible_phase_values']for c in r['cases']),65536)
        for key in('incoming_phase_initialization_proved','observed_phase_value_proved','whole_callback_CFG_closed','native_admission'):
            self.assertIs(r[key],False)

    def test_each_named_phase_stops_before_its_unproved_body(self):
        for value,offset in((0,56),(1,152),(256,158),(257,512),(258,584)):
            r=derive(Word.constant(value));self.assertEqual(len(r['cases']),1)
            case=r['cases'][0];self.assertEqual(case['stop_before'],fixture()[1]+offset)
            self.assertIsNone(case['conditional_result']);self.assertFalse(case['phase_body_effects_closed'])

    def test_partial_low_byte_preserves_every_compatible_high_byte(self):
        word=Word((('constant',0),('unproved','phase-high',1),('unproved','unused2',2),('unproved','unused3',3)))
        r=derive(word);self.assertEqual(r['possible_phase_values'],256)
        self.assertEqual({c['case']:c['compatible_phase_values']for c in r['cases']},
                         {'phase0':1,'phase256':1,'default259to65535':254})

    def test_unused_upper_word_bytes_do_not_become_phase_reads(self):
        word=Word((('constant',1),('constant',0),('pointer',24,2),('pointer',24,3)))
        r=derive(word);self.assertEqual(r['cases'][0]['case'],'phase1')
        self.assertEqual(r['observed_phase_atoms'],list(word.bytes[:2]))

    def test_phase_is_unsigned_halfword_at_high_bit_boundary(self):
        r=derive(Word.constant(0xffff));self.assertEqual(r['cases'][0]['case'],'default259to65535')
        self.assertEqual(r['cases'][0]['conditional_result'],0)

    def test_default_returns_retain_saved_origins_and_do_not_touch_payload(self):
        r=derive();origin=registers()
        for c in r['cases']:
            self.assertEqual(c['calls_executed'],[])
            self.assertFalse(any(e['role']=='payload'for e in c['ordered_accesses']))
            if c['stop_before']is None:
                self.assertEqual(c['return_SP'],-132)
                self.assertEqual(c['conditional_return_target'],list(origin[14].bytes))
                self.assertEqual(c['conditional_preserved_origins']['9'],list(origin[9].bytes))

    def test_literal_read_occurs_only_on_high_dispatch_arm(self):
        for c in derive()['cases']:
            reads=[e for e in c['ordered_accesses']if e['role']=='ROM']
            self.assertEqual(len(reads),int(c['case']in('phase257','phase258','default259to65535')))

    def test_relocated_complete_dispatch_keeps_relative_cutpoints(self):
        body,address=fixture(0x08009000);binding=dispatch.bind(body,address,selector=dispatch.SELECTOR)
        r=derive(Word.constant(258),binding=binding)
        self.assertEqual(r['cases'][0]['stop_before'],address+584)

    def test_mutated_dispatch_literal_or_return_refuses(self):
        body,address=fixture()
        for offset in(0,18,22,32,40,50,52,55,648,656):
            data=bytearray(body);data[offset]^=1
            with self.subTest(offset=offset),self.assertRaises(ValueError):
                dispatch.bind(bytes(data),address,selector=dispatch.SELECTOR)

    def test_complete_hash_binds_unexecuted_bytes_without_claiming_their_effects(self):
        original=bind();body=bytearray(original.body);body[600]^=1
        changed=dispatch.bind(bytes(body),original.address,selector=dispatch.SELECTOR)
        self.assertNotEqual(changed.sha256,original.sha256)
        self.assertFalse(derive(binding=changed)['whole_callback_CFG_closed'])
        with self.assertRaises(ValueError):derive(binding=replace(original,body=bytes(body)))

    def test_explicit_selector_identity_and_complete_span_required(self):
        body,address=fixture()
        for bad in(None,True,1,'ordinary'):
            with self.subTest(selector=bad),self.assertRaises(ValueError):dispatch.bind(body,address,selector=bad)
        for data,base in((body[:-1],address),(bytearray(body),address),(body,address+2),(body,True),(body,2**32-656)):
            with self.subTest(base=base),self.assertRaises(ValueError):dispatch.bind(data,base,selector=dispatch.SELECTOR)

    def test_pointer_phase_and_missing_register_origins_refuse(self):
        for word in(Word.pointer(-16),None,0):
            with self.subTest(word=word),self.assertRaises(ValueError):derive(word,phase_word=word)
        regs=registers();regs.pop(9)
        with self.assertRaises(ValueError):derive(registers=regs)
        for sp in(True,2,-772):
            with self.subTest(sp=sp),self.assertRaises(ValueError):derive(entry_sp=sp)


if __name__=='__main__':unittest.main()
