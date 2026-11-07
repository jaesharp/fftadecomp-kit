"""Independent bitvector oracles and closed synthetic Thumb value traces."""
from pathlib import Path
import hashlib
import struct
import sys
import unittest

sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import palette_value_composition as v

A=0x08004000


def machine(words,**kwargs):
    data=struct.pack('<'+'H'*len(words),*words)
    return v.Machine(data,A,{A+2*i for i in range(len(words))},kwargs.pop('literals',{}),
                     kwargs.pop('external_records',[]),**kwargs)


def copy_fixture():
    m=v.Machine(struct.pack('<HH',0xf000,0xf806),A,{A},{},[])
    row={'site':A,'consumer_sha256':hashlib.sha256(m.data).hexdigest(),'address':A+16,
         'source':-16,'destination':-32,'count':12,'preserved_registers':list(range(4,13)),
         'SP_restored':True,'returned_local_aliases':[[0,-32],[3,-4]],
         'transfers':[[-16+i,-32+i] for i in range(12)]}
    m.copy_observation=row
    s=v.State({0:('stack',-32),1:('stack',-16),2:v.constant(12),4:('opaque','saved4')},{},-48)
    for i in range(3):s.store_local(-16+4*i,4,('stack',-48+2*i))
    return m,s,row


def arithmetic_fixture():
    row={'entry':A,'exit':A+4,'entry_bindings':[[0,'adjustment_pointer'],[5,'channel_pointer'],[1,'channel_value'],[10,0]],
         'authenticated_entry_evidence':{'local_role_offsets':{'adjustment_pointer':[-8],'channel_pointer':[-12]}},
         'reached_sites':[A,A+2]}
    m=machine([0x2001,0x8069],arithmetic_regions=[row])
    s=v.State({0:('stack',-8),5:('stack',-12),1:v.constant(255),10:v.constant(0),4:('opaque','saved4')},
              {(-8,2):v.constant(0),(-12,2):v.constant(255)},-16)
    return m,s,row


class PaletteValueTests(unittest.TestCase):
    def test_affine_ring_canonicalization(self):
        x=('input','x',32)
        self.assertEqual(v.add(x,v.multiply(2,x),v.constant(-1),v.constant(2)),v.add(v.multiply(3,x),v.constant(1)))
        for n in (0,1,511,65535,0x80000000,0xffffffff):
            self.assertEqual(v.evaluate(v.add(x,x,v.multiply(3,x),v.constant(-7)),{'x':n}),(5*n-7)&v.MASK)

    def test_wrapped_last_matches_u16_reference(self):
        expression=v.reference_values()[-1]
        for first in (0,1,511,512,65535,0xffff0001):
            for count in (0,1,2,512,65535,0xabcd1234):
                self.assertEqual(v.evaluate(expression,{'r0':first,'r1':count}),((first&65535)+(count&65535)-1)&65535)

    def test_shift_narrowing_is_exact_for_word_inputs(self):
        x=('input','x',32)
        for amount in (0,5,10,16,24,31):
            for n in (0,1,255,65535,0x80000000,0xffffffff):
                self.assertEqual(v.evaluate(v.left(x,amount),{'x':n}),(n<<amount)&v.MASK)
                if amount:self.assertEqual(v.evaluate(v.right(v.left(x,amount),amount),{'x':n}),n&((1<<(32-amount))-1))

    def test_distinct_palette_reads_stay_distinct(self):
        a=v.constant(0x03001000)
        channels=[v.low(('read',0,2,a),5),v.right(v.band(('read',1,2,a),992),5),v.right(v.band(('read',2,2,a),31744),10)]
        values=[1,2<<5,3<<10]
        self.assertEqual([v.evaluate(x,{},values) for x in channels],[1,2,3])
        self.assertEqual(v.evaluate(v.pack_channels(channels),{},values),1|(2<<5)|(3<<10))

    def test_adjustment_all_signed_halfword_deltas(self):
        channel=('input','channel',8);delta=('input','delta',16);expression=v.adjust(channel,delta)
        for c in (0,31,255):
            for d in range(65536):
                total=(c+d)&65535;signed=total if total<32768 else total-65536
                expected=c if d==0 else min(max(signed,0),31)
                self.assertEqual(v.evaluate(expression,{'channel':c,'delta':d}),expected)

    def test_zero_delta_preserves_unrestricted_history_byte(self):
        self.assertEqual(v.adjust(v.constant(255),v.constant(0)),v.constant(255))
        c=('input','c',8);d=('input','d',16)
        self.assertEqual(v.bounds(v.adjust(c,d)),(0,255))
        self.assertEqual(v.evaluate(v.adjust(v.constant(1),v.constant(32767)),{}),0)

    def test_restore_pack_is_halfword_truncated_without_signed_overflow(self):
        channels=[('input',str(i),8) for i in range(3)]
        word=v.bor(channels[0],v.left(channels[1],5),v.left(channels[2],10))
        self.assertEqual(v.bounds(word),(0,262143))
        for values in ((255,255,255),(0,255,1),(31,0,255)):
            inputs={str(i):n for i,n in enumerate(values)}
            self.assertEqual(v.evaluate(v.pack_channels(channels),inputs),(values[0]|values[1]<<5|values[2]<<10)&65535)

    def test_local_pointer_rejects_symbolic_or_double_pointer_addition(self):
        self.assertEqual(v.add(('stack',-12),v.constant(-4)),('stack',-16))
        for value in (('input','i',2),('stack',-4)):
            with self.assertRaisesRegex(ValueError,'exact scalar offset'):v.add(('stack',-12),value)

    def test_local_width_alias_invalidates_prior_word(self):
        s=v.State({}, {},-16);s.store_local(-8,4,v.constant(0x12345678));s.store_local(-8,2,v.constant(3))
        self.assertEqual(s.load_local(-8,2),v.constant(3))
        with self.assertRaisesRegex(ValueError,'uninitialized'):s.load_local(-8,4)

    def test_protected_saves_cannot_be_rewritten_even_as_saves(self):
        s=v.State({}, {},-16);s.store_local(-4,4,('opaque','saved'),save=True)
        for save in (False,True):
            with self.assertRaisesRegex(ValueError,'protected saves'):s.store_local(-4,4,v.constant(0),save=save)

    def test_frame_bounds_alignment_and_pointer_width_are_enforced(self):
        s=v.State({}, {},-16)
        for offset,width in ((-20,4),(0,4),(-3,2),(-8,3)):
            with self.assertRaises(ValueError):s.store_local(offset,width,v.constant(0))
        with self.assertRaisesRegex(ValueError,'truncates'):s.store_local(-8,2,('stack',-12))

    def test_push_high_register_save_and_local_round_trip(self):
        m=machine([0xb510,0x4644,0xb410,0xb082,0x9000,0x9800])
        s=v.initial_state();out=m.run(A,s,{A+12})[0][1]
        self.assertEqual(out.sp,-20);self.assertEqual(out.value(0),s.value(0))
        self.assertEqual(out.memory[-12,4],s.value(8));self.assertEqual(len(out.protected),12)

    def test_word_literal_requires_declared_partition(self):
        m=machine([0x4800],literals={A+4:0x12345678})
        self.assertEqual(m.step(A,v.State({},{}))[0][1].value(0),v.constant(0x12345678))
        m.literals={}
        with self.assertRaisesRegex(ValueError,'literal differs'):m.step(A,v.State({},{}))

    def test_three_external_reads_use_event_identity(self):
        m=machine([0x8801,0x8802,0x8803],external_records=[['external-read',A+2*i,0x3001000,0x3001002,2] for i in range(3)])
        out=m.run(A,v.State({0:v.constant(0x3001000)},{}),{A+6})[0][1]
        self.assertEqual([row[4][1] for row in out.events],[0,1,2])
        self.assertEqual(len({out.value(i) for i in (1,2,3)}),3)

    def test_external_read_after_write_is_fresh(self):
        m=machine([0x8001,0x8802],external_records=[['external-write',A,0x3001000,0x3001002,2],['external-read',A+2,0x3001000,0x3001002,2]])
        out=m.run(A,v.State({0:v.constant(0x3001000),1:v.constant(7)},{}),{A+4})[0][1]
        self.assertEqual(out.value(2),('read',1,2,v.constant(0x3001000)))
        self.assertNotEqual(out.value(2),v.constant(7))

    def test_external_envelope_rejects_wrapping_or_outside_address(self):
        m=machine([0x8801],external_records=[['external-read',A,0x3001000,0x3001002,2]])
        for address in (v.constant(0x3001002),v.add(v.constant(0xfffffff0),('input','index',9))):
            with self.assertRaisesRegex(ValueError,'numerical footprint'):m.step(A,v.State({0:address},{}))

    def test_external_pointer_escape_refuses(self):
        m=machine([0x6001],external_records=[['external-write',A,0x3001000,0x3001004,4]])
        with self.assertRaisesRegex(ValueError,'exports'):m.step(A,v.State({0:v.constant(0x3001000),1:('stack',-4)},{}))

    def test_symbolic_unsigned_guard_records_both_exact_relations(self):
        m=machine([0x2807,0xd900,0x2100,0x2101]);s=v.State({0:('input','x',16)}, {})
        result=m.run(A,s,{A+4,A+6})
        self.assertEqual({(pc,st.guards) for pc,st in result},{(A+6,(('ule',s.value(0),v.constant(7)),)),(A+4,(('ugt',s.value(0),v.constant(7)),))})

    def test_flag_overwrite_invalidates_saved_comparison(self):
        m=machine([0x2807,0x2100,0xd900])
        with self.assertRaisesRegex(ValueError,'comparison'):m.run(A,v.State({0:v.constant(1)},{}),{A+6})

    def test_concrete_inner_counter_executes_three_times(self):
        m=machine([0x2200,0x3201,0x2a02,0xd9fc])
        out=m.run(A,v.State({},{}),{A+8})[0][1]
        self.assertEqual(out.value(2),v.constant(3));self.assertEqual(out.trace.count(A+2),3)

    def test_unsupported_arithmetic_and_unbounded_backedge_refuse(self):
        with self.assertRaisesRegex(ValueError,'unsupported'):machine([0x4041]).step(A,v.State({0:v.constant(1),1:v.constant(2)},{}))
        with self.assertRaisesRegex(ValueError,'step budget'):machine([0xe7fe]).run(A,v.State({},{}),set())

    def test_copy_preserves_pointer_order_and_kills_callers(self):
        m,s,row=copy_fixture();pc,out=m.copy(s,A)
        self.assertEqual(pc,A+4)
        self.assertEqual([out.load_local(-32+4*i,4) for i in range(3)],[('stack',-48+2*i) for i in range(3)])
        self.assertEqual(out.value(4),('opaque','saved4'));self.assertIsNone(out.registers[1]);self.assertEqual(out.value(3),('stack',-4))

    def test_copy_rejects_changed_count_or_target(self):
        for kind in ('count','target'):
            m,s,row=copy_fixture()
            if kind=='count':s.registers[2]=v.constant(8)
            else:row['address']+=2
            with self.assertRaisesRegex(ValueError,'actual arguments'):m.copy(s,A)

    def test_copy_rejects_missing_pointer_initialization(self):
        m,s,_=copy_fixture();del s.memory[-12,4]
        with self.assertRaisesRegex(ValueError,'uninitialized'):m.copy(s,A)

    def test_copy_rejects_incomplete_byte_effects(self):
        m,s,row=copy_fixture();row['transfers'].pop()
        with self.assertRaisesRegex(ValueError,'not complete'):m.copy(s,A)

    def test_copy_rejects_unproven_saved_register_survival(self):
        m,s,row=copy_fixture();row['preserved_registers'].remove(8)
        with self.assertRaisesRegex(ValueError,'effects differ'):m.copy(s,A)

    def test_copy_rejects_overlapping_spans(self):
        m,s,row=copy_fixture();row['destination']=-20;s.registers[0]=('stack',-20)
        row['returned_local_aliases'][0][1]=-20;row['transfers']=[[-16+i,-20+i] for i in range(12)]
        with self.assertRaisesRegex(ValueError,'disjoint'):m.copy(s,A)

    def test_arithmetic_macro_preserves_zero_delta_byte_and_kills_written_registers(self):
        m,s,_=arithmetic_fixture();pc,out=m.arithmetic(s,A)
        self.assertEqual(pc,A+4);self.assertEqual(out.load_local(-12,2),v.constant(255))
        self.assertIsNone(out.registers[0]);self.assertEqual(out.value(4),('opaque','saved4'));self.assertIsNone(out.comparison)

    def test_arithmetic_macro_rejects_mismatched_preload(self):
        m,s,_=arithmetic_fixture();s.registers[1]=v.constant(31)
        with self.assertRaisesRegex(ValueError,'preloaded'):m.arithmetic(s,A)

    def test_arithmetic_macro_rejects_wrong_pointer_role(self):
        m,s,_=arithmetic_fixture();s.registers[0]=('stack',-10)
        with self.assertRaisesRegex(ValueError,'retained role'):m.arithmetic(s,A)

    def test_arithmetic_macro_rejects_unestablished_zero_register(self):
        m,s,_=arithmetic_fixture();s.registers[10]=v.constant(1)
        with self.assertRaisesRegex(ValueError,'constant input'):m.arithmetic(s,A)

    def test_selector_and_missing_authority_refuse(self):
        with self.assertRaisesRegex(ValueError,'explicit'):v.verify(b'',A,b'',{},selector='default',reuse_authority={},palette_base=0,history_base=0)
        with self.assertRaisesRegex(ValueError,'independent'):v.verify(b'',A,b'',{},selector=v.SELECTOR,reuse_authority={},palette_base=0,history_base=0)

    def test_changed_frozen_certificate_digest_refuses(self):
        certificates={key:{} for key in ('copy','frame','numeric','arithmetic','first_use','loops')}
        authority={'independently_established_frozen_certificates':True}
        with self.assertRaisesRegex(ValueError,'digest differs'):v.verify(b'',A,b'',certificates,selector=v.SELECTOR,reuse_authority=authority,palette_base=0,history_base=0)


if __name__=='__main__':unittest.main()
