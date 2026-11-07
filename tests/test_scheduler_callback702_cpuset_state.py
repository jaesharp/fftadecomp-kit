"""New CpuSet-boundary states and an independent concrete post-call oracle."""
from dataclasses import replace
import copy
import hashlib
import os
from pathlib import Path
import unittest
from unittest.mock import patch

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
import scheduler_callback702_cpuset_state as model
from test_scheduler_copy_state import layout as scheduler_layout

BODY_PATH = Path(os.environ.get('FFTA_CALLBACK702_BODY',str(
    Path(__file__).resolve().parents[1] / 'inputs/callback702.bin')))
if not BODY_PATH.is_file():
    raise unittest.SkipTest('Set FFTA_CALLBACK702_BODY to the external callback702 fixture')
BODY = BODY_PATH.read_bytes()
BASE, PAYLOAD, SP = 0x02000000, 280, 1984
W, P = model.words._constant, model.words._pointer


def put(m,at,word):
    m.update({at+i:v for i,v in enumerate(word)})


def layout():
    return model.Layout(model.prefix.Layout(scheduler_layout(),model.prefix.ADDRESS,BODY),model.bios.WRAPPER)


def fixture(*,base=BASE,payload=PAYLOAD,sp=SP):
    source = model.SOURCE-base
    r = {i:tuple(('opaque-byte','CpuSet incoming R'+str(i),j) for j in range(4)) for i in range(15)}
    r.update({0:W(model.SOURCE),1:P(payload+16),2:W(16),4:W(0),6:P(payload),8:P(256),13:P(sp)})
    m = {source+i:(37*i+19)&255 for i in range(32)}
    put(m,payload+72,P(6400))
    return dict(layout=layout(),arena_base=base,cells=m,registers=r,selector=model.SELECTOR,
                cpuset_contract=model.CONTRACT,source_coordinate=source)


def byte(v,base=BASE):
    if type(v) is int:
        return v
    if v[0] == 'base-plus-byte':
        return ((base+v[1]) >> (8*v[2])) & 255
    return hashlib.sha256((v[1]+':'+str(v[2])).encode()).digest()[0]


def number(word,base=BASE):
    return int.from_bytes(bytes(byte(v,base) for v in word),'little')


def raw(f):
    """Assume the specified BIOS relation, independently decode actual suffix."""
    base,l = f['arena_base'],f['layout']
    r = {i:number(v,base) for i,v in f['registers'].items()}
    m = {base+k:byte(v,base) for k,v in f['cells'].items()}
    source,destination = r[0],r[1]
    # Deliberately no BIOS instruction/access-order claim in this oracle.
    transferred = [m[source+i] for i in range(16*2)]
    m.update({destination+i:v for i,v in enumerate(transferred)})
    for reg in (0,1,2,3,12,14):
        r[reg] = (0xA1020304+reg*0x1020304)&0xffffffff
    cb = l.prefix.callback
    pc,trace,events = cb+124,[cb+120],[]
    decoder = Cs(CS_ARCH_ARM,CS_MODE_THUMB)
    decoder.detail = True
    aliases = dict(sp=13,lr=14,pc=15,sb=9,sl=10,fp=11,ip=12)

    def reg(identifier):
        name = decoder.reg_name(identifier)
        return aliases[name] if name in aliases else int(name[1:])

    for _ in range(7):
        ins = next(decoder.disasm(l.prefix.body[pc-cb:pc-cb+4],pc,1))
        trace.append(pc)
        ops = ins.operands
        if ins.mnemonic == 'ldr':
            bn = reg(ops[1].mem.base)
            if bn == 15:
                at = ((pc+4)&~3)+ops[1].mem.disp
                r[reg(ops[0].reg)] = int.from_bytes(l.prefix.body[at-cb:at-cb+4],'little')
            else:
                at = r[bn]+ops[1].mem.disp
                vals = tuple(m[at+i] for i in range(4))
                r[reg(ops[0].reg)] = int.from_bytes(bytes(vals),'little')
                events.append((pc,'read32',at-base,vals))
        elif ins.mnemonic == 'str':
            bn = reg(ops[1].mem.base)
            at = r[bn]+ops[1].mem.disp
            vals = tuple(r[reg(ops[0].reg)].to_bytes(4,'little'))
            m.update({at+i:v for i,v in enumerate(vals)})
            events.append((pc,'write32',at-base,vals))
        elif ins.mnemonic in ('mov','movs'):
            r[reg(ops[0].reg)] = ops[1].imm if ops[1].type == 2 else r[reg(ops[1].reg)]
        else:
            raise AssertionError((hex(pc),ins.mnemonic,ins.op_str))
        pc += ins.size
    return r,m,trace,events,pc


def prefix_report(f):
    """An interface fixture, never proof of actual ROM reaching state."""
    l = f['layout'].prefix
    r = copy.deepcopy(f['registers'])
    e = model.words.observe(r[13])['coordinate']+64
    return dict(schema=model.prefix.SELECTOR,complete_owner_pins=model.prefix._pins(model.prefix._validate(l)),
        starts_at=l.scheduler.callback_thunk,callback_entry_reached=True,reaches_memcpy_boundary=True,
        final_PC=l.callback+120,observed_phase=0,observed_phase_bytes=(0,0),frame_bytes=64,
        boundary=dict(site=l.callback+120),callback_entry_SP=e,registers=r,
        pending_call=dict(site=l.callback+120,target=model.CPUSET,register_arguments={i:r[i] for i in range(4)},
                          SP=r[13],LR=r[14],callee_executed=False),
        post_cells={str(k):v for k,v in f['cells'].items()},retired_spans=[],obligations=[])


class CpuSetContinuationTests(unittest.TestCase):
    def assert_raw(self,f,result):
        r,m,trace,events,pc = raw(f)
        self.assertTrue(result['reaches_helper_boundary'],result['boundary'])
        self.assertEqual(result['trace'],trace)
        self.assertEqual(result['final_PC'],pc)
        for reg in set(range(15))-{12,14}:
            self.assertEqual(number(result['registers'][reg],f['arena_base']),r[reg],reg)
        for key,value in result['post_cells'].items():
            self.assertEqual(byte(value,f['arena_base']),m[f['arena_base']+int(key)],key)
        actual = [(v['site'],v['operation'],v['coordinate'],tuple(byte(a,f['arena_base']) for a in v['bytes']))
                  for v in result['memory_events'] if v['operation'] in ('read32','write32')]
        self.assertEqual(actual,events)

    def test_actual_32_bytes_and_next_helper_arguments(self):
        f = fixture()
        out = model.derive(**f)
        self.assert_raw(f,out)
        call = out['pending_call']
        self.assertEqual(call['target'],0x080E03F8)
        self.assertEqual(call['register_arguments'],{0:P(6400),1:W(0x0839D7E4),2:W(2),3:W(7)})
        self.assertEqual(call['stack_argument_bytes'],{0:W(0),4:P(256)})
        self.assertEqual(out['transfer_bytes'],32)
        self.assertFalse(call['callee_executed'])
        self.assertNotIn(f['layout'].prefix.callback+138,out['trace'])
        for key,value in out.items():
            if key.endswith('_proved') or key.endswith('_closed') or key.endswith('_admission'):
                self.assertIs(value,False,key)
        self.assertTrue(all(v['proved'] is False for v in out['obligations']))

    def test_unknown_source_bytes_are_transported_without_scalar_observation(self):
        f = fixture()
        src = f['source_coordinate']
        for i in range(32):
            f['cells'][src+i] = ('opaque-byte','CpuSet unknown source',i)
        out = model.derive(**f)
        self.assert_raw(f,out)
        self.assertEqual(tuple(out['post_cells'][str(PAYLOAD+16+i)] for i in range(32)),
                         tuple(f['cells'][src+i] for i in range(32)))

    def test_pointer_byte_origins_survive_halfword_transport(self):
        f = fixture()
        src = f['source_coordinate']
        for i in range(8):
            put(f['cells'],src+4*i,P(7000+4*i))
        out = model.derive(**f)
        self.assert_raw(f,out)
        self.assertEqual(tuple(out['post_cells'][str(PAYLOAD+16+i)] for i in range(4)),P(7000))

    def test_halfword_transfer_can_precede_unaligned_word_load_refusal(self):
        f = fixture(payload=282)
        out = model.derive(**f)
        self.assertTrue(out['conditional_copy_applied'])
        self.assertFalse(out['reaches_helper_boundary'])
        self.assertEqual(out['final_PC'],model.prefix.ADDRESS+124)
        self.assertIn('unaligned',out['boundary']['reason'])
        self.assertEqual(len(out['changed_cells']),32)

    def test_exact_self_copy_is_explicit(self):
        src = model.SOURCE-BASE
        f = fixture(payload=src-16)
        out = model.derive(**f)
        self.assert_raw(f,out)
        self.assertTrue(out['memory_events'][0]['exact_self_copy'])

    def test_partial_overlap_both_directions_refuses_without_effects(self):
        src = model.SOURCE-BASE
        for delta in (-2,2):
            with self.subTest(delta=delta):
                f = fixture(payload=src+delta-16)
                out = model.derive(**f)
                self.assertIn('overlapping',out['boundary']['reason'])
                self.assertFalse(out['conditional_copy_applied'])
                self.assertEqual(out['changed_cells'],{})

    def test_source_can_alias_later_stack_stores(self):
        f = fixture(sp=model.SOURCE-BASE)
        out = model.derive(**f)
        self.assert_raw(f,out)
        self.assertEqual(tuple(out['post_cells'][str(f['source_coordinate']+i)] for i in range(4)),W(0))
        self.assertEqual(tuple(out['post_cells'][str(PAYLOAD+16+i)] for i in range(4)),
                         tuple(f['cells'][f['source_coordinate']+i] for i in range(4)))

    def test_destination_can_alias_later_stack_stores(self):
        f = fixture(sp=PAYLOAD+20)
        out = model.derive(**f)
        self.assert_raw(f,out)
        self.assertEqual(tuple(out['post_cells'][str(PAYLOAD+20+i)] for i in range(8)),W(0)+P(256))

    def test_field_load_occurs_before_first_stack_store_alias(self):
        f = fixture(sp=PAYLOAD+72)
        out = model.derive(**f)
        self.assert_raw(f,out)
        self.assertEqual(out['registers'][0],P(6400))
        self.assertEqual(tuple(out['post_cells'][str(PAYLOAD+72+i)] for i in range(4)),W(0))

    def test_field_load_occurs_before_second_stack_store_alias(self):
        f = fixture(sp=PAYLOAD+68)
        out = model.derive(**f)
        self.assert_raw(f,out)
        self.assertEqual(out['registers'][0],P(6400))
        self.assertEqual(tuple(out['post_cells'][str(PAYLOAD+72+i)] for i in range(4)),P(256))

    def test_source_can_also_be_post_call_field(self):
        src = model.SOURCE-BASE
        f = fixture(payload=src-72)
        put(f['cells'],src,tuple(('opaque-byte','CpuSet loaded argument',i) for i in range(4)))
        out = model.derive(**f)
        self.assert_raw(f,out)
        self.assertEqual(out['registers'][0],tuple(f['cells'][src+i] for i in range(4)))

    def test_missing_last_source_byte_refuses_before_copy(self):
        f = fixture()
        del f['cells'][f['source_coordinate']+31]
        out = model.derive(**f)
        self.assertIn('all32',out['boundary']['reason'])
        self.assertEqual(out['changed_cells'],{})
        self.assertFalse(out['conditional_copy_applied'])

    def test_source_literal_alone_does_not_grant_readability(self):
        f = fixture()
        for i in range(32):
            del f['cells'][f['source_coordinate']+i]
        out = model.derive(**f)
        self.assertFalse(out['conditional_copy_applied'])
        self.assertEqual(out['memory_events'],[])

    def test_explicit_conditional_contract_is_required(self):
        for contract in ('',False,'ordinary-memcpy',None):
            with self.subTest(contract=contract):
                f = fixture()
                f['cpuset_contract'] = contract
                with self.assertRaises(ValueError):
                    model.derive(**f)

    def test_control_is_not_a_byte_count_fill_or_word_copy(self):
        for control in (32,0x01000010,0x04000010,0x80000010):
            with self.subTest(control=control):
                f = fixture()
                f['registers'][2] = W(control)
                out = model.derive(**f)
                self.assertFalse(out['conditional_copy_applied'])
                self.assertIn('control',out['boundary']['reason'])

    def test_destination_must_equal_actual_payload_plus16(self):
        f = fixture()
        f['registers'][1] = P(PAYLOAD+20)
        out = model.derive(**f)
        self.assertIn('payload plus16',out['boundary']['reason'])
        self.assertFalse(out['conditional_copy_applied'])

    def test_opaque_destination_is_not_an_address(self):
        f = fixture()
        f['registers'][1] = tuple(('opaque-byte','CpuSet unproved destination',i) for i in range(4))
        out = model.derive(**f)
        self.assertIn('provenance',out['boundary']['reason'])
        self.assertFalse(out['conditional_copy_applied'])

    def test_protected_transfer_refuses_before_any_write(self):
        f = fixture()
        out = model.derive(**f,protected_spans=((PAYLOAD+47,PAYLOAD+48),))
        self.assertFalse(out['conditional_copy_applied'])
        self.assertEqual(out['changed_cells'],{})

    def test_protected_source_still_allows_conditional_reads(self):
        f = fixture()
        src = f['source_coordinate']
        out = model.derive(**f,protected_spans=((src,src+32),))
        self.assert_raw(f,out)

    def test_retired_or_unavailable_source_and_destination_refuse(self):
        for role in ('source','destination'):
            for guard in ('retired_spans','unavailable_spans'):
                with self.subTest(role=role,guard=guard):
                    f = fixture()
                    at = f['source_coordinate'] if role == 'source' else PAYLOAD+16
                    out = model.derive(**f,**{guard:((at+30,at+32),)})
                    self.assertFalse(out['conditional_copy_applied'])
                    self.assertEqual(out['changed_cells'],{})

    def test_stack_protection_retains_already_completed_transfer(self):
        f = fixture()
        out = model.derive(**f,protected_spans=((SP,SP+4),))
        self.assertTrue(out['conditional_copy_applied'])
        self.assertFalse(out['reaches_helper_boundary'])
        self.assertEqual(out['final_PC'],model.prefix.ADDRESS+128)
        self.assertEqual(len(out['changed_cells']),32)

    def test_post_call_stack_write_cannot_modify_complete_code_owner(self):
        for owner in (model.CPUSET,model.prefix.ADDRESS):
            with self.subTest(owner=owner):
                f = fixture(sp=owner-BASE)
                out = model.derive(**f)
                self.assertTrue(out['conditional_copy_applied'])
                self.assertFalse(out['reaches_helper_boundary'])
                self.assertIn('immutable',out['boundary']['reason'])
                self.assertEqual(out['final_PC'],model.prefix.ADDRESS+128)
                self.assertEqual(len(out['changed_cells']),32)

    def test_second_stack_write_protection_preserves_completed_first_store(self):
        f = fixture()
        out = model.derive(**f,protected_spans=((SP+4,SP+8),))
        self.assertTrue(out['conditional_copy_applied'])
        self.assertFalse(out['reaches_helper_boundary'])
        self.assertEqual(out['final_PC'],model.prefix.ADDRESS+132)
        self.assertIn('protected',out['boundary']['reason'])
        self.assertEqual(len(out['changed_cells']),36)
        self.assertEqual(tuple(out['post_cells'][str(SP+i)] for i in range(4)),W(0))
        self.assertEqual(out['registers'][2],P(256))

    def test_missing_post_call_field_does_not_invent_pointer(self):
        f = fixture()
        del f['cells'][PAYLOAD+75]
        out = model.derive(**f)
        self.assertTrue(out['conditional_copy_applied'])
        self.assertIn('reaching byte origins',out['boundary']['reason'])
        self.assertIsNone(out['pending_call'])

    def test_all_complete_code_owners_are_immutable(self):
        for address in (model.CPUSET,model.prefix.ADDRESS):
            with self.subTest(address=address):
                f = fixture(payload=address-BASE-16)
                out = model.derive(**f)
                self.assertIn('immutable',out['boundary']['reason'])
                self.assertFalse(out['conditional_copy_applied'])

    def test_physical_transfer_must_not_wrap(self):
        f = fixture(base=0x80000000,payload=0x7fffffe0)
        f['cells'] = {k:v for k,v in f['cells'].items() if -(2**31) <= k < 2**31}
        out = model.derive(**f)
        self.assertIn('wraps',out['boundary']['reason'])
        self.assertFalse(out['conditional_copy_applied'])

    def test_source_coordinate_must_bind_actual_literal(self):
        f = fixture()
        f['source_coordinate'] += 4
        out = model.derive(**f)
        self.assertIn('source literal',out['boundary']['reason'])
        self.assertFalse(out['conditional_copy_applied'])

    def test_caller_saved_unknowns_are_fresh_and_callee_saved_origins_survive(self):
        f = fixture()
        f['cells'][f['source_coordinate']] = ('opaque-byte','conditional CpuSet clobbers',0)
        out = model.derive(**f)
        self.assert_raw(f,out)
        for reg in (12,14):
            self.assertEqual(model.words.observe(out['registers'][reg])['kind'],'opaque-or-partial')
            self.assertNotEqual(out['registers'][reg],f['registers'][reg])
            self.assertNotEqual(out['registers'][reg][0][1],'conditional CpuSet clobbers')
        for reg in (*range(4,12),13):
            self.assertEqual(out['registers'][reg],f['registers'][reg])

    def test_step_bound_leaves_unknown_arguments_and_pending_instructions(self):
        f = fixture()
        out = model.derive(**f,max_steps=1)
        self.assertTrue(out['conditional_copy_applied'])
        self.assertEqual(out['registers'][0],P(6400))
        self.assertEqual(model.words.observe(out['registers'][1])['kind'],'opaque-or-partial')
        self.assertEqual(out['final_PC'],model.prefix.ADDRESS+126)
        self.assertIsNone(out['pending_call'])

    def test_new_prefix_result_is_consumed_without_producer_replay(self):
        f = fixture()
        l = f['layout'].prefix
        r = copy.deepcopy(f['registers'])
        r.update({0:P(256),1:P(2304),2:P(PAYLOAD),3:W(l.callback|1),13:P(2048)})
        m = dict(f['cells'])
        for i in range(28):
            m[2304+i] = ('opaque-byte','CpuSet new descriptor',i)
        put(m,2304,(0,0,0,0))
        put(m,2308,P(6400))
        put(m,2312,P(6500))
        put(m,2324,(0xCD,0xAB,0x34,0x12))
        prior = model.prefix.derive(l,BASE,m,r,selector=model.prefix.SELECTOR)
        self.assertTrue(prior['reaches_memcpy_boundary'],prior['boundary'])
        with patch.object(model.prefix,'derive',side_effect=AssertionError('producer replay')):
            out = model.continue_from_prefix(f['layout'],BASE,prior,selector=model.SELECTOR,
                cpuset_contract=model.CONTRACT,source_coordinate=f['source_coordinate'])
        self.assertTrue(out['reaches_helper_boundary'],out['boundary'])
        self.assertFalse(out['actual_prior_report_authentication_proved'])
        self.assertIn('CpuSet',out['legacy_boundary_label_corrected'])

    def test_malformed_prefix_interfaces_cannot_grant_transfer(self):
        f = fixture()
        good = prefix_report(f)
        for field,value in [('observed_phase',1),('frame_bytes',40),('final_PC',model.prefix.ADDRESS+124),
                            ('complete_owner_pins',[]),('callback_entry_SP',2044),
                            ('post_cells',{'01':0})]:
            with self.subTest(field=field):
                report = copy.deepcopy(good)
                report[field] = value
                with self.assertRaises(ValueError):
                    model.continue_from_prefix(f['layout'],BASE,report,selector=model.SELECTOR,
                        cpuset_contract=model.CONTRACT,source_coordinate=f['source_coordinate'])

    def test_complete_wrapper_identity_and_exact_selector_are_required(self):
        l = layout()
        with self.assertRaises(ValueError):
            model.bind(l.prefix,l.wrapper,model.CPUSET+2,selector=model.SELECTOR)
        with self.assertRaises(ValueError):
            model.bind(l.prefix,l.wrapper,model.CPUSET,selector='ordinary-copy')
        with self.assertRaises(ValueError):
            model.bind(l.prefix,b'\x70\x47',model.CPUSET,selector=model.SELECTOR)
        bad = replace(l.prefix,body=bytes([BODY[0]^1])+BODY[1:])
        with self.assertRaises(ValueError):
            model.bind(bad,l.wrapper,model.CPUSET,selector=model.SELECTOR)
