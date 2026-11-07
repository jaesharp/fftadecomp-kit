"""New callback702 states with an independent concrete Thumb decoder oracle."""
from dataclasses import replace
import copy
import hashlib
import os
from pathlib import Path
import unittest

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
import scheduler_callback702_state as model
from test_scheduler_copy_state import layout as scheduler_layout
import test_scheduler_zero112_state as allocation

BODY_PATH = Path(os.environ.get('FFTA_CALLBACK702_BODY',str(
    Path(__file__).resolve().parents[1] / 'inputs/callback702.bin')))
if not BODY_PATH.is_file():
    raise unittest.SkipTest('Set FFTA_CALLBACK702_BODY to the retained external702B fixture')
BODY = BODY_PATH.read_bytes()
BASE, E, D, NODE = 0x02000000, 2048, 2304, 256


def put(m,at,w):
    m.update({at+i:v for i,v in enumerate(w)})


def half(m,at,n):
    put(m,at,tuple(n.to_bytes(2,'little')))


def layout():
    return model.Layout(scheduler_layout(),model.ADDRESS,BODY)


def fixture(phase=0, *, descriptor=D, payload=NODE+24):
    l = layout()
    r = {i:tuple(('opaque-byte','702 incoming R'+str(i),j) for j in range(4)) for i in range(15)}
    r.update({0:model.words._pointer(NODE),1:model.words._pointer(descriptor),
              2:model.words._pointer(payload),3:model.words._constant(l.callback|1),
              13:model.words._pointer(E),14:model.words._constant((l.scheduler.address+184)|1)})
    m = {descriptor+i:('opaque-byte','702 descriptor',i) for i in range(28)}
    half(m,descriptor,phase)
    put(m,descriptor+4,model.words._pointer(6400))
    put(m,descriptor+8,model.words._pointer(6500))
    half(m,descriptor+20,0xABCD)
    half(m,descriptor+22,0x1234)
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR)


def byte(v,base=BASE):
    if type(v) is int:
        return v
    if v[0] == 'base-plus-byte':
        return ((base+v[1]) >> (8*v[2])) & 255
    return hashlib.sha256((v[1]+':'+str(v[2])).encode()).digest()[0]


def number(word,base=BASE):
    return int.from_bytes(bytes(byte(v,base) for v in word),'little')


def raw(f):
    """Concrete mnemonic effects independent of production decode/flag helpers."""
    l,base = f['layout'],f['arena_base']
    r = {i:number(w,base) for i,w in f['registers'].items()}
    m = {base+k:byte(v,base) for k,v in f['cells'].items()}
    pc,trace,events,comparison = l.scheduler.callback_thunk,[],[],None
    decoder = Cs(CS_ARCH_ARM,CS_MODE_THUMB)
    decoder.detail = True
    aliases = dict(sp=13,lr=14,pc=15,sb=9,sl=10,fp=11,ip=12)

    def reg(op):
        n = decoder.reg_name(op.reg)
        return aliases[n] if n in aliases else int(n[1:])

    def value(op):
        return op.imm if op.type == 2 else r[reg(op)]

    def load(at,width):
        vals = tuple(m[at+i] for i in range(width))
        events.append((pc,'read'+str(8*width),at-base,vals))
        return int.from_bytes(bytes(vals),'little')

    def store(at,width,value):
        vals = tuple((value & 0xffffffff).to_bytes(4,'little')[:width])
        m.update({at+i:v for i,v in enumerate(vals)})
        events.append((pc,'write'+str(8*width),at-base,vals))

    for _ in range(128):
        off = pc-l.callback
        if pc != l.scheduler.callback_thunk and not (
                0 <= off < 42 or 48 <= off < 90 or 96 <= off < 120):
            return r,m,trace,events,pc
        data = b'\x18\x47' if pc == l.scheduler.callback_thunk else l.body[off:off+4]
        ins = next(decoder.disasm(data,pc,1))
        trace.append(pc)
        name,ops,nxt = ins.mnemonic,ins.operands,pc+ins.size
        if name == 'bx':
            nxt = r[reg(ops[0])] & ~1
        elif name == 'push':
            selected = [reg(op) for op in ops]
            r[13] -= 4*len(selected)
            for i,n in enumerate(selected):
                store(r[13]+4*i,4,r[n])
        elif name in ('mov','movs'):
            r[reg(ops[0])] = value(ops[1])
        elif name in ('add','adds','sub','subs'):
            n = reg(ops[0]);left = r[n] if len(ops) == 2 else value(ops[1])
            delta = value(ops[-1])
            r[n] = (left-delta if name.startswith('sub') else left+delta) & 0xffffffff
        elif name == 'lsls':
            r[reg(ops[0])] = (value(ops[1]) << value(ops[2])) & 0xffffffff
        elif name == 'cmp':
            comparison = (value(ops[0]),value(ops[1]))
        elif name in ('beq','bne','bgt','bge'):
            a,b = comparison
            if dict(beq=a==b,bne=a!=b,bgt=a>b,bge=a>=b)[name]:
                nxt = ops[0].imm
        elif name == 'b':
            nxt = ops[0].imm
        elif name in ('ldr','ldrh','str','strb'):
            base_reg = decoder.reg_name(ops[1].mem.base)
            width = 2 if name.endswith('h') else 1 if name.endswith('b') else 4
            if base_reg == 'pc':
                at = ((pc+4)&~3)+ops[1].mem.disp
                r[reg(ops[0])] = int.from_bytes(l.body[at-l.callback:at-l.callback+4],'little')
            else:
                bn = aliases[base_reg] if base_reg in aliases else int(base_reg[1:])
                at = r[bn]+ops[1].mem.disp
                if name.startswith('ldr'):
                    r[reg(ops[0])] = load(at,width)
                else:
                    store(at,width,r[reg(ops[0])])
        else:
            raise AssertionError((hex(pc),name,ins.op_str))
        pc = nxt
    raise AssertionError('independent callback bound exhausted')


def copied(phase):
    cells = allocation.fixture(phase)
    r = allocation.run(phase,copied=True,cells=cells)
    assert r['reaches_callback_thunk'],r['boundary']
    return cells,r


class Callback702Tests(unittest.TestCase):
    def assert_raw(self,f,r):
        regs,memory,trace,events,pc = raw(f)
        self.assertEqual(r['trace'],trace)
        self.assertEqual(r['final_PC'],pc)
        self.assertEqual({i:number(w,f['arena_base']) for i,w in r['registers'].items()},regs)
        self.assertEqual([(e['site'],e['operation'],e['coordinate'],tuple(byte(v,f['arena_base']) for v in e['bytes']))
                          for e in r['memory_events'] if 'coordinate' in e],events)
        for key,v in r['changed_cells'].items():
            self.assertEqual(byte(v,f['arena_base']),memory[f['arena_base']+int(key)])

    def test_complete_callback_and_nine_retained_owner_pins(self):
        l = model.bind(scheduler_layout(),BODY,model.ADDRESS,selector=model.SELECTOR)
        self.assertEqual(len(model._pins(model._validate(l))),10)
        self.assertEqual(hashlib.sha256(l.body).hexdigest(),model.BODY_SHA256)

    def test_inactive_bytes_pools_frame_call_and_tail_mutations_refuse(self):
        for at in (0,4,6,14,44,92,96,120,200,700):
            body = bytearray(BODY);body[at] ^= 1
            with self.subTest(at=at),self.assertRaises(ValueError):
                model.bind(scheduler_layout(),bytes(body),model.ADDRESS,selector=model.SELECTOR)
        with self.assertRaises(ValueError):
            model.bind(scheduler_layout(),BODY[:-2],model.ADDRESS,selector=model.SELECTOR)

    def test_wrong_selector_or_changed_retained_scheduler_refuses(self):
        with self.assertRaises(ValueError):
            model.derive(**dict(fixture(),selector='automatic'))
        with self.assertRaises(ValueError):
            model._validate(replace(layout(),scheduler=replace(scheduler_layout(),sha256='0'*64)))

    def test_phase_zero_actual64byte_frame_stores_and_true_pending_arguments(self):
        f = fixture();r = model.derive(**f)
        self.assertTrue(r['reaches_memcpy_boundary'],r['boundary'])
        self.assertEqual(r['registers'][13],model.words._pointer(E-64))
        self.assertEqual(r['pending_call']['target'],0x0814186C)
        self.assertEqual(r['pending_call']['register_arguments'],{
            0:model.words._constant(0x03003920),1:model.words._pointer(NODE+40),
            2:model.words._constant(16),3:model.words._constant(model.ADDRESS|1)})
        self.assertEqual(r['pending_call']['LR'],f['registers'][14])
        self.assertIs(r['pending_call']['callee_executed'],False)
        self.assertNotIn(model.ADDRESS+120,r['trace'])
        self.assert_raw(f,r)

    def test_all_known_nonzero_dispatch_cases_stop_before_unmodeled_phase(self):
        for phase,target in [(1,688),(256,160),(257,232),(258,436),(259,548),(260,608),(261,672),(65535,688)]:
            f = fixture(phase);r = model.derive(**f)
            with self.subTest(phase=phase):
                self.assertFalse(r['reaches_memcpy_boundary'])
                self.assertEqual(r['observed_phase'],phase)
                self.assertEqual(r['final_PC'],model.ADDRESS+target)
                self.assertIsNone(r['pending_call'])
                self.assert_raw(f,r)

    def test_discarded_unknown_high_tag_byte_does_not_block_low_byte_transport(self):
        f = fixture();f['cells'][D+21] = ('opaque-byte','unknown tag high',3)
        f['cells'][D+23] = ('opaque-byte','unknown variant high',4)
        r = model.derive(**f)
        self.assertTrue(r['reaches_memcpy_boundary'],r['boundary'])
        self.assertEqual((r['changed_cells'][str(NODE+30)],r['changed_cells'][str(NODE+31)]),(0xCD,0x34))
        self.assert_raw(f,r)

    def test_opaque_low_byte_is_transported_without_scalar_or_pointer_authority(self):
        f = fixture();f['cells'][D+20] = ('opaque-byte','unknown tag low',7)
        r = model.derive(**f)
        self.assertTrue(r['reaches_memcpy_boundary'],r['boundary'])
        self.assertEqual(r['changed_cells'][str(NODE+30)],('opaque-byte','unknown tag low',7))
        self.assertFalse(r['physical_access_proved'] or r['source_or_native_admission'])
        self.assert_raw(f,r)

    def test_opaque_or_pointer_phase_never_becomes_a_scalar_comparison(self):
        for value in [('opaque-byte','unknown phase',0),('base-plus-byte',5000,0)]:
            f = fixture();f['cells'][D] = value;r = model.derive(**f)
            with self.subTest(value=value):
                self.assertEqual(r['boundary']['site'],model.ADDRESS+18)
                self.assertIn('scalar/control',r['boundary']['reason'])
                self.assertIsNone(r['observed_phase'])
                self.assertFalse(r['reaches_memcpy_boundary'])

    def test_missing_phase_byte_refuses_after_actual_saves(self):
        f = fixture();del f['cells'][D+1];r = model.derive(**f)
        self.assertEqual(r['boundary']['site'],model.ADDRESS+14)
        self.assertEqual(len([e for e in r['memory_events'] if e['operation']=='write32']),6)

    def test_saved_old_R8_alias_determines_phase_after_both_pushes(self):
        f = fixture(17,descriptor=E-24);f['registers'][8] = model.words._constant(0xBCDE0000)
        r = model.derive(**f)
        self.assertTrue(r['reaches_memcpy_boundary'],r['boundary'])
        self.assertEqual(r['observed_phase'],0)
        self.assertEqual(tuple(r['post_cells'][str(E-24+i)] for i in range(4)),model.words._constant(0xBCDE0000))
        self.assert_raw(f,r)

    def test_first_payload_store_changes_later_descriptor_word_read(self):
        f = fixture(payload=D-64);r = model.derive(**f)
        self.assertTrue(r['reaches_memcpy_boundary'],r['boundary'])
        self.assertEqual(tuple(r['post_cells'][str(D-52+i)] for i in range(4)),model.words._pointer(6400))
        self.assert_raw(f,r)

    def test_byte_store_changes_following_variant_halfword_before_truncation(self):
        f = fixture(payload=D+16);r = model.derive(**f)
        self.assertTrue(r['reaches_memcpy_boundary'],r['boundary'])
        self.assertEqual((r['post_cells'][str(D+22)],r['post_cells'][str(D+23)]),(0xCD,0xCD))
        self.assert_raw(f,r)

    def test_protected_payload_write_refuses_after_real_source_load(self):
        f = fixture();f['protected_spans'] = ((NODE+96,NODE+100),)
        r = model.derive(**f)
        self.assertEqual(r['boundary']['site'],model.ADDRESS+98)
        self.assertEqual(r['memory_events'][-1]['operation'],'read32')
        self.assertNotIn(str(NODE+96),r['changed_cells'])

    def test_protected_second_push_preserves_first_push_effects_only(self):
        f = fixture();f['protected_spans'] = ((E-24,E-20),);r = model.derive(**f)
        self.assertEqual(r['boundary']['site'],model.ADDRESS+4)
        self.assertEqual(r['registers'][13],model.words._pointer(E-20))
        self.assertEqual(len(r['changed_cells']),20)

    def test_local_allocation_grants_no_write_or_initialization_of_protected_bytes(self):
        f = fixture();f['protected_spans'] = ((E-64,E-24),);f['cells'][E-40] = 0xA5
        r = model.derive(**f)
        self.assertTrue(r['reaches_memcpy_boundary'],r['boundary'])
        self.assertEqual(r['post_cells'][str(E-40)],0xA5)
        self.assertNotIn(str(E-40),r['changed_cells'])
        self.assertTrue(all(not e['initialization_granted'] for e in r['stack_activations']))
        self.assert_raw(f,r)

    def test_retired_frames_need_explicit_reuse_and_payloads_never_revive(self):
        f = fixture();f['retired_spans'] = ((E-64,E),);r = model.derive(**f)
        self.assertIn('nonreusable retired',r['boundary']['reason'])
        self.assertEqual(r['changed_cells'],{})
        f = fixture();f.update(retired_spans=((E-76,E),),reusable_frame_spans=((E-76,E),))
        r = model.derive(**f)
        self.assertTrue(r['reaches_memcpy_boundary'],r['boundary'])
        self.assertEqual(r['retired_spans'],[(E-76,E-64)])
        self.assert_raw(f,r)
        f = fixture();f.update(retired_spans=((E-64,E),),reusable_frame_spans=((E-64,E),),
                              unavailable_spans=((E-64,E-60),))
        r = model.derive(**f)
        self.assertEqual(r['boundary']['site'],model.ADDRESS+6)
        self.assertIn('unavailable',r['boundary']['reason'])

    def test_descriptor_data_cannot_be_read_from_expired_nonframe_payload(self):
        f = fixture();f['retired_spans'] = ((D+4,D+8),);r = model.derive(**f)
        self.assertEqual(r['boundary']['site'],model.ADDRESS+96)
        self.assertIn('retired',r['boundary']['reason'])

    def test_numeric_address_bits_or_missing_registers_do_not_gain_provenance(self):
        f = fixture();f['registers'][1] = model.words._constant(BASE+D);r = model.derive(**f)
        self.assertEqual(r['boundary']['site'],model.ADDRESS+14)
        self.assertIn('provenance',r['boundary']['reason'])
        f = fixture();del f['registers'][12]
        with self.assertRaises(ValueError):
            model.derive(**f)

    def test_actual_save_wrap_and_code_overwrite_are_refused(self):
        f = fixture();f['registers'][13] = model.words._pointer(-BASE+8);r = model.derive(**f)
        self.assertIn('wraps',r['boundary']['reason'])
        f = fixture(payload=model.ADDRESS-BASE-72);r = model.derive(**f)
        self.assertEqual(r['boundary']['site'],model.ADDRESS+98)
        self.assertIn('immutable complete owner',r['boundary']['reason'])

    def test_step_bound_is_an_open_boundary_without_pending_call_effects(self):
        f = fixture();f['max_steps'] = 5;r = model.derive(**f)
        self.assertFalse(r['reaches_memcpy_boundary'])
        self.assertIn('step bound',r['boundary']['reason'])
        self.assertIsNone(r['pending_call'])

    def test_count112_adapter_carries_new_postcopy_bytes_to_true_callback_call(self):
        cells,prior = copied(301)
        r = model.continue_from_copy(layout(),BASE,cells,prior,selector=model.SELECTOR)
        self.assertTrue(r['reaches_memcpy_boundary'],r['boundary'])
        self.assertEqual(r['observed_phase'],0)
        self.assertEqual(r['callback_entry_SP'],allocation.E-56)
        self.assertEqual(r['pending_call']['register_arguments'][1],model.words._pointer(allocation.NODE+40))
        self.assertEqual(r['changed_cells'][str(allocation.NODE+30)],('opaque-byte','count112 descriptor 301',20))
        self.assertFalse(r['actual_prior_report_authentication_proved'])

    def test_adapter_rejects_changed_count_body_frame_return_and_descriptor(self):
        cells,prior = copied(302)
        variants = []
        for kind in ('count','body','return','descriptor','certificate'):
            bad = copy.deepcopy(prior)
            if kind == 'count':bad['prefix']['count'] = 92
            elif kind == 'body':bad['bodies']['scheduler'] = '0'*64
            elif kind == 'return':bad['callback_registers'][14] = model.words._constant(0x08030001)
            elif kind == 'descriptor':bad['descriptor_bytes'] = (9,)*28
            else:
                for event in bad['prefix']['memory_events']:
                    if event['operation'] == 'conditional-installed-zero112':event['receipt_sha256'] = '0'*64
            variants.append((kind,bad))
        for kind,bad in variants:
            with self.subTest(kind=kind),self.assertRaises(ValueError):
                model.continue_from_copy(layout(),BASE,cells,bad,selector=model.SELECTOR)

    def test_adapter_preserves_real_callback_target_refusal(self):
        cells,prior = copied(303)
        for i in range(4):prior['prefix']['changed_cells'][str(allocation.NODE+i)] = 0
        prior['callback_registers'][3] = model.words._constant(0)
        prior['observed_callback_word'] = model.words._constant(0)
        r = model.continue_from_copy(layout(),BASE,cells,prior,selector=model.SELECTOR)
        self.assertFalse(r['callback_entry_reached'])
        self.assertEqual(r['boundary']['site'],layout().scheduler.callback_thunk)

    def test_adapter_forgets_old_allocator_bytes_and_never_revives_unavailable_payload(self):
        cells,prior = copied(304)
        e = allocation.E
        cells[e-100] = ('base-plus-byte',9000,0)
        r = model.continue_from_copy(layout(),BASE,cells,prior,selector=model.SELECTOR)
        self.assertTrue(r['reaches_memcpy_boundary'],r['boundary'])
        self.assertEqual(r['post_cells'][str(e-100)][0],'opaque-byte')
        self.assertEqual(r['forgotten_allocator_private_span'],[e-132,e-56])
        cells,prior = copied(305)
        r = model.continue_from_copy(layout(),BASE,cells,prior,selector=model.SELECTOR,
                                    unavailable_spans=((e-120,e-116),))
        self.assertIn('unavailable',r['boundary']['reason'])
        self.assertEqual(r['boundary']['site'],model.ADDRESS+6)
