"""New helper2 states, ordered aliases and an independent concrete oracle."""
from dataclasses import replace
import copy
import hashlib
import os
from pathlib import Path
import unittest
from unittest.mock import patch

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
import scheduler_helper2_state as model
from test_scheduler_copy_state import layout as scheduler_layout

INPUTS = Path(__file__).resolve().parents[1] / 'inputs'
CB_PATH = Path(os.environ.get('FFTA_CALLBACK702_BODY',str(INPUTS/'callback702.bin')))
H_PATH = Path(os.environ.get('FFTA_HELPER2_BODY',str(INPUTS/'helper2.bin')))
if not CB_PATH.is_file() or not H_PATH.is_file():
    raise unittest.SkipTest('Set FFTA_CALLBACK702_BODY and FFTA_HELPER2_BODY to retained external fixtures')
CB, HELPER = CB_PATH.read_bytes(),H_PATH.read_bytes()
BASE, E = 0x02000000,2048
G = model.GLOBAL-BASE
W, P = model.words._constant,model.words._pointer


def put(m,at,word):
    m.update({at+i:v for i,v in enumerate(word)})


def layout():
    sc = scheduler_layout()
    sc = replace(sc,address=model.SCHEDULER,sha256=hashlib.sha256(
        model.prefix.state._identity(model.SCHEDULER,sc.allocator,sc.callback_thunk)).hexdigest())
    callback = model.prefix.Layout(sc,model.prefix.ADDRESS,CB)
    prior = model.cpuset.Layout(callback,model.cpuset.bios.WRAPPER)
    return model.Layout(prior,model.ADDRESS,HELPER)


def fixture(*,sp=E):
    r = {i:tuple(('opaque-byte','helper2 incoming R'+str(i),j) for j in range(4)) for i in range(15)}
    r.update({0:P(7200),1:W(0x0839D7E4),2:W(2),3:W(7),4:W(0),6:P(536),8:P(384),13:P(sp)})
    m = {sp-72+i:('opaque-byte','helper2 supplied local',i) for i in range(52)}
    put(m,sp,W(0))
    put(m,sp+4,P(384))
    put(m,G,P(1024))
    return dict(layout=layout(),arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR,global_coordinate=G)


def byte(v,base=BASE):
    if type(v) is int:
        return v
    if v[0] == 'base-plus-byte':
        return ((base+v[1]) >> (8*v[2])) & 255
    return hashlib.sha256((v[1]+':'+str(v[2])).encode()).digest()[0]


def number(word,base=BASE):
    return int.from_bytes(bytes(byte(v,base) for v in word),'little')


def raw(f):
    """Decode real instructions without production masks, flags or guards."""
    l,base = f['layout'],f['arena_base']
    cb,h = l.prior.prefix.callback,l.helper
    pc = cb+138
    r = {i:number(v,base) for i,v in f['registers'].items()}
    m = {base+k:byte(v,base) for k,v in f['cells'].items()}
    trace,events,comparison = [],[],None
    decoder = Cs(CS_ARCH_ARM,CS_MODE_THUMB)
    decoder.detail = True
    aliases = dict(sp=13,lr=14,pc=15,sb=9,sl=10,fp=11,ip=12)

    def reg(identifier):
        name = decoder.reg_name(identifier)
        return aliases[name] if name in aliases else int(name[1:])

    def value(op):
        return op.imm if op.type == 2 else r[reg(op.reg)]

    def load(at):
        vals = tuple(m[at+i] for i in range(4))
        events.append((pc,'read32',at-base,vals))
        return int.from_bytes(bytes(vals),'little')

    def store(at,val):
        vals = tuple(val.to_bytes(4,'little'))
        m.update({at+i:v for i,v in enumerate(vals)})
        events.append((pc,'write32',at-base,vals))

    for _ in range(64):
        if pc == h+266:
            return r,m,trace,events,pc
        data = l.prior.prefix.body[138:142] if pc == cb+138 else l.body[pc-h:pc-h+4]
        ins = next(decoder.disasm(data,pc,1))
        trace.append(pc)
        ops,name,nxt = ins.operands,ins.mnemonic,pc+ins.size
        if name == 'bl':
            r[14] = nxt|1
            nxt = ops[0].imm
        elif name == 'push':
            selected = [reg(op.reg) for op in ops]
            r[13] -= 4*len(selected)
            for i,n in enumerate(selected):
                store(r[13]+4*i,r[n])
        elif name in ('add','adds','sub','subs'):
            n = reg(ops[0].reg)
            a = r[n] if len(ops) == 2 else value(ops[1])
            b = value(ops[-1])
            r[n] = (a-b if name.startswith('sub') else a+b)&0xffffffff
        elif name in ('lsls','lsrs'):
            a,b = value(ops[1]),value(ops[2])
            r[reg(ops[0].reg)] = ((a << b) if name == 'lsls' else (a >> (b or 32)))&0xffffffff
        elif name in ('ands','orrs'):
            n = reg(ops[0].reg)
            r[n] = r[n] & value(ops[1]) if name == 'ands' else r[n] | value(ops[1])
        elif name == 'cmp':
            comparison = value(ops[0]),value(ops[1])
        elif name in ('bne','bhi'):
            a,b = comparison
            take = (a != b) if name == 'bne' else (a > b)
            if take:
                nxt = ops[0].imm
        elif name in ('ldr','str'):
            n = reg(ops[1].mem.base)
            if n == 15:
                at = ((pc+4)&~3)+ops[1].mem.disp
                r[reg(ops[0].reg)] = int.from_bytes(l.body[at-h:at-h+4],'little')
            else:
                at = r[n]+ops[1].mem.disp
                if name == 'ldr':
                    r[reg(ops[0].reg)] = load(at)
                else:
                    store(at,r[reg(ops[0].reg)])
        elif name in ('mov','movs'):
            r[reg(ops[0].reg)] = value(ops[1])
        else:
            raise AssertionError((hex(pc),name,ins.op_str))
        pc = nxt
    raise AssertionError('oracle did not reach scheduler boundary')


def cpuset_report(f):
    """An interface fixture with no actual reaching-state authority."""
    l,r = f['layout'].prior,copy.deepcopy(f['registers'])
    e = model.words.observe(r[13])['coordinate']
    m = f['cells']
    return dict(schema=model.cpuset.SELECTOR,complete_owner_pins=model.prefix._pins(model.cpuset._validate(l)),
        conditional_copy_applied=True,transfer_bytes=32,CpuSet_contract=model.cpuset.CONTRACT,
        reaches_helper_boundary=True,final_PC=l.prefix.callback+138,boundary=dict(site=l.prefix.callback+138),
        registers=r,post_cells={str(k):v for k,v in m.items()},retired_spans=[],
        pending_call=dict(site=l.prefix.callback+138,target=model.ADDRESS,
            register_arguments={i:r[i] for i in range(4)},
            stack_argument_bytes={i:tuple(m[e+i+j] for j in range(4)) for i in (0,4)},
            SP=r[13],LR=r[14],callee_executed=False),
        obligations=[dict(id='BIOS',proved=False,text='Conditional BIOS effects remain a premise.')])


class Helper2StateTests(unittest.TestCase):
    def assert_raw(self,f,out):
        r,m,trace,events,pc = raw(f)
        self.assertTrue(out['reaches_scheduler_boundary'],out['boundary'])
        self.assertEqual(out['trace'],trace)
        self.assertEqual(out['final_PC'],pc)
        self.assertEqual({i:number(v) for i,v in out['registers'].items()},r)
        for key,value in out['post_cells'].items():
            self.assertEqual(byte(value),m[BASE+int(key)],key)
        actual = [(v['site'],v['operation'],v['coordinate'],tuple(byte(a) for a in v['bytes']))
                  for v in out['memory_events'] if v['operation'] in ('read32','write32')]
        self.assertEqual(actual,events)

    def test_actual_frame_and_nested_scheduler_arguments(self):
        f = fixture()
        out = model.derive(**f)
        self.assert_raw(f,out)
        sp = E-72
        call = out['pending_call']
        self.assertEqual(call['register_arguments'],{0:P(1024),1:W(0x080DFF05),2:W(12),3:P(sp+4)})
        self.assertEqual(call['stack_argument_bytes'],{0:P(384),8:P(sp+44)})
        self.assertEqual(out['private_frame_bytes'],72)
        self.assertEqual(out['registers'][14],W((model.prefix.ADDRESS+142)|1))
        self.assertFalse(call['callee_executed'])
        self.assertNotIn(model.ADDRESS+266,out['trace'])
        self.assertEqual(out['descriptor_bytes'][4:8],P(sp+44))
        for key,value in out.items():
            if key.endswith('_proved') or key.endswith('_closed') or key.endswith('_admission'):
                self.assertIs(value,False,key)

    def test_masks_preserve_unknown_high_byte_and_replace_only_selected_bytes(self):
        f = fixture()
        out = model.derive(**f)
        self.assert_raw(f,out)
        at = E-72+44
        word = tuple(out['post_cells'][str(at+i)] for i in range(4))
        self.assertEqual(word,(0,0,2,f['cells'][at+3]))
        self.assertEqual(model.words.observe(word)['kind'],'opaque-or-partial')

    def test_masked_pointer_byte_origins_remain_partial_data(self):
        f = fixture()
        at = E-72+44
        put(f['cells'],at,P(6000))
        out = model.derive(**f)
        self.assert_raw(f,out)
        self.assertEqual(tuple(out['post_cells'][str(at+i)] for i in range(4)),(0,0,2,P(6000)[3]))

    def test_missing_local_bytes_get_fresh_unknowns_without_initialization_writes(self):
        f = fixture()
        for at in range(E-72,E-20):
            del f['cells'][at]
        out = model.derive(**f)
        self.assertTrue(out['reaches_scheduler_boundary'],out['boundary'])
        at = E-72+44
        self.assertEqual(tuple(out['post_cells'][str(at+i)] for i in range(3)),(0,0,2))
        self.assertEqual(out['post_cells'][str(at+3)],('opaque-byte','helper2 local',47))
        self.assertTrue(all(str(E-72+4+i) not in out['changed_cells'] for i in range(4)))
        self.assertTrue(all(v['initialization_granted'] is False for v in out['stack_activations']))

    def test_unknown_parent_stack_word_is_transported_without_pointer_invention(self):
        f = fixture()
        value = tuple(('opaque-byte','helper2 unknown parent',i) for i in range(4))
        put(f['cells'],E+4,value)
        out = model.derive(**f)
        self.assert_raw(f,out)
        self.assertEqual(out['pending_call']['stack_argument_bytes'][0],value)

    def test_global_alias_of_masked_local_word_observes_actual_stores(self):
        f = fixture(sp=G+28)
        original_high = f['cells'][G+3]
        out = model.derive(**f)
        self.assert_raw(f,out)
        self.assertEqual(out['registers'][0],(0,0,2,original_high))

    def test_global_alias_of_saved_descriptor_observes_literal_store(self):
        f = fixture(sp=G+24)
        out = model.derive(**f)
        self.assert_raw(f,out)
        self.assertEqual(out['registers'][0],W(0x0839D7E4))

    def test_global_alias_of_frame_link_observes_pointer_store(self):
        f = fixture(sp=G+64)
        out = model.derive(**f)
        self.assert_raw(f,out)
        self.assertEqual(out['registers'][0],P(G-8+44))

    def test_global_alias_of_push_uses_lr_from_actual_caller_bl(self):
        f = fixture(sp=G+4)
        out = model.derive(**f)
        self.assert_raw(f,out)
        expected = W((model.prefix.ADDRESS+142)|1)
        self.assertEqual(out['registers'][0],expected)
        self.assertNotEqual(expected,f['registers'][14])

    def test_missing_global_byte_retains_prior_stack_effects(self):
        f = fixture()
        del f['cells'][G+3]
        out = model.derive(**f)
        self.assertFalse(out['reaches_scheduler_boundary'])
        self.assertEqual(out['final_PC'],model.ADDRESS+254)
        self.assertIn('reaching byte origins',out['boundary']['reason'])
        self.assertTrue(out['changed_cells'])
        self.assertIsNone(out['pending_call'])

    def test_global_literal_requires_explicit_coordinate_binding(self):
        f = fixture()
        f['global_coordinate'] += 4
        with self.assertRaises(ValueError):
            model.derive(**f)

    def test_protected_push_refuses_before_any_save(self):
        f = fixture()
        out = model.derive(**f,protected_spans=((E-4,E),))
        self.assertIn('protected',out['boundary']['reason'])
        self.assertEqual(out['final_PC'],model.ADDRESS)
        self.assertEqual(out['changed_cells'],{})
        self.assertEqual(out['registers'][13],P(E))

    def test_protected_masked_word_retains_only_completed_push(self):
        f = fixture()
        at = E-72+44
        out = model.derive(**f,protected_spans=((at,at+4),))
        self.assertEqual(out['final_PC'],model.ADDRESS+40)
        self.assertIn('protected',out['boundary']['reason'])
        self.assertEqual(len(out['changed_cells']),20)
        self.assertEqual(tuple(out['post_cells'][str(at+i)] for i in range(4)),
                         tuple(f['cells'][at+i] for i in range(4)))

    def test_late_stack_protection_preserves_completed_descriptor_stores(self):
        f = fixture()
        sp = E-72
        out = model.derive(**f,protected_spans=((sp,sp+4),))
        self.assertEqual(out['final_PC'],model.ADDRESS+260)
        self.assertFalse(out['reaches_scheduler_boundary'])
        self.assertEqual(len(out['changed_cells']),32)

    def test_retired_frame_requires_complete_explicit_reuse(self):
        f = fixture()
        retired = ((E-72,E),)
        out = model.derive(**f,retired_spans=retired)
        self.assertIn('nonreusable',out['boundary']['reason'])
        self.assertEqual(out['changed_cells'],{})
        out = model.derive(**f,retired_spans=retired,reusable_frame_spans=((E-20,E),))
        self.assertEqual(out['final_PC'],model.ADDRESS+2)
        self.assertEqual(len(out['changed_cells']),20)
        out = model.derive(**f,retired_spans=retired,reusable_frame_spans=retired)
        self.assert_raw(f,out)
        self.assertEqual(out['retired_spans'],[])

    def test_split_reuse_does_not_reactivate_unavailable_payload(self):
        f = fixture()
        retired = ((E-80,E),)
        reusable = ((E-72,E-40),(E-40,E))
        out = model.derive(**f,retired_spans=retired,reusable_frame_spans=reusable)
        self.assert_raw(f,out)
        self.assertEqual(out['retired_spans'],[(E-80,E-72)])
        out = model.derive(**f,retired_spans=retired,reusable_frame_spans=reusable,
                           unavailable_spans=((E-40,E-36),))
        self.assertIn('unavailable',out['boundary']['reason'])
        self.assertFalse(out['reaches_scheduler_boundary'])

    def test_push_cannot_write_any_complete_code_owner(self):
        for owner in (model.ADDRESS,model.cpuset.CPUSET,model.prefix.ADDRESS):
            with self.subTest(owner=owner):
                f = fixture(sp=owner-BASE+20)
                out = model.derive(**f)
                self.assertIn('immutable',out['boundary']['reason'])
                self.assertEqual(out['changed_cells'],{})

    def test_unaligned_and_wrapping_stack_accesses_refuse(self):
        for sp in (E+1,-BASE+16):
            with self.subTest(sp=sp):
                out = model.derive(**fixture(sp=sp))
                self.assertFalse(out['reaches_scheduler_boundary'])
                self.assertEqual(out['changed_cells'],{})

    def test_other_controls_do_not_reuse_r2zero_early_return(self):
        for reg,value in [(2,W(0)),(2,W(258)),(3,W(6)),
                          (2,tuple(('opaque-byte','helper2 unknown control',i) for i in range(4)))]:
            with self.subTest(reg=reg,value=value):
                f = fixture()
                f['registers'][reg] = value
                out = model.derive(**f)
                self.assertEqual(out['trace'],[])
                self.assertFalse(out['helper_entry_reached'])

    def test_step_bound_does_not_execute_local_allocation(self):
        out = model.derive(**fixture(),max_steps=2)
        self.assertEqual(out['final_PC'],model.ADDRESS+2)
        self.assertEqual(out['registers'][13],P(E-20))
        self.assertEqual(len(out['changed_cells']),20)
        self.assertEqual(len(out['stack_activations']),1)

    def test_new_local_origins_do_not_alias_incoming_namespace(self):
        f = fixture()
        for at in range(E-72,E-20):
            del f['cells'][at]
        f['registers'][12] = tuple(('opaque-byte','helper2 local',i) for i in range(4))
        out = model.derive(**f)
        self.assertTrue(out['reaches_scheduler_boundary'])
        self.assertEqual(out['post_cells'][str(E-72+47)][1],'helper2 local:1')

    def test_new_cpuset_result_is_consumed_without_producer_replay(self):
        f = fixture()
        r,m = copy.deepcopy(f['registers']),dict(f['cells'])
        src,payload = model.cpuset.SOURCE-BASE,512
        r.update({0:W(model.cpuset.SOURCE),1:P(payload+16),2:W(16),6:P(payload)})
        m.update({src+i:('opaque-byte','helper2 new CpuSet source',i) for i in range(32)})
        put(m,payload+72,P(8128))
        prior = model.cpuset.derive(f['layout'].prior,BASE,m,r,selector=model.cpuset.SELECTOR,
            cpuset_contract=model.cpuset.CONTRACT,source_coordinate=src)
        self.assertTrue(prior['reaches_helper_boundary'],prior['boundary'])
        with patch.object(model.cpuset,'derive',side_effect=AssertionError('producer replay')):
            out = model.continue_from_cpuset(f['layout'],BASE,prior,selector=model.SELECTOR,global_coordinate=G)
        self.assertTrue(out['reaches_scheduler_boundary'],out['boundary'])
        self.assertFalse(out['actual_prior_report_authentication_proved'])
        self.assertTrue(any(v['id']=='BIOS' and v['proved'] is False for v in out['inherited_CpuSet_obligations']))

    def test_consumed_retirement_and_write_protection_are_preserved(self):
        f = fixture()
        report = cpuset_report(f)
        report['retired_spans'] = [(E-72,E)]
        out = model.continue_from_cpuset(f['layout'],BASE,report,selector=model.SELECTOR,global_coordinate=G)
        self.assertIn('nonreusable',out['boundary']['reason'])
        out = model.continue_from_cpuset(f['layout'],BASE,report,selector=model.SELECTOR,global_coordinate=G,
            reusable_frame_spans=((E-72,E),),protected_spans=((E-72,E-68),))
        self.assertEqual(out['final_PC'],model.ADDRESS+260)
        self.assertFalse(out['reaches_scheduler_boundary'])

    def test_malformed_cpuset_interfaces_cannot_grant_entry(self):
        f = fixture()
        good = cpuset_report(f)
        for field,value in [('transfer_bytes',16),('complete_owner_pins',[]),
                            ('final_PC',model.prefix.ADDRESS+142),('CpuSet_contract','ordinary-copy'),
                            ('post_cells',{'01':0}),('pending_call',{}),('retired_spans',None)]:
            with self.subTest(field=field):
                report = copy.deepcopy(good)
                report[field] = value
                with self.assertRaises(ValueError):
                    model.continue_from_cpuset(f['layout'],BASE,report,selector=model.SELECTOR,global_coordinate=G)

    def test_complete_helper_identity_and_selector_are_required(self):
        l = layout()
        for body,address,selector in [(HELPER,model.ADDRESS+2,model.SELECTOR),
                                     (HELPER,model.ADDRESS,'R2zero'),
                                     (bytes([HELPER[0]^1])+HELPER[1:],model.ADDRESS,model.SELECTOR)]:
            with self.subTest(address=address,selector=selector):
                with self.assertRaises(ValueError):
                    model.bind(l.prior,body,address,selector=selector)
