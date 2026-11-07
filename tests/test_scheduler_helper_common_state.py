"""New helper-entry/gate states, raw Thumb execution and explicit refusals."""
from dataclasses import replace
import copy
import itertools
import unittest

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
import scheduler_helper_common_state as helper
import scheduler_copy_state as words
import allocator_remove_relation as branch

BASE = 0x02000000
H, G, I, C = 0x080a0000, 0x080b0000, 0x080c0000, 0x080d0000
EXTERNAL, POINT = 0x08100000, BASE+2400
E, SUBJECT, FIELDS = 4096, 5000, 5200
SEEDS = itertools.count(1)


def opaque(name):return tuple(('opaque-byte', name, i) for i in range(4))
def put(m, at, value):m.update({at+i:v for i, v in enumerate(value)})
def half(m, at, value):put(m, at, tuple((value & 65535).to_bytes(2, 'little')))


def layout():
    b = bytearray(helper.HELPER)
    for offset in helper.CALL_OFFSETS:
        target = G if offset == 114 else C if offset == 130 else EXTERNAL+offset*4
        b[offset:offset+4] = branch._bl(H+offset, target)
    b[80:84] = (H+84).to_bytes(4, 'little')
    for i, offset in enumerate(helper.TABLE_OFFSETS):b[84+4*i:88+4*i] = (H+offset).to_bytes(4, 'little')
    b[284:288] = POINT.to_bytes(4, 'little'); b[288:292] = (EXTERNAL+0x2001).to_bytes(4, 'little')
    getter = helper.GETTER[:2]+branch._bl(G+2, I)+helper.GETTER[6:]
    coordinates = helper.COORDINATES[:28]+branch._bl(C+28, EXTERNAL+0x1000)+helper.COORDINATES[32:]
    return helper.Layout(H, bytes(b), G, getter, I, b'\x70\x47', C, coordinates)


def fixture(*, mode=5, dispatch=0):
    seed = next(SEEDS)
    r = {n:opaque('new075 '+str(seed)+' R'+str(n)) for n in range(15)}
    r.update({0:words._pointer(SUBJECT), 1:words._constant(0x0839d798),
              2:words._constant(mode), 3:words._constant(dispatch),
              13:words._pointer(E), 14:words._constant(0x08012301+2*seed)})
    m = {}
    put(m, E, words._constant(0)); put(m, E+4, words._pointer(7000+4*seed))
    put(m, SUBJECT, words._pointer(FIELDS))
    for offset, value in [(8,-123), (10,234), (12,-300)]:half(m, FIELDS+offset, value)
    put(m, POINT-BASE, words._pointer(8000))
    return dict(layout=layout(), arena_base=BASE, cells=m, registers=r, selector=helper.SELECTOR)


def mem(r):return {int(k):v for k, v in r['post_cells'].items()}
def run(f):return helper.derive(**f)


def raw(f, *, start=H, stop_before=None, gate=False):
    """Independent Capstone execution, including symbolic bit-mask operations."""
    l = f['layout']; r, m = dict(f['registers']), dict(f['cells']); trace, events = [], []
    bodies = {l.helper:l.helper_data, l.getter:l.getter_data, l.identity:l.identity_data,
              l.coordinates:l.coordinates_data}
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB); decoder.detail = True
    pc = start; comparison = None
    def reg(op):
        name = decoder.reg_name(op.reg)
        return {'sp':13,'lr':14,'pc':15,'sb':9,'sl':10,'fp':11,'ip':12}.get(name, int(name[1:]) if name.startswith('r') else -1)
    def num(value):
        assert all(type(v) is int for v in value)
        return sum(v << (8*i) for i, v in enumerate(value))
    def address(value):
        assert value == words._pointer(value[0][1]); return value[0][1]
    def forget(low, high):
        names = {v[1] for v in [*m.values(), *(v for w in r.values() for v in w)] if type(v) is tuple and v[0]=='opaque-byte'}
        name = 'unmodeled helper local'; count = 0
        while name in names:count += 1; name = 'unmodeled helper local:'+str(count)
        for at in range(low, high):m[at] = ('opaque-byte',name,at-low)
    def bits(value):
        return [(v >> n) & 1 if type(v) is int else ('bit',v,n) for v in value for n in range(8)]
    def word(value):
        output = []
        for at in range(0,32,8):
            octet = value[at:at+8]
            if all(type(v) is int for v in octet):output.append(sum(v << n for n,v in enumerate(octet)))
            else:
                origin = next(v[1] for v in octet if type(v) is tuple)
                assert octet == [('bit',origin,n) for n in range(8)]
                output.append(origin)
        return tuple(output)
    def logic(a,b,name):
        result=[]
        for x,y in zip(bits(a),bits(b)):
            if name=='ands':z=0 if x==0 or y==0 else y if x==1 else x if y==1 or x==y else None
            else:z=1 if x==1 or y==1 else y if x==0 else x if y==0 or x==y else None
            assert z is not None;result.append(z)
        return word(result)
    def load(at,width,signed=False):
        value=tuple(m[at+i] for i in range(width));events.append((pc,'read'+str(width*8),at,value))
        if width==4:return value
        scalar=num(value)
        if signed and scalar & (1 << (8*width-1)):scalar-=1 << (8*width)
        return words._constant(scalar & 0xffffffff)
    def store(at,value):
        put(m,at,value);events.append((pc,'write'+str(len(value)*8),at,value))
    def location(op):
        base=decoder.reg_name(op.mem.base)
        if base=='pc':return ((pc+4)&~3)+op.mem.disp,True
        n={'sp':13}.get(base,int(base[1:]) if base.startswith('r') else -1)
        if op.mem.index:
            name=decoder.reg_name(op.mem.index);offset=num(r[int(name[1:])])
        else:offset=op.mem.disp
        if all(type(v)is int for v in r[n]):
            at=num(r[n])+offset
            if l.helper<=at<l.helper+292:return at,True
            return at-f['arena_base'],False
        return address(r[n])+offset,False
    if gate:forget(E-72,E-20)
    for _ in range(180):
        if pc==stop_before:return r,m,trace,events,pc
        owner=next((a for a,b in bodies.items() if a<=pc<a+len(b)),None)
        if owner is None or pc==l.helper+270:return r,m,trace,events,pc
        ins=next(decoder.disasm(bodies[owner][pc-owner:],pc,1));ops=ins.operands;name=ins.mnemonic
        trace.append(pc);nxt=pc+ins.size
        if name=='push':
            selected=[reg(o) for o in ops];low=address(r[13])-4*len(selected)
            for i,n in enumerate(selected):store(low+4*i,r[n])
            r[13]=words._pointer(low)
        elif name in ('sub','add') and len(ops)==2 and reg(ops[0])==13:
            old=address(r[13]);new=old+(-1 if name=='sub' else 1)*ops[1].imm
            if name=='sub':forget(new,old)
            r[13]=words._pointer(new)
        elif name=='pop':
            selected=[reg(o) for o in ops];low=address(r[13])
            for i,n in enumerate(selected):r[n]=load(low+4*i,4)
            r[13]=words._pointer(low+4*len(selected))
        elif name=='movs':r[reg(ops[0])]=words._constant(ops[1].imm)
        elif name=='mov':
            if reg(ops[0])==15:nxt=num(r[reg(ops[1])])
            else:r[reg(ops[0])]=r[reg(ops[1])]
        elif name in ('lsls','lsrs','asrs'):
            value=bits(r[reg(ops[1])]);shift=ops[2].imm
            if name=='lsls':value=([0]*shift+value)[:32]
            elif name=='lsrs':value=value[shift:]+[0]*shift
            else:value=value[shift:]+[value[-1]]*shift
            r[reg(ops[0])]=word(value)
        elif name in ('ands','orrs'):r[reg(ops[0])]=logic(r[reg(ops[0])],r[reg(ops[1])],name)
        elif name=='adds':
            dst=reg(ops[0])
            if len(ops)==3:
                if ops[2].type==2:
                    assert ops[2].imm==0;r[dst]=r[reg(ops[1])]
                else:r[dst]=words._constant((num(r[reg(ops[1])])+num(r[reg(ops[2])]))&0xffffffff)
            else:
                value=r[dst];delta=ops[1].imm
                r[dst]=words._constant((num(value)+delta)&0xffffffff) if all(type(v)is int for v in value) else words._pointer(address(value)+delta)
        elif name=='subs':r[reg(ops[0])]=words._constant((num(r[reg(ops[0])])-ops[1].imm)&0xffffffff)
        elif name=='add':r[reg(ops[0])]=words._pointer(address(r[reg(ops[1])])+ops[2].imm)
        elif name=='cmp':comparison=(num(r[reg(ops[0])]),ops[1].imm)
        elif name in ('beq','bne','bhi'):
            a,b=comparison
            if {'beq':a==b,'bne':a!=b,'bhi':a>b}[name]:nxt=ops[0].imm
        elif name=='b':nxt=ops[0].imm
        elif name=='bl':r[14]=words._constant(nxt|1);nxt=ops[0].imm
        elif name=='bx':nxt=num(r[reg(ops[0])])&~1
        elif name in ('ldr','ldrh','ldrsh'):
            at,rom=location(ops[1]);width=4 if name=='ldr' else 2
            r[reg(ops[0])]=tuple(l.helper_data[at-l.helper:at-l.helper+4]) if rom else load(at,width,name=='ldrsh')
        elif name=='str':
            at,rom=location(ops[1]);assert not rom;store(at,r[reg(ops[0])])
        else:raise AssertionError((hex(pc),name,ins.op_str))
        pc=nxt
    raise AssertionError('raw helper bound exhausted')


class HelperTests(unittest.TestCase):
    def test_mode5_reaches_real_coordinate_callee_with_signed_fields_and_stack_outputs(self):
        f=fixture();r=run(f)
        self.assertEqual(r['boundary']['site'],EXTERNAL+0x1000)
        self.assertEqual(r['nested_call_cutpoint']['call_site'],C+28)
        self.assertEqual(r['registers'][0],words._constant((-123)&0xffffffff))
        self.assertEqual(r['registers'][1],words._constant(234))
        self.assertEqual(r['registers'][2],words._constant((-300)&0xffffffff))
        self.assertEqual(r['registers'][3],words._pointer(E-40))
        self.assertEqual(r['registers'][13],words._pointer(E-100))
        self.assertEqual(tuple(mem(r)[E-100+i] for i in range(4)),words._pointer(E-38))
        self.assertEqual(tuple(mem(r)[E-96+i] for i in range(4)),words._pointer(E-36))
        self.assertFalse(r['nested_call_cutpoint']['callee_executed'])

    def test_masks_initialize_only_low_halfword_and_mode_byte(self):
        f=fixture(mode=0x123456ab);r=run(f);m=mem(r)
        self.assertEqual(tuple(m[E-28+i] for i in range(3)),(0,0,0xab))
        self.assertEqual(m[E-25][0],'opaque-byte')
        self.assertEqual(tuple(m[E-24+i] for i in range(4)),f['registers'][1])
        self.assertEqual(r['observed_mode'],0xab)

    def test_opaque_high_mode_dispatch_bits_are_discarded_by_real_byte_shifts(self):
        f=fixture();f['registers'][2]=(5,*opaque('discard mode')[1:]);f['registers'][3]=(0,*opaque('discard dispatch')[1:])
        r=run(f);self.assertTrue(r['reaches_explicit_nested_call'],r['boundary'])
        self.assertEqual((r['observed_mode'],r['observed_dispatch']),(5,0))

    def test_unknown_low_mode_cannot_supply_comparison_or_descriptor_bits(self):
        f=fixture();f['registers'][2]=opaque('unknown mode');r=run(f)
        self.assertEqual(r['boundary']['site'],H+18)
        self.assertFalse(r['selected_nonzero_branch'])

    def test_first_argument_alias_of_real_getter_save_changes_the_subject_read(self):
        f=fixture();f['registers'][0]=words._pointer(E-76);put(f['cells'],E-76,words._pointer(FIELDS))
        r=run(f)
        self.assertEqual(r['boundary']['site'],C+8)
        self.assertEqual(r['registers'][0],words._constant((H+118)|1))
        self.assertIn('provenance',r['boundary']['reason'])

    def test_incoming_field_pointer_aliases_helper_descriptor_and_observes_opaque_byte(self):
        f=fixture();put(f['cells'],SUBJECT,words._pointer(E-36));r=run(f)
        self.assertEqual(r['boundary']['site'],C+12)
        self.assertEqual(r['registers'][4],words._constant(0))
        self.assertIn('opaque',r['boundary']['reason'])

    def test_retired_getter_save_is_reactivated_by_coordinate_push(self):
        r=run(fixture());self.assertEqual(r['retired_spans'],[])
        events=r['memory_events']
        self.assertTrue(any(e['operation']=='retire-frame' and e['coordinates']==[E-76,E-72] for e in events))
        self.assertTrue(any(e['operation']=='allocate-frame' and e['coordinates']==[E-92,E-72] for e in events))

    def test_alias_of_coordinate_saves_observes_new_actual_push_before_signed_reads(self):
        f=fixture();put(f['cells'],SUBJECT,words._pointer(E-100))
        r=run(f)
        self.assertEqual(r['boundary']['site'],C+8)
        self.assertIn('pointer',r['boundary']['reason'])

    def test_protected_descriptor_store_refuses_after_real_masks(self):
        f=fixture();f['protected_spans']=((E-28,E-24),);r=run(f)
        self.assertEqual(r['boundary']['site'],H+40)
        self.assertEqual(r['registers'][0][2],5)
        self.assertEqual(mem(r)[E-28][0],'opaque-byte')

    def test_missing_fifth_argument_refuses_before_any_branch(self):
        f=fixture();del f['cells'][E+2];r=run(f)
        self.assertEqual(r['boundary']['site'],H+8)
        self.assertEqual(r['registers'][13],words._pointer(E-72))

    def test_missing_subject_field_does_not_get_initialized(self):
        f=fixture();del f['cells'][FIELDS+10];r=run(f)
        self.assertEqual(r['boundary']['site'],C+12)
        self.assertEqual(r['registers'][4],words._constant((-123)&0xffffffff))

    def test_numeric_subject_word_is_not_promoted_to_live_pointer(self):
        f=fixture();put(f['cells'],SUBJECT,words._constant(BASE+FIELDS));r=run(f)
        self.assertEqual(r['boundary']['site'],C+8)
        self.assertIn('provenance',r['boundary']['reason'])

    def test_dispatch_table_routes_each_unsupported_call_without_a_fake_return(self):
        for dispatch,site in [(1,150),(2,158),(3,164),(4,172),(5,194),(6,228)]:
            f=fixture(mode=13,dispatch=dispatch)
            if dispatch==6:
                put(f['cells'],E,words._pointer(9000));half(f['cells'],9000,-32768);half(f['cells'],9002,32767)
            r=run(f)
            self.assertEqual(r['nested_call_cutpoint']['call_site'],H+site)
            self.assertEqual(r['boundary']['site'],EXTERNAL+site*4)
            self.assertFalse(r['returns_to_caller'])

    def test_default_dispatch_transports_actual_sixth_arg_and_stops_at_distinct_scheduler(self):
        f=fixture(dispatch=9);r=run(f)
        self.assertEqual(r['nested_call_cutpoint']['call_site'],H+266)
        self.assertEqual(r['registers'][0],words._pointer(8000))
        self.assertEqual(r['registers'][1],words._constant(EXTERNAL+0x2001))
        self.assertEqual(r['registers'][2],words._constant(12))
        self.assertEqual(r['registers'][3],words._pointer(E-68))
        self.assertEqual(tuple(mem(r)[E-72+i] for i in range(4)),tuple(f['cells'][E+4+i] for i in range(4)))
        self.assertEqual(tuple(mem(r)[E-64+i] for i in range(4)),words._pointer(E-28))
        self.assertEqual(mem(r)[E-68][0],'opaque-byte')

    def test_missing_sixth_argument_stops_after_fixed_point_read(self):
        f=fixture(dispatch=10);del f['cells'][E+5];r=run(f)
        self.assertEqual(r['boundary']['site'],H+258)
        self.assertEqual(r['registers'][0],words._pointer(8000))

    def test_fixed_point_read_observes_alias_of_actual_stack_save(self):
        f=fixture(dispatch=11)
        b=bytearray(f['layout'].helper_data);b[284:288]=(BASE+E-20).to_bytes(4,'little')
        f['layout']=replace(f['layout'],helper_data=bytes(b));f['registers'][4]=opaque('saved fixed word')
        r=run(f)
        self.assertEqual(r['registers'][0],f['registers'][4])
        self.assertTrue(r['reaches_explicit_nested_call'])

    def test_early_zero_seven_path_is_retained_as_existing_module_boundary(self):
        r=run(fixture(mode=0,dispatch=7))
        self.assertEqual(r['boundary']['site'],H+270)
        self.assertFalse(r['selected_nonzero_branch'])

    def test_input_retired_subject_read_is_rejected(self):
        f=fixture();f['retired_spans']=((SUBJECT,SUBJECT+4),);r=run(f)
        self.assertEqual(r['boundary']['site'],G+6)
        self.assertIn('retired',r['boundary']['reason'])

    def test_known_negative_halfwords_reach_callee_as_sign_extended_words(self):
        f=fixture(mode=21)
        for offset,value in [(8,-32768),(10,-1),(12,32767)]:half(f['cells'],FIELDS+offset,value)
        r=run(f)
        self.assertEqual([r['registers'][i] for i in range(3)],
                         [words._constant(0xffff8000),words._constant(0xffffffff),words._constant(32767)])

    def test_unknown_local_namespace_does_not_collide_with_entry_tokens(self):
        f=fixture();f['cells'][100]=('opaque-byte','unmodeled helper local',0);r=run(f)
        self.assertEqual(mem(r)[E-25][1],'unmodeled helper local:1')
        self.assertEqual(mem(r)[100],f['cells'][100])

    def test_inputs_immutable_and_actual_memory_native_claims_false(self):
        f=fixture();before=copy.deepcopy(f);r=run(f);self.assertEqual(f,before)
        for k in ['fabricated_callee_results','fabricated_saved_words','role_separation_assumed','ABI_preservation_assumed',
                  'physical_access_proved','actual_heap_or_SP_proved','actual_lifetime_proved','actual_code_execution_proved',
                  'actual_termination_proved','returns_to_caller','full_CFG_closed','source_or_ELF_admission','native_admission']:
            self.assertFalse(r[k],k)

    def test_eight_new_raw_complete_owner_compositions(self):
        for mode,dispatch in [(5,0),(0,0),(255,0),(7,1),(9,3),(11,5),(13,6),(17,12)]:
            with self.subTest(mode=mode,dispatch=dispatch):
                f=fixture(mode=mode,dispatch=dispatch)
                if dispatch==6:
                    put(f['cells'],E,words._pointer(9000));half(f['cells'],9000,-17);half(f['cells'],9002,31)
                r=run(f);regs,m,trace,events,pc=raw(f)
                self.assertEqual(r['registers'],regs);self.assertEqual(mem(r),m)
                self.assertEqual(r['trace'],trace);self.assertEqual(r['boundary']['site'],pc)
                got=[(e['site'],e['operation'],e['coordinate'],e['bytes']) for e in r['memory_events'] if e['operation'].startswith(('read8','read16','read32','write'))]
                self.assertEqual(got,events)

    def test_actual_gate_state_can_continue_without_replaying_old_prefix(self):
        f=fixture(mode=29);regs,m,_,_,pc=raw(f,stop_before=H+30)
        self.assertEqual(pc,H+30)
        gate=dict(f,cells=m,registers=regs)
        r=helper.continue_from_gate(**gate,entry_sp=E)
        expected,after,trace,_,cut=raw(gate,start=H+30,gate=True)
        self.assertEqual(r['starts_at'],H+30);self.assertEqual(r['registers'],expected)
        self.assertEqual(mem(r),after);self.assertEqual(r['trace'],trace);self.assertEqual(r['boundary']['site'],cut)

    def test_gate_rejects_inconsistent_SP_or_retired_live_frame(self):
        f=fixture(mode=31);regs,m,_,_,_=raw(f,stop_before=H+30)
        bad=dict(regs);bad[13]=words._pointer(E-68)
        r=helper.continue_from_gate(**dict(f,registers=bad,cells=m),entry_sp=E)
        self.assertEqual(r['boundary']['site'],H+30)
        r=helper.continue_from_gate(**dict(f,registers=regs,cells=m),entry_sp=E,retired_spans=((E-72,E-20),))
        self.assertIn('live helper gate frame',r['boundary']['reason'])

    def test_numeric_frame_wrapping_and_unaligned_subject_access_refuse(self):
        f=fixture(mode=37);f['arena_base']=2**32-E;r=run(f)
        self.assertEqual(r['boundary']['site'],H);self.assertEqual(r['changed_cells'],{})
        f=fixture(mode=39);f['registers'][13]=words._pointer(-BASE+64);r=run(f)
        self.assertEqual(r['boundary']['site'],H+2);self.assertIn('wraps',r['boundary']['reason'])
        f=fixture(mode=41);f['registers'][0]=words._pointer(SUBJECT+1);r=run(f)
        self.assertEqual(r['boundary']['site'],G+6);self.assertIn('unaligned',r['boundary']['reason'])

    def test_push_budget_refuses_before_any_save_or_frame_activation(self):
        f=fixture(mode=43);at=100000
        while len(f['cells'])<4096:f['cells'][at]=0;at+=1
        f['retired_spans']=((E-20,E),);r=run(f)
        self.assertEqual(r['boundary']['site'],H);self.assertIn('4096',r['boundary']['reason'])
        self.assertEqual(r['changed_cells'],{});self.assertEqual(r['retired_spans'],[(E-20,E)])
        self.assertEqual(r['registers'][13],words._pointer(E));self.assertEqual(r['memory_events'],[])

    def test_local_budget_refuses_without_reactivating_or_forgetting_bytes(self):
        f=fixture(mode=47);at=100000
        while len(f['cells'])<4030:f['cells'][at]=0;at+=1
        f['retired_spans']=((E-72,E-20),);r=run(f)
        self.assertEqual(r['boundary']['site'],H+2);self.assertIn('4096',r['boundary']['reason'])
        self.assertEqual(r['retired_spans'],[(E-72,E-20)])
        self.assertEqual(r['registers'][13],words._pointer(E-20))
        self.assertFalse(any(e.get('opaque_locals') for e in r['memory_events']))

    def test_protected_nested_push_does_not_fabricate_coordinate_outputs(self):
        f=fixture(mode=53);f['protected_spans']=((E-92,E-88),);r=run(f)
        self.assertEqual(r['boundary']['site'],C);self.assertIn('protected',r['boundary']['reason'])
        self.assertFalse(r['reaches_explicit_nested_call'])
        self.assertEqual(r['registers'][13],words._pointer(E-72))
        self.assertEqual(mem(r)[E-40][0],'opaque-byte')


class BindingTests(unittest.TestCase):
    def test_new_complete_four_owner_binding(self):
        l=layout()
        self.assertEqual(helper.bind(l.helper_data,l.helper,l.getter_data,l.getter,l.identity_data,
            l.identity,l.coordinates_data,l.coordinates,selector=helper.SELECTOR),l)

    def test_complete_body_table_literals_and_nested_shapes_remain_guarded(self):
        l=layout()
        for at in [0,30,36,72,76,80,84,108,114,130,270,278,280]:
            b=bytearray(l.helper_data);b[at]^=1
            with self.assertRaises(ValueError):helper._validate(replace(l,helper_data=bytes(b)))
        with self.assertRaises(ValueError):helper._validate(replace(l,identity_data=b'\x18\x47'))
        with self.assertRaises(ValueError):helper._validate(replace(l,coordinates_data=l.coordinates_data[:-2]))

    def test_unknown_call_cannot_alias_a_composed_owner(self):
        l=layout();b=bytearray(l.helper_data);b[150:154]=branch._bl(H+150,G)
        with self.assertRaisesRegex(ValueError,'aliases'):helper._validate(replace(l,helper_data=bytes(b)))

    def test_selector_state_and_bounds_remain_explicit(self):
        for change in [dict(selector='default'),dict(registers={}),dict(arena_base=True),dict(cells={0:True})]:
            f=fixture();f.update(change)
            with self.assertRaises(ValueError):run(f)


if __name__=='__main__':unittest.main()
