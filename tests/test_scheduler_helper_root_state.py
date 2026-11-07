"""New080 conditional root states and independent raw Thumb continuation."""
from dataclasses import replace
import copy,hashlib,unittest
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_helper_root_state as root
import test_scheduler_zero40_state as prior

words=root.words
BASE,E,ROOT,NODE,PAYLOAD,REQUEST=0x02000000,8192,0x08190000,140,9000,8000

def integer(n):return words._constant(n)
def pointer(n):return words._pointer(n)
def opaque(n):return tuple(('opaque-byte',n,i) for i in range(4))
def put(m,a,w):m.update({a+i:v for i,v in enumerate(w)})
def half(m,a,v):put(m,a,tuple((v&65535).to_bytes(2,'little')))
def mem(r):return {int(k):v for k,v in r['post_cells'].items()}
def byte(v,base=BASE):
    if type(v) is int:return v
    if v[0]=='base-plus-byte':return ((base+v[1])>>(8*v[2]))&255
    return hashlib.sha256((v[1]+':'+str(v[2])).encode()).digest()[0]
def number(w,base=BASE):return int.from_bytes(bytes(byte(v,base) for v in w),'little')

def layout():
    l=prior.fixture()['layout'];h=l.prior.coordinate.helper.helper
    b=bytearray(root.ROOT)
    for off in root.CALLS:b[off:off+4]=root.atoms.remove._bl(ROOT+off,h if off==80 else 0x081a0000+off)
    return root.Layout(l,ROOT,bytes(b))

def entry_fixture(*,phase=0,option=0,entry=E):
    l=layout();r={i:opaque('080 incoming R'+str(i)) for i in range(15)}
    r.update({0:pointer(7000),1:pointer(REQUEST),2:pointer(PAYLOAD),13:pointer(entry),14:integer(0x08012345)})
    m={};half(m,REQUEST,phase);half(m,REQUEST+22,option);put(m,REQUEST+4,pointer(5000))
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=root.SELECTOR)

def tail_fixture(*,entry=E,payload=PAYLOAD):
    l=layout();h=l.prior.prior.coordinate.helper.helper
    r={i:opaque('080 post079 R'+str(i)) for i in range(15)}
    r.update({0:pointer(NODE),1:integer((h+270)|1),13:pointer(entry-124)})
    m={}
    for off,value in [(-72,pointer(payload)),(-68,pointer(REQUEST)),(-64,pointer(7000)),
                      (-60,opaque('helper saved R7')),(-56,integer((ROOT+84)|1)),
                      (-16,opaque('root saved R4')),(-12,opaque('root saved R5')),
                      (-8,opaque('root saved R6')),(-4,integer(0x08012345))]:put(m,entry+off,value)
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,root_entry_sp=entry,
                root_return_word=integer(0x08012345),selector=root.SELECTOR)


def raw(f,*,entry=False,stop_before=None):
    """Separate concrete mnemonic effects; no production executor/flags used."""
    l,base=f['layout'],f['arena_base'];h=l.prior.prior.coordinate.helper
    bodies={l.root:l.root_data,h.helper:h.helper_data}
    regs={i:number(v,base) for i,v in f['registers'].items()};m={base+k:byte(v,base) for k,v in f['cells'].items()}
    pc=l.root if entry else h.helper+270;trace=[];events=[];comparison=None
    md=Cs(CS_ARCH_ARM,CS_MODE_THUMB);md.detail=True
    names=dict(sp=13,lr=14,pc=15,sb=9,sl=10,fp=11,ip=12)
    def reg(o):
        name=md.reg_name(o.reg);return names.get(name,int(name[1:]) if name.startswith('r') else -1)
    def num(o):return o.imm if o.type==2 else regs[reg(o)]
    def read(at,width):
        vals=tuple(m[at+i] for i in range(width));events.append((pc,'read'+str(width*8),at-base,vals));return int.from_bytes(bytes(vals),'little')
    def write(at,width,value):
        vals=tuple((value&0xffffffff).to_bytes(4,'little')[:width]);m.update({at+i:v for i,v in enumerate(vals)})
        events.append((pc,'write'+str(width*8),at-base,vals))
    for _ in range(256):
        if pc==stop_before:trace.append(pc);return regs,m,trace,events,pc
        owner=next((a for a,b in bodies.items() if a<=pc<a+len(b)),None)
        if owner is None:return regs,m,trace,events,pc
        ins=next(md.disasm(bodies[owner][pc-owner:],pc,1));ops,n,nxt=ins.operands,ins.mnemonic,pc+ins.size;trace.append(pc)
        if n=='push':
            selected=[reg(o) for o in ops];at=regs[13]-4*len(selected);values=[regs[i] for i in selected]
            for i,v in enumerate(values):write(at+4*i,4,v)
            regs[13]=at
        elif n=='pop':
            at=regs[13];values=[read(at+4*i,4) for i in range(len(ops))]
            for o,v in zip(ops,values):regs[reg(o)]=v
            regs[13]=at+4*len(ops)
        elif n in ('mov','movs'):regs[reg(ops[0])]=num(ops[1])
        elif n in ('add','adds','sub','subs'):
            d=reg(ops[0]);a=num(ops[1]) if len(ops)==3 else regs[d];b=num(ops[-1]);regs[d]=(a-b if n.startswith('sub') else a+b)&0xffffffff
        elif n=='lsls':regs[reg(ops[0])]=(num(ops[1])<<num(ops[2]))&0xffffffff
        elif n=='cmp':comparison=(num(ops[0]),num(ops[1]))
        elif n in ('beq','bne','bgt'):
            a,b=comparison;aa=a-2**32 if a&0x80000000 else a;bb=b-2**32 if b&0x80000000 else b
            if dict(beq=a==b,bne=a!=b,bgt=aa>bb)[n]:nxt=ops[0].imm
        elif n=='b':nxt=ops[0].imm
        elif n=='bl':
            regs[14]=nxt|1;nxt=ops[0].imm
            if entry:return regs,m,trace,events,nxt
        elif n=='bx':nxt=regs[reg(ops[0])]&~1
        elif n in ('ldr','ldrb','ldrh','str','strb','strh'):
            bn=md.reg_name(ops[1].mem.base);width=1 if n.endswith('b') else 2 if n.endswith('h') else 4
            if bn=='pc':
                at=((pc+4)&~3)+ops[1].mem.disp;regs[reg(ops[0])]=int.from_bytes(bodies[owner][at-owner:at-owner+4],'little')
            else:
                at=regs[names.get(bn,int(bn[1:]) if bn.startswith('r') else -1)]+ops[1].mem.disp
                if n.startswith('ldr'):regs[reg(ops[0])]=read(at,width)
                else:write(at,width,regs[reg(ops[0])])
        else:raise AssertionError((hex(pc),n,ins.op_str))
        pc=nxt
    raise AssertionError('independent raw bound exhausted')


class ContinuationTests(unittest.TestCase):
    def assert_raw(self,f,r,*,entry=False,stop_before=None):
        regs,m,trace,events,pc=raw(f,entry=entry,stop_before=stop_before)
        self.assertEqual(r['trace'],trace);self.assertEqual(r['final_PC'],pc)
        self.assertEqual({i:number(v,f['arena_base']) for i,v in r['registers'].items()},regs)
        for a,v in m.items():self.assertEqual(byte(mem(r)[a-f['arena_base']],f['arena_base']),v)
        got=[(v['site'],v['operation'],v['coordinate'],tuple(byte(b,f['arena_base']) for b in v['bytes'])) for v in r['memory_events'] if 'coordinate' in v]
        self.assertEqual(got,events)

    def test_new_helper_tail_and_root_return_equal_raw(self):
        f=tail_fixture();r=root.derive_continuation(**f)
        self.assertIsNone(r['boundary']);self.assertEqual(r['conditional_returns'],dict(helper=True,root=True))
        self.assertEqual(r['registers'][0],integer(0));self.assertEqual(r['registers'][13],pointer(E));self.assert_raw(f,r)
        self.assertEqual(tuple(mem(r)[PAYLOAD+20+i] for i in range(4)),pointer(NODE))

    def test_new_root_phase0_mode5_entry_equal_raw(self):
        f=entry_fixture();r=root.derive_entry(**f)
        self.assertTrue(r['reaches_helper_entry']);self.assertEqual(r['helper_mode'],5);self.assert_raw(f,r,entry=True)
        self.assertEqual(r['registers'][0],pointer(5000));self.assertEqual(r['registers'][13],pointer(E-52))

    def test_new_root_phase0_nonzero_low_option_mode0_equal_raw(self):
        f=entry_fixture(option=257);r=root.derive_entry(**f)
        self.assertEqual(r['helper_mode'],0);self.assert_raw(f,r,entry=True)
        self.assertEqual(mem(r)[PAYLOAD+2],1)

    def test_new_root_phase0_option_high_byte_does_not_change_mode(self):
        f=entry_fixture(option=256);r=root.derive_entry(**f)
        self.assertEqual(r['helper_mode'],5);self.assert_raw(f,r,entry=True)

    def test_new_root_payload_store_overwrites_saved_R4_observed_at_POP(self):
        f=tail_fixture(payload=E-36);r=root.derive_continuation(**f)
        self.assertIsNone(r['boundary']);self.assertEqual(r['registers'][4],pointer(NODE));self.assert_raw(f,r)

    def test_new_root_payload_store_overwrites_saved_LR_pointer_not_code(self):
        f=tail_fixture(payload=E-24);r=root.derive_continuation(**f)
        self.assertEqual(r['boundary']['site'],ROOT+228);self.assertIn('scalar/control',r['boundary']['reason'])
        self.assertEqual(r['registers'][1],pointer(NODE));self.assertFalse(r['conditional_returns']['root'])

    def test_new_root_payload_store_wrong_numeric_LR_is_observed(self):
        f=tail_fixture(payload=E-24);f['registers'][0]=integer(0x08015555);r=root.derive_continuation(**f)
        self.assertEqual(r['boundary']['site'],ROOT+228);self.assertIn('differs from incoming LR',r['boundary']['reason'])
        self.assert_raw(f,r,stop_before=ROOT+228)

    def test_new_helper_corrupted_LR_stops_before_root_write(self):
        f=tail_fixture();put(f['cells'],E-56,integer(0x08013333));r=root.derive_continuation(**f)
        self.assertEqual(r['boundary']['site'],f['layout'].prior.prior.coordinate.helper.helper+276)
        self.assertFalse(r['conditional_returns']['helper']);self.assertNotIn(ROOT+84,r['trace'])

    def test_new_helper_opaque_return_is_not_inferred_from_expected_call(self):
        f=tail_fixture();put(f['cells'],E-56,opaque('unknown helper return'));r=root.derive_continuation(**f)
        self.assertIn('scalar/control',r['boundary']['reason']);self.assertFalse(r['conditional_returns']['helper'])

    def test_new_retired_helper_local_payload_write_is_refused(self):
        f=tail_fixture(payload=E-120);r=root.derive_continuation(**f)
        self.assertEqual(r['boundary']['site'],ROOT+84);self.assertIn('retired',r['boundary']['reason'])

    def test_new_retired_predecessor_save_is_preserved_as_dead(self):
        f=tail_fixture(payload=E-160);f['retired_spans']=((E-180,E-124),);r=root.derive_continuation(**f)
        self.assertIn('retired',r['boundary']['reason'])

    def test_new_live_root_local_write_precedes_real_retirement(self):
        f=tail_fixture(payload=E-64);r=root.derive_continuation(**f)
        self.assertIsNone(r['boundary']);self.assertEqual(tuple(mem(r)[E-44+i] for i in range(4)),pointer(NODE));self.assert_raw(f,r)

    def test_new_protected_payload_write_is_refused(self):
        f=tail_fixture();f['protected_spans']=((PAYLOAD+20,PAYLOAD+24),);r=root.derive_continuation(**f)
        self.assertIn('protected',r['boundary']['reason']);self.assertTrue(r['conditional_returns']['helper'])

    def test_new_payload_aliases_executing_root_is_refused(self):
        f=tail_fixture(payload=ROOT-BASE-20);r=root.derive_continuation(**f)
        self.assertIn('immutable owner',r['boundary']['reason'])

    def test_new_missing_actual_helper_save_is_precise(self):
        f=tail_fixture();del f['cells'][E-71];r=root.derive_continuation(**f)
        self.assertEqual(r['boundary']['site'],f['layout'].prior.prior.coordinate.helper.helper+272)
        self.assertEqual(r['boundary']['coordinate'],E-72)

    def test_new_wrong_helper_frame_is_rejected_before_execution(self):
        f=tail_fixture();f['registers'][13]=pointer(E-120);r=root.derive_continuation(**f)
        self.assertEqual(r['trace'],[]);self.assertIn('frame relation',r['boundary']['reason'])

    def test_new_root_even_return_has_no_Thumb_authority(self):
        f=tail_fixture();f['root_return_word']=integer(0x08012344);put(f['cells'],E-4,f['root_return_word'])
        r=root.derive_continuation(**f);self.assertIn('Thumb continuation',r['boundary']['reason'])

    def test_new_root_entry_option_write_aliases_following_subject_word(self):
        f=entry_fixture(option=0x55);f['registers'][2]=pointer(REQUEST+2)
        r=root.derive_entry(**f);self.assertFalse(r['reaches_helper_entry'])
        self.assertEqual(r['boundary']['site'],ROOT+58);self.assertIn('unaligned',r['boundary']['reason'])
        self.assertNotEqual(r['registers'][5],pointer(5000));self.assertEqual(r['registers'][5][0],0x55)
        self.assert_raw(f,r,entry=True,stop_before=ROOT+58)

    def test_new_root_entry_saved_LR_alias_is_written_not_sanitized(self):
        f=entry_fixture();f['registers'][2]=pointer(E-20);r=root.derive_entry(**f)
        self.assertEqual(tuple(mem(r)[E-4+i] for i in range(4)),pointer(5000));self.assert_raw(f,r,entry=True)

    def test_new_entry_nonzero_phase_stops_at_exact_other_case(self):
        f=entry_fixture(phase=1);r=root.derive_entry(**f)
        self.assertEqual(r['boundary']['site'],ROOT+92);self.assertFalse(r['reaches_helper_entry'])

    def test_new_entry_phase257_remains_outside_this_branch(self):
        f=entry_fixture(phase=257);r=root.derive_entry(**f)
        self.assertEqual(r['boundary']['site'],ROOT+136);self.assertFalse(r['reaches_helper_entry'])

    def test_new_entry_does_not_initialize_opaque_private_record(self):
        f=entry_fixture();r=root.derive_entry(**f);m=mem(r)
        for off in range(8,36):self.assertEqual(m[E-52+off],('opaque-byte','080 root local',off))
        self.assertFalse(r['actual_reaching_state_proved'])

    def test_new_complete_root_unused_byte_mutation_rejected(self):
        f=tail_fixture();b=bytearray(f['layout'].root_data);b[200]^=1;f['layout']=replace(f['layout'],root_data=bytes(b))
        with self.assertRaisesRegex(ValueError,'complete230B'):root.derive_continuation(**f)

    def test_new_root_helper_call_identity_cannot_be_swapped(self):
        f=tail_fixture();b=bytearray(f['layout'].root_data);b[80:84]=root.atoms.remove._bl(ROOT+80,0x08011110);f['layout']=replace(f['layout'],root_data=bytes(b))
        with self.assertRaisesRegex(ValueError,'identify retained helper'):root.derive_continuation(**f)

    def test_new_explicit_selector_has_no_default_admission(self):
        f=tail_fixture();f['selector']='default'
        with self.assertRaisesRegex(ValueError,'explicit080'):root.derive_continuation(**f)

    def test_new_real_prefix_through_retained_chain_to_root_return(self):
        f=entry_fixture(entry=E+256);l=f['layout'];m=f['cells'];p=l.prior.prior
        m.update(prior.prior_fixtures.heap(size=10));put(m,2400,pointer(11000));put(m,11000,pointer(0))
        half(m,11012,42);put(m,7000+16,integer(0));put(m,5000,pointer(5200))
        for off,v in [(8,30),(10,40),(12,50)]:half(m,5200+off,v)
        for off,v in [(32,1000),(34,2000),(36,870),(38,1904)]:half(m,10000+off,v)
        report=root.compose(**f)
        self.assertTrue(report['conditional_root_return'],(report['stage'],report['boundary']))
        self.assertEqual(list(report['stages']),['root-entry','helper075','coordinate076','scheduler078','zero079','return080'])
        first=report['stages']['root-entry'];self.assert_raw(f,first,entry=True)
        before=report['stages']['zero079'];end=report['stages']['return080']
        tail=dict(layout=l,arena_base=BASE,cells=mem(before),registers=before['registers'],root_entry_sp=E+256,root_return_word=f['registers'][14],selector=root.SELECTOR)
        self.assert_raw(tail,end)
        self.assertEqual(tuple(mem(report)[PAYLOAD+20+i] for i in range(4)),pointer(140))
        self.assertEqual(report['registers'][13],pointer(E+256));self.assertFalse(report['actual_root_return_executed'])
        changed=copy.deepcopy(before);changed['scheduler_entry_SP']+=4
        with self.assertRaisesRegex(ValueError,'079 successful'):root.continue_from_079(l,BASE,changed,E+256,f['registers'][14],selector=root.SELECTOR)

    def test_new_output_preserves_remaining_conditions_and_stale_alias(self):
        f=tail_fixture();f['registers'][10]=pointer(E-100);r=root.derive_continuation(**f)
        self.assertIsNone(r['boundary']);self.assertEqual(r['known_retired_alias_registers']['10'],E-100)
        for key in ['actual_reaching_state_proved','physical_access_proved','actual_heap_or_SP_proved',
                    'actual_lifetime_proved','actual_installed_identity_proved','actual_code_execution_proved',
                    'actual_termination_proved','whole_owner_CFG_closed','Sqrt_effect_proved',
                    'actual_root_return_executed','source_or_ELF_admission','native_admission']:
            self.assertFalse(r[key],key)
        self.assertEqual(len(r['obligations']),6)


    def test_new_alias_composition_restores_actual_written_saved_R4(self):
        import json
        from pathlib import Path
        e=E+512;f=entry_fixture(entry=e);f['registers'][2]=pointer(e-36);m=f['cells']
        m.update(prior.prior_fixtures.heap(size=10));put(m,2400,pointer(11000));put(m,11000,pointer(0))
        half(m,11012,39);put(m,7016,integer(0));put(m,5000,pointer(5200))
        for off,v in [(8,36),(10,40),(12,50)]:half(m,5200+off,v)
        for off,v in [(32,1000),(34,2000),(36,873),(38,1905)]:half(m,10000+off,v)
        report=root.compose(**f)
        self.assertTrue(report['conditional_root_return'],(report['stage'],report['boundary']))
        self.assertEqual(report['registers'][4],pointer(140));self.assertNotEqual(report['registers'][4],f['registers'][4])
        self.assert_raw(f,report['stages']['root-entry'],entry=True)
        before=report['stages']['zero079'];end=report['stages']['return080']
        tail=dict(layout=f['layout'],arena_base=BASE,cells=mem(before),registers=before['registers'],root_entry_sp=e,root_return_word=f['registers'][14],selector=root.SELECTOR)
        self.assert_raw(tail,end)
        artifact=Path(__file__).resolve().parents[1]/'build/new-composition-alias.json'
        self.assertFalse(artifact.exists());artifact.write_text(json.dumps(report,indent=2)+'\n')
        self.assertEqual(end['inherited_079_obligations'],before['obligations'])
        self.assertEqual(end['inherited_078_obligations'],before['inherited_078_obligations'])

    def test_new_nonmatching_motion_state_retains_exact_Sqrt_entry(self):
        f=entry_fixture(entry=E+768);m=f['cells'];p=f['layout'].prior.prior
        put(m,5000,pointer(5200))
        for off,v in [(8,44),(10,12),(12,20)]:half(m,5200+off,v)
        for off,v in [(32,1000),(34,2000),(36,999),(38,999)]:half(m,10000+off,v)
        r=root.compose(**f)
        self.assertFalse(r['conditional_root_return']);self.assertEqual(r['stage'],'coordinate076')
        target=root.helper.shapes._call(p.coordinate.motion_data,p.coordinate.motion,128)
        self.assertEqual(r['boundary']['site'],target);self.assertFalse(r['Sqrt_effect_proved'])
        self.assertNotIn('scheduler078',r['stages'])

    def test_new_opaque_root_return_is_not_replaced_by_incoming_snapshot(self):
        f=tail_fixture();put(f['cells'],E-4,opaque('opaque root saved LR'));r=root.derive_continuation(**f)
        self.assertEqual(r['boundary']['site'],ROOT+228);self.assertIn('scalar/control',r['boundary']['reason'])

    def test_new_root_entry_push_aliases_phase_before_phase_read(self):
        f=entry_fixture();f['registers'][1]=pointer(E-16);f['registers'][4]=integer(256)
        r=root.derive_entry(**f)
        self.assertEqual(r['observed_root_phase'],256);self.assertEqual(r['boundary']['site'],ROOT+98)
        self.assertFalse(r['reaches_helper_entry'])

    def test_new_return_budget_stops_without_invented_helper_return(self):
        f=tail_fixture();f['max_steps']=2;r=root.derive_continuation(**f)
        self.assertIn('bound exhausted',r['boundary']['reason']);self.assertEqual(len(r['trace']),2)
        self.assertFalse(r['conditional_returns']['helper'])

    def test_new_root_SP_numeric_wrap_has_no_successful_return(self):
        f=tail_fixture();f['arena_base']=2**32-4096;r=root.derive_continuation(**f)
        self.assertIn('wraps',r['boundary']['reason']);self.assertEqual(r['trace'],[])

    def test_new_root_complete_owner_cannot_alias_image(self):
        f=tail_fixture();f['layout']=replace(f['layout'],root=f['layout'].prior.image_base)
        with self.assertRaisesRegex(ValueError,'overlaps retained'):root.derive_continuation(**f)

    def test_new_false079_success_report_cannot_transport_state(self):
        f=tail_fixture()
        with self.assertRaisesRegex(ValueError,'079 successful'):
            root.continue_from_079(f['layout'],BASE,dict(schema=prior.zero.SELECTOR,boundary=None),E,integer(0x08012345),selector=root.SELECTOR)
