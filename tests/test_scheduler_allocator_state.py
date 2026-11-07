"""New shared-arena scheduler states, aliases, opaque bytes and refusals."""
from pathlib import Path
import copy
import unittest

import scheduler_allocator_state as state
import allocator_wrapper_relation as wrapper
import allocator_split_relation as split
import allocator_search_relation as search
import allocator_remove_relation as remove
import allocator_insert_relation as insert

INPUTS=Path(__file__).resolve().parents[1]/'inputs'
Z12=(INPUTS/'retained-zero12.json').read_bytes()
Z92=(INPUTS/'retained-zero92.json').read_bytes()
CALLBACK=0x080e5f51


def field(cells,at,value):
    cells[at]=value&255;cells[at+1]=(value>>8)&255


def pointer(cells,at,value):
    for i in range(4):cells[at+i]=0 if value is None else ('base-plus-byte',value,i)


def fixture(*,parent=None,chain=(),scheduler=1024,descriptor=512,phase=7,block_size=40):
    cells={}
    for at,value in [(0,32),(2,32),(4,1),(130,0),(134,block_size),(136,0),(138,0)]:field(cells,at,value)
    pointer(cells,-64,parent);pointer(cells,scheduler,0)
    pointer(cells,scheduler+4,None);field(cells,scheduler+12,phase)
    pointer(cells,(scheduler+4) if parent is None else (parent+16),chain[0] if chain else None)
    for i,node in enumerate(chain):pointer(cells,node+8,chain[i+1] if i+1<len(chain) else None)
    for i in range(28):cells[descriptor+i]=('opaque-byte','original descriptor',i)
    return cells


def layout(a=0x08004000):
    w=a+0x1000;c=a+0x2000;s=a+0x3000;r=a+0x4000;m=a+0x5000;i=a+0x6000;t=a+0x7000;cb=a+0x8000
    sl=search.bind(search.SHAPE,s,87,selector=search.SELECTOR)
    ml=remove.bind(remove.REMOVE_HEAD+remove._bl(r+124,m)+remove.REMOVE_TAIL,r,remove.MEDIAN,m,(66,51),selector=remove.SELECTOR)
    il=insert.bind(insert.HEAD+remove._bl(i+22,s)+insert.MIDDLE+remove._bl(i+138,m)+insert.TAIL,i,73,sl,ml,selector=insert.SELECTOR)
    al=split.bind(split._encoded(c,il,t,0x08300000),c,127,il,t,b'\x10\x47',0x08300000,selector=split.SELECTOR)
    wl=wrapper.bind(wrapper.HEAD+remove._bl(w+34,c)+wrapper.TAIL,w,26,al,selector=wrapper.SELECTOR)
    return state.bind(state._encoded(a,wl,cb),a,97,wl,cb,b'\x18\x47',selector=state.SELECTOR)


def run(cells=None,*,size=64,scheduler=1024,descriptor=512,callback=CALLBACK,**kw):
    kw.setdefault('zero12_receipt',Z12);kw.setdefault('zero92_receipt',Z92);kw.setdefault('observed_zero_target',0x03005e79)
    return state.derive(layout(),size,fixture() if cells is None else cells,scheduler,descriptor,callback,-64,selector=state.SELECTOR,**kw)


def output_pointer(cells,at):
    values=[cells[str(at+i)] for i in range(4)]
    return None if values==[0]*4 else values[0][1]


class SchedulerStateTests(unittest.TestCase):
    def test_closed_complete_partition_and_relocated_owner(self):
        l=layout(0x08020000);b=state._encoded(l.address,l.allocator,l.callback_thunk)
        self.assertEqual(len(b),206);self.assertEqual(b[98:100],b'\x00\x00')
        self.assertEqual(int.from_bytes(b[100:104],'little'),l.allocator.allocator.pointer_literal)

    def test_mutated_body_calls_pool_padding_count_and_callback_refuse(self):
        l=layout();b=state._encoded(l.address,l.allocator,l.callback_thunk)
        for at in [0,18,34,48,82,98,100,140,154,180,204]:
            changed=bytearray(b);changed[at]^=1
            with self.subTest(at=at),self.assertRaises(ValueError):
                state.bind(bytes(changed),l.address,97,l.allocator,l.callback_thunk,b'\x18\x47',selector=state.SELECTOR)
        for count,thunk in [(98,b'\x18\x47'),(97,b'\x10\x47')]:
            with self.subTest(count=count,thunk=thunk),self.assertRaises(ValueError):
                state.bind(b,l.address,count,l.allocator,l.callback_thunk,thunk,selector=state.SELECTOR)

    def test_full_allocator_zero_global_empty_and_cutpoint(self):
        r=run();self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        self.assertEqual((r['count'],r['allocation'],r['phase_after_effects']),(92,140,7))
        self.assertEqual(output_pointer(r['changed_cells'],1028),140)
        self.assertEqual(r['conditional_cutpoint_registers'],dict(R2=['base-plus',164],R4=92,R5=['base-plus',1024],R6=0,
            R7=['base-plus',140],R8=CALLBACK,R9=['base-plus',512],SP=-120))
        self.assertEqual(r['descriptor_snapshot'],[('opaque-byte','original descriptor',i) for i in range(28)])

    def test_parent_empty_updates_parent_head_and_allocation_parent(self):
        r=run(fixture(parent=768));self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        self.assertEqual(output_pointer(r['changed_cells'],784),140)
        self.assertEqual(output_pointer(r['changed_cells'],152),768)
        self.assertNotIn('1028',r['changed_cells'])

    def test_global_chain_performs_every_real_advance_reload(self):
        r=run(fixture(chain=(600,640,680)));self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        self.assertEqual(r['visited_nodes'],[600,640,680])
        reads=[e for e in r['memory_events'] if e.get('role') in ['initial next test','loop advance reload','loop next test']]
        self.assertEqual([(e['site']-0x08004000,e['coordinate']) for e in reads],[(130,608),(140,608),(142,648),(140,648),(142,688)])
        self.assertEqual(output_pointer(r['changed_cells'],688),140)
        self.assertEqual(output_pointer(r['changed_cells'],144),680)

    def test_parent_chain_has_distinct_sites_and_parent_store_last(self):
        r=run(fixture(parent=768,chain=(600,640)));self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        writes=[e for e in r['memory_events'] if e.get('role') in ['tail next assignment','allocation previous assignment','allocation parent assignment']]
        self.assertEqual([e['site']-0x08004000 for e in writes],[92,94,110])
        self.assertEqual([e['coordinate'] for e in writes],[648,144,152])

    def test_stable_cycle_refuses_before_tail_write(self):
        cells=fixture(chain=(600,640));pointer(cells,648,600)
        r=run(cells);self.assertFalse(r['reaches_copy_cutpoint']);self.assertIn('cycle',r['boundary']['reason'])
        self.assertFalse(any(e.get('role')=='tail next assignment' for e in r['memory_events']))

    def test_link_budget_is_refusal_not_termination(self):
        r=run(fixture(chain=(600,640)),max_links=1)
        self.assertFalse(r['reaches_copy_cutpoint']);self.assertIn('link bound',r['boundary']['reason'])
        self.assertEqual(r['boundary']['site'],0x0800408c)

    def test_opaque_phase_not_initialized_by_unrelated_zero(self):
        cells=fixture();cells[1036]=('opaque-byte','unknown phase',0)
        r=run(cells);self.assertFalse(r['reaches_copy_cutpoint'])
        self.assertEqual(r['boundary']['site'],0x08004038);self.assertIn('opaque',r['boundary']['reason'])

    def test_zero_alias_derives_phase0_and_reloads_head_after_write(self):
        r=run(fixture(scheduler=140),scheduler=140)
        self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        self.assertEqual(r['phase_after_effects'],0)
        self.assertEqual(output_pointer(r['changed_cells'],144),140)
        self.assertFalse(r['actual_phase_zero_proved'])

    def test_callback_bits_can_alias_phase_without_becoming_heap_pointer(self):
        # Scheduler128 phase140 is overwritten by callback before LDRH.
        cells=fixture(scheduler=128)
        # Scheduler.head132 overlaps selected.size134. Restore size25 after
        # constructing that shared word; the actual no-split path avoids
        # interpreting physical-next130, which overlaps the heap pointer.
        field(cells,134,25)
        r=run(cells,scheduler=128)
        self.assertFalse(r['reaches_copy_cutpoint'])
        self.assertEqual(r['phase_after_effects'],CALLBACK&65535)
        self.assertEqual(r['boundary']['site'],0x08004072)
        self.assertIn('pointer word',r['boundary']['reason'])

    def test_existing_head_at_allocation_creates_real_self_links(self):
        r=run(fixture(chain=(140,)))
        self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        self.assertEqual(output_pointer(r['changed_cells'],148),140)
        self.assertEqual(output_pointer(r['changed_cells'],144),140)
        self.assertEqual(r['visited_nodes'],[140])

    def test_parent_head_alias_can_replace_callback_slot(self):
        r=run(fixture(parent=124),callback=0)
        self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        self.assertEqual(r['callback_slot_snapshot'],[('base-plus-byte',140,i) for i in range(4)])
        self.assertEqual(r['conditional_cutpoint_registers']['R8'],0)
        self.assertFalse(r['callback_effects_closed'])

    def test_unknown_callback_origin_survives_without_scalar_promotion(self):
        r=run(callback=('word-origin','incoming callback'))
        self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        self.assertEqual(r['callback_slot_snapshot'],[('opaque-byte','incoming callback',i) for i in range(4)])

    def test_numeric_nonzero_head_does_not_gain_pointer_provenance(self):
        cells=fixture()
        for i in range(4):cells[1028+i]=(0x02000000>>(8*i))&255
        r=run(cells);self.assertFalse(r['reaches_copy_cutpoint']);self.assertIn('pointer word',r['boundary']['reason'])

    def test_missing_parent_word_refuses_before_allocator(self):
        cells=fixture();del cells[-63]
        r=run(cells);self.assertFalse(r['reaches_copy_cutpoint'])
        self.assertEqual(r['boundary']['site'],0x08004012);self.assertIsNone(r['allocator_relation'])

    def test_null_or_different_heap_word_refuses_formal_base_binding(self):
        for target in [None,4]:
            cells=fixture();pointer(cells,1024,target)
            r=run(cells);self.assertFalse(r['reaches_copy_cutpoint']);self.assertIn('chosen symbolic heap base',r['boundary']['reason'])

    def test_null_allocator_result_remains_exact_direct_zero_boundary(self):
        r=run(fixture(block_size=22));self.assertFalse(r['reaches_copy_cutpoint'])
        self.assertEqual(r['boundary']['site'],0x08004030);self.assertIn('destination is null',r['boundary']['reason'])

    def test_different_count_keeps_allocator_effects_then_refuses_zero(self):
        r=run(size=65);self.assertFalse(r['reaches_copy_cutpoint'])
        self.assertEqual(r['count'],93);self.assertIn('count92',r['boundary']['reason'])
        self.assertTrue(r['allocator_relation']['returns_under_witness'])
        self.assertFalse(any(e['operation']=='conditional-installed-zero92' for e in r['memory_events']))

    def test_zero92_receipt_and_target_remain_explicit(self):
        r=run(zero92_receipt=Z92+b' ')
        self.assertFalse(r['reaches_copy_cutpoint']);self.assertIn('certificate',r['boundary']['reason'])
        r=run(fixture(block_size=23),observed_zero_target=None)
        self.assertFalse(r['reaches_copy_cutpoint']);self.assertIn('R2 word',r['boundary']['reason'])

    def test_protected_descriptor_alias_stops_before_zero(self):
        cells=fixture(descriptor=160)
        r=run(cells,descriptor=160,protected_spans=((160,188),))
        self.assertFalse(r['reaches_copy_cutpoint']);self.assertEqual(r['boundary']['site'],0x08004030)
        self.assertIn('protected',r['boundary']['reason'])

    def test_unprotected_descriptor_alias_keeps_changed_bytes(self):
        r=run(fixture(descriptor=160),descriptor=160)
        self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        self.assertEqual(r['descriptor_snapshot'][:4],[0,0,7,0])
        self.assertFalse(r['source_initialization_proved'])

    def test_scheduler_saved_frame_cannot_overlap_protected_source(self):
        r=run(protected_spans=((-80,-76),))
        self.assertFalse(r['reaches_copy_cutpoint']);self.assertEqual(r['memory_events'],[])

    def test_parent_pointer_alignment_refuses_at_actual_word_access(self):
        cells=fixture();pointer(cells,-64,601)
        r=run(cells);self.assertFalse(r['reaches_copy_cutpoint'])
        self.assertEqual(r['boundary']['site'],0x08004040)
        self.assertIn('unaligned',r['boundary']['reason'])

    def test_later_link_cannot_read_expired_allocator_save_as_heap(self):
        cells=fixture(chain=(600,));pointer(cells,608,-180)
        r=run(cells);self.assertFalse(r['reaches_copy_cutpoint']);self.assertIn('frame envelope',r['boundary']['reason'])
        self.assertEqual(r['boundary']['coordinate'],-172)

    def test_source_omission_and_input_state_do_not_create_initialization(self):
        cells=fixture();before=copy.deepcopy(cells)
        for i in range(28):del cells[512+i]
        r=run(cells);self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        self.assertEqual(r['descriptor_snapshot'],[None]*28)
        self.assertEqual(cells,{k:v for k,v in before.items() if not 512<=k<540})
        self.assertTrue(all(not o['proved'] for o in r['obligations']))
        self.assertFalse(r['full_scheduler_proved']);self.assertFalse(r['source_or_native_admission'])

    def test_closed_input_shapes_and_existing_budgets(self):
        for kw in [dict(size=True),dict(max_links=129),dict(max_search_transitions=257),dict(max_median_links=257),
                   dict(callback=('guessed-function',1)),dict(scheduler=1025)]:
            with self.subTest(kw=kw),self.assertRaises(ValueError):run(**kw)

    def test_eight_new_prefix_states_match_raw_thumb_with_retained_callee_effects(self):
        cases=[
            (dict(scheduler=1152,descriptor=896,phase=9),CALLBACK+16),
            (dict(scheduler=1152,descriptor=896,phase=13,parent=832),CALLBACK+16),
            (dict(scheduler=1152,descriptor=896,phase=5,chain=(704,736,800)),CALLBACK+16),
            (dict(scheduler=1152,descriptor=896,phase=2,parent=832,chain=(704,736)),CALLBACK+16),
            (dict(scheduler=140,descriptor=896,phase=17),CALLBACK+16),
            (dict(scheduler=1152,descriptor=896,phase=9,chain=(140,)),CALLBACK+16),
            (dict(scheduler=1152,descriptor=896,phase=11,parent=124),0),
            (dict(scheduler=1152,descriptor=896,phase=11),('word-origin','transport-only'))]
        for parameters,callback in cases:
            with self.subTest(parameters=parameters,callback=callback):
                cells=fixture(**parameters)
                r=run(cells,scheduler=parameters['scheduler'],descriptor=parameters['descriptor'],callback=callback)
                self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
                events,memory,regs=execute_prefix(layout(),cells,parameters['scheduler'],parameters['descriptor'],callback,r['allocator_relation'])
                actual=[]
                for e in r['memory_events']:
                    if not 0x08004000<=e['site']<0x0800409a:continue
                    op=e['operation']
                    if op in ('read32','write32','read16','write16','write32-origin'):
                        actual.append((e['site'],op,e['coordinate'],e['value']))
                    elif op=='zero-write':actual.append((e['site'],op,e['coordinate'],e['width'],e['value']))
                self.assertEqual(actual,events)
                self.assertEqual(r['changed_cells'],{str(k):memory[k] for k in map(int,r['changed_cells'])})
                self.assertEqual(r['conditional_cutpoint_registers'],regs)
                self.assertEqual(r['descriptor_snapshot'],[memory.get(parameters['descriptor']+i) for i in range(28)])

    def test_incoming_parent_word_cannot_be_reused_as_heap_next(self):
        cells=fixture(chain=(-72,))
        r=run(cells)
        self.assertFalse(r['reaches_copy_cutpoint'])
        self.assertEqual(r['boundary']['coordinate'],-64)
        self.assertIn('protected',r['boundary']['reason'])

    def test_pointer_arithmetic_does_not_wrap_outside_relative_arena(self):
        cells=fixture();pointer(cells,1028,2**31-4)
        r=run(cells)
        self.assertFalse(r['reaches_copy_cutpoint'])
        self.assertIn('outside bounded arena',r['boundary']['reason'])

    def test_scheduler_phase_and_descriptor_phase_are_distinct(self):
        cells=fixture(phase=19);field(cells,512,0xabcd)
        r=run(cells)
        self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        self.assertEqual(r['phase_after_effects'],19)
        self.assertEqual(r['descriptor_snapshot'][:2],[0xcd,0xab])
        self.assertFalse(r['actual_phase_zero_proved'])
        # Retained062 separately copies these bytes then explicitly stores0
        # to the local descriptor halfword; no callback observation occurs here.
        self.assertFalse(r['callback_effects_closed'])

    def test_descriptor_inside_private_frame_never_reuses_entry_bytes(self):
        cells=fixture(descriptor=-96)
        for i in range(28):cells[-96+i]=0xaa
        r=run(cells,descriptor=-96)
        self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        self.assertTrue(r['descriptor_intersects_unmodeled_frame'])
        self.assertFalse(r['descriptor_frame_transport_authorized'])
        self.assertEqual(r['descriptor_snapshot'],[('opaque-byte','unmodeled private-frame byte',100+i) for i in range(28)])

    def test_descriptor_partial_frame_overlap_masks_only_unmodeled_bytes(self):
        r=run(fixture(descriptor=-204),descriptor=-204)
        self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        self.assertEqual(r['descriptor_snapshot'][:8],[('opaque-byte','original descriptor',i) for i in range(8)])
        self.assertEqual(r['descriptor_snapshot'][8:],[('opaque-byte','unmodeled private-frame byte',i) for i in range(20)])
        self.assertFalse(r['descriptor_frame_transport_authorized'])

    def test_new_outside_frame_snapshot_keeps_post_effect_alias_bytes(self):
        r=run(fixture(descriptor=168,phase=21),descriptor=168)
        self.assertTrue(r['reaches_copy_cutpoint'],r['boundary'])
        self.assertFalse(r['descriptor_intersects_unmodeled_frame'])
        self.assertEqual(r['descriptor_snapshot'],[0]*28)
        self.assertIsNone(r['descriptor_frame_transport_authorized'])


def execute_prefix(l,cells,scheduler,descriptor,callback,allocator_report):
    """Raw prefix instructions; apply already-derived explicit callee effects.

The supplied allocator report is from this NEW composed witness. It is not
recomputed in the oracle. The retained zero92 contract is applied at its call.
"""
    data=state._encoded(l.address,l.allocator,l.callback_thunk)
    memory=dict(cells);regs=[('entry',i) for i in range(16)]
    regs[0]=('base',scheduler);regs[1]=callback;regs[2]=64;regs[3]=('base',descriptor)
    regs[13]=('base',-64);pc=l.address;zero=False;events=[]
    def add(x,y):
        return ('base',x[1]+y) if type(x)is tuple and x[0]=='base' else (x+y)&0xffffffff
    def visible(x):return ['base-plus',x[1]] if type(x)is tuple and x[0]=='base' else x
    def at(reg,offset):
        p=regs[reg];assert type(p)is tuple and p[0]=='base';return p[1]+offset
    def store_word(where,value):
        if type(value)is int:bs=[(value>>(8*i))&255 for i in range(4)]
        elif value[0]=='base':bs=[('base-plus-byte',value[1],i) for i in range(4)]
        elif value[0]=='word-origin':bs=[('opaque-byte',value[1],i) for i in range(4)]
        else:bs=[('saved-word-byte',value,i) for i in range(4)]
        for i,b in enumerate(bs):memory[where+i]=b
    def load_word(where):
        bs=[memory[where+i] for i in range(4)]
        if all(type(b)is int for b in bs):return sum(b<<(8*i) for i,b in enumerate(bs))
        assert all(type(b)is tuple and b[2]==i and b[:2]==bs[0][:2] for i,b in enumerate(bs))
        return ('base',bs[0][1]) if bs[0][0]=='base-plus-byte' else ('word-origin',bs[0][1])
    for _ in range(1000):
        if pc==l.address+154:
            result={f'R{i}':visible(regs[i]) for i in [2,4,5,6,7,8,9]}
            result['SP']=regs[13][1]
            return events,memory,result
        off=pc-l.address;raw=int.from_bytes(data[off:off+2],'little');nxt=pc+2
        if raw&0xf800==0xf000:
            second=int.from_bytes(data[off+2:off+4],'little');delta=((raw&2047)<<12)|((second&2047)<<1)
            if delta&(1<<22):delta-=1<<23
            target=pc+4+delta;regs[14]=(pc+4)|1;nxt=pc+4
            if target==l.allocator.address:
                assert pc==l.address+34 and regs[0]==('base',0) and regs[1]==92 and regs[13]==('base',-120)
                assert allocator_report['returns_under_witness'] and allocator_report['arithmetic']['input_u32']==regs[1]
                memory.update({int(k):v for k,v in allocator_report['changed_cells'].items()})
                result=allocator_report['result_pointer'];regs[0]=0 if result==0 else ('base',result[1])
                regs[1]=regs[14]
            else:
                assert target==l.allocator.allocator.thunk and pc==l.address+48
                assert regs[2]==0x03005e79 and regs[1]==92 and regs[0][0]=='base'
                destination=regs[0][1]
                for i in range(0,92,4):
                    store_word(destination+i,0);events.append((pc,'zero-write',destination+i,4,0))
                regs[2]=add(regs[0],92);regs[0]=regs[14];regs[1]=0
        elif raw&0xfe00==0xb400:
            numbers=[i for i in range(8) if raw>>i&1]+([14] if raw&256 else [])
            regs[13]=add(regs[13],-4*len(numbers))
            for i,reg in enumerate(numbers):store_word(at(13,4*i),regs[reg])
        elif raw&0xff00==0xb000:regs[13]=add(regs[13],4*(raw&127)*(-1 if raw&128 else 1))
        elif raw&0xff00==0x4600:regs[(raw&7)|((raw>>4)&8)]=regs[(raw>>3)&15]
        elif raw&0xf800==0x9800:
            where=at(13,4*(raw&255));reg=(raw>>8)&7;regs[reg]=load_word(where)
            events.append((pc,'read32',where,visible(regs[reg])))
        elif raw&0xf800==0x4800:
            where=((pc+4)&~3)+4*(raw&255)-l.address
            regs[(raw>>8)&7]=int.from_bytes(data[where:where+4],'little')
        elif raw&0xf800==0x2000:regs[(raw>>8)&7]=raw&255
        elif raw&0xf800 in (0,0x0800):
            src=(raw>>3)&7;dst=raw&7;shift=(raw>>6)&31
            regs[dst]=(regs[src]<<shift)&0xffffffff if raw&0xf800==0 else regs[src]>>(shift or 32)
        elif raw&0xfe00==0x1c00:regs[raw&7]=add(regs[(raw>>3)&7],(raw>>6)&7)
        elif raw&0xfe00==0x1800:regs[raw&7]=add(regs[(raw>>3)&7],regs[(raw>>6)&7])
        elif raw&0xf800==0x3000:regs[(raw>>8)&7]=add(regs[(raw>>8)&7],raw&255)
        elif raw&0xf800==0x2800:
            value=regs[(raw>>8)&7];zero=type(value)is int and value==(raw&255)
        elif raw&0xf800 in (0x6000,0x6800):
            source=(raw>>3)&7;offset=4*((raw>>6)&31);reg=raw&7
            if type(regs[source])is int:
                assert raw&0xf800==0x6800 and regs[source]+offset==l.allocator.allocator.pointer_literal
                regs[reg]=0x03005e79
            else:
                where=at(source,offset)
                if raw&0xf800==0x6800:
                    regs[reg]=load_word(where);events.append((pc,'read32',where,visible(regs[reg])))
                else:
                    store_word(where,regs[reg]);op='write32-origin' if pc==l.address+54 else 'write32'
                    events.append((pc,op,where,visible(regs[reg])))
        elif raw&0xf800 in (0x8000,0x8800):
            where=at((raw>>3)&7,2*((raw>>6)&31));reg=raw&7
            if raw&0xf800==0x8800:
                regs[reg]=memory[where]|memory[where+1]<<8;events.append((pc,'read16',where,regs[reg]))
            else:
                memory[where]=regs[reg]&255;memory[where+1]=(regs[reg]>>8)&255
                events.append((pc,'write16',where,regs[reg]&65535))
        elif raw&0xf000==0xd000:
            cond=(raw>>8)&15;assert cond in (0,1)
            take=zero if cond==0 else not zero;delta=(raw&255)-(256 if raw&128 else 0)
            if take:nxt=pc+4+2*delta
        elif raw&0xf800==0xe000:
            delta=(raw&2047)-(2048 if raw&1024 else 0);nxt=pc+4+2*delta
        else:raise AssertionError(f'unsupported prefix opcode{raw:04x} at{pc:08x}')
        pc=nxt
    raise AssertionError('prefix oracle bound exceeded')


if __name__=='__main__':unittest.main()
