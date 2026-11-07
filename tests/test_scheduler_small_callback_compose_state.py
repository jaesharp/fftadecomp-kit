"""New small-callback composition cases with an independent concrete Thumb oracle."""
from dataclasses import replace
import hashlib
import unittest
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
import test_scheduler_requester_callback_state as fx
import scheduler_small_callback_compose_state as model

I, P, O, put, half = fx.I, fx.P, fx.O, fx.put, fx.half
BASE, E, DESC, PAYLOAD, RECORD, RETURN = fx.BASE, fx.E, fx.DESC, fx.PAYLOAD, fx.RECORD, fx.RETURN
QUERY = 0x7F74
OUTER_SP = E + 16
memory, byte, number = fx.memory, fx.byte, fx.number

def at(layout, role, offset=0):
    return model._validate(layout)[role][0] + offset

def fixture(phase=256, query=0, count=3, first=8192, second=8192, installed=True, parent=0):
    f = fx.requester_fixture(first=first, second=second, installed=installed, count=count, parent=parent)
    f['layout'] = model.Layout(f['layout'])
    f['selector'] = model.SELECTOR
    f['registers'] = {i: O('101 incoming R' + str(i)) for i in range(15)}
    f['registers'].update({0: I(0) if parent == 0 else P(parent), 1:P(DESC), 2:P(PAYLOAD), 13:P(OUTER_SP), 14:I(RETURN)})
    half(f['cells'], DESC, phase)
    half(f['cells'], PAYLOAD, 5)
    f['cells'][PAYLOAD+2] = count
    put(f['cells'], PAYLOAD+4, P(RECORD))
    put(f['cells'], PAYLOAD+8, I(0xABCDEF00))
    f['cells'][QUERY] = query
    f['literal_points'] = (*f['literal_points'], BASE+QUERY)
    return f

def raw(f,stop_before=None,stop_visit=1,step_limit=None,link_written=False):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for a,b in model._validate(f['layout']).values()};regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
    mem={f['arena_base']+k:byte(v,f['arena_base']) for k,v in f['cells'].items()};pc=at(f['layout'],'callback');events=[];trace=[]
    decoder=Cs(CS_ARCH_ARM,CS_MODE_THUMB);decoder.detail=True;flags=(False,False,False,False)
    names=dict(sp=13,lr=14,pc=15,sb=9,sl=10,fp=11,ip=12)
    def reg(o):
        n=decoder.reg_name(o.reg);return names.get(n,int(n[1:]) if n.startswith('r') else -1)
    def val(o):return o.imm if o.type==2 else regs[reg(o)]
    def read(a,w):
        v=tuple(mem[a+i] for i in range(w));events.append((pc,'read'+str(8*w),a-f['arena_base'],v));return int.from_bytes(bytes(v),'little')
    def write(a,w,v):
        b=tuple((v&0xffffffff).to_bytes(4,'little')[:w]);mem.update({a+i:x for i,x in enumerate(b)});events.append((pc,'write'+str(8*w),a-f['arena_base'],b))
    def arithmetic(a,b,sub):
        v=(a-b if sub else a+b)&0xffffffff
        return v,(bool(v&0x80000000),v==0,a>=b if sub else a+b>0xffffffff,bool(((a^b) if sub else ~(a^b))&(a^v)&0x80000000))
    for step in range(model.MAX_STEPS+1):
        if step_limit is not None and step>=step_limit:break
        if pc==stop_before and trace.count(pc)+1==stop_visit:
            if link_written:
                owner=next(a for a,b in bodies.items() if a<=pc<a+len(b))
                ins=next(decoder.disasm(bodies[owner][pc-owner:],pc,1))
                assert ins.mnemonic=='bl' and ins.size==4
                regs[14]=(pc+ins.size)|1
            trace.append(pc);break
        owner=next((a for a,b in bodies.items() if a<=pc<a+len(b)),None)
        if owner is None:break
        i=next(decoder.disasm(bodies[owner][pc-owner:],pc,1));ops,n,nxt=i.operands,i.mnemonic,pc+i.size;trace.append(pc)
        if n=='push':
            selected=[reg(o) for o in ops];a=regs[13]-4*len(ops);values=[regs[j] for j in selected]
            for j,v in enumerate(values):write(a+4*j,4,v)
            regs[13]=a
        elif n=='pop':
            a=regs[13];values=[read(a+4*j,4) for j in range(len(ops))]
            for o,v in zip(ops,values):regs[reg(o)]=v
            regs[13]=a+4*len(ops)
        elif n in ('mov','movs'):
            d=reg(ops[0]);v=val(ops[1])
            if d==15:nxt=v
            else:regs[d]=v
            if n=='movs':flags=(bool(v&0x80000000),v==0,flags[2],flags[3])
        elif n in ('add','adds','sub','subs'):
            d=reg(ops[0]);a=val(ops[1]) if len(ops)==3 else regs[d];b=val(ops[-1]);v,newflags=arithmetic(a,b,n.startswith('sub'));regs[d]=v
            if n.endswith('s'):flags=newflags
        elif n=='cmp':_,flags=arithmetic(val(ops[0]),val(ops[1]),True)
        elif n in ('lsls','lsrs','asrs'):
            d=reg(ops[0]);v=val(ops[1]);count=val(ops[2]);c=flags[2]
            if n=='lsls':
                if count:c=bool(v&(1<<(32-count)))
                v=(v<<count)&0xffffffff
            else:
                count=count or 32;c=bool(v&(1<<(count-1)));v=(v-2**32 if v&0x80000000 else v)>>count if n=='asrs' else v>>count;v&=0xffffffff
            regs[d]=v;flags=(bool(v&0x80000000),v==0,c,flags[3])
        elif n in ('orrs','ands','eors'):
            d=reg(ops[0]);b=val(ops[1]);v=regs[d]|b if n=='orrs' else regs[d]&b if n=='ands' else regs[d]^b;regs[d]=v;flags=(bool(v&0x80000000),v==0,flags[2],flags[3])
        elif n=='rsbs':
            d=reg(ops[0]);v,flags=arithmetic(0,val(ops[1]),True);regs[d]=v
        elif n in ('beq','bne','bhi','bls','bge','bgt','blt','ble','bhs','blo'):
            nf,z,c,v=flags
            if dict(beq=z,bne=not z,bhi=c and not z,bls=not c or z,bge=nf==v,bgt=not z and nf==v,blt=nf!=v,ble=z or nf!=v,bhs=c,blo=not c)[n]:nxt=ops[0].imm
        elif n=='b':nxt=ops[0].imm
        elif n=='bl':regs[14]=nxt|1;nxt=ops[0].imm
        elif n=='bx':nxt=regs[reg(ops[0])]&~1
        elif n in ('ldm','stm'):
            rn=reg(ops[0]);a=regs[rn]
            if n=='ldm':
                values=[read(a+4*j,4) for j in range(len(ops)-1)]
                for o,v in zip(ops[1:],values):regs[reg(o)]=v
            else:
                values=[regs[reg(o)] for o in ops[1:]]
                for j,v in enumerate(values):write(a+4*j,4,v)
            regs[rn]=a+4*(len(ops)-1)
        elif n in ('ldr','str','ldrb','strb','ldrh','strh'):
            width=1 if n.endswith('b') else 2 if n.endswith('h') else 4;bn=decoder.reg_name(ops[1].mem.base)
            if bn=='pc':
                a=((pc+4)&~3)+ops[1].mem.disp;regs[reg(ops[0])]=int.from_bytes(bodies[owner][a-owner:a-owner+4],'little')
            else:
                index=names.get(bn,int(bn[1:]) if bn.startswith('r') else -1);a=regs[index]+ops[1].mem.disp
                if n.startswith('ldr'):
                    rom_owner=next((p for p,b in bodies.items() if p<=a and a+width<=p+len(b)),None)
                    if rom_owner is not None:regs[reg(ops[0])]=int.from_bytes(bodies[rom_owner][a-rom_owner:a-rom_owner+width],'little')
                    else:regs[reg(ops[0])]=read(a,width)
                else:write(a,width,regs[reg(ops[0])])
        elif n=='svc':break
        else:raise AssertionError((hex(pc),n,i.op_str))
        pc=nxt
    else:raise AssertionError('raw oracle bound exhausted')
    return regs,mem,trace,events,pc


@unittest.skipIf(fx.IMAGE is None, 'set FFTA_SOURCE84_IMAGE to the private source image')
class SmallCallbackCompositionTests(unittest.TestCase):
    def compare_raw(self, f, r, stop_before=None, step_limit=None):
        regs, cells, trace, events, pc = raw(f, stop_before=stop_before, step_limit=step_limit)
        self.assertEqual(r['trace'], trace)
        self.assertEqual(r['final_PC'], pc)
        self.assertEqual({k:number(v, f['arena_base']) for k,v in r['registers'].items()}, regs)
        got = memory(r)
        for a,v in cells.items():
            self.assertEqual(byte(got[a-f['arena_base']], f['arena_base']), v, hex(a))
        actual = [(e['site'], e['operation'], e['coordinate'], tuple(byte(v, f['arena_base']) for v in e['bytes']))
                  for e in r['memory_events'] if 'coordinate' in e]
        self.assertEqual(actual, events)

    def returned(self, f, r):
        self.assertTrue(r['conditional_small_callback_return'], r['boundary'])
        self.assertIsNone(r['boundary'])
        self.assertEqual(r['pending_calls'], [])
        self.assertEqual(r['registers'][0], I(0))
        self.assertEqual(r['registers'][13], f['registers'][13])
        self.assertEqual(r['final_PC'], RETURN & ~1)
        self.compare_raw(f,r)

    def word(self,r,a):
        m=memory(r)
        return tuple(m[a+i] for i in range(4))

    def halfword(self,r,a):
        m=memory(r)
        return m[a] | m[a+1]<<8

    def test_entire_query_requester_scheduler_callback_and_outer_return(self):
        f=fixture();r=model.derive(**f);self.returned(f,r)
        self.assertTrue(r['conditional_requester_return'])
        self.assertEqual(self.word(r,PAYLOAD+8),P(fx.JOB))
        self.assertEqual(self.halfword(r,DESC),257)
        self.assertEqual([x['size_word'] for x in r['actual_allocation_requests']],[I(68),I(0x3000),I(0x4000)])
        self.assertEqual(r['actual_requester_entries'][0]['SP'],E)
        self.assertEqual(r['actual_scheduler_entries'][0]['SP'],E-36)
        self.assertEqual(r['small_callback_observed_phase'],dict(kind='constant',value=256))

    def test_parent_child_chain_is_created_from_actual_outer_r0(self):
        parent=25000;f=fixture(parent=parent);put(f['cells'],parent+16,I(0))
        r=model.derive(**f);self.returned(f,r)
        self.assertEqual(self.word(r,parent+16),P(fx.JOB))
        self.assertEqual(self.word(r,fx.JOB+12),P(parent))

    def test_nonzero_actual_query_returns_without_request_or_phase_change(self):
        f=fixture(query=0x80);r=model.derive(**f);self.returned(f,r)
        self.assertEqual(r['actual_requester_entries'],[])
        self.assertEqual(self.halfword(r,DESC),256)
        self.assertEqual(self.word(r,PAYLOAD+8),I(0xABCDEF00))

    def test_null_payload_source_increments_reloaded_phase_without_request(self):
        f=fixture();put(f['cells'],PAYLOAD+4,I(0));r=model.derive(**f);self.returned(f,r)
        self.assertEqual(r['actual_requester_entries'],[])
        self.assertEqual(self.halfword(r,DESC),257)

    def test_zero_mode_skips_request_even_with_nonzero_source(self):
        f=fixture(count=0);r=model.derive(**f);self.returned(f,r)
        self.assertEqual(r['actual_requester_entries'],[])
        self.assertEqual(self.halfword(r,DESC),257)

    def test_unhandled_and_idle_phases_follow_real_branch_tree(self):
        for phase in (1,2,258,65535):
            f=fixture(phase=phase);r=model.derive(**f);self.returned(f,r)
            self.assertEqual(r['actual_requester_entries'],[])
            self.assertEqual(self.halfword(r,DESC),phase)

    def test_phase_zero_copies_real_record_fields(self):
        f=fixture(phase=0);half(f['cells'],RECORD,0x2345);f['cells'][RECORD+2]=7;put(f['cells'],RECORD+4,P(8000))
        r=model.derive(**f);self.returned(f,r)
        self.assertEqual(self.halfword(r,PAYLOAD),0x2345)
        self.assertEqual(memory(r)[PAYLOAD+2],7)
        self.assertEqual(self.word(r,PAYLOAD+4),P(8000))

    def test_phase_zero_alias_changes_later_halfword_load(self):
        f=fixture(phase=0);f['registers'][2]=P(RECORD-4)
        half(f['cells'],RECORD,0x2345);f['cells'][RECORD+2]=7;put(f['cells'],RECORD+4,I(0x67891234))
        r=model.derive(**f);self.returned(f,r)
        self.assertEqual(self.halfword(r,RECORD-4),0x1234)

    def test_phase_zero_transports_unknown_word_without_observation(self):
        f=fixture(phase=0);half(f['cells'],RECORD,9);f['cells'][RECORD+2]=3;unknown=O('101 record unknown');put(f['cells'],RECORD+4,unknown)
        r=model.derive(**f);self.returned(f,r)
        self.assertEqual(self.word(r,PAYLOAD+4),unknown)

    def test_actual_save_alias_changes_fixed_query_byte(self):
        f=fixture(query=0);f['registers'][13]=P(QUERY+4)
        r=model.derive(**f);self.returned(f,r)
        self.assertEqual(memory(r)[QUERY],RETURN&255)
        self.assertEqual(r['actual_requester_entries'],[])

    def test_nested_allocation_can_overwrite_outer_descriptor(self):
        f=fixture();f['registers'][1]=P(fx.JOB+20);half(f['cells'],fx.JOB+20,256)
        r=model.derive(**f);self.returned(f,r)
        self.assertEqual(self.halfword(r,fx.JOB+20),257)
        reads=[e for e in r['memory_events'] if e.get('site')==at(f['layout'],'callback',90) and e['operation']=='read16']
        self.assertEqual(reads[-1]['bytes'],(0,1))

    def test_payload_result_store_alias_precedes_phase_reload(self):
        f=fixture();f['registers'][1]=P(PAYLOAD+8);half(f['cells'],PAYLOAD+8,256)
        r=model.derive(**f)
        self.assertIn('narrow read observes',r['boundary']['reason'])
        self.assertEqual(self.word(r,PAYLOAD+8),P(fx.JOB))
        self.compare_raw(f,r,stop_before=at(f['layout'],'callback',90))

    def test_nested_unknown_descriptor_bytes_remain_unknown(self):
        f=fixture(first=17,second=0);r=model.derive(**f);self.returned(f,r)
        for off in (8,12,16,24):
            self.assertEqual(self.word(r,E-32+off),self.word(r,E-92+off))
            self.assertTrue(all(type(x)is tuple and x[0]=='opaque-byte' for x in self.word(r,E-92+off)))

    def test_outer_saved_words_restored_from_actual_memory(self):
        f=fixture();r=model.derive(**f);self.returned(f,r)
        for register in range(4,12):self.assertEqual(r['registers'][register],f['registers'][register])

    def test_zero_image_remains_an_explicit_condition(self):
        f=fixture(installed=False);r=model.derive(**f)
        self.assertIn('zero image installation',r['boundary']['reason'])
        self.assertFalse(r['conditional_small_callback_return'])
        self.compare_raw(f,r,stop_before=at(f['layout'],'zero_thunk'))

    def test_null_scheduler_allocation_does_not_create_memory(self):
        f=fixture(first=0);r=model.derive(**f)
        self.assertIn('address lacks',r['boundary']['reason'])
        self.assertEqual(r['registers'][0],I(0))
        self.assertEqual(r['actual_callback_entries'],[])
        self.compare_raw(f,r,stop_before=at(f['layout'],'zero_thunk'))

    def test_missing_literal_point_stops_actual_query_load(self):
        f=fixture();f['literal_points']=fx.RELEASE_POINTS;r=model.derive(**f)
        self.assertIn('address lacks',r['boundary']['reason'])
        self.compare_raw(f,r,stop_before=at(f['layout'],'getter256',4))

    def test_missing_query_byte_is_not_initialized_by_its_address(self):
        f=fixture();del f['cells'][QUERY];r=model.derive(**f)
        self.assertIn('read lacks reaching',r['boundary']['reason'])
        self.compare_raw(f,r,stop_before=at(f['layout'],'getter256',4))

    def test_opaque_query_byte_is_not_observed_as_scalar(self):
        f=fixture();f['cells'][QUERY]=('opaque-byte','101 query',0);r=model.derive(**f)
        self.assertIn('narrow read observes',r['boundary']['reason'])
        self.compare_raw(f,r,stop_before=at(f['layout'],'getter256',4))

    def test_retired_query_byte_stops_before_read(self):
        f=fixture();f['released_payload_spans']=((QUERY,QUERY+1),);r=model.derive(**f)
        self.assertIn('retired',r['boundary']['reason'])
        self.compare_raw(f,r,stop_before=at(f['layout'],'getter256',4))

    def test_declared_retired_outer_frame_cannot_be_revived(self):
        f=fixture();f['retired_stack_spans']=((E,E+4),);r=model.derive(**f)
        self.assertIn('externally retired',r['boundary']['reason'])
        self.compare_raw(f,r,stop_before=at(f['layout'],'callback'))

    def test_protected_outer_save_stops_before_first_write(self):
        f=fixture();f['protected_spans']=((E,E+4),);r=model.derive(**f)
        self.assertIn('protected',r['boundary']['reason'])
        self.compare_raw(f,r,stop_before=at(f['layout'],'callback'))

    def test_full_composition_shares_one_instruction_budget(self):
        f=fixture();f['max_steps']=100;r=model.derive(**f)
        self.assertIn('budget',r['boundary']['reason'])
        self.assertEqual(len(r['trace']),100)
        self.compare_raw(f,r,step_limit=100)

    def test_phase257_countdown_stops_at_actual_unclosed_helper_entry(self):
        f=fixture(phase=257);put(f['cells'],PAYLOAD+8,I(0));r=model.derive(**f)
        target=model._call(model._validate(f['layout'])['callback'][1],at(f['layout'],'callback'),108)
        self.assertEqual(r['final_PC'],target)
        self.assertEqual(self.halfword(r,PAYLOAD),4)
        self.assertEqual(r['nested_call_cutpoint']['call_site'],at(f['layout'],'callback',108))
        self.assertFalse(r['nested_call_cutpoint']['callee_executed'])
        self.compare_raw(f,r)

    def test_phase257_zero_count_does_not_underflow_before_cutpoint(self):
        f=fixture(phase=257);half(f['cells'],PAYLOAD,0);put(f['cells'],PAYLOAD+8,I(0));r=model.derive(**f)
        self.assertEqual(self.halfword(r,PAYLOAD),0)
        self.assertFalse(r['conditional_small_callback_return'])
        self.compare_raw(f,r)

    def test_numeric_payload_address_does_not_supply_pointer_origin(self):
        f=fixture();f['registers'][2]=I(BASE+PAYLOAD);r=model.derive(**f)
        self.assertIn('address lacks',r['boundary']['reason'])
        self.compare_raw(f,r,stop_before=at(f['layout'],'callback',66))

    def test_wrong_selector_and_missing_layout_are_rejected(self):
        f=fixture();f['selector']='wrong'
        with self.assertRaises(ValueError):model.derive(**f)
        with self.assertRaises(ValueError):model.bind(None,selector=model.SELECTOR)

    def test_actual_entry_return_requires_thumb_tag(self):
        f=fixture();f['registers'][14]=I(RETURN&~1);r=model.derive(**f)
        self.assertIn('not Thumb tagged',r['boundary']['reason'])
        self.assertEqual(r['trace'],[])


if __name__ == '__main__':
    unittest.main()
