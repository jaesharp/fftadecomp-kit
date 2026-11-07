"""New phase257 query/list/free tests; independent raw Thumb execution."""
from dataclasses import replace
import hashlib
import unittest
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
import test_scheduler_small_callback_compose_state as previous
import scheduler_small_callback_release_state as model

I,P,O,put,half=previous.I,previous.P,previous.O,previous.put,previous.half
BASE,E,DESC,PAYLOAD,RETURN=previous.BASE,previous.E,previous.DESC,previous.PAYLOAD,previous.RETURN
memory,byte,number=previous.memory,previous.byte,previous.number
NODE,HEAP,SCHED,GLOBAL=20256,20000,18000,0x8FF0

def at(layout,role,offset=0):return model._validate(layout)[role][0]+offset

def layout(prior,query=0x081D0C00):
    def patch_callback(node):
        if hasattr(node,'owners'):
            owners=[]
            for role,a,b in node.owners:
                if role=='callback':
                    b=bytearray(b);b[108:112]=model.removal._bl(a+108,query);b=bytes(b)
                owners.append((role,a,b))
            return replace(node,owners=tuple(owners))
        return replace(node,prior=patch_callback(node.prior))
    prior=patch_callback(prior);owners=model.small101._validate(prior)
    b=bytearray(model.phase081.SHAPES['query'])
    for off,role in ((8,'status'),(28,'scheduler_remove')):b[off:off+4]=model.removal._bl(query+off,owners[role][0])
    return model.Layout(prior,query,bytes(b))

def fixture(status=2,node=NODE,count=1,callback='callback40'):
    f=previous.fixture(phase=257);f['layout']=layout(f['layout']);f['selector']=model.SELECTOR;m=f['cells']
    half(m,PAYLOAD,count);put(m,PAYLOAD+8,I(0) if node is None else P(node))
    put(m,GLOBAL,P(SCHED));put(m,SCHED,P(HEAP));put(m,SCHED+4,I(0) if node is None else P(node))
    for a in range(HEAP,HEAP+12):m[a]=0
    if node is not None:
        for a in range(node-12,node+24):m[a]=0
        half(m,node-8,0x7373);half(m,node-6,35);half(m,node+20,status);put(m,node,I(at(f['layout'],callback)|1))
    f['release_spans']=((node,node+128),) if node is not None else ()
    f['literal_points']=tuple(dict.fromkeys((*f['literal_points'],BASE+GLOBAL)))
    return f

def add_child(f,node,parent,callback='callback'):
    m=f['cells']
    for a in range(node-12,node+24):m[a]=0
    half(m,node-8,0x7373);half(m,node-6,19);half(m,node+20,2)
    put(m,node,I(at(f['layout'],callback)|1));put(m,node+12,P(parent));put(m,parent+16,P(node))
    f['release_spans']=(*f['release_spans'],(node,node+64))

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


@unittest.skipIf(previous.fx.IMAGE is None,'set FFTA_SOURCE84_IMAGE to the private source image')
class SmallCallbackReleaseTests(unittest.TestCase):
    def compare_raw(self,f,r,stop_before=None,step_limit=None):
        regs,cells,trace,events,pc=raw(f,stop_before=stop_before,step_limit=step_limit)
        self.assertEqual(r['trace'],trace);self.assertEqual(r['final_PC'],pc)
        self.assertEqual({k:number(v,f['arena_base']) for k,v in r['registers'].items()},regs)
        got=memory(r)
        for a,v in cells.items():self.assertEqual(byte(got[a-f['arena_base']],f['arena_base']),v,hex(a))
        actual=[(e['site'],e['operation'],e['coordinate'],tuple(byte(v,f['arena_base']) for v in e['bytes'])) for e in r['memory_events'] if 'coordinate' in e]
        self.assertEqual(actual,events)

    def returned(self,f,r):
        self.assertTrue(r['conditional_small_callback_return'],r['boundary']);self.assertIsNone(r['boundary'])
        self.assertEqual(r['pending_calls'],[]);self.assertEqual(r['final_PC'],RETURN&~1)
        self.assertEqual(r['registers'][13],f['registers'][13]);self.assertEqual(r['registers'][0],I(0))
        self.compare_raw(f,r)

    def word(self,r,a):return tuple(memory(r)[a+i] for i in range(4))
    def halfword(self,r,a):return memory(r)[a]|memory(r)[a+1]<<8

    def test_finished_node_runs_callback_unlink_allocator_and_outer_return(self):
        f=fixture();r=model.derive(**f);self.returned(f,r)
        self.assertEqual(r['conditional_released_payloads'],[(NODE,NODE+128)])
        self.assertEqual(self.word(r,PAYLOAD+8),I(0));self.assertEqual(self.halfword(r,DESC),2)
        self.assertEqual(self.word(r,SCHED+4),I(0));self.assertEqual(self.halfword(r,HEAP+4),1)
        self.assertEqual(r['small_callback_observed_phase'],dict(kind='constant',value=257))
        self.assertEqual(r['actual_removal_callback_entries'][0]['role'],'callback40')

    def test_bound_small_callback_phase_one_returns_into_removal(self):
        f=fixture(callback='callback');r=model.derive(**f);self.returned(f,r)
        self.assertEqual(r['actual_removal_callback_entries'][0]['role'],'callback')
        self.assertEqual(r['small_callback_observed_phase'],dict(kind='constant',value=257))
        self.assertEqual(r['conditional_released_payloads'],[(NODE,NODE+128)])

    def test_null_node_with_expired_count_sets_phase_two(self):
        f=fixture(node=None,count=0);r=model.derive(**f);self.returned(f,r)
        self.assertEqual(self.halfword(r,DESC),2);self.assertEqual(r['conditional_released_payloads'],[])

    def test_null_node_with_positive_count_retains_phase257(self):
        f=fixture(node=None,count=3);r=model.derive(**f);self.returned(f,r)
        self.assertEqual(self.halfword(r,PAYLOAD),2);self.assertEqual(self.halfword(r,DESC),257)

    def test_unfinished_node_retains_actual_pointer_after_count_expires(self):
        for status in (0,1,256,65535):
            f=fixture(status=status);r=model.derive(**f);self.returned(f,r)
            self.assertEqual(self.word(r,PAYLOAD+8),P(NODE));self.assertEqual(self.halfword(r,DESC),257)
            self.assertEqual(r['actual_removal_callback_entries'],[])

    def test_finished_node_with_remaining_count_keeps_phase257(self):
        f=fixture(count=5);r=model.derive(**f);self.returned(f,r)
        self.assertEqual(self.halfword(r,PAYLOAD),4);self.assertEqual(self.halfword(r,DESC),257)
        self.assertEqual(self.word(r,PAYLOAD+8),I(0))

    def test_child_and_parent_callbacks_and_frees_share_memory(self):
        f=fixture();child=20640;add_child(f,child,NODE);r=model.derive(**f);self.returned(f,r)
        self.assertEqual(r['conditional_released_payloads'],[(child,child+64),(NODE,NODE+128)])
        self.assertEqual([x['role'] for x in r['actual_removal_callback_entries']],['callback','callback40'])

    def test_adjacent_list_link_writes_are_observed_in_order(self):
        f=fixture();previous_node,next_node=22000,23000;m=f['cells'];put(m,NODE+4,P(previous_node));put(m,NODE+8,P(next_node))
        put(m,previous_node+8,P(NODE));put(m,next_node+4,P(NODE))
        r=model.derive(**f);self.returned(f,r)
        self.assertEqual(self.word(r,previous_node+8),P(next_node));self.assertEqual(self.word(r,next_node+4),P(previous_node))

    def test_parent_child_head_is_updated_from_actual_comparison(self):
        f=fixture();parent=24000;put(f['cells'],NODE+12,P(parent));put(f['cells'],parent+16,P(NODE))
        r=model.derive(**f);self.returned(f,r);self.assertEqual(self.word(r,parent+16),I(0))

    def test_unknown_callback_remains_an_exact_tail_entry_boundary(self):
        f=fixture();put(f['cells'],NODE,I(0x08123457));r=model.derive(**f)
        self.assertIn('removal callback identity',r['boundary']['reason']);self.assertEqual(r['conditional_released_payloads'],[])
        self.assertEqual(r['nested_call_cutpoint']['target'],0x08123456)
        self.compare_raw(f,r,stop_before=at(f['layout'],'thunk'))

    def test_even_bound_callback_word_is_not_a_thumb_target(self):
        f=fixture();put(f['cells'],NODE,I(at(f['layout'],'callback40')));r=model.derive(**f)
        self.assertIn('removal callback identity',r['boundary']['reason'])
        self.compare_raw(f,r,stop_before=at(f['layout'],'thunk'))

    def test_opaque_callback_word_is_not_a_concrete_identity(self):
        f=fixture();put(f['cells'],NODE,O('102 callback'));r=model.derive(**f)
        self.assertIn('opaque',r['boundary']['reason']);self.compare_raw(f,r,stop_before=at(f['layout'],'thunk'))

    def test_missing_payload_lifetime_stops_after_actual_metadata_updates(self):
        f=fixture();f['release_spans']=();r=model.derive(**f)
        self.assertIn('lifetime premise',r['boundary']['reason']);self.assertEqual(r['conditional_released_payloads'],[])
        self.assertEqual(self.halfword(r,HEAP+4),1)
        self.compare_raw(f,r,stop_before=r['boundary']['site'])

    def test_retired_payload_alias_is_not_read_by_outer_countdown(self):
        f=fixture();f['registers'][2]=P(NODE+24);half(f['cells'],NODE+24,1);put(f['cells'],NODE+32,P(NODE))
        r=model.derive(**f)
        self.assertIn('retired',r['boundary']['reason']);self.assertEqual(r['conditional_released_payloads'],[(NODE,NODE+128)])
        self.compare_raw(f,r,stop_before=at(f['layout'],'callback',112))

    def test_missing_scheduler_literal_provenance_is_not_inferred(self):
        f=fixture();f['literal_points']=tuple(x for x in f['literal_points'] if x!=BASE+GLOBAL);r=model.derive(**f)
        self.assertIn('address lacks',r['boundary']['reason']);self.compare_raw(f,r,stop_before=at(f['layout'],'scheduler_remove',6))

    def test_opaque_scheduler_word_is_not_a_live_heap_handle(self):
        f=fixture();put(f['cells'],GLOBAL,O('102 scheduler'));r=model.derive(**f)
        self.assertIn('address lacks',r['boundary']['reason']);self.compare_raw(f,r,stop_before=r['boundary']['site'])

    def test_unknown_node_status_is_not_assumed_finished(self):
        f=fixture();f['cells'][NODE+20]=('opaque-byte','102 status',0);r=model.derive(**f)
        self.assertIn('narrow read observes',r['boundary']['reason']);self.compare_raw(f,r,stop_before=at(f['layout'],'status',4))

    def test_protected_unlink_field_stops_before_the_store(self):
        f=fixture();f['protected_spans']=((NODE+12,NODE+16),);r=model.derive(**f)
        self.assertIn('protected',r['boundary']['reason']);self.compare_raw(f,r,stop_before=at(f['layout'],'list_remove',130))

    def test_child_cycle_exhausts_shared_instruction_budget(self):
        f=fixture();put(f['cells'],NODE+16,P(NODE));put(f['cells'],NODE+8,P(NODE));f['max_steps']=120
        r=model.derive(**f);self.assertIn('budget',r['boundary']['reason']);self.assertEqual(r['conditional_released_payloads'],[])
        self.compare_raw(f,r,step_limit=120)

    def test_numeric_node_bits_do_not_grant_pointer_provenance(self):
        f=fixture();put(f['cells'],PAYLOAD+8,I(BASE+NODE));r=model.derive(**f)
        self.assertIn('address lacks',r['boundary']['reason']);self.compare_raw(f,r,stop_before=at(f['layout'],'status',4))

    def test_status_save_alias_changes_observed_node_halfword(self):
        f=fixture(node=E-32,status=2);r=model.derive(**f)
        self.returned(f,r)
        self.assertEqual(self.halfword(r,E-12),(at(f['layout'],'query257',12)|1)&0xffff)
        self.assertEqual(self.word(r,PAYLOAD+8),P(E-32))
        self.assertEqual(r['conditional_released_payloads'],[])
        observed=[e for e in r['memory_events'] if e['site']==at(f['layout'],'status',4)]
        self.assertEqual(observed[0]['bytes'],((at(f['layout'],'query257',12)|1)&255,(at(f['layout'],'query257',12)>>8)&255))

    def test_generic_query_relocation_preserves_complete_binding(self):
        f=fixture(status=0);l=f['layout'];a=l.query+0x40;b=bytearray(l.query_data)
        for off,role in ((8,'status'),(28,'scheduler_remove')):b[off:off+4]=model.removal._bl(a+off,at(l,role))
        f['layout']=layout(l.prior,a);r=model.derive(**f);self.returned(f,r)

    def test_changed_query_nested_target_is_rejected(self):
        f=fixture();l=f['layout'];b=bytearray(l.query_data);b[8:12]=model.removal._bl(l.query+8,at(l,'free'))
        with self.assertRaisesRegex(ValueError,'nested target'):model.bind(l.prior,l.query,bytes(b),selector=model.SELECTOR)

    def test_query_body_corruption_is_rejected(self):
        f=fixture();l=f['layout'];b=bytearray(l.query_data);b[12]^=1
        with self.assertRaisesRegex(ValueError,'shape'):model.bind(l.prior,l.query,bytes(b),selector=model.SELECTOR)

    def test_query_overlap_or_wrong_selector_is_rejected(self):
        f=fixture();l=f['layout']
        with self.assertRaises(ValueError):model.bind(l.prior,at(l,'callback'),l.query_data,selector=model.SELECTOR)
        with self.assertRaises(ValueError):model.bind(l.prior,l.query,l.query_data,selector='wrong')

    def test_phase256_path_still_uses_real_nested_requester_on_new_layout(self):
        f=previous.fixture(count=7,first=5000,second=6000);f['layout']=layout(f['layout']);f['selector']=model.SELECTOR
        r=model.derive(**f);self.returned(f,r)
        self.assertEqual(self.halfword(r,DESC),257);self.assertTrue(r['conditional_requester_return'])
        self.assertEqual(r['actual_removal_callback_entries'],[])


if __name__=='__main__':unittest.main()
