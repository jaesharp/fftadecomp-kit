"""New081 states, compared with an independent concrete Thumb mnemonic oracle."""
from dataclasses import replace
import hashlib,unittest
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
import scheduler_phase256_state as model

BASE,SP,REQUEST,PAYLOAD,NODE,HEAP,SCHED,GLOBAL=0x02000000,8192,8000,9000,1200,1000,5000,6000
I=model.words._constant;P=model.words._pointer

def O(name):return tuple(('opaque-byte',name,i) for i in range(4))
def put(m,a,value):m.update({a+i:v for i,v in enumerate(value)})
def half(m,a,v):put(m,a,tuple((v&65535).to_bytes(2,'little')))
def memory(r):return {int(k):v for k,v in r['post_cells'].items()}
def byte(v,base=BASE):
    if type(v) is int:return v
    if v[0]=='base-plus-byte':return ((base+v[1])>>(8*v[2]))&255
    return hashlib.sha256((v[1]+':'+str(v[2])).encode()).digest()[0]
def number(w,base=BASE):return int.from_bytes(bytes(byte(v,base) for v in w),'little')
def role(l,name):return next((a,b) for n,a,b in l.owners if n==name)
def at(l,name,off=0):return role(l,name)[0]+off

def layout(shift=0):
    addresses={name:0x08180000+shift+i*0x400 for i,name in enumerate(sorted(model.SHAPES))};owners=[]
    for name,shape in model.SHAPES.items():
        a=addresses[name];b=bytearray(shape)
        for off,target in model.EDGES.get(name,{}).items():
            b[off:off+4]=model.removal._bl(a+off,addresses[target] if target else 0x081C0000+off)
        if name=='scheduler_remove':b[16:20]=(BASE+GLOBAL).to_bytes(4,'little')
        owners.append((name,a,bytes(b)))
    return model.Layout(tuple(owners))

def fixture(status=2,node=NODE):
    l=layout();m={};r={i:O('081 incoming R'+str(i)) for i in range(15)}
    r.update({0:P(7000),1:P(REQUEST),2:P(PAYLOAD),13:P(SP),14:I(0x08012345)})
    half(m,REQUEST,256);put(m,PAYLOAD+20,I(0) if node is None else P(node));put(m,PAYLOAD+16,P(5500))
    put(m,GLOBAL,P(SCHED));put(m,SCHED,P(HEAP));put(m,SCHED+4,P(node or NODE))
    for a in range(HEAP,HEAP+12):m[a]=0
    if node is not None:
        block=node-12
        for a in range(block,node+24):m[a]=0
        half(m,block+4,0x7373);half(m,block+6,35)
        put(m,node,I(at(l,'callback')|1));half(m,node+20,status)
    return dict(layout=l,arena_base=BASE,cells=m,registers=r,selector=model.SELECTOR,
                release_spans=((node,node+128),) if node is not None else (),literal_points=(BASE+GLOBAL,))

def add_free_neighbor(f,block,*,prev=0,nxt=0,size=16):
    m=f['cells']
    for a in range(block,block+12):m[a]=0
    half(m,block,prev);half(m,block+2,nxt);half(m,block+4,0x7370);half(m,block+6,size)
    half(m,HEAP,(block-HEAP)//4);half(m,HEAP+2,(block-HEAP)//4);half(m,HEAP+4,1)


def raw(f,stop_before=None):
    """Independent concrete decoder/effects, no production executor or flags."""
    bodies={a:b for _,a,b in f['layout'].owners};regs={i:number(v,f['arena_base']) for i,v in f['registers'].items()}
    mem={f['arena_base']+k:byte(v,f['arena_base']) for k,v in f['cells'].items()};pc=at(f['layout'],'root');events=[];trace=[]
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
    for _ in range(4096):
        if pc==stop_before:trace.append(pc);break
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
            d=reg(ops[0]);regs[d]=val(ops[1]);v=regs[d]
            if n=='movs':flags=(bool(v&0x80000000),v==0,flags[2],flags[3])
        elif n in ('add','adds','sub','subs'):
            d=reg(ops[0]);a=val(ops[1]) if len(ops)==3 else regs[d];b=val(ops[-1]);v,newflags=arithmetic(a,b,n.startswith('sub'));regs[d]=v
            if n.endswith('s'):flags=newflags
        elif n=='cmp':_,flags=arithmetic(val(ops[0]),val(ops[1]),True)
        elif n in ('lsls','lsrs'):
            d=reg(ops[0]);v=val(ops[1]);count=val(ops[2]);c=flags[2]
            if n=='lsls':
                if count:c=bool(v&(1<<(32-count)))
                v=(v<<count)&0xffffffff
            else:
                count=count or 32;c=bool(v&(1<<(count-1)));v>>=count
            regs[d]=v;flags=(bool(v&0x80000000),v==0,c,flags[3])
        elif n in ('orrs','ands'):
            d=reg(ops[0]);b=val(ops[1]);v=regs[d]|b if n=='orrs' else regs[d]&b;regs[d]=v;flags=(bool(v&0x80000000),v==0,flags[2],flags[3])
        elif n in ('beq','bne','bhi','bls','bge','bgt'):
            nf,z,c,v=flags
            if dict(beq=z,bne=not z,bhi=c and not z,bls=not c or z,bge=nf==v,bgt=not z and nf==v)[n]:nxt=ops[0].imm
        elif n=='b':nxt=ops[0].imm
        elif n=='bl':regs[14]=nxt|1;nxt=ops[0].imm
        elif n=='bx':nxt=regs[reg(ops[0])]&~1
        elif n in ('ldr','str','ldrb','strb','ldrh','strh'):
            width=1 if n.endswith('b') else 2 if n.endswith('h') else 4;bn=decoder.reg_name(ops[1].mem.base)
            if bn=='pc':
                a=((pc+4)&~3)+ops[1].mem.disp;regs[reg(ops[0])]=int.from_bytes(bodies[owner][a-owner:a-owner+4],'little')
            else:
                index=names.get(bn,int(bn[1:]) if bn.startswith('r') else -1);a=regs[index]+ops[1].mem.disp
                if n.startswith('ldr'):regs[reg(ops[0])]=read(a,width)
                else:write(a,width,regs[reg(ops[0])])
        else:raise AssertionError((hex(pc),n,i.op_str))
        pc=nxt
    else:raise AssertionError('raw oracle bound exhausted')
    return regs,mem,trace,events,pc


class Phase256Tests(unittest.TestCase):
    def assert_raw(self,f,result,stop_before=None):
        regs,mem,trace,events,pc=raw(f,stop_before)
        self.assertEqual(result['trace'],trace);self.assertEqual(result['final_PC'],pc)
        self.assertEqual({k:number(v,f['arena_base']) for k,v in result['registers'].items()},regs)
        got=memory(result)
        for a,v in mem.items():self.assertEqual(byte(got[a-f['arena_base']],f['arena_base']),v,(hex(a),v))
        actual=[(e['site'],e['operation'],e['coordinate'],tuple(byte(v,f['arena_base']) for v in e['bytes'])) for e in result['memory_events'] if 'coordinate' in e]
        self.assertEqual(actual,events)
    def derive(self,f):return model.derive(**f)
    def next(self,f,r):
        self.assertEqual(r['final_PC'],at(f['layout'],'next'));self.assertIn('independent closure',r['boundary']['reason']);self.assert_raw(f,r,r['final_PC'])

    def test_phase256_incomplete_node_returns_through_real_saves(self):
        f=fixture(status=0);r=self.derive(f);self.assertTrue(r['conditional_root_return']);self.assertIsNone(r['boundary']);self.assert_raw(f,r)
        self.assertEqual(r['registers'][13],P(SP));self.assertEqual(r['registers'][0],I(0));self.assertEqual(r['conditional_released_payloads'],[])

    def test_phase256_status_one_is_not_finished(self):
        f=fixture(status=1);r=self.derive(f);self.assertTrue(r['conditional_root_return']);self.assert_raw(f,r)
        self.assertNotIn(at(f['layout'],'scheduler_remove'),r['trace'])

    def test_null_node_reaches_real_source_call_interface(self):
        f=fixture(node=None);r=self.derive(f);self.next(f,r)
        self.assertEqual([r['registers'][j] for j in range(4)],[P(5500),I(5),I(0),P(PAYLOAD+3)])
        self.assertEqual(r['registers'][14],I(at(f['layout'],'root',124)|1))

    def test_single_node_real_free_insert_median_and_root_source_cut(self):
        f=fixture();r=self.derive(f);self.next(f,r)
        self.assertEqual(r['conditional_released_payloads'],[(NODE,NODE+128)])
        m=memory(r);self.assertEqual(bytes(m[HEAP+i] for i in range(6)),bytes([47,0,47,0,1,0]))
        self.assertEqual(bytes(m[NODE-8+i] for i in range(4)),bytes([0x70,0x73,32,0]))
        self.assertEqual(tuple(m[SCHED+4+i] for i in range(4)),I(0));self.assertEqual(tuple(m[PAYLOAD+20+i] for i in range(4)),I(0))
        self.assertEqual(r['registers'][8],f['registers'][8]);self.assertEqual(r['registers'][9],f['registers'][9])

    def test_backward_free_neighbor_is_removed_and_combined(self):
        f=fixture();previous=1100;add_free_neighbor(f,previous,nxt=(NODE-12-HEAP)//4,size=16)
        half(f['cells'],NODE-12,(previous-HEAP)//4)
        r=self.derive(f);self.next(f,r);m=memory(r)
        self.assertIn(at(f['layout'],'remove'),r['trace']);self.assertEqual(m[previous+6]|m[previous+7]<<8,51)
        self.assertEqual(m[HEAP]|m[HEAP+1]<<8,25)

    def test_forward_free_neighbor_is_removed_and_combined(self):
        f=fixture();following=1400;add_free_neighbor(f,following,prev=(NODE-12-HEAP)//4,size=11)
        half(f['cells'],NODE-10,(following-HEAP)//4)
        r=self.derive(f);self.next(f,r);m=memory(r)
        self.assertEqual(m[NODE-6]|m[NODE-5]<<8,46);self.assertIn(at(f['layout'],'remove'),r['trace'])

    def test_nonfree_next_header_backlink_write_is_real(self):
        f=fixture();following=1400
        for a in range(following,following+12):f['cells'][a]=0
        half(f['cells'],following+4,0x7373);half(f['cells'],NODE-10,100)
        r=self.derive(f);self.next(f,r);m=memory(r);self.assertEqual((m[following],m[following+1]),(47,0))

    def test_previous_and_next_scheduler_links_observe_ordered_alias(self):
        f=fixture();neighbor=2000;put(f['cells'],NODE+4,P(neighbor));put(f['cells'],NODE+8,P(neighbor));put(f['cells'],NODE+12,I(0))
        r=self.derive(f);self.next(f,r);m=memory(r)
        self.assertEqual(tuple(m[neighbor+4+i] for i in range(4)),P(neighbor));self.assertEqual(tuple(m[neighbor+8+i] for i in range(4)),P(neighbor))

    def test_parent_child_head_unlink_is_actual_read_compare_write(self):
        f=fixture();parent=2400;put(f['cells'],NODE+12,P(parent));put(f['cells'],parent+16,P(NODE))
        r=self.derive(f);self.next(f,r);m=memory(r);self.assertEqual(tuple(m[parent+16+i] for i in range(4)),I(0))

    def test_list_write_corrupts_saved_query_return_without_ABI_repair(self):
        f=fixture();put(f['cells'],NODE+4,P(SP-64));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'query',42));self.assertIn('Thumb tagged',r['boundary']['reason'])
        self.assertEqual(r['registers'][1],I(0));self.assert_raw(f,r,r['final_PC'])

    def test_callback_push_alias_changes_node_status_before_reload(self):
        f=fixture(node=SP-124);f['release_spans']=()
        # The callback's real save frame overlaps this node's first pointer.
        r=self.derive(f);self.assertIsNotNone(r['boundary']);self.assertFalse(r['conditional_root_return'])
        self.assertTrue(any(e['operation']=='write32' and e.get('coordinate')==SP-124 for e in r['memory_events']))

    def test_unknown_callback_stops_at_actual_thunk(self):
        f=fixture();put(f['cells'],NODE,I(0x081f0001));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'thunk'));self.assertIn('callback identity',r['boundary']['reason']);self.assert_raw(f,r,r['final_PC'])

    def test_even_callback_control_word_stops_at_thunk(self):
        f=fixture();put(f['cells'],NODE,I(at(f['layout'],'callback')));r=self.derive(f)
        self.assertIn('Thumb tagged',r['boundary']['reason']);self.assert_raw(f,r,r['final_PC'])

    def test_opaque_callback_is_never_inferred(self):
        f=fixture();put(f['cells'],NODE,O('callback unknown'));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'thunk'));self.assertIn('opaque',r['boundary']['reason'])

    def test_missing_free_lifetime_extent_stops_after_actual_metadata_effects(self):
        f=fixture();f['release_spans']=();r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'free',250));self.assertIn('lifetime premise',r['boundary']['reason']);self.assert_raw(f,r,r['final_PC'])
        self.assertEqual(memory(r)[HEAP+4],1);self.assertEqual(r['conditional_released_payloads'],[])

    def test_release_alias_with_live_saved_frame_is_refused_at_actual_pop(self):
        f=fixture();f['release_spans']=((NODE,SP),);r=self.derive(f)
        # The proposed release already crosses retired nested saves; stop before wrapper POP.
        self.assertEqual(r['boundary']['site'],at(f['layout'],'free',250));self.assertIn('retired',r['boundary']['reason'])

    def test_literal_numeric_point_does_not_supply_provenance_implicitly(self):
        f=fixture();f['literal_points']=();r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'scheduler_remove',6));self.assertIn('provenance',r['boundary']['reason'])

    def test_literal_provenance_does_not_supply_missing_data(self):
        f=fixture();del f['cells'][GLOBAL+2];r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'scheduler_remove',6));self.assertIn('reaching',r['boundary']['reason'])

    def test_status_halfword_opaque_bytes_stay_unknown(self):
        f=fixture();put(f['cells'],NODE+20,O('status unknown'));r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'status',4));self.assertIn('opaque',r['boundary']['reason'])

    def test_allocator_size_unknown_is_not_promoted_to_scalar(self):
        f=fixture();f['cells'][NODE-6]=('opaque-byte','size unknown',0);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'free',14));self.assertIn('opaque',r['boundary']['reason'])

    def test_opaque_global_word_is_not_allocator_or_scheduler(self):
        f=fixture();put(f['cells'],GLOBAL,O('scheduler unknown'));r=self.derive(f)
        self.assertIn('provenance',r['boundary']['reason']);self.assertFalse(r['conditional_root_return'])

    def test_protected_unlink_store_stops_before_writing(self):
        f=fixture();f['protected_spans']=((NODE+12,NODE+16),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'list_remove',130));self.assertIn('protected',r['boundary']['reason'])

    def test_incoming_retired_payload_is_not_reactivated_by_stack(self):
        f=fixture();f['retired_spans']=((SP-16,SP),);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'root'));self.assertIn('externally retired',r['boundary']['reason'])

    def test_root_non256_phase_stops_without_old_phase_execution(self):
        f=fixture();half(f['cells'],REQUEST,0);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'root',20));self.assertIn('phase',r['boundary']['reason']);self.assert_raw(f,r,r['final_PC'])

    def test_frame_allocation_preserves_known_aliased_local_bytes(self):
        f=fixture();f['cells'][SP-104]=0xA7;r=self.derive(f);self.next(f,r)
        self.assertEqual(memory(r)[SP-104],0xA7)

    def test_unaligned_scheduler_status_dereference_stops(self):
        f=fixture(node=NODE+1);r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'status',4));self.assertIn('unaligned',r['boundary']['reason'])

    def test_numeric_pointer_wrap_has_no_memory_permission(self):
        f=fixture();f['arena_base']=0xfffff000;r=self.derive(f)
        self.assertIn('wrap',r['boundary']['reason']);self.assertEqual(r['trace'],[])

    def test_child_cycle_stops_at_explicit_budget(self):
        f=fixture();put(f['cells'],NODE+16,P(NODE));put(f['cells'],NODE+8,P(NODE));f['max_steps']=100;r=self.derive(f)
        self.assertEqual(len(r['trace']),100);self.assertIn('budget',r['boundary']['reason']);self.assertEqual(r['conditional_released_payloads'],[])

    def test_complete_owner_mutation_rejected_before_state_effects(self):
        f=fixture();owners=list(f['layout'].owners);i=next(j for j,v in enumerate(owners) if v[0]=='free');n,a,b=owners[i]
        b=bytearray(b);b[22]^=1;owners[i]=(n,a,bytes(b));f['layout']=model.Layout(tuple(owners))
        with self.assertRaisesRegex(ValueError,'shape'):self.derive(f)

    def test_nested_direct_target_identity_rejected(self):
        f=fixture();owners=list(f['layout'].owners);i=next(j for j,v in enumerate(owners) if v[0]=='query');n,a,b=owners[i]
        b=bytearray(b);b[8:12]=model.removal._bl(a+8,at(f['layout'],'free'));owners[i]=(n,a,bytes(b));f['layout']=model.Layout(tuple(owners))
        with self.assertRaisesRegex(ValueError,'target'):self.derive(f)

    def test_allocator_marker_is_not_arbitrary_relocatable_data(self):
        f=fixture();owners=list(f['layout'].owners);i=next(j for j,v in enumerate(owners) if v[0]=='free');n,a,b=owners[i]
        b=bytearray(b);b[44]=1;owners[i]=(n,a,bytes(b));f['layout']=model.Layout(tuple(owners))
        with self.assertRaisesRegex(ValueError,'marker'):self.derive(f)

    def test_generic_relocated_complete_binding_and_query_return(self):
        f=fixture(status=0);l=layout(0x10000);f['layout']=model.bind(l.owners,selector=model.SELECTOR)
        r=self.derive(f);self.assertTrue(r['conditional_root_return']);self.assert_raw(f,r)

    def test_duplicate_owner_roles_and_overlaps_refused(self):
        l=layout();o=list(l.owners);o[1]=o[0]
        with self.assertRaises(ValueError):model.bind(tuple(o),selector=model.SELECTOR)
        o=list(l.owners);n,a,b=o[1];o[1]=(n,o[0][1],b)
        with self.assertRaisesRegex(ValueError,'overlap'):model.bind(tuple(o),selector=model.SELECTOR)

    def test_explicit_selector_and_interval_validation(self):
        f=fixture();f['selector']='default'
        with self.assertRaises(ValueError):self.derive(f)
        f=fixture();f['release_spans']=((NODE,NODE+32),(NODE,NODE+64))
        with self.assertRaises(ValueError):self.derive(f)

class ExtendedPhase256Tests(unittest.TestCase):
    assert_raw=Phase256Tests.assert_raw
    derive=Phase256Tests.derive
    next=Phase256Tests.next
    # Only the newly named methods are selected; inherited successes are never replayed.
    def test_new_both_neighbor_coalescing_matches_raw(self):
        f=fixture();left,right=1100,1400
        add_free_neighbor(f,left,nxt=47,size=16)
        add_free_neighbor(f,right,prev=47,size=11)
        half(f['cells'],HEAP,25);half(f['cells'],HEAP+2,25);half(f['cells'],HEAP+4,2)
        half(f['cells'],left+10,100);half(f['cells'],right+8,25)
        half(f['cells'],NODE-12,25);half(f['cells'],NODE-10,100)
        r=self.derive(f);self.next(f,r);m=memory(r)
        self.assertEqual(m[left+6]|m[left+7]<<8,65);self.assertEqual(m[HEAP+4],1)
        self.assertEqual(r['trace'].count(at(f['layout'],'remove')),2)

    def test_new_child_then_parent_free_with_one_state(self):
        f=fixture();child=1600
        for a in range(child-12,child+24):f['cells'][a]=0
        half(f['cells'],child-8,0x7373);half(f['cells'],child-6,19)
        put(f['cells'],child,I(at(f['layout'],'callback')|1));put(f['cells'],child+12,P(NODE))
        put(f['cells'],NODE+16,P(child));f['release_spans']=((NODE,NODE+128),(child,child+64))
        r=self.derive(f);self.next(f,r)
        self.assertEqual(r['conditional_released_payloads'],[(child,child+64),(NODE,NODE+128)])
        self.assertEqual(r['trace'].count(at(f['layout'],'callback')),2)
        self.assertEqual(memory(r)[HEAP+4],2)

    def test_new_status_comparison_accepts_high_unsigned_halfword(self):
        f=fixture(status=65535);r=self.derive(f);self.assertTrue(r['conditional_root_return']);self.assert_raw(f,r)

    def test_new_numeric_debug_point_equals_node_uses_real_delay(self):
        f=fixture();o=[]
        for n,a,b in f['layout'].owners:
            if n=='list_remove':b=b[:172]+(BASE+NODE).to_bytes(4,'little')
            o.append((n,a,b))
        f['layout']=model.Layout(tuple(o));r=self.derive(f);self.next(f,r)
        self.assertEqual(r['trace'].count(at(f['layout'],'list_remove',146)),4)

    def test_new_descriptor_phase_unknown_after_alias_is_not_assumed_one(self):
        f=fixture(node=SP-116)
        # List's own saves overwrite the node interface before callback entry.
        r=self.derive(f);self.assertIsNotNone(r['boundary']);self.assertFalse(r['conditional_root_return'])
        self.assertNotIn(at(f['layout'],'free'),r['trace'])

    def test_new_released_alias_cursor_is_not_followed_again(self):
        f=fixture();child=1600
        for a in range(child-12,child+24):f['cells'][a]=0
        half(f['cells'],child-8,0x7373);half(f['cells'],child-6,19)
        put(f['cells'],child,I(at(f['layout'],'callback')|1));put(f['cells'],child+4,P(child))
        put(f['cells'],child+12,P(NODE));put(f['cells'],NODE+16,P(child))
        f['release_spans']=((NODE,NODE+128),(child,child+64))
        r=self.derive(f);self.assertIn('retired',r['boundary']['reason']);self.assertEqual(r['conditional_released_payloads'],[(child,child+64)])
        self.assertEqual(r['boundary']['site'],at(f['layout'],'list_remove',20))

    def test_new_complete_selected_bind_rejects_short_body(self):
        f=fixture();o=list(f['layout'].owners);n,a,b=o[0];o[0]=(n,a,b[:-2])
        with self.assertRaisesRegex(ValueError,'shape'):model.bind(tuple(o),selector=model.SELECTOR)

    def test_new_metadata_arithmetic_wrap_is_machine_bits_not_size_authority(self):
        f=fixture();half(f['cells'],NODE-6,1);r=self.derive(f);self.next(f,r);m=memory(r)
        self.assertEqual((m[NODE-6],m[NODE-5]),(254,255));self.assertFalse(r['actual_heap_lifetime_proved'])

class ReleaseProtectionTests(unittest.TestCase):
    assert_raw=Phase256Tests.assert_raw
    derive=Phase256Tests.derive
    next=Phase256Tests.next

    def test_new_release_preserves_protected_payload_lifetime(self):
        f=fixture();f['protected_spans']=((NODE+100,NODE+104),)
        r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'free',250))
        self.assertIn('release intersects protected',r['boundary']['reason'])
        self.assertEqual(r['conditional_released_payloads'],[])
        self.assert_raw(f,r,r['final_PC'])

    def test_new_release_cannot_retire_bound_code(self):
        code=at(layout(),'callback')-BASE;node=code-128;heap=node-200
        f=fixture(node=node);put(f['cells'],SCHED,P(heap))
        for a in range(heap,heap+12):f['cells'][a]=0
        f['release_spans']=((node,code+4),)
        r=self.derive(f)
        self.assertEqual(r['boundary']['site'],at(f['layout'],'free',250))
        self.assertIn('release intersects immutable owner',r['boundary']['reason'])
        self.assertEqual(r['conditional_released_payloads'],[])
        self.assert_raw(f,r,r['final_PC'])

    def test_new_disjoint_protection_leaves_conditional_free_path(self):
        f=fixture();f['protected_spans']=((NODE+200,NODE+204),)
        r=self.derive(f);self.next(f,r)
        self.assertEqual(r['conditional_released_payloads'],[(NODE,NODE+128)])

if __name__=='__main__':unittest.main()
