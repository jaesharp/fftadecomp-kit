"""New caller-entry, partial initialization and shared-save alias states."""
import copy
from dataclasses import replace
import unittest

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

import scheduler_request_entry_state as request
import scheduler_copy_state as words
import scheduler_entry_state as entry
import scheduler_return_state as returns
import allocator_remove_relation as branch
from test_scheduler_entry_state import layout as wrapper_layout
from test_scheduler_callback_state import layout as callback_layout

BASE = 0x02000000
C = 0x080a0000
E = 2048
D = 6000
P = 7000


def opaque(name):
    return tuple(('opaque-byte', name, i) for i in range(4))


def put(memory, at, word):
    memory.update({at+i:value for i, value in enumerate(word)})


def half(memory, at, value):
    memory[at] = value & 255
    memory[at+1] = value >> 8 & 255


def layout():
    w, cb = wrapper_layout(), callback_layout()
    body = bytearray(230)
    body[:48] = request.HEAD; body[48:52] = (257).to_bytes(4, 'little')
    body[136:174] = request.SELECTED; body[174:178] = branch._bl(C+174, w.wrapper)
    body[188:192] = (cb.callback | 1).to_bytes(4, 'little')
    return request.Layout(C, bytes(body), w, cb)


def fixture(*,phase=257,completion=1,payload=P,descriptor=D):
    r = {reg:opaque('root R'+str(reg)) for reg in range(15)}
    r.update({0:words._pointer(9000),1:words._pointer(descriptor),
              2:words._pointer(payload),13:words._pointer(E)})
    m = {}; half(m, descriptor, phase); m[payload+3] = completion
    put(m, payload+16, words._pointer(11000))
    return dict(layout=layout(),arena_base=BASE,cells=m,registers=r,selector=request.SELECTOR)


def raw(f):
    """Independent Capstone execution of the selected original instruction path."""
    l=f['layout'];r=dict(f['registers']);m=dict(f['cells']);pc=l.address;trace=[];events=[]
    decoder=Cs(CS_ARCH_ARM,CS_MODE_THUMB);decoder.detail=True
    allowed=set(range(0,48,2))|set(range(136,176,2));comparison=None
    def reg(op):
        name=decoder.reg_name(op.reg)
        return {'sp':13,'lr':14,'pc':15,'sb':9,'sl':10,'fp':11,'ip':12}.get(name,int(name[1:]) if name.startswith('r')else -1)
    def number(word):
        assert all(type(v)is int for v in word)
        return sum(v<<(8*i)for i,v in enumerate(word))
    def coordinate(word):
        assert word==words._pointer(word[0][1])
        return word[0][1]
    def memory_at(op):
        name=decoder.reg_name(op.mem.base)
        if name=='pc':return ((pc+4)&~3)+op.mem.disp,True
        index={'sp':13}.get(name,int(name[1:])if name.startswith('r')else -1)
        return coordinate(r[index])+op.mem.disp,False
    def read(at,width):
        value=tuple(m[at+i]for i in range(width));events.append((pc,'read'+str(width*8),at,value))
        return value if width==4 else words._constant(sum(v<<(8*i)for i,v in enumerate(value)))
    def write(at,width,value):
        value=value[:width];put(m,at,value);events.append((pc,'write'+str(width*8),at,value))
    for _ in range(80):
        if pc==l.wrapper.wrapper:return r,m,trace,events,True,pc
        if pc-l.address not in allowed:return r,m,trace,events,False,pc
        ins=next(decoder.disasm(l.data[pc-l.address:],pc,1));ops=ins.operands;name=ins.mnemonic
        trace.append(pc);nxt=pc+ins.size
        if name=='push':
            selected=[reg(op)for op in ops];at=coordinate(r[13])-4*len(selected)
            for n,index in enumerate(selected):write(at+4*n,4,r[index])
            r[13]=words._pointer(at)
        elif name=='sub':
            assert reg(ops[0])==13;old=coordinate(r[13]);new=old-ops[1].imm;r[13]=words._pointer(new)
            for at in range(new,old):m[at]=('opaque-byte','unmodeled request local',at-new)
        elif name=='adds':
            dst=reg(ops[0])
            if len(ops)==3:
                assert ops[2].imm==0;r[dst]=r[reg(ops[1])]
            else:r[dst]=words._constant(number(r[dst])+ops[1].imm)
        elif name=='add':
            assert reg(ops[1])==13;r[reg(ops[0])]=words._pointer(coordinate(r[13])+ops[2].imm)
        elif name=='movs':r[reg(ops[0])]=words._constant(ops[1].imm)
        elif name=='lsls':r[reg(ops[0])]=words._constant(number(r[reg(ops[1])])<<ops[2].imm&0xffffffff)
        elif name=='cmp':
            a=number(r[reg(ops[0])]);b=ops[1].imm if ins.op_str.split(',')[1].strip().startswith('#')else number(r[reg(ops[1])])
            comparison=(a,b)
        elif name in ('beq','bne','bgt'):
            a,b=comparison;take={'beq':a==b,'bne':a!=b,'bgt':a>b}[name]
            if take:nxt=ops[0].imm
        elif name=='b':nxt=ops[0].imm
        elif name=='bl':r[14]=words._constant(nxt|1);nxt=ops[0].imm
        elif name in ('ldr','ldrh','ldrb'):
            at,literal=memory_at(ops[1]);width={'ldr':4,'ldrh':2,'ldrb':1}[name]
            r[reg(ops[0])]=tuple(l.data[at-l.address:at-l.address+4])if literal else read(at,width)
        elif name in ('str','strh'):
            at,literal=memory_at(ops[1]);assert not literal;write(at,4 if name=='str'else 2,r[reg(ops[0])])
        else:raise AssertionError((hex(pc),name,ins.op_str))
        pc=nxt
    raise AssertionError('selected raw execution did not reach a cutpoint')


class RequestEntryTests(unittest.TestCase):
    def test_independent_thumb_execution_eight_new_dispatch_and_call_states(self):
        for phase,option in [(257,3),(257,17),(257,255),(257,0),(257,2),(0,9),(258,11),(65535,13)]:
            with self.subTest(phase=phase,option=option):
                f=fixture(phase=phase,completion=option);r=request.derive(**f);regs,memory,trace,events,reached,pc=raw(f)
                self.assertEqual(r['registers'],regs);self.assertEqual(r['trace'],trace)
                self.assertEqual({int(k):v for k,v in r['post_cells'].items()},memory)
                observed=[(v['site'],v['operation'],v['coordinate'],v['bytes'])for v in r['memory_events']if v['operation'].startswith(('read8','read16','read32','write'))]
                self.assertEqual(observed,events);self.assertEqual(r['reaches_wrapper_entry_under_conditions'],reached)
                if not reached:self.assertEqual(r['boundary']['site'],pc)

    def test_only_three_descriptor_fields_are_initialized(self):
        f=fixture(completion=23);r=request.derive(**f);d=E-44;m=r['post_cells']
        self.assertTrue(r['reaches_wrapper_entry_under_conditions'])
        self.assertEqual(tuple(m[str(d+4+i)]for i in range(4)),words._pointer(11000))
        self.assertEqual(tuple(m[str(d+20+i)]for i in range(4)),(158,0,1,0))
        self.assertTrue(all(type(m[str(d+i)])is tuple for i in [0,1,2,3,8,9,24,25,26,27]))
        self.assertFalse(r['descriptor_phase_initialized']);self.assertFalse(r['whole_descriptor_initialized'])

    def test_phase_dispatch_retains_exact_unmodeled_branch_targets(self):
        for phase,offset in [(0,52),(1,92),(2,220),(256,98),(258,192),(500,220)]:
            r=request.derive(**fixture(phase=phase,completion=29))
            self.assertEqual(r['boundary']['site'],C+offset);self.assertEqual(len(r['changed_cells']),16)

    def test_completion_zero_and_two_do_not_force_the_scheduler_path(self):
        for option,offset in [(0,220),(2,218)]:
            r=request.derive(**fixture(completion=option));self.assertEqual(r['boundary']['site'],C+offset)
            self.assertFalse(r['reaches_wrapper_entry_under_conditions']);self.assertEqual(len(r['changed_cells']),16)
            if option==2:self.assertEqual(r['registers'][0],words._constant(258))

    def test_actual_saved_word_can_replace_preentry_phase(self):
        f=fixture(descriptor=E-16,phase=0,completion=31);f['registers'][4]=words._constant(0x03000101)
        r=request.derive(**f);self.assertEqual(r['observed_phase'],257)
        self.assertTrue(r['reaches_wrapper_entry_under_conditions'])

    def test_actual_saved_word_can_replace_preentry_completion(self):
        f=fixture(payload=E-16,completion=0);f['registers'][4]=words._constant(0x05000000)
        r=request.derive(**f);self.assertEqual(r['observed_completion'],5)
        self.assertTrue(r['reaches_wrapper_entry_under_conditions'])

    def test_private_descriptor_cannot_reuse_old_scalar_phase(self):
        f=fixture(descriptor=E-32);r=request.derive(**f)
        self.assertEqual(r['boundary']['site'],C+10);self.assertIn('opaque',r['boundary']['reason'])

    def test_subject_read_from_unmodeled_local_transports_opaque_origins(self):
        f=fixture(payload=E-56,completion=37);r=request.derive(**f)
        self.assertTrue(r['reaches_wrapper_entry_under_conditions'])
        self.assertTrue(all(type(v)is tuple and v[0]=='opaque-byte'for v in r['observed_subject_word']))
        self.assertEqual(tuple(r['post_cells'][str(E-40+i)]for i in range(4)),r['observed_subject_word'])

    def test_protected_tag_refuses_before_any_descriptor_store(self):
        f=fixture(completion=41);f['protected_spans']=((E-24,E-22),);r=request.derive(**f)
        self.assertEqual(r['boundary']['site'],C+156);self.assertEqual(len(r['changed_cells']),16)

    def test_protected_subject_retains_prior_real_tag_and_option_writes(self):
        f=fixture(completion=43);f['protected_spans']=((E-40,E-36),);r=request.derive(**f)
        self.assertEqual(r['boundary']['site'],C+164);self.assertEqual(len(r['changed_cells']),20)
        self.assertEqual(tuple(r['changed_cells'][str(E-24+i)]for i in range(4)),(158,0,1,0))

    def test_unknown_missing_and_unaligned_reads_refuse_without_invented_bits(self):
        cases=[dict(descriptor=D+1),dict(payload=P+1)]
        for kwargs in cases:
            r=request.derive(**fixture(**kwargs));self.assertFalse(r['reaches_wrapper_entry_under_conditions'])
        f=fixture();del f['cells'][D];self.assertEqual(request.derive(**f)['boundary']['site'],C+10)
        f=fixture();f['cells'][P+3]=('opaque-byte','unknown completion',0)
        self.assertEqual(request.derive(**f)['boundary']['site'],C+136)

    def test_unmodeled_namespace_does_not_collide_with_incoming_origins(self):
        f=fixture(completion=47);f['cells'][0]=('opaque-byte','unmodeled request local',0)
        f['cells'][1]=('opaque-byte','unmodeled request local:1',0);r=request.derive(**f)
        self.assertEqual(r['unmodeled_private_namespace'],'unmodeled request local:2')
        self.assertEqual(r['post_cells']['0'],f['cells'][0])

    def test_complete_shapes_call_literal_and_explicit_input_types_are_required(self):
        l=layout()
        for offset in [0,48,156,174,188]:
            b=bytearray(l.data);b[offset]^=1
            with self.assertRaises(ValueError):request.bind(bytes(b),C,l.wrapper,l.callback,selector=request.SELECTOR)
        for change in [{'selector':None},{'arena_base':True},{'registers':{}},{'cells':{0:True}},
                       {'layout':replace(l,data=l.data[:-1])}]:
            f=fixture();f.update(change)
            with self.assertRaises(ValueError):request.derive(**f)

    def test_scalar_unaligned_and_wrapping_stack_inputs_refuse(self):
        for sp in [words._constant(E),words._pointer(E+2),words._pointer(-BASE+48)]:
            f=fixture();f['registers'][13]=sp;r=request.derive(**f)
            self.assertFalse(r['reaches_wrapper_entry_under_conditions']);self.assertEqual(r['changed_cells'],{})
        f=fixture();f['arena_base']=2**32-E;r=request.derive(**f)
        self.assertFalse(r['reaches_wrapper_entry_under_conditions']);self.assertEqual(r['changed_cells'],{})

    def test_inputs_are_immutable_and_runtime_admission_stays_unproved(self):
        f=fixture(completion=53);before=copy.deepcopy(f);r=request.derive(**f);self.assertEqual(f,before)
        for key in ['actual_reaching_state_proved','physical_access_proved','actual_code_execution_proved',
                    'actual_heap_or_SP_proved','whole_owner_CFG_closed','source_or_ELF_admission','native_admission']:
            self.assertFalse(r[key])

    def test_new_root_to_entry_composition_materializes_real_saved_words(self):
        f=fixture(completion=59);root=request.derive(**f);memory={int(k):v for k,v in root['post_cells'].items()}
        put(memory,f['layout'].wrapper.scheduler_point-BASE,words._pointer(14000))
        transported=entry.derive(f['layout'].wrapper,BASE,memory,root['registers'],selector=entry.SELECTOR)
        self.assertTrue(transported['reaches_scheduler_count_prefix'],transported['boundary'])
        memory.update({int(k):v for k,v in transported['changed_cells'].items()})
        for at,word in returns._saved(f['layout'].wrapper,root['registers'],E-52).items():
            self.assertEqual(tuple(memory[at+i]for i in range(4)),word)
        self.assertEqual(transported['registers'][9],words._pointer(E-44))
        self.assertEqual(transported['registers'][8],words._constant(f['layout'].callback.callback|1))
        self.assertEqual(transported['registers'][6],f['registers'][0])
        self.assertEqual(transported['registers'][4],words._constant(64))


if __name__ == '__main__':
    unittest.main()
