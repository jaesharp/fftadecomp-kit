"""Independent selected-path execution and hostile input/ownership cases."""
import unittest
import scheduler_callback_zero_phase as kernel
from descriptor_partial_word_prerequisite import Word


def branch_link(site,target):
    d=target-site-4
    return (0xf000|((d>>12)&2047)).to_bytes(2,'little')+(0xf800|((d>>1)&2047)).to_bytes(2,'little')


def fixture(a=0x08001000,h=0x08003000,literal=0x08397280):
    c=bytearray(658);helper=bytearray(292)
    chunks={
        0:'b5f0 b084 1c06 1c0f 1c15 8839 2080 0040 4281 d044 4281 dc04 2900 d00d 2901 d03b e132 4804 4281 d100 e0ea 3001 4281 d100 e10a e129',
        56:'70e9 7129 2301 2014 5e39 299e d102 70eb 2307 e007',
        92:'78e8 2802 d006 8af8 70a8 6878 60e8 e003',
        116:'2405 78a8 2800 d000 2400 68e8 4904 2200 9200 9601 1c22',
        142:'6368 e0fa',648:'2000 b004 bcf0 bc02 4708'}
    for offset,words in chunks.items():
        raw=b''.join(int(w,16).to_bytes(2,'little')for w in words.split());c[offset:offset+len(raw)]=raw
    c[138:142]=branch_link(a+138,h);c[148:152]=literal.to_bytes(4,'little')
    head='b5f0 b08d 1c06 1c0c 9d12 0612 0e12 061b 0e1b 2a00 d103 2b07 d101 2000 e077'
    helper[:30]=b''.join(int(w,16).to_bytes(2,'little')for w in head.split())
    helper[270:278]=bytes.fromhex('0db0 f0bc 02bc 0847')
    return bytes(c),a,bytes(helper),h


def bind(p=None):return kernel.bind(*(fixture()if p is None else p),selector=kernel.SELECTOR)
def inputs():return {r:Word.unproved(f'incoming-r{r}')for r in (*range(13),14)}
def relation(**kw):
    args=dict(binding=bind(),phase=0,tag=158,option=1,descriptor_word=Word.unproved('descriptor-word4'),registers=inputs(),entry_sp=-132,selector=kernel.SELECTOR)
    args.update(kw);return kernel.derive(**args)


def execute(p,option,opaque):
    """Independent integer Thumb interpreter for constructed concrete witnesses.

    It shares no instruction decoder, path template or semantic helper with the
    relation. Unknown code is refused, missing data faults, and stack bytes are
    actually written/read rather than supplied as an ABI register summary.
    """
    c,a,h,ha=p;code={a+i:b for i,b in enumerate(c)};code.update({ha+i:b for i,b in enumerate(h)})
    memory={};reads=[];writes=[];trace=[]
    def store(addr,width,value,record=True):
        for i in range(width):memory[addr+i]=(value>>(8*i))&255
        if record:writes.append((addr,width,value&((1<<(8*width))-1)))
    def load(addr,width):
        source=code if addr in code else memory
        v=sum(source[addr+i]<<(8*i)for i in range(width));reads.append((addr,width,v));return v
    initial={r:0x12340000+4*r for r in range(16)}
    initial.update({0:0x6000,1:0x4000,2:0x5000,13:0x10000,14:0x09000001})
    regs=dict(initial);pc=a;comparison=None;deepest=regs[13]
    store(0x4000,2,0,False);store(0x4014,2,158,False);store(0x4016,2,option,False);store(0x4004,4,opaque,False)
    def signed(v):return v-0x100000000 if v&0x80000000 else v
    for _ in range(160):
        trace.append(pc);op=code[pc]|code[pc+1]<<8;following=pc+2
        if op&0xfe00==0xb400:
            selected=[r for r in range(8)if op>>r&1]+([14]if op&256 else [])
            regs[13]-=4*len(selected)
            for i,r in enumerate(selected):store(regs[13]+4*i,4,regs[r])
        elif op&0xfe00==0xbc00:
            selected=[r for r in range(8)if op>>r&1]
            for i,r in enumerate(selected):regs[r]=load(regs[13]+4*i,4)
            regs[13]+=4*len(selected)
        elif op&0xff00==0xb000:
            regs[13]+=4*(op&127)*(1 if not op&128 else -1)
        elif op&0xffc0==0x1c00:regs[op&7]=regs[(op>>3)&7]
        elif op&0xf800==0x2000:regs[(op>>8)&7]=op&255
        elif op&0xe000==0 and op&0x1800 in (0,0x0800):
            shift=(op>>6)&31;value=regs[(op>>3)&7]
            regs[op&7]=((value<<shift)&0xffffffff)if not op&0x0800 else(value>>(shift or 32))
        elif op&0xf800==0x2800:comparison=(regs[(op>>8)&7],op&255)
        elif op&0xffc0==0x4280:comparison=(regs[op&7],regs[(op>>3)&7])
        elif op&0xf800 in (0x6800,0x7800,0x8800,0x6000,0x7000):
            family=op&0xf800;width={0x6800:4,0x7800:1,0x8800:2,0x6000:4,0x7000:1}[family]
            addr=regs[(op>>3)&7]+width*((op>>6)&31)
            if family in(0x6000,0x7000):store(addr,width,regs[op&7])
            else:regs[op&7]=load(addr,width)
        elif op&0xfe00==0x5e00:
            v=load(regs[(op>>3)&7]+regs[(op>>6)&7],2);regs[op&7]=(v if v<32768 else v-65536)&0xffffffff
        elif op&0xf800==0x4800:regs[(op>>8)&7]=load(((pc+4)&~3)+4*(op&255),4)
        elif op&0xf000==0x9000:
            addr=regs[13]+4*(op&255);r=(op>>8)&7
            if op&0x0800:regs[r]=load(addr,4)
            else:store(addr,4,regs[r])
        elif op&0xf000==0xd000:
            left,right=comparison;condition=(op>>8)&15
            taken={0:left==right,1:left!=right,12:signed(left)>signed(right)}[condition]
            if taken:following=pc+4+2*((op&255)-256 if op&128 else op&255)
        elif op&0xf800==0xe000:
            d=op&2047;following=pc+4+2*(d-2048 if d&1024 else d)
        elif op&0xf800==0xf000:
            low=code[pc+2]|code[pc+3]<<8
            if low&0xf800!=0xf800:raise AssertionError('bad BL')
            d=((op&2047)<<12)|((low&2047)<<1)
            if d&(1<<22):d-=1<<23
            regs[14]=(pc+4)|1;following=pc+4+d
        elif op&0xff87==0x4700:
            target=regs[(op>>3)&15]
            if target==initial[14]:return regs,initial,memory,trace,reads,writes,deepest
            following=target&~1
        else:raise AssertionError(f'unmodeled independent instruction {pc:08X}:{op:04X}')
        deepest=min(deepest,regs[13]);pc=following
    raise AssertionError('independent instruction budget exceeded')


class CallbackTests(unittest.TestCase):
    def test_relocated_complete_bodies_bind(self):
        b=bind(fixture(0x08009000,0x08007000));self.assertEqual(b.helper,0x08007000)

    def test_independent_paths_match_conditional_trace_and_memory(self):
        p=fixture();r=relation();a=p[1];h=p[3]
        expected=[x for x in r['selected_callback_trace']if x<=a+138]+r['selected_helper_trace']+[x for x in r['selected_callback_trace']if x>a+138]
        for option,opaque in ((1,0xaabbccdd),(2,0),(255,0xffffffff),(0x101,0x76543210),(0xff80,0x11223344)):
            regs,initial,mem,trace,reads,writes,deepest=execute(p,option,opaque)
            self.assertEqual(trace,expected);self.assertEqual(regs[0],0);self.assertEqual(regs[13],initial[13])
            self.assertTrue(all(regs[r]==initial[r]for r in range(4,13)))
            external=[v for v in writes if 0x5000<=v[0]<0x5100]
            self.assertEqual(external,[(0x5003,1,0),(0x5004,1,0),(0x5003,1,1),(0x5002,1,option&255),(0x500c,4,opaque),(0x5034,4,0)])
            self.assertEqual(deepest,initial[13]-108)

    def test_descriptor_word_is_forwarded_without_scalar_fabrication(self):
        word=Word.unproved('opaque-may-contain-pointer');r=relation(descriptor_word=word)
        self.assertEqual(r['helper_entry_registers']['0'],list(word.bytes));self.assertFalse(r['nonescape_proved'])

    def test_saved_origins_restore_r4_through_r12(self):
        regs=inputs();r=relation(registers=regs)
        self.assertEqual(r['conditional_preserved_origins'],{str(n):list(regs[n].bytes)for n in range(4,13)})

    def test_nested_stack_argument_uses_exact72_byte_private_frame(self):
        r=relation();h=r['helper']['address'];row=next(v for v in r['ordered_accesses']if v['site']==h+8)
        self.assertEqual(row['address'],['stack',-168]);self.assertEqual(row['value'],list(Word.constant(0).bytes))

    def test_unknown_phase_does_not_become_zero(self):
        with self.assertRaisesRegex(ValueError,'phase0'):relation(phase=Word.unproved('phase'))

    def test_nonzero_phase_is_outside_selected_path(self):
        with self.assertRaisesRegex(ValueError,'phase0'):relation(phase=1)

    def test_alternate_tag_is_not_admitted(self):
        with self.assertRaisesRegex(ValueError,'tag158'):relation(tag=395)

    def test_zero_low_byte_does_not_use_helper_early_return(self):
        with self.assertRaisesRegex(ValueError,'low byte'):relation(option=256)

    def test_bool_is_not_a_machine_word(self):
        with self.assertRaises(ValueError):relation(phase=False)

    def test_option_outside_halfword_is_refused(self):
        with self.assertRaises(ValueError):relation(option=65537)

    def test_missing_ambient_origin_is_refused(self):
        regs=inputs();del regs[9]
        with self.assertRaisesRegex(ValueError,'origins'):relation(registers=regs)

    def test_unaligned_or_unbounded_frame_is_refused(self):
        for sp in(-133,-772,4):
            with self.assertRaises(ValueError):relation(entry_sp=sp)

    def test_wrong_selector_is_refused(self):
        with self.assertRaisesRegex(ValueError,'selector'):kernel.bind(*fixture(),selector=None)

    def test_mutated_effect_instruction_is_refused(self):
        p=list(fixture());c=bytearray(p[0]);c[100]^=1;p[0]=bytes(c)
        with self.assertRaisesRegex(ValueError,'path differs'):bind(p)

    def test_changed_helper_gate_is_refused(self):
        p=list(fixture());c=bytearray(p[2]);c[22]^=1;p[2]=bytes(c)
        with self.assertRaisesRegex(ValueError,'path differs'):bind(p)

    def test_wrong_nested_call_target_is_refused(self):
        p=list(fixture());c=bytearray(p[0]);c[138:142]=branch_link(p[1]+138,p[3]+2);p[0]=bytes(c)
        with self.assertRaisesRegex(ValueError,'target differs'):bind(p)

    def test_wrong_common_return_branch_is_refused(self):
        p=list(fixture());c=bytearray(p[0]);c[144:146]=bytes.fromhex('f9e0');p[0]=bytes(c)
        with self.assertRaisesRegex(ValueError,'target differs'):bind(p)

    def test_complete_size_and_unique_spans_are_required(self):
        p=list(fixture());p[0]=p[0][:-2]
        with self.assertRaisesRegex(ValueError,'complete'):bind(p)
        p=list(fixture());p[3]=p[1]+4
        with self.assertRaisesRegex(ValueError,'overlap'):bind(p)

    def test_unvisited_byte_change_is_bound_without_whole_cfg_claim(self):
        p=list(fixture());c=bytearray(p[0]);c[300]=17;p[0]=bytes(c);b=bind(p)
        self.assertNotEqual(b.callback_sha,bind().callback_sha);self.assertFalse(relation(binding=b)['whole_callback_CFG_closed'])

    def test_literal_value_is_derived_from_actual_bound_bytes(self):
        r=relation(binding=bind(fixture(literal=0x08004444)))
        self.assertEqual(r['helper_entry_registers']['1'],list(Word.constant(0x08004444).bytes))

    def test_every_admission_and_actual_premise_remains_false(self):
        r=relation();self.assertEqual(len(r['obligations']),8);self.assertTrue(all(v['proved']is False for v in r['obligations']))
        for k in('actual_reaching_state_proved','actual_phase_zero_proved','physical_permissions_proved','role_separation_proved','nonescape_proved','source_initialization_proved','unconditional_termination','source_or_ELF_admission','native_admission'):
            self.assertIs(r[k],False)


if __name__=='__main__':unittest.main()
