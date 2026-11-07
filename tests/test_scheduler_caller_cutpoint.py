"""New synthetic prefix programs; no ROM or original producer calls."""
import unittest

import scheduler_caller_cutpoint as kernel


def fixture(extra=b''):
    address=0x08001000; target=0x08002000
    code=bytearray(); labels={}; fixups=[]
    def emit(value):
        offset=len(code); code.extend(value.to_bytes(2,'little'));return offset
    def branch(condition,label):fixups.append((emit(0),condition,label))
    def literal(register,label):fixups.append((emit(0),'literal'+str(register),label))
    for x in (0xb570,0xb089,0x1c06,0x1c0d,0x1c14):emit(x)
    code.extend(extra)
    emit(0x882b);literal(0,'command');emit(0x4283);branch(1,'return')
    emit(0x78e0);emit(0x2800);branch(0,'return');emit(0x2802);branch(0,'return')
    for x in (0xa902,0x209e,0x8288,0x2001,0x82c8,0x6920,0x9003):emit(x)
    literal(0,'callback')
    for x in (0x2140,0xaa02,0x1c33):emit(x)
    labels['call']=len(code)
    delta=target-(address+len(code))-4
    code.extend((0xf000|((delta>>12)&2047)).to_bytes(2,'little'))
    code.extend((0xf800|((delta>>1)&2047)).to_bytes(2,'little'))
    labels['return']=len(code)
    for x in (0xb009,0xbc70,0xbc02,0x4708):emit(x)
    code_end=len(code);alignment=[]
    if len(code)%4:
        alignment=[[address+len(code),address+len(code)+2]];emit(0)
    words=[]
    for label,value in [('command',257),('callback',0x08003001)]:
        labels[label]=len(code);code.extend(value.to_bytes(4,'little'))
        words.append(dict(address=address+labels[label],value=value,load_sites=[],switch_word=False))
    for offset,condition,label in fixups:
        if isinstance(condition,str):
            value=0x4800|(int(condition[-1])<<8)|((address+labels[label]-((address+offset+4)&~3))//4)
            next(w for w in words if w['address']==address+labels[label])['load_sites'].append(address+offset)
        else:value=0xd000|(condition<<8)|(((labels[label]-offset-4)//2)&255)
        code[offset:offset+2]=value.to_bytes(2,'little')
    partition=dict(code_bytes=code_end,literal_and_table_bytes=8,alignment_bytes=2*len(alignment),alignment=alignment,words=words)
    return bytes(code),address,partition,target,labels


def bind(f=None,selector=kernel.SELECTOR):
    if f is None:f=fixture()
    return kernel.bind(*f[:4],selector=selector)


def run(f=None):return kernel.derive(bind(f),selector=kernel.SELECTOR)


class SchedulerCallerCutpointTests(unittest.TestCase):
    def test_one_feasible_descriptor_call_path(self):self.assertEqual(len(run()),1)

    def test_command_is_exactly_257_on_call_path(self):
        state=run()[0];name=state['reads'][0]['origin'];self.assertEqual(state['domains'][name],((257,257),))

    def test_completion_excludes_zero_and_two(self):
        state=run()[0];name=state['reads'][1]['origin'];self.assertEqual(state['domains'][name],((1,1),(3,255)))

    def test_exact_frame_and_descriptor_pointer(self):
        state=run()[0];self.assertEqual(state['SP'],-52);self.assertEqual(state['registers'][2],kernel.Value('local',-44))

    def test_four_saved_words_keep_exact_origins(self):
        state=run()[0]
        for offset,reg in [(-16,4),(-12,5),(-8,6),(-4,14)]:
            self.assertEqual(state['words'][offset],kernel.Word.unproved(f'entry-r{reg}'))
            self.assertEqual(state['classes'][offset],kernel.SAVED)

    def test_halfword_initializers_combine_without_other_bytes(self):
        self.assertEqual(run()[0]['words'][-24].known_value(),158+(1<<16))

    def test_subject_is_actual_external_load_origin(self):
        state=run()[0];self.assertEqual(state['words'][-40],kernel.Word.unproved(state['reads'][2]['origin']))
        self.assertEqual((state['reads'][2]['base'],state['reads'][2]['offset'],state['reads'][2]['width']),('entry-r2',16,4))

    def test_unwritten_word_stays_opaque(self):
        word=run()[0]['words'][-44];self.assertIsNone(word.known_value())
        with self.assertRaises(ValueError):word.read_scalar(0,4)

    def test_task_state_request_aliases_preserved(self):
        state=run()[0];regs=state['registers']
        self.assertEqual(regs[3],regs[6]);self.assertEqual(regs[3],kernel.Value('opaque','entry-r0'))
        self.assertEqual(regs[4],kernel.Value('external','entry-r2'));self.assertEqual(regs[5],kernel.Value('external','entry-r1'))

    def test_callback_size_and_return_word_are_concrete(self):
        f=fixture();regs=run(f)[0]['registers']
        self.assertEqual(regs[0].value,0x08003001);self.assertEqual(regs[1].value,64)
        self.assertEqual(regs[14].value,(f[1]+f[4]['call']+4)|1)

    def test_nonargument_registers_keep_entry_origins(self):
        regs=run()[0]['registers']
        for reg in range(7,13):self.assertEqual(regs[reg],kernel.Value('opaque',f'entry-r{reg}'))

    def test_explicit_bind_selector(self):
        with self.assertRaisesRegex(ValueError,'selector'):bind(selector='default')

    def test_explicit_derive_selector(self):
        with self.assertRaisesRegex(ValueError,'selector'):kernel.derive(bind(),selector='default')

    def test_no_selected_call_rejected(self):
        f=list(fixture());f[3]+=4
        with self.assertRaisesRegex(ValueError,'selected call'):bind(f)

    def test_odd_target_rejected(self):
        f=list(fixture());f[3]+=1
        with self.assertRaisesRegex(ValueError,'aligned'):bind(f)

    def test_literal_reference_site_required(self):
        f=fixture();f[2]['words'][0]['load_sites']=[]
        with self.assertRaisesRegex(ValueError,'referenced word'):run(f)

    def test_partition_literal_value_checked(self):
        f=fixture();f[2]['words'][0]['value']=258
        with self.assertRaisesRegex(ValueError,'literal words'):bind(f)

    def test_partition_byte_counts_checked(self):
        f=fixture();f[2]['code_bytes']+=2
        with self.assertRaisesRegex(ValueError,'byte counts'):bind(f)

    def test_prior_ordinary_call_is_not_an_abi_assumption(self):
        with self.assertRaisesRegex(ValueError,'earlier ordinary call'):bind(fixture(bytes.fromhex('02f0f9ff')))

    def test_unmodeled_multiply_is_not_ignored(self):
        with self.assertRaisesRegex(ValueError,'unmodeled'):run(fixture(bytes.fromhex('4043')))

    def test_external_store_is_not_assumed_safe(self):
        with self.assertRaisesRegex(ValueError,'unmodeled'):run(fixture(bytes.fromhex('2070')))

    def test_word_store_cannot_overwrite_saved_word(self):
        f=list(fixture());offset=f[0].index(bytes.fromhex('0390'));f[0]=f[0][:offset]+bytes.fromhex('0990')+f[0][offset+2:]
        with self.assertRaisesRegex(ValueError,'protected'):run(f)

    def test_sp_alias_must_point_into_live_local_storage(self):
        f=list(fixture());offset=f[0].index(bytes.fromhex('02a9'));f[0]=f[0][:offset]+bytes.fromhex('20a9')+f[0][offset+2:]
        with self.assertRaisesRegex(ValueError,'live caller locals'):run(f)

    def test_signed_branch_rejects_high_bit_scalar(self):
        with self.assertRaisesRegex(ValueError,'nonnegative'):
            kernel._branch({},(kernel.Value('constant',0xffffffff),kernel.Value('constant',0)),'gt')

    def test_report_retains_all_admission_limits(self):
        layout=bind();report=kernel.report(layout,kernel.derive(layout,selector=kernel.SELECTOR))
        for key in ('caller_memory_physical_permission','source_C_initialization','whole_owner_admission','scheduler_prefix_closed','callback_effects_closed','nonescape_proved','unconditional_termination','source_or_ELF_admission','native_admission'):
            self.assertIs(report[key],False)
        self.assertEqual(report['states'][0]['protected'],[-16,-12,-8,-4])

    def test_interval_narrowing_outside_domain_is_empty(self):
        self.assertEqual(kernel._restrict(((0,255),),'eq',257),())

    def test_nonzero_symbolic_arithmetic_rejected(self):
        with self.assertRaisesRegex(ValueError,'symbolic arithmetic'):kernel._plus(kernel.Value('opaque','x'),1)


if __name__=='__main__':unittest.main()
