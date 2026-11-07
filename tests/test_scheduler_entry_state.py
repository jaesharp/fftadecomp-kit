"""New entry/save states, including an independent raw Thumb interpreter."""
import copy
from dataclasses import replace
import hashlib
import unittest

import scheduler_entry_state as entry
import scheduler_return_state as ret
import scheduler_allocator_state as state
import scheduler_copy_state as words
import allocator_search_relation as search
import allocator_remove_relation as remove
import allocator_insert_relation as insert
import allocator_split_relation as split
import allocator_wrapper_relation as wrapper

BASE = 0x02000000
POINT = BASE+4096


def sha(data):
    return hashlib.sha256(data).hexdigest()


def layout():
    s, r, m, i, a, w, t, cb, c = [0x08060000+n*0x1000 for n in range(9)]
    sl = search.Layout(s, sha(search.SHAPE))
    ml = remove.Layout(r, m, sha(remove.REMOVE_HEAD+remove._bl(r+124, m)+remove.REMOVE_TAIL), sha(remove.MEDIAN))
    il = insert.Layout(i, sha(insert.HEAD+remove._bl(i+22, s)+insert.MIDDLE+remove._bl(i+138, m)+insert.TAIL), sl, ml)
    al = split.Layout(a, sha(split._encoded(a, il, t, 0x08304000)), il, t, 0x08304000)
    wl = wrapper.Layout(w, sha(wrapper.HEAD+remove._bl(w+34, a)+wrapper.TAIL), al)
    st = state.Layout(c, sha(state._encoded(c, wl, cb)), wl, cb)
    w = 0x0805f000
    return ret.Layout(w, sha(ret._wrapper(w, st, POINT)), POINT, st)


def opaque(label):
    return tuple(('opaque-byte', label, i) for i in range(4))


def put(cells, at, word):
    cells.update({at+i:value for i, value in enumerate(word)})


def fixture(e=1024, size=0x12345678):
    regs = {r:opaque('incoming '+str(r)) for r in range(15)}
    regs.update({0:words._constant(0x080e5f51), 1:words._constant(size),
                 2:words._pointer(e+96), 3:words._pointer(7000), 13:words._pointer(e)})
    cells = {99:17}
    put(cells, POINT-BASE, words._pointer(6144))
    return dict(layout=layout(), arena_base=BASE, cells=cells, registers=regs, selector=entry.SELECTOR)


def raw(f):
    """Decode both actual entry byte strings without the entry relation."""
    l = f['layout']; regs = dict(f['registers']); memory = dict(f['cells']); events = []
    def constant(value):
        return tuple((value >> (8*i)) & 255 for i in range(4))
    def pointer(value):
        return tuple(('base-plus-byte', value, i) for i in range(4))
    def coordinate(word):
        if all(type(v) is int for v in word):
            return sum(v << (8*i) for i,v in enumerate(word))-f['arena_base']
        assert word == pointer(word[0][1])
        return word[0][1]
    def read(at, site):
        value = tuple(memory[at+i] for i in range(4))
        events.append((site, 'read32', at, value)); return value
    def write(at, value, site):
        put(memory, at, value); events.append((site, 'write32', at, value))
    sequences = [(l.wrapper, ret._wrapper(l.wrapper, l.callee, l.scheduler_point), 34),
                 (l.callee.address, state._encoded(l.callee.address, l.callee.allocator, l.callee.callback_thunk), 20)]
    for address, body, end in sequences:
        pc = 0
        while pc < end:
            op = int.from_bytes(body[pc:pc+2], 'little'); site = address+pc
            if op & 0xfe00 == 0xb400:
                numbers = [r for r in range(8) if op & (1 << r)]
                if op & 256:numbers.append(14)
                at = coordinate(regs[13])-4*len(numbers)
                for n,r in enumerate(numbers):write(at+4*n, regs[r], site)
                regs[13] = pointer(at)
            elif op & 0xff80 == 0xb080:
                regs[13] = pointer(coordinate(regs[13])-4*(op & 127))
            elif op & 0xff00 == 0x4600:
                regs[(op & 7) | ((op >> 4) & 8)] = regs[(op >> 3) & 15]
            elif op & 0xfe00 == 0x1c00:
                assert (op >> 6) & 7 == 0
                regs[op & 7] = regs[(op >> 3) & 7]
            elif op & 0xf800 in (0x0000, 0x0800):
                assert (op >> 6) & 31 == 16
                source = regs[(op >> 3) & 7]
                regs[op & 7] = (0, 0)+source[:2] if op & 0xf800 == 0 else source[2:]+(0, 0)
            elif op & 0xf800 == 0x4800:
                at = ((site+4) & ~3)+4*(op & 255)
                regs[(op >> 8) & 7] = tuple(body[at-address:at-address+4])
            elif op & 0xf800 == 0x6800:
                regs[op & 7] = read(coordinate(regs[(op >> 3) & 7])+4*((op >> 6) & 31), site)
            elif op & 0xf800 == 0x9000:
                write(coordinate(regs[13])+4*(op & 255), regs[(op >> 8) & 7], site)
            elif op & 0xf800 == 0x9800:
                regs[(op >> 8) & 7] = read(coordinate(regs[13])+4*(op & 255), site)
            elif op & 0xf800 == 0xf000:
                low = int.from_bytes(body[pc+2:pc+4], 'little'); assert low & 0xf800 == 0xf800
                offset = ((op & 2047) << 12) | ((low & 2047) << 1)
                if offset & (1 << 22):offset -= 1 << 23
                assert site+4+offset == l.callee.address
                regs[14] = constant((site+4) | 1); pc += 2
            else:
                raise AssertionError((hex(site), hex(op)))
            pc += 2
    return regs, memory, events


class EntryTests(unittest.TestCase):
    def test_independent_decoder_on_six_new_alias_and_size_states(self):
        for e,size in [(1200,0),(1400,65535),(1600,0x10001),(4112,0x87654321),(4120,7),(4140,19)]:
            with self.subTest(e=e,size=size):
                f=fixture(e,size); r=entry.derive(**f); regs,memory,events=raw(f)
                self.assertTrue(r['reaches_scheduler_count_prefix'])
                self.assertEqual(r['registers'],regs)
                changed=dict(f['cells']);changed.update({int(k):v for k,v in r['changed_cells'].items()})
                self.assertEqual(changed,memory)
                observed=[(v['site'],v['operation'],v['coordinate'],v['bytes'])for v in r['memory_events']if v['operation']in('read32','write32')]
                self.assertEqual(observed,events)

    def test_all_twelve_saved_words_match_return_consumer(self):
        f=fixture();r=entry.derive(**f); memory={int(k):v for k,v in r['changed_cells'].items()}
        for at,word in ret._saved(f['layout'],f['registers'],1024).items():
            self.assertEqual(tuple(memory[at+i]for i in range(4)),word)
        self.assertEqual(len(ret._saved(f['layout'],f['registers'],1024)),12)
        self.assertEqual(r['registers'][13],words._pointer(944))
        self.assertEqual(r['registers'][6],f['registers'][3])

    def test_prior_wrapper_save_changes_actual_fixed_point_read(self):
        f=fixture(4112);r=entry.derive(**f)
        self.assertEqual(r['observed_scheduler_word'],f['registers'][4])
        self.assertEqual(r['registers'][5],f['registers'][4])

    def test_parent_store_after_fixed_point_read_does_not_retroactively_change_it(self):
        f=fixture(4120);r=entry.derive(**f)
        self.assertEqual(r['observed_scheduler_word'],words._pointer(6144))
        self.assertEqual(tuple(r['changed_cells'][str(4096+i)]for i in range(4)),f['registers'][3])
        self.assertEqual(r['registers'][6],f['registers'][3])

    def test_later_scheduler_save_can_overwrite_fixed_point_bytes(self):
        f=fixture(4140);r=entry.derive(**f)
        self.assertEqual(r['observed_scheduler_word'],words._pointer(6144))
        self.assertEqual(tuple(r['changed_cells'][str(4096+i)]for i in range(4)),words._constant(0x5678))

    def test_missing_word_refuses_after_real_wrapper_saves(self):
        f=fixture();del f['cells'][4098];r=entry.derive(**f)
        self.assertFalse(r['reaches_scheduler_count_prefix']);self.assertEqual(len(r['changed_cells']),20)
        self.assertEqual(r['boundary']['site'],f['layout'].wrapper+20)

    def test_protected_parent_store_is_checked_after_pointer_read(self):
        f=fixture();f['protected_spans']=((1000,1004),);r=entry.derive(**f)
        self.assertFalse(r['reaches_scheduler_count_prefix']);self.assertEqual(len(r['changed_cells']),20)
        self.assertEqual(r['observed_scheduler_word'],words._pointer(6144))
        self.assertEqual(r['boundary']['site'],f['layout'].wrapper+22)

    def test_protected_first_save_refuses_without_claiming_all_saves(self):
        f=fixture();f['protected_spans']=((1008,1012),);r=entry.derive(**f)
        self.assertEqual(r['changed_cells'],{});self.assertFalse(r['all_saves_materialized'])

    def test_opaque_low_size_bytes_remain_opaque_and_high_bytes_are_discarded(self):
        f=fixture();f['registers'][1]=opaque('size');r=entry.derive(**f)
        self.assertEqual(r['registers'][4],f['registers'][1][:2]+(0,0))
        self.assertTrue(r['reaches_scheduler_count_prefix'])

    def test_entry_state_is_immutable(self):
        f=fixture();before=copy.deepcopy(f);entry.derive(**f);self.assertEqual(f,before)

    def test_explicit_types_complete_registers_and_retained_identity_required(self):
        for change in [{'selector':None},{'arena_base':True},{'registers':{}},
                       {'cells':{1:True}},{'protected_spans':[(0,4)]},
                       {'layout':replace(layout(),wrapper_sha256='0'*64)}]:
            f=fixture();f.update(change)
            with self.assertRaises(ValueError):entry.derive(**f)

    def test_scalar_unaligned_underflow_and_one_past_SP_refuse(self):
        cases=[words._constant(1024),words._pointer(1026),words._pointer(-BASE+76)]
        for sp in cases:
            f=fixture();f['registers'][13]=sp;r=entry.derive(**f)
            self.assertFalse(r['reaches_scheduler_count_prefix']);self.assertEqual(r['changed_cells'],{})
        f=fixture();f['arena_base']=2**32-1024;r=entry.derive(**f)
        self.assertFalse(r['reaches_scheduler_count_prefix']);self.assertEqual(r['changed_cells'],{})

    def test_numeric_base_changes_read_coordinate_and_execution_stays_unproved(self):
        f=fixture();f['arena_base']=0;r=entry.derive(**f)
        self.assertFalse(r['reaches_scheduler_count_prefix'])
        r=entry.derive(**fixture());self.assertEqual(r['stop_before'],layout().callee.address+20)
        for key in ['actual_reaching_state_proved','actual_code_execution_proved','physical_access_proved',
                    'allocation_or_initialization_proved','callback_effects_closed','source_or_ELF_admission','native_admission']:
            self.assertFalse(r[key])


if __name__ == '__main__':
    unittest.main()
