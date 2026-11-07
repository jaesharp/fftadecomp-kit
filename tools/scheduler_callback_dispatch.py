"""Exhaustive conditional dispatch for a possibly opaque descriptor phase.

The observed halfword is a post-save machine read, not an initialized C scalar.
Named phase continuations remain cutpoints. Only the two default returns close.
"""
from dataclasses import dataclass
import hashlib

from descriptor_partial_word_prerequisite import Word
from scheduler_callback_zero_phase import DISPATCH, RETURN

SELECTOR = 'conditional-scheduler-opaque-phase-dispatch-v1'
PATHS = {
    'phase0': (0, 56, tuple(range(0, 28, 2))),
    'phase1': (1, 152, tuple(range(0, 32, 2))),
    'phase256': (256, 158, tuple(range(0, 20, 2))),
    'phase257': (257, 512, tuple(range(0, 24, 2)) + (34, 36, 38, 40)),
    'phase258': (258, 584, tuple(range(0, 24, 2)) + (34, 36, 38, 42, 44, 46, 48)),
    'default2to255': (None, 648, tuple(range(0, 34, 2))),
    'default259to65535': (None, 648, tuple(range(0, 24, 2)) + (34, 36, 38, 42, 44, 46, 50)),
}


@dataclass(frozen=True)
class Binding:
    address: int
    body: bytes
    sha256: str


def _validate(binding):
    if type(binding) is not Binding or type(binding.address) is not int or \
            binding.address % 4 or not 0 <= binding.address <= 2**32-658 or \
            type(binding.body) is not bytes or len(binding.body) != 658 or \
            binding.body[:52] != DISPATCH or binding.body[52:56] != b'\x01\x01\0\0' or \
            binding.body[648:] != RETURN or \
            binding.sha256 != hashlib.sha256(binding.body).hexdigest():
        raise ValueError('complete callback identity, dispatch literal and return required')


def bind(body, address, *, selector):
    if type(selector) is not str or selector != SELECTOR or type(body) is not bytes:
        raise ValueError('explicit complete callback dispatch selector required')
    binding = Binding(address, body, hashlib.sha256(body).hexdigest())
    _validate(binding)
    return binding


def derive(binding, phase_word, registers, *, entry_sp, selector):
    """Partition all possible observed low-halfword bits without initializing them."""
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit conditional dispatch selector required')
    _validate(binding)
    if type(phase_word) is not Word or any(a[0] not in ('constant', 'unproved') for a in phase_word.bytes[:2]):
        raise ValueError('observed phase requires concrete or opaque machine-byte facts')
    if type(registers) is not dict or set(registers) != set(range(13)) | {14} or \
            any(type(v) is not Word for v in registers.values()):
        raise ValueError('all incoming register origins required')
    if type(entry_sp) is not int or entry_sp % 4 or not -768 <= entry_sp <= 0:
        raise ValueError('aligned bounded relative entry SP required')
    atoms = phase_word.bytes[:2]
    def compatible(value):
        return all(atom[0] == 'unproved' or atom[1] == (value >> (8*i)) & 255
                   for i, atom in enumerate(atoms))
    total = 1
    for atom in atoms:
        if atom[0] == 'unproved': total *= 256
    counts = {name: int(compatible(value)) for name, (value, _, _) in PATHS.items() if value is not None}
    counts['default2to255'] = sum(compatible(value) for value in range(2, 256))
    counts['default259to65535'] = total - sum(counts.values())
    assert sum(counts.values()) == total and min(counts.values()) >= 0
    c = binding.address
    cases = []
    for name, (value, destination, trace) in PATHS.items():
        if not counts[name]: continue
        events = [dict(site=c, operation='write', role='stack', offset=entry_sp-20+4*i,
                       bytes=4, value=list(registers[r].bytes))
                  for i, r in enumerate((4, 5, 6, 7, 14))]
        events.append(dict(site=c+10, operation='read', role='descriptor', offset=0,
                           bytes=2, observed_atoms=list(atoms), observed_after_saves=True))
        high = name in ('phase257', 'phase258', 'default259to65535')
        if high:
            events.append(dict(site=c+34, operation='read', role='ROM', offset=c+52, bytes=4, value=257))
        default = value is None
        if default:
            for i, r in enumerate((4, 5, 6, 7, 14)):
                events.append(dict(site=c+(654 if r == 14 else 652), operation='read', role='stack',
                                   offset=entry_sp-20+4*i, bytes=4, value=list(registers[r].bytes)))
        working = {str(r): list(w.bytes) for r, w in registers.items()}
        working.update({'0': list(Word.constant(258 if name in ('phase258', 'default259to65535') else
                                               257 if name == 'phase257' else 256).bytes),
                        '1': ['zero-extended-observed-u16', list(atoms)],
                        '5': list(registers[2].bytes), '6': list(registers[0].bytes), '7': list(registers[1].bytes)})
        cases.append(dict(case=name, guard=dict(equals=value) if value is not None else
                          dict(inclusive_range=[2, 255] if name == 'default2to255' else [259, 65535]),
                          compatible_phase_values=counts[name], trace=[c+o for o in trace] +
                          ([c+o for o in range(648, 658, 2)] if default else []),
                          stop_before=None if default else c+destination,
                          working_register_origins=working, ordered_accesses=events,
                          body_SP=entry_sp-36, return_SP=entry_sp if default else None,
                          conditional_result=0 if default else None,
                          conditional_preserved_origins={str(r): list(registers[r].bytes) for r in range(4, 13)}
                          if default else None,
                          conditional_return_target=list(registers[14].bytes) if default else None,
                          calls_executed=[], phase_body_effects_closed=False))
    return dict(schema=SELECTOR, callback=dict(address=c, bytes=658, sha256=binding.sha256),
                observed_phase_atoms=list(atoms), possible_phase_values=total,
                cases=cases, phase_partition_exhaustive=True, phase_partition_disjoint=True,
                incoming_phase_initialization_proved=False, observed_phase_value_proved=False,
                actual_reaching_state_proved=False, whole_callback_CFG_closed=False,
                physical_permissions_proved=False, role_separation_proved=False,
                allocation_proved=False, nonescape_proved=False, source_or_ELF_admission=False,
                native_admission=False, obligations=[dict(id=name, proved=False, scope=text) for name, text in (
                    ('observed-phase', 'The supplied atoms equal the actual descriptor halfword read after the callback saves; no incoming-byte initialization follows.'),
                    ('byte-identity', 'Complete callback bytes and literal remain the bound values, including against private-save or ambient aliases.'),
                    ('access', 'Listed stack, descriptor and literal reads/writes are physically permitted, aligned, little-endian and nonwrapping.'),
                    ('frame', 'The36-byte private frame is live, its saved words survive, and incoming LR is a valid Thumb continuation.'),
                    ('interference', 'No asynchronous writer changes the required code, phase observation or saved words.'),
                    ('continuations', 'Named phase bodies are not executed by this relation and retain all field, nested-call, lifetime and return obligations.'),
                )])
