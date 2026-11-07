"""One conditional callback phase and its actual nested early-return path.

Only the selected paths are closed. Complete body hashes bind untouched bytes;
neither hash nor the path relation admits the complete owner or actual memory.
The phase word, permissions, role separation and stable saved words are premises.
"""
from dataclasses import dataclass
import hashlib

from descriptor_partial_word_prerequisite import Word

SELECTOR = 'conditional-scheduler-zero-phase-early-return-v1'
DISPATCH = bytes.fromhex(
    'f0b5 84b0 061c 0f1c 151c 3988 8020 4000 8142 44d0 8142 04dc '
    '0029 0dd0 0129 3bd0 32e1 0448 8142 00d1 eae0 0130 8142 00d1 0ae1 29e1')
PHASE = bytes.fromhex('e970 2971 0123 1420 395e 9e29 02d1 eb70 0723 07e0')
COPY_FIELDS = bytes.fromhex('e878 0228 06d0 f88a a870 7868 e860 03e0')
CALL_SETUP = bytes.fromhex('0524 a878 0028 00d0 0024 e868 0449 0022 0092 0196 221c')
RETURN = bytes.fromhex('0020 04b0 f0bc 02bc 0847')
HELPER_GATE = bytes.fromhex(
    'f0b5 8db0 061c 0c1c 129d 1206 120e 1b06 1b0e 002a 03d1 072b 01d1 0020 77e0')
HELPER_RETURN = bytes.fromhex('0db0 f0bc 02bc 0847')
CALLBACK_PATH = tuple(range(0,28,2)) + tuple(range(56,76,2)) + tuple(range(92,108,2)) + tuple(range(116,140,2)) + (142,144) + tuple(range(648,658,2))
HELPER_PATH = tuple(range(0,30,2)) + tuple(range(270,278,2))


def _branch(data, base, offset):
    raw = int.from_bytes(data[offset:offset+2], 'little')
    if raw & 0xf800 != 0xe000:
        raise ValueError('selected branch must be direct unconditional Thumb B')
    displacement = raw & 2047
    if displacement & 1024: displacement -= 2048
    return base + offset + 4 + 2*displacement


def _call(data, base, offset):
    hi = int.from_bytes(data[offset:offset+2], 'little')
    lo = int.from_bytes(data[offset+2:offset+4], 'little')
    if hi & 0xf800 != 0xf000 or lo & 0xf800 != 0xf800:
        raise ValueError('selected nested call must be complete Thumb BL')
    displacement = ((hi & 2047) << 12) | ((lo & 2047) << 1)
    if displacement & (1 << 22): displacement -= 1 << 23
    return base + offset + 4 + displacement


@dataclass(frozen=True)
class Binding:
    callback: int
    helper: int
    callback_sha: str
    helper_sha: str
    literal: int


def bind(callback, address, helper, helper_address, *, selector):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('explicit callback zero-phase selector required')
    if type(callback) is not bytes or len(callback) != 658 or type(helper) is not bytes or len(helper) != 292:
        raise ValueError('complete callback and helper bodies required')
    if any(type(a) is not int or a % 4 or not 0 <= a < a+n <= 0x100000000
           for a,n in ((address,len(callback)),(helper_address,len(helper)))):
        raise ValueError('aligned nonwrapping complete Thumb spans required')
    if max(address,helper_address) < min(address+len(callback),helper_address+len(helper)):
        raise ValueError('complete callback and helper spans overlap')
    if callback[:52] != DISPATCH or callback[56:76] != PHASE or callback[92:108] != COPY_FIELDS or \
            callback[116:138] != CALL_SETUP or callback[142:144] != bytes.fromhex('6863') or \
            callback[648:] != RETURN or helper[:30] != HELPER_GATE or helper[270:278] != HELPER_RETURN:
        raise ValueError('selected callback/helper instruction path differs')
    if _call(callback,address,138) != helper_address or _branch(callback,address,144) != address+648 or \
            _branch(helper,helper_address,28) != helper_address+270:
        raise ValueError('selected call or return branch target differs')
    # LDR R1 at +128 references the complete aligned word at +148.
    if ((address+128+4)&~3)+16 != address+148:
        raise ValueError('selected literal ownership differs')
    literal = int.from_bytes(callback[148:152], 'little')
    return Binding(address,helper_address,hashlib.sha256(callback).hexdigest(),hashlib.sha256(helper).hexdigest(),literal)


def derive(binding, phase, tag, option, descriptor_word, registers, *, entry_sp, selector):
    """Conditional relation for phase0/tag158 and nonzero truncated option.

Role-addressed effects require actual separation from the descriptor and every
saved span. They are not silently inferred from the role names below. Unknown
descriptor bytes remain unknown when copied into allocation storage.
"""
    if type(selector) is not str or selector != SELECTOR or type(binding) is not Binding:
        raise ValueError('explicit bound callback relation required')
    if type(phase) is not int or phase != 0 or type(tag) is not int or tag != 158 or \
            type(option) is not int or not 0 <= option <= 65535 or not option & 255:
        raise ValueError('selected path requires phase0, signed tag158 and nonzero option low byte')
    expected = set(range(13)) | {14}
    if type(registers) is not dict or set(registers) != expected or \
            any(type(w) is not Word for w in registers.values()) or type(descriptor_word) is not Word:
        raise ValueError('all incoming register origins and descriptor word must be explicit immutable Words')
    if type(entry_sp) is not int or entry_sp % 4 or not -768 <= entry_sp <= 0:
        raise ValueError('bounded aligned relative entry SP required')
    c,h = binding.callback,binding.helper
    events = []
    def event(site,operation,role,offset,width,value):
        events.append(dict(site=site,operation=operation,address=[role,offset],bytes=width,value=value))
    # Ordinary local stack operations are separate from external role accesses.
    for index,reg in enumerate((4,5,6,7,14)):
        event(c,'write','stack',entry_sp-20+4*index,4,list(registers[reg].bytes))
    event(c+10,'read','descriptor',0,2,phase)
    event(c+56,'write','payload',3,1,0);event(c+58,'write','payload',4,1,0)
    event(c+64,'read-signed','descriptor',20,2,tag)
    event(c+70,'write','payload',3,1,1)
    event(c+92,'read','payload',3,1,1)
    event(c+98,'read','descriptor',22,2,option)
    event(c+100,'write','payload',2,1,option & 255)
    event(c+102,'read','descriptor',4,4,list(descriptor_word.bytes))
    event(c+104,'write','payload',12,4,list(descriptor_word.bytes))
    event(c+118,'read','payload',2,1,option & 255)
    event(c+126,'read','payload',12,4,list(descriptor_word.bytes))
    event(c+128,'read','ROM-literal',c+148,4,binding.literal)
    callback_sp=entry_sp-36
    event(c+132,'write','stack',callback_sp,4,list(Word.constant(0).bytes))
    event(c+134,'write','stack',callback_sp+4,4,list(registers[0].bytes))
    helper_entry = {0:descriptor_word,1:Word.constant(binding.literal),2:Word.constant(0),3:Word.constant(7),
                    4:Word.constant(0),5:registers[2],6:registers[0],7:registers[1],
                    **{r:registers[r] for r in range(8,13)},14:Word.constant((c+142)|1)}
    for index,reg in enumerate((4,5,6,7,14)):
        event(h,'write','stack',callback_sp-20+4*index,4,list(helper_entry[reg].bytes))
    # SUB SP,52 makes LDR [SP,72] read the actual incoming first stack word.
    event(h+8,'read','stack',callback_sp,4,list(Word.constant(0).bytes))
    for index,reg in enumerate((4,5,6,7,14)):
        event(h+(272 if reg != 14 else 274),'read','stack',callback_sp-20+4*index,4,list(helper_entry[reg].bytes))
    event(c+142,'write','payload',52,4,list(Word.constant(0).bytes))
    for index,reg in enumerate((4,5,6,7,14)):
        event(c+(652 if reg != 14 else 654),'read','stack',entry_sp-20+4*index,4,list(registers[reg].bytes))
    conditions = [
        ('actual-reaching-state','Actual callback reaches entry with phase0, descriptor signed+20=158, unsigned+22=option, and listed +4 bytes. The retained caller initializes no phase0 word.'),
        ('complete-byte-identity','Complete indexed owner spans, selected code and literal retain the bound bytes on this machine throughout execution.'),
        ('physical-access','Every listed descriptor, payload, stack and literal access is permitted, aligned where required, little-endian, nonwrapping ordinary memory.'),
        ('role-separation','All payload writes are disjoint from descriptor, code, executing saves and protected caller/source state. Role names establish no physical separation.'),
        ('saved-frame','The complete callback36-byte and nested helper72-byte private frames are live and do not overwrite incoming protected/source state; all saved words retain origins.'),
        ('stable-memory','No interrupt, asynchronous writer or external alias changes any required read equality or executing code.'),
        ('return-continuation','Incoming callback LR is a valid Thumb continuation. The nested helper returns through its actually saved BL continuation.'),
        ('ambient-aliases','Unknown descriptor and ambient register words may still encode original/copy/expired pointers. No nonescape or future-use conclusion follows.')]
    return dict(schema=SELECTOR,callback=dict(address=c,bytes=658,sha256=binding.callback_sha),
        helper=dict(address=h,bytes=292,sha256=binding.helper_sha),
        conditional_inputs=dict(phase=phase,signed_tag=tag,option=option,descriptor_word=list(descriptor_word.bytes)),
        selected_callback_trace=[c+o for o in CALLBACK_PATH],selected_helper_trace=[h+o for o in HELPER_PATH],
        helper_entry_registers={str(r):list(w.bytes) for r,w in sorted(helper_entry.items())},
        helper_stack_arguments=[list(Word.constant(0).bytes),list(registers[0].bytes)],
        frame=dict(entry_SP=entry_sp,callback_body_SP=callback_sp,deepest_SP=callback_sp-72,return_SP=entry_sp),
        ordered_accesses=events,helper_conditional_result=0,callback_conditional_result=0,
        preserved_registers=list(range(4,13)),conditional_preserved_origins={str(r):list(registers[r].bytes)for r in range(4,13)},
        conditional_return_target=list(registers[14].bytes),
        only_nested_call=dict(site=c+138,target=h,entry_R2=0,entry_R3=7,early_result=0),
        helper_external_calls_on_selected_path=[],
        obligations=[dict(id=name,proved=False,scope=scope)for name,scope in conditions],
        whole_callback_CFG_closed=False,actual_reaching_state_proved=False,actual_phase_zero_proved=False,
        physical_permissions_proved=False,role_separation_proved=False,nonescape_proved=False,
        source_initialization_proved=False,unconditional_termination=False,source_or_ELF_admission=False,native_admission=False)
