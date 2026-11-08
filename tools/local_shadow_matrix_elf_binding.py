"""Original zero-addend memcpy/data identities for the closed matrix owner.

Identity transport only: this does not grant source admission, helper effects,
physical access, index bounds, or permission to change the original object.
"""
import hashlib
import json
import struct

import match
from local_rom_halfword_table_profile import COPY_SHA256, _indexed
from local_shadow_halfword_matrix import ROOT_WORDS, require


def binding_plan(raw, address, rom, mapping, index, objects):
    plan=image_binding_plan(match.elf_image(raw),address,rom,mapping,index,objects)
    plan['original_sha256']=hashlib.sha256(raw).hexdigest()
    return plan


def image_binding_plan(image, address, rom, mapping, index, objects):
    require(image['type']==1 and address%4==0, 'original relocatable aligned owner required')
    match.allocated_text_only(image)
    symbol,offset=match.function_record(image,f'func_{address:08X}',address,True)
    require(offset==0 and symbol['size']==96 and len(image['text'])==96 and not any(
        item['type']==2 and item is not symbol and item['section'] or
        item['type']==1 and item['section'] or item['name'].startswith('$a')
        for item in image['symbols']), 'sole complete96-byte Thumb function required')
    actual=rom[address-match.ROM_BASE:address-match.ROM_BASE+96]
    _indexed(actual,address,45,rom,mapping,index)
    require(all(struct.unpack_from('<H',actual,p)[0]==value and
                struct.unpack_from('<H',image['text'],p)[0]==value
                for p,value in ROOT_WORDS.items()), 'actual and original matrix instructions differ')
    decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
    call=next(decoder.disasm(actual[66:70],address+66),None)
    require(call is not None and call.id==match.ARM_INS_BL and call.size==4,
            'actual complete direct copy BL required')
    helper=call.operands[0].imm
    helper_body=rom[helper-match.ROM_BASE:helper-match.ROM_BASE+98]
    _indexed(helper_body,helper,49,rom,mapping,index)
    require(hashlib.sha256(helper_body).hexdigest()==COPY_SHA256, 'actual copy helper identity differs')
    shadow=struct.unpack_from('<I',actual,92)[0]
    names=match.parse_data_symbols(objects)
    identities=[name for name,value in names.items() if value==shadow]
    require(len(identities)==1, 'unique canonical current data identity required')
    expected={66:(10,'memcpy',2,helper|1),92:(2,identities[0],1,shadow)}
    seen=set();targets={}
    for section_index in image['relocations']:
        section=image['sections'][section_index]
        require(section[1]==9 and section[7]==image['text_index'] and section[9]==8 and section[5]%8==0,
                'canonical original text REL records required')
        symbols=image['symbol_tables'].get(section[6])
        for position in range(0,section[5],8):
            site,info=struct.unpack_from('<II',image['section_data'][section_index],position)
            require(site in expected and site not in seen and symbols is not None and info>>8<len(symbols),
                    'exact unique original relocation sites required')
            kind,name,typed,point=expected[site];target=symbols[info>>8]
            require(info&255==kind and target['name']==name and target['section']==0 and
                    target['value']==0 and target['bind']==1 and target['type'] in (0,typed) and
                    sum(item['name']==name for item in image['symbols'])==1,
                    'genuine unique undefined global identity and original type required')
            if kind==10:
                instruction=next(decoder.disasm(image['text'][site:site+4],address+site),None)
                require(instruction is not None and instruction.id==match.ARM_INS_BL and
                        instruction.size==4 and instruction.operands[0].imm==address+site,
                        'original compiler memcpy BL must have zero addend')
            else:
                require(struct.unpack_from('<I',image['text'],site)[0]==0,
                        'original data literal must have zero addend')
            targets[name]=(point,typed);seen.add(site)
    require(seen==set(expected) and not any(item['name'] and not item['section'] and
        item['name'] not in targets for item in image['symbols']), 'complete original relocation inventory required')
    return dict(bindings=dict(calls=[[66,'memcpy']],data=[[92,identities[0],0]],functions=[],switches=[]),
        targets=targets,
        actual_helper=helper,source_or_native_admission=False,physical_access_granted=False)
