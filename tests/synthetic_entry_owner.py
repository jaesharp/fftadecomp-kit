"""Synthetic Thumb owners, never copied from a game ROM."""
import json
import struct
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

ADDRESS = 0x08080000
HELPER = 0x08090000

def bl(site, target):
    delta = target - site - 4
    assert delta % 2 == 0 and -(1 << 22) <= delta < (1 << 22)
    delta &= 0x7fffff
    return struct.pack('<HH', 0xf000 | (delta >> 12), 0xf800 | ((delta >> 1) & 0x7ff))

def body():
    return (bytes.fromhex('10b5002805d0041c') + bl(ADDRESS+8, ADDRESS) +
            bytes.fromhex('201c') + bl(ADDRESS+14, HELPER) + bytes.fromhex('10bc01bc0047'))

def snapshots(data):
    return (json.dumps([{'rom':f'0x{ADDRESS:08X}', 'end':f'0x{ADDRESS+len(data):08X}', 'mode':'thumb'},
                        {'rom':f'0x{HELPER:08X}', 'end':f'0x{HELPER+2:08X}', 'mode':'thumb'}]).encode(),
            f'{ADDRESS:08X} {ADDRESS+len(data):08X} {len(data)} 10 bx\n{HELPER:08X} {HELPER+2:08X} 2 1 bx\n'.encode())

def frame_fixture():
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB); decoder.detail = True
    instructions = {i.address:i for i in decoder.disasm(body(), ADDRESS)}
    edges = {site:(site+i.size,) for site,i in instructions.items()}
    edges[ADDRESS+4] = (ADDRESS+18, ADDRESS+6)
    edges[ADDRESS+22] = ()
    calls = {ADDRESS+8:ADDRESS, ADDRESS+14:HELPER}
    return instructions, edges, calls
