"""Portable synthetic three-call owner constructors, with no game-data fixtures."""
import json
import struct

import match
import owner_admission_profile as owner
import owner_graph_profile as graph

A = 0x08010000
T0, T1, T2, CHILD = (A + offset for offset in (0x300, 0x400, 0x500, 0x600))
OBJECTS = b'{"data_02000000":"0x02000000"}'


def words(*values):
    return struct.pack('<' + 'H' * len(values), *values)


def bl(site, target):
    delta = target - site - 4
    return words(0xF000 | ((delta >> 12) & 0x7ff), 0xF800 | ((delta >> 1) & 0x7ff))


def assemble(sequence):
    labels, site = {}, A
    for item in sequence:
        if isinstance(item, str): labels[item[:-1]] = site
        else: site += 2
    output, site = bytearray(), A
    for item in sequence:
        if isinstance(item, str): continue
        if isinstance(item, tuple):
            name, label = item
            item = {'bls': 0xd900, 'beq': 0xd000, 'b': 0xe000}[name] | (
                (labels[label] - site - 4) // 2 & (2047 if name == 'b' else 255))
        output += words(item)
        site += 2
    return bytes(output)


def fixture(*, missing_init=False, bad_consumer=False, extra_call=False, role_swap=False):
    from three_call_composition_profile import ThreeCallCompositionProof, SELECTOR
    # Fixed 56B local frame; four words, four halfwords, pointer SP44, scalar SP52.
    sequence = [0xb5b0, 0xb08e, 0x4669, 0x3120, 0x910b, 0x2100,
        0x2500, 'words:', 0x00ac, 0x466b, 0x191a,
        0x2000 if missing_init else 0x6010,
        0x1c68, 0x0600, 0x0e05, 0x2d03, ('bls', 'words'),
        0xab00, 0x6818, 0x2200, 0x2300,
        0x2500, 'halves:', 0x0069, 0x980b, 0x1841, 0x2007, 0x8008,
        0x1c68, 0x0600, 0x0e05, 0x2d03, ('bls', 'halves'),
        0x2002, 0x900d, 0x2200, 0x2300, 0xa908]
    body = assemble(sequence)
    first = A + len(body)
    body += bl(first, T0) + words(0x2100, 0x466a)
    second = A + len(body)
    body += bl(second, T1)
    body += words(0x1c10, 0x2200) if bad_consumer else words(0x2200)
    body += words(0x9a0b, 0x2300, 0x5ed1)
    third = A + len(body)
    body += bl(third, T2) + words(0x2200)
    if extra_call:
        body += words(0x466a)
        body += bl(A + len(body), T0) + words(0x2200)
    body += words(0x9b0b, 0x8818, 0x2300, 0x990d, 0x2200,
                  0xb00e, 0xbcb0, 0xbc02, 0x4708)
    leaf0 = words(0x0600, 0x4903, 0x0dc0, 0x3040, 0x1840,
                  0x2100, 0x5e40, 0x4770) + struct.pack('<I', 0x02000000)
    leaf1 = words(0x4801, 0x2100, 0x5e40, 0x4770) + struct.pack('<I', 0x02000000)
    ordinary = words(0xb510, 0x0409, 0x1c03, 0x1c1a, 0x7011)
    ordinary += bl(T2 + len(ordinary), CHILD) + words(0xbc10, 0xbc01, 0x4700)
    bodies = [(A, body), (T0, leaf0), (T1, leaf1), (T2, ordinary), (CHILD, words(0x4770))]
    rows = [{'rom': f'0x{address:08X}', 'end': f'0x{address+len(data):08X}',
             'mode': 'thumb'} for address, data in bodies]
    mapping = json.dumps(rows).encode()
    for row, (address, data) in zip(rows, bodies):
        row['instrs'] = owner.refine(data, address, mapping)['instrs']
    mapping = json.dumps(rows).encode()
    index = ''.join(f"{int(r['rom'],16):08X} {int(r['end'],16):08X} "
        f"{int(r['end'],16)-int(r['rom'],16)} {r['instrs']} return\n" for r in rows).encode()
    rom = bytearray(CHILD - match.ROM_BASE + 2)
    for address, data in bodies: rom[address-match.ROM_BASE:address-match.ROM_BASE+len(data)] = data
    ins, edges, branches, calls, _ = graph.graph(body, A, owner.refine(body, A, mapping))
    sites = {'leaf_overwrite': [first, T0], 'consumer_scratch': [second, T1],
             'ordinary_overwrite': [third, T2]}
    if role_swap:
        sites['leaf_overwrite'], sites['consumer_scratch'] = sites['consumer_scratch'], sites['leaf_overwrite']
    proof = ThreeCallCompositionProof(bytes(rom), mapping, index, OBJECTS,
                                     A, len(body), calls, sites, policy=SELECTOR)
    return proof, ins, edges, branches, calls
