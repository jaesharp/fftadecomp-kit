"""Native saved control bits retain only the explicit ordinary ABI premise."""
import json
import struct
import unittest

from capstone.arm_const import ARM_REG_R0

import test_bios_cpuset_fill_profile as fixtures

bios, profile, match = fixtures.bios, fixtures.profile, fixtures.match
A = fixtures.A


class BiosSavedControlTests(fixtures.BiosCpuSetFillTests):
    def paired(self, register=6, middle=()):
        # Save r6 and LR, allocate one word, construct bit24 in the saved
        # control register, and supply two distinct aligned local sources.
        tokens = [0xB540, 0xB081, 0x2080 | (register << 8),
                  (17 << 6) | (register << 3) | register,
                  0x4668, 0x2100, 0x1C02 | (register << 3), 'bios',
                  *middle, 0xA800, 0x3002, 0x2100,
                  0x1C02 | (register << 3), 'bios',
                  0xB001, 0xBC40, 0xBC01, 0x4700]
        body, calls, bindings = bytearray(), {}, {}
        for token in tokens:
            if token == 'bios':
                site = A + len(body)
                calls[site] = bios.ADDRESS
                bindings[site] = bios.NAME
                body += fixtures.fixtures.fixtures.bl(site, bios.ADDRESS)
            else:
                body += struct.pack('<H', token)
        rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(body):08X}',
                     mode='thumb', instrs=len(tokens)),
                dict(rom=f'0x{bios.ADDRESS:08X}',
                     end=f'0x{bios.ADDRESS+4:08X}', mode='thumb', instrs=2)]
        mapping, index = fixtures.fixtures.fixtures.indexes(rows)
        rom = bytearray(0x143000)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        at = bios.ADDRESS-match.ROM_BASE
        rom[at:at+4] = bios.WRAPPER
        return dict(data=bytes(body), address=A, rom=bytes(rom),
                    mapping=mapping, index=index, calls=calls,
                    bindings=bindings, selector=profile.BIOS_SELECTOR)

    def test_saved_control_survives_both_calls_and_manifest_replay(self):
        f = self.paired()
        manifest, _ = profile.verify(**f)
        proof = manifest['native_buffers']['bios_fill']
        self.assertEqual([s[2] for s in proof['sites']], [2, 2])
        self.assertEqual(len(proof['sites']), 2)
        self.assertIn('r4-r11 survive calls', proof['contract'])
        self.assertEqual(profile.verify(**f, manifest=manifest)[0], manifest)

    def test_caller_saved_or_written_saved_control_is_not_retained(self):
        for register, middle in ((3, ()), (6, (0x2600,)), (6, (0x6836,))):
            with self.subTest(register=register, middle=middle), \
                    self.assertRaisesRegex(ValueError, 'bit24'):
                profile.verify(**self.paired(register=register, middle=middle))

    def test_join_intersects_saved_bits_and_unknown_width_stays_bounded(self):
        # Either branch reaches the second call; a possible zero write must
        # erase the fill fact at their join.
        with self.assertRaisesRegex(ValueError, 'bit24'):
            profile.verify(**self.paired(middle=(0x2B00, 0xD000, 0x2600)))
        f = self.paired()
        proof = bios.BiosFillProof(f['data'], A, f['rom'], f['mapping'],
                                  f['index'], f['calls'])
        site = max(f['calls'])
        self.assertEqual(proof.states[site][ARM_REG_R0+2], bios.exact(1 << 24))
        # The independent frame boundary still rejects a source crossing the
        # live allocation even when the control word is retained correctly.
        with self.assertRaises(ValueError):
            proof.check_call(site, {ARM_REG_R0:-2}, [(False, True, False)])


if __name__ == '__main__':
    unittest.main()
