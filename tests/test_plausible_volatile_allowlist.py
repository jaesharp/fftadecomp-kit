import json
import sys
import tempfile
from pathlib import Path
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import plausible


SYMBOL = "g_control_flags_03000940"
HEADER = "include/control_flags.h"
ENTRY = {"symbol": SYMBOL, "address": "0x03000940", "header": HEADER,
         "member_types": ["u8"], "evidence": "#90", "reason": "test"}
MAPPING = {SYMBOL: "0x03000940"}
DECLARATION = ("extern struct {\n    u16 display;\n    u8 unknown_02[0x3A];\n"
               "    volatile u8 unknown_3C : 8;\n    volatile u8 unknown_3D;\n"
               "} " + SYMBOL + ";\n")
RECORD = (f"* allowlisted volatile: `{SYMBOL}` at `0x03000940` declared in `{HEADER}`")


class VolatileAllowlistTests(unittest.TestCase):
    def rules(self, source, relpath=HEADER, mapping=MAPPING, entries=(ENTRY,)):
        return [rule for _, rule, _, _ in plausible.check_text(
            source, data_symbols=mapping, relpath=relpath, volatile_allow=list(entries))]

    def test_listed_header_declaration_is_exempt(self):
        self.assertEqual(self.rules("/* volatile: #90 */\n" + DECLARATION), [])
        self.assertEqual(self.rules(DECLARATION.replace("u16 display;", "u8 *cursor;")), [])

    def test_shipped_allow_list_holds_only_the_issue_entry(self):
        entries = plausible.volatile_allow_entries()
        self.assertEqual([(e["symbol"], e["address"], e["header"], e["member_types"])
                          for e in entries], [(SYMBOL, "0x03000940", HEADER, ["u8"])])

    def test_wrong_or_missing_address_binding_is_rejected(self):
        for mapping in ({}, {SYMBOL: "0x03000944"}, {SYMBOL: "invalid"}, {"other": "0x03000940"}):
            with self.subTest(mapping=mapping):
                self.assertIn("volatile", self.rules(DECLARATION, mapping=mapping))
        moved = dict(ENTRY, address="0x03000944")
        self.assertIn("volatile", self.rules(DECLARATION, entries=(moved,)))
        self.assertIn("volatile", self.rules(DECLARATION, entries=()))
        for broken in (dict(ENTRY, member_types=[]), dict(ENTRY, symbol="a b"),
                       {k: v for k, v in ENTRY.items() if k != "header"}):
            with self.subTest(entry=broken):
                self.assertIn("volatile", self.rules(DECLARATION, entries=(broken,)))

    def test_only_the_listed_header_path_is_exempt(self):
        for relpath in (None, "src/08028C34.c", "include/other.h", "src/control_flags.h",
                        "include/sub/control_flags.h"):
            with self.subTest(relpath=relpath):
                self.assertIn("volatile", self.rules(DECLARATION, relpath=relpath))
        self.assertIn("volatile-allowlist", self.rules(
            "#define FLAGS " + SYMBOL + "\n", relpath="include/other.h"))

    def test_volatile_elsewhere_in_the_header_is_rejected(self):
        for extra in ("extern volatile u8 other;", "volatile int local;",
                      "#define V volatile", "*(volatile u8 *)0x03000941 = 0;"):
            with self.subTest(extra=extra):
                self.assertIn("volatile", self.rules(DECLARATION + extra + "\n"))

    def test_qualifier_must_start_a_listed_scalar_member(self):
        for member in ("volatile u16 unknown_3D;", "volatile u8 *unknown_3D;",
                       "volatile u8 unknown_3D[2];", "u8 volatile unknown_3D;",
                       "u8 * volatile unknown_3D;", "volatile unknown_3D;",
                       "volatile u8 unknown_3D, unknown_3E;"):
            with self.subTest(member=member):
                self.assertIn("volatile", self.rules(
                    DECLARATION.replace("volatile u8 unknown_3D;", member)))

    def test_declaration_shape_is_exact(self):
        for source in (DECLARATION.replace("extern struct {", "extern volatile struct {"),
                       DECLARATION.replace("extern struct {", "extern struct Tag {"),
                       DECLARATION.replace("extern struct {", "struct {"),
                       DECLARATION.replace("extern struct {", "typedef struct {")):
            with self.subTest(source=source):
                self.assertIn("volatile", self.rules(source))
        for source in (DECLARATION + DECLARATION,
                       DECLARATION + "#define FLAGS " + SYMBOL + "\n",
                       DECLARATION.replace("u16 display;", "struct Inner { u8 a; } inner;"),
                       DECLARATION.replace("u16 display;", "u8 unknown_00[N];"),
                       DECLARATION.replace("u16 display;", "void (*callback)(void);"),
                       DECLARATION.replace("u16 display;", "u16 display __attribute__((packed));"),
                       DECLARATION.replace("u16 display;", "u16 display;\\\n")):
            with self.subTest(source=source):
                findings = self.rules(source)
                self.assertTrue("volatile" in findings or "volatile-allowlist" in findings)

    def test_typeof_is_refused_while_an_entry_is_active(self):
        for relpath in (HEADER, "src/08028C34.c", "include/other.h"):
            for spelling in ("typeof", "__typeof", "__typeof__"):
                with self.subTest(relpath=relpath, spelling=spelling):
                    source = spelling + "(" + SYMBOL + ".unknown_3C) local;\n"
                    if relpath == HEADER:
                        source = DECLARATION + source
                    self.assertIn("volatile-allowlist", self.rules(source, relpath=relpath))
        self.assertEqual(self.rules("__typeof__(x) y;", relpath="src/a.c", mapping={}), [])

    def test_source_files_never_qualify(self):
        source = DECLARATION + "void f(void) { " + SYMBOL + ".unknown_3C = 1; }\n"
        self.assertIn("volatile", self.rules(source, relpath="src/08028C34.c"))
        self.assertEqual(self.rules("void f(void) { " + SYMBOL + ".unknown_3C = 1; }\n",
                                    relpath="src/08028C34.c"), [])

    def test_file_paths_bind_to_the_project_root_or_a_replay_capture(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "config").mkdir()
            (root / "config" / "data_symbols.json").write_text(json.dumps(MAPPING))

            def rules(relative):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(DECLARATION)
                return [rule for _, rule, _, _ in plausible.check_file(path)]

            self.assertEqual(rules(HEADER), [])
            self.assertEqual(rules("build/ffta_replay_x/" + HEADER), [])
            for relative in ("src/control_flags.h", "include/sub/control_flags.h",
                             "build/" + HEADER, "build/x/src/control_flags.h",
                             "other/" + HEADER):
                with self.subTest(relative=relative):
                    self.assertIn("volatile", rules(relative))
            (root / "config" / "data_symbols.json").write_text(json.dumps({SYMBOL: "0x03000944"}))
            self.assertIn("volatile", rules(HEADER))

    def test_report_records_only_real_uses(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "config").mkdir()
            (root / "src").mkdir()
            (root / "config" / "data_symbols.json").write_text(json.dumps(MAPPING))
            source = root / "src" / "08028C34.c"

            def uses(text, entries=(ENTRY,)):
                source.write_text(text)
                return plausible.allowlisted_volatile_uses(root, 0x08028C34, list(entries))

            access = "void f(void) { " + SYMBOL + ".unknown_3C = 1; }\n"
            self.assertEqual(uses('#include "control_flags.h"\n' + access), [RECORD])
            self.assertEqual(uses("/* " + SYMBOL + " */ void f(void) {}\n"), [])
            self.assertEqual(uses("extern u16 " + SYMBOL + ";\n" + access), [])
            self.assertEqual(uses("extern struct { u8 a; } " + SYMBOL + ";\n" + access), [])
            self.assertEqual(uses(access, entries=()), [])
            (root / "config" / "data_symbols.json").write_text(json.dumps({SYMBOL: "0x03000944"}))
            self.assertEqual(uses(access), [])


if __name__ == "__main__":
    unittest.main()
