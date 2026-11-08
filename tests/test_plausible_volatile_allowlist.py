import hashlib
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
DECLARATION = ("extern struct {\n    u16 display;\n    u8 unknown_02[0x3A];\n"
               "    volatile u8 unknown_3C : 8;\n    volatile u8 unknown_3D : 8;\n"
               "} " + SYMBOL + ";\n")
ENTRY = {"symbol": SYMBOL, "address": "0x03000940", "header": HEADER,
         "member_types": ["u8"], "declaration": " ".join(DECLARATION.split()),
         "evidence": "#90", "reason": "test"}
MAPPING = {SYMBOL: "0x03000940"}
ACCESS = "void f(void) { " + SYMBOL + ".unknown_3C = 1; }\n"


def pinned(source):
    """an entry pinning the declaration in source, to exercise the shape rules"""
    start = source.index("extern")
    return dict(ENTRY, declaration=source[start:source.index(";", source.index(SYMBOL)) + 1])


class VolatileAllowlistTests(unittest.TestCase):
    def rules(self, source, relpath=HEADER, mapping=MAPPING, entries=(ENTRY,)):
        return [rule for _, rule, _, _ in plausible.check_text(
            source, data_symbols=mapping, relpath=relpath, volatile_allow=list(entries))]

    def refused(self, findings):
        self.assertTrue("volatile" in findings or "volatile-allowlist" in findings, findings)

    def test_listed_header_declaration_is_exempt(self):
        self.assertEqual(self.rules("/* volatile: #90 */\n" + DECLARATION), [])
        self.assertEqual(self.rules(DECLARATION.replace("\n", "\n\n  ")), [])
        cursor = DECLARATION.replace("u16 display;", "u8 *cursor;")
        self.assertEqual(self.rules(cursor, entries=(pinned(cursor),)), [])

    def test_shipped_allow_list_holds_only_the_issue_entry(self):
        entries = plausible.volatile_allow_entries()
        self.assertEqual([(e["symbol"], e["address"], e["header"], e["member_types"])
                          for e in entries], [(SYMBOL, "0x03000940", HEADER, ["u8"])])
        tokens = plausible.declaration_tokens(entries[0]["declaration"])
        self.assertEqual(tokens[:3] + tokens[-2:], ["extern", "struct", "{", SYMBOL, ";"])
        qualifiers = [index for index, token in enumerate(tokens) if token == "volatile"]
        self.assertTrue(qualifiers)
        for index in qualifiers:
            self.assertEqual((tokens[index + 1], tokens[index + 3], tokens[index + 5]),
                             ("u8", ":", ";"))

    def test_wrong_or_missing_address_binding_is_rejected(self):
        for mapping in ({}, {SYMBOL: "0x03000944"}, {SYMBOL: "invalid"}, {"other": "0x03000940"}):
            with self.subTest(mapping=mapping):
                self.assertIn("volatile", self.rules(DECLARATION, mapping=mapping))
        moved = dict(ENTRY, address="0x03000944")
        self.assertIn("volatile", self.rules(DECLARATION, entries=(moved,)))
        self.assertIn("volatile", self.rules(DECLARATION, entries=()))
        for broken in (dict(ENTRY, member_types=[]), dict(ENTRY, symbol="a b"),
                       {k: v for k, v in ENTRY.items() if k != "header"},
                       {k: v for k, v in ENTRY.items() if k != "declaration"}):
            with self.subTest(entry=broken):
                self.assertIn("volatile", self.rules(DECLARATION, entries=(broken,)))

    def test_header_drift_from_the_pinned_declaration_is_rejected(self):
        for source in (DECLARATION.replace("u8 unknown_02[0x3A];", "u8 unknown_02[0x3A00];"),
                       DECLARATION.replace("} ", "    u8 unknown_44[0x1000];\n} "),
                       DECLARATION.replace("    u8 unknown_02", "    volatile u8 unknown_01 : 8;\n    u8 unknown_02"),
                       DECLARATION.replace("unknown_3D : 8", "unknown_3D : 4"),
                       DECLARATION.replace("u16 display;", "volatile u8 display : 8;")):
            with self.subTest(source=source):
                self.assertIn("volatile", self.rules(source))
                self.assertIn("volatile-allowlist", self.rules(source))

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

    def test_qualifier_must_start_a_listed_bitfield_member(self):
        for member in ("volatile u8 unknown_3D;", "volatile u16 unknown_3D : 8;",
                       "volatile u8 *unknown_3D;", "volatile u8 unknown_3D[2];",
                       "u8 volatile unknown_3D : 8;", "u8 * volatile unknown_3D;",
                       "volatile unknown_3D : 8;", "volatile u8 unknown_3D : 4, unknown_3E : 4;"):
            with self.subTest(member=member):
                source = DECLARATION.replace("volatile u8 unknown_3D : 8;", member)
                self.assertIn("volatile", self.rules(source, entries=(pinned(source),)))

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
                self.refused(self.rules(source))
                self.refused(self.rules(source, entries=(pinned(source),)))

    def test_typeof_is_refused_while_an_entry_is_active(self):
        for relpath in (HEADER, "src/08028C34.c", "include/other.h"):
            for spelling in ("typeof", "__typeof", "__typeof__"):
                with self.subTest(relpath=relpath, spelling=spelling):
                    source = spelling + "(" + SYMBOL + ".unknown_3C) local;\n"
                    if relpath == HEADER:
                        source = DECLARATION + source
                    self.assertIn("volatile-allowlist", self.rules(source, relpath=relpath))
        self.assertEqual(self.rules("__typeof__(x) y;", relpath="src/a.c", mapping={}), [])

    def test_address_and_pointer_arithmetic_are_refused_in_users(self):
        for statement in ("(&" + SYMBOL + ")[1].unknown_3C = 1;",
                          "*((u8 *)&" + SYMBOL + " + 0x100) = 1;",
                          "p = & ( " + SYMBOL + " );", "p = &" + SYMBOL + ".unknown_02[4];"):
            with self.subTest(statement=statement):
                self.assertIn("volatile-allowlist",
                              self.rules("void f(void) { " + statement + " }\n",
                                         relpath="src/08028C34.c"))
        self.assertEqual(self.rules("void f(void) { if (a && " + SYMBOL + ".unknown_3C) g(); }\n",
                                    relpath="src/08028C34.c"), [])
        # A source declaring the symbol itself never sees the volatile declaration.
        self.assertEqual(self.rules("extern u16 " + SYMBOL + ";\nvoid f(void) { p = &" +
                                    SYMBOL + "; }\n", relpath="src/0800337C.c"), [])

    def test_declaration_identifiers_cannot_be_redefined(self):
        for relpath, source in (("src/08028C34.c", "#define u8 u8 *\n#include \"control_flags.h\"\n"),
                                ("src/08028C34.c", "#undef u8\n"),
                                ("src/08028C34.c", "#define unknown_3C unknown_3C[64]\n"),
                                ("src/08028C34.c", "# define \\\nu8 u32\n"),
                                ("include/other.h", "#define u16 u32\n"),
                                (HEADER, "#define u8 u32\n" + DECLARATION),
                                (HEADER, "#define struct union\n" + DECLARATION)):
            with self.subTest(relpath=relpath, source=source):
                self.assertIn("volatile-allowlist", self.rules(source, relpath=relpath))
        self.assertEqual(self.rules("#define FLAG_MASK 0x40\n", relpath="src/a.c"), [])
        self.assertEqual(self.rules("#define u8 u32\n", relpath="src/a.c", mapping={}), [])

    def test_source_files_never_qualify(self):
        source = DECLARATION + ACCESS
        self.assertIn("volatile", self.rules(source, relpath="src/08028C34.c"))
        self.assertEqual(self.rules(ACCESS, relpath="src/08028C34.c"), [])

    def test_file_paths_bind_to_the_project_root_or_a_replay_capture(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "config").mkdir()
            (root / "config" / "data_symbols.json").write_text(json.dumps(MAPPING))

            def rules(relative):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(plausible.volatile_allow_entries()[0]["declaration"] + "\n")
                return [rule for _, rule, _, _ in plausible.check_file(path)]

            self.assertEqual(rules(HEADER), [])
            self.assertEqual(rules("build/ffta_replay_x/" + HEADER), [])
            for relative in ("src/control_flags.h", "include/sub/control_flags.h",
                             "build/" + HEADER, "build/x/src/control_flags.h",
                             "build/a/b/" + HEADER, "build/a/b/c/" + HEADER,
                             "other/" + HEADER):
                with self.subTest(relative=relative):
                    self.assertIn("volatile", rules(relative))
            (root / "config" / "data_symbols.json").write_text(json.dumps({SYMBOL: "0x03000944"}))
            self.assertIn("volatile", rules(HEADER))

    def test_report_records_only_real_uses_and_bind_the_header(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "config").mkdir()
            (root / "src").mkdir()
            (root / "include").mkdir()
            (root / "config" / "data_symbols.json").write_text(json.dumps(MAPPING))
            header = root / HEADER
            header.write_text(DECLARATION)
            source = root / "src" / "08028C34.c"

            def record():
                digest = hashlib.sha256(header.read_bytes()).hexdigest()
                return (f"* allowlisted volatile: `{SYMBOL}` at `0x03000940` declared in "
                        f"`{HEADER}` (SHA-256 `{digest}`)")

            def uses(text, entries=(ENTRY,)):
                source.write_text(text)
                return plausible.allowlisted_volatile_uses(root, 0x08028C34, list(entries))

            first = record()
            self.assertEqual(uses('#include "control_flags.h"\n' + ACCESS), [first])
            header.write_text("/* drift */\n" + DECLARATION)
            self.assertEqual(uses(ACCESS), [record()])
            self.assertNotEqual(record(), first)
            self.assertEqual(uses("/* " + SYMBOL + " */ void f(void) {}\n"), [])
            self.assertEqual(uses("extern u16 " + SYMBOL + ";\n" + ACCESS), [])
            self.assertEqual(uses("extern struct { u8 a; } " + SYMBOL + ";\n" + ACCESS), [])
            self.assertEqual(uses(ACCESS, entries=()), [])
            header.unlink()
            with self.assertRaises(OSError):
                uses(ACCESS)
            (root / "config" / "data_symbols.json").write_text(json.dumps({SYMBOL: "0x03000944"}))
            self.assertEqual(uses(ACCESS), [])


if __name__ == "__main__":
    unittest.main()
