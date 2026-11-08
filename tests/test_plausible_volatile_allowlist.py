import hashlib
import json
import sys
import tempfile
from pathlib import Path
import unittest
from unittest import mock

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
    def rules(self, source, relpath=HEADER, mapping=MAPPING, entries=(ENTRY,), closure=None):
        return [rule for _, rule, _, _ in plausible.check_text(
            source, data_symbols=mapping, relpath=relpath, volatile_allow=list(entries),
            closure=closure)]

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
                          for e in entries], [(SYMBOL, "0x03000940", HEADER, ["u8", "u16"])])
        tokens = plausible.declaration_tokens(entries[0]["declaration"])
        self.assertEqual(tokens[:3] + tokens[-2:], ["extern", "struct", "{", SYMBOL, ";"])
        qualifiers = [index for index, token in enumerate(tokens) if token == "volatile"]
        self.assertTrue(qualifiers)
        for index in qualifiers:
            self.assertIn((tokens[index + 1], tokens[index + 3], tokens[index + 4], tokens[index + 5]),
                          (("u8", ":", "8", ";"), ("u16", ":", "16", ";")))

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

    def test_listed_halfword_members_must_be_full_width_bit_fields(self):
        halfword = DECLARATION.replace("u8 unknown_02[0x3A];",
                                       "volatile u16 unknown_02 : 16;\n    u8 unknown_04[0x38];")
        both = dict(pinned(halfword), member_types=["u8", "u16"])
        self.assertEqual(self.rules(halfword, entries=(both,)), [])
        # u16 is not listed for this entry
        self.assertIn("volatile", self.rules(halfword, entries=(pinned(halfword),)))
        for member in ("volatile u16 unknown_02 : 8;", "volatile u16 unknown_02 : 15;",
                       "volatile u16 unknown_02 : 32;", "volatile u16 unknown_02;",
                       "volatile u16 unknown_02[1];"):
            with self.subTest(member=member):
                source = halfword.replace("volatile u16 unknown_02 : 16;", member)
                self.assertIn("volatile", self.rules(source, entries=(dict(both, declaration=pinned(
                    source)["declaration"]),)))
        for member, types in (("volatile u8 unknown_3D : 4;", ["u8"]),
                              ("volatile u8 unknown_3D : 16;", ["u8"]),
                              ("volatile u32 unknown_3D : 32;", ["u8", "u32"]),
                              ("volatile int unknown_3D : 32;", ["u8", "int"])):
            with self.subTest(member=member):
                source = DECLARATION.replace("volatile u8 unknown_3D : 8;", member)
                self.assertIn("volatile", self.rules(source, entries=(dict(pinned(source),
                                                                           member_types=types),)))

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
                          "p = & ( " + SYMBOL + " );", "copy = " + SYMBOL + ";",
                          "escape(" + SYMBOL + ");", "(" + SYMBOL + ").unknown_3C = 1;"):
            with self.subTest(statement=statement):
                self.assertIn("volatile-allowlist",
                              self.rules("void f(void) { " + statement + " }\n",
                                         relpath="src/08028C34.c"))
        self.assertEqual(self.rules("void f(void) { if (a && " + SYMBOL + ".unknown_3C) g(); }\n",
                                    relpath="src/08028C34.c"), [])
        # No member's address may be taken: it could reach a volatile byte.
        self.assertIn("volatile-allowlist", self.rules("void f(void) { p = &" + SYMBOL + ".unknown_02[4]; }\n",
                                                       relpath="src/08028C34.c"))
        # A source declaring the symbol itself never sees the volatile declaration.
        self.assertEqual(self.rules("extern u16 " + SYMBOL + ";\nvoid f(void) { p = &" +
                                    SYMBOL + "; }\n", relpath="src/0800337C.c",
                                    closure=({"src/0800337C.c"}, [])), [])
        # ...but only when it provably cannot see the listed declaration.
        for closure in (None, ({"src/0800337C.c", HEADER}, [])):
            with self.subTest(closure=closure):
                self.assertIn("volatile-allowlist", self.rules(
                    "extern u16 " + SYMBOL + ";\nvoid f(void) { p = &" + SYMBOL + "; }\n",
                    relpath="src/0800337C.c", closure=closure))

    def test_second_review_bypasses_are_refused(self):
        include = '#include "control_flags.h"\n'
        for name, source in (
                ("macro alias", include + "#define CF " + SYMBOL + "\nvoid f(void) { (&CF)[1].unknown_3C = 1; }\n"),
                ("macro alias member", include + "#define CF " + SYMBOL + ".unknown_3C\nvoid f(void) { CF = 1; }\n"),
                ("pasted name", include + "#define CAT(a, b) a##b\nvoid f(void) { (&CAT(g_control_flags_, 03000940))[1].unknown_3C = 1; }\n"),
                ("digraph paste", include + "#define CAT(a, b) a%:%:b\n"),
                ("parameter name", include + "extern void g(int " + SYMBOL + ");\nvoid f(void) { (&" + SYMBOL + ")[1].unknown_3C = 1; }\n"),
                ("prototype pointer", include + "extern void g(u8 *" + SYMBOL + ", int);\nvoid f(void) { p = &" + SYMBOL + "; }\n"),
                ("spliced address", include + "void f(void) { (&\\\n" + SYMBOL + ")[1].unknown_3C = 1; }\n"),
                ("pasted typeof", include + "#define TY __type##of__\nvoid f(void) { TY(" + SYMBOL + ".unknown_3C) l; }\n"),
                ("spliced typeof", include + "void f(void) { type\\\nof(" + SYMBOL + ".unknown_3C) l; }\n"),
                ("digraph define", "%:define u8 int\n" + include),
                ("trigraph define", "??=define u8 int\n" + include),
                ("trigraph splice", "#define u8 ??/\nint\n" + include),
                ("comment define", "#/*\n*/define u8 int\n" + include),
                ("line directive", "#line 1 \"include/control_flags.h\"\n"),
                ("linemarker", "# 1 \"include/control_flags.h\"\n"),
                ("import", '#import "control_flags.h"\n'),
                ("include_next", '#include_next "control_flags.h"\n'),
                ("computed include", "#define H \"control_flags.h\"\n#include H\n")):
            with self.subTest(name=name):
                self.assertIn("volatile-allowlist", self.rules(source, relpath="src/08028C34.c"))
        self.assertEqual(self.rules(include + "extern void g(int " + SYMBOL + "_count);\n" + ACCESS,
                                    relpath="src/08028C34.c"), [])
        self.assertEqual(self.rules("#define CAT(a, b) a##b\n", relpath="src/a.c", mapping={}), [])

    def test_whitespace_before_a_splice_newline_still_splices(self):
        include = '#include "control_flags.h"\n'
        for name, source in (
                ("address", include + "void f(int n) { (&g_control_flags_\\ \n03000940 + n)->unknown_3C = 1; }\n"),
                ("typeof", include + "void f(void) { type\\\t\nof(" + SYMBOL + ".unknown_3C) l; }\n"),
                ("define", "#define u8 \\ \nint\n" + include),
                ("directive", "#\\ \ndefine u8 int\n" + include),
                ("macro", include + "#define CF \\  \n" + SYMBOL + "\n"),
                ("linemarker", "#\\ \nline 1\n"),
                ("computed include", "#define H \"control_flags.h\"\n#include \\ \nH\n")):
            with self.subTest(name=name):
                self.assertIn("volatile-allowlist", self.rules(source, relpath="src/08028C34.c"))
        spliced = DECLARATION.replace("u16 display;", "u16 \\ \ndisplay;")
        self.assertIn("volatile", self.rules(spliced, entries=(pinned(spliced),)))

    def test_guarded_declarations_do_not_exempt_a_header_user(self):
        include = '#include "control_flags.h"\n'
        for guard in ("#ifdef NEVER_DEFINED", "#if defined(X)", "#if 1-1", "#if 0"):
            source = (include + guard + "\nextern char " + SYMBOL + "[1];\n#endif\n"
                      "void f(int n) { (&" + SYMBOL + " + n)->unknown_3C = 1; }\n")
            with self.subTest(guard=guard):
                self.assertIn("volatile-allowlist", self.rules(
                    source, relpath="src/08028C34.c", closure=({"src/08028C34.c", HEADER}, [])))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("config", "src", "include"):
                (root / name).mkdir()
            (root / "config" / "data_symbols.json").write_text(json.dumps(MAPPING))
            (root / HEADER).write_text(plausible.volatile_allow_entries()[0]["declaration"] + "\n")
            (root / "include" / "wrapper.h").write_text("#include <control_flags.h>\n")
            source = root / "src" / "08028C34.c"
            for text in (include, '#include "wrapper.h"\n'):
                source.write_text(text + "#ifdef NEVER\nextern int " + SYMBOL + ";\n#endif\n"
                                  "void f(int n) { (&" + SYMBOL + " + n)->unknown_3C = 1; }\n")
                with self.subTest(text=text):
                    self.assertIn("volatile-allowlist",
                                  [rule for _, rule, _, _ in plausible.check_file(source)])
            source.write_text("extern u16 " + SYMBOL + ";\nvoid f(void) { p = &" + SYMBOL + "; }\n")
            self.assertEqual(plausible.check_file(source), [])

    def test_includes_must_stay_inside_linted_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("config", "src", "include", "Parked"):
                (root / name).mkdir()
            (root / "config" / "data_symbols.json").write_text(json.dumps(MAPPING))
            (root / "Parked" / "x.h").write_text("#define u8 int\n")
            (root / "src" / "helper.c").write_text("int helper;\n")
            (root / "src" / "local.h").write_text("int local;\n")
            outside = root.parent / (root.name + "_outside.h")
            outside.write_text("int outside;\n")
            source = root / "src" / "08028C34.c"
            try:
                for include in ('"../Parked/x.h"', '"' + str(outside) + '"', '"helper.c"',
                                '<../Parked/x.h>'):
                    source.write_text("#include " + include + "\nvoid f(void) { g(); }\n")
                    with self.subTest(include=include):
                        self.assertIn("volatile-allowlist",
                                      [rule for _, rule, _, _ in plausible.check_file(source)])
                source.write_text('#include "local.h"\n#include "../include/control_flags.h"\n'
                                  "void f(void) { g(); }\n")
                self.assertEqual(plausible.check_file(source), [])
                (root / "config" / "data_symbols.json").write_text("{}")
                source.write_text('#include "../Parked/x.h"\nvoid f(void) { g(); }\n')
                self.assertEqual(plausible.check_file(source), [])
            finally:
                outside.unlink()

    def test_form_feed_vertical_tab_and_lone_carriage_return_are_refused(self):
        grow = "unknown_3C big[0x1000]; u8 dummy\n"
        tail = '#include "control_flags.h"\nvoid f(void) { ' + SYMBOL + '.big[0x400] = 1; }\n'
        cases = {"ff": "#define\f" + grow + tail, "ff2": "\f#define " + grow + tail,
                 "vt": "#\vdefine " + grow + tail, "midline": "int y; \v#define " + grow + tail,
                 "cr": "int x;\r#define " + grow.rstrip("\n") + '\r#include "control_flags.h"\n' +
                       "void f(void) { " + SYMBOL + ".big[0x400] = 1; }\n"}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("config", "src", "include", "out"):
                (root / name).mkdir()
            (root / "config" / "data_symbols.json").write_text(json.dumps(MAPPING))
            (root / HEADER).write_text(plausible.volatile_allow_entries()[0]["declaration"] + "\n")
            evil = root / "out" / "evil.h"
            evil.write_text("#define unknown_3C big[0x1000]; u8 dummy\n")
            cases["esc"] = '\f#include "' + str(evil) + '"\n' + tail
            source = root / "src" / "08028C34.c"
            for name, text in cases.items():
                source.write_bytes(text.encode())
                with self.subTest(name=name):
                    self.assertIn("volatile-allowlist",
                                  [rule for _, rule, _, _ in plausible.check_file(source)])
                    self.assertIn("volatile-allowlist", self.rules(text, relpath="src/08028C34.c"))
            source.write_bytes(('#include "control_flags.h"\r\n' + ACCESS.replace("\n", "\r\n")).encode())
            self.assertEqual(plausible.check_file(source), [])
        self.assertEqual(self.rules("\f#define X 1\n", relpath="src/a.c", mapping={}), [])

    def test_member_reads_are_left_to_the_semantic_check(self):
        # Planted reads are refused by match.py's stripped-declaration compile
        # (tests/test_volatile_semantics.py), which sees every spelling; the
        # lint no longer guesses at them.
        for statement in (SYMBOL + ".unknown_3C;", "(void)" + SYMBOL + ".unknown_3D;",
                          "x = " + SYMBOL + ".unknown_3C;", "f(a, " + SYMBOL + ".unknown_3C);",
                          "return " + SYMBOL + ".unknown_3C;", "if (" + SYMBOL + ".unknown_3C) g();",
                          SYMBOL + ".unknown_3C = 1;", "x = c ? " + SYMBOL + ".unknown_3C : 0;"):
            with self.subTest(statement=statement):
                self.assertEqual(self.rules("void f(void) { " + statement + " }\n",
                                            relpath="src/08028C34.c"), [])

    def test_array_member_subscripts_stay_in_bounds(self):
        # review repros 08000002/08000003: a subscript past an array member
        # reaches a volatile byte without its qualifier
        for statement in (SYMBOL + ".unknown_02[0x3A] = a;", SYMBOL + ".unknown_02[58] = a;",
                          SYMBOL + ".unknown_02[-1] = a;", SYMBOL + ".unknown_02[i] = a;",
                          SYMBOL + ".unknown_02[0x30 + 0xA] = a;", "x = " + SYMBOL + ".unknown_02[0x40];"):
            with self.subTest(statement=statement):
                self.assertIn("volatile-allowlist", self.rules("void f(void) { " + statement + " }\n",
                                                               relpath="src/08028C34.c"))
        for statement in (SYMBOL + ".unknown_02[0] = a;", SYMBOL + ".unknown_02[0x39] = a;",
                          "x = " + SYMBOL + ".unknown_02[57];"):
            with self.subTest(statement=statement):
                self.assertEqual(self.rules("void f(void) { " + statement + " }\n",
                                            relpath="src/08028C34.c"), [])

    def test_pinned_bytes_are_reached_only_through_their_members(self):
        # round-2 repros (08000011-08000018, 08000031-08000033)
        for statement in ("*(" + SYMBOL + ".unknown_02 + 0x3A) = a;",
                          "(" + SYMBOL + ".unknown_02)[0x3A] = a;",
                          "0x3A[" + SYMBOL + ".unknown_02] = a;",
                          "*(&" + SYMBOL + ".unknown_3E - 2) = a;",
                          "((u8 *)&" + SYMBOL + ".display)[0x3C] = a;",
                          "*(" + SYMBOL + ".unknown_02 - 1) = a;",
                          "{ u8 *p = " + SYMBOL + ".unknown_02; p[0x3A] = a; }",
                          "*(u8 *)((u32)&" + SYMBOL + ".unknown_3E - 2) = a;",
                          "memcpy(&" + SYMBOL + ".display, src, 0x4E);",
                          "k(*(" + SYMBOL + ".unknown_02 + 0x3A));",
                          "p = & (" + SYMBOL + ".unknown_3C);"):
            with self.subTest(statement=statement):
                self.assertIn("volatile-allowlist", self.rules("void f(void) { " + statement + " }\n",
                                                               relpath="src/08028C34.c"))
        self.assertEqual(self.rules("void f(void) { if (a && " + SYMBOL + ".unknown_02[1]) "
                                    + SYMBOL + ".unknown_02[0x39 ] = a; }\n", relpath="src/08028C34.c"), [])

    def test_round_three_macro_operator_and_literal_spellings(self):
        include = '#include "control_flags.h"\n'
        closure = ({"src/08028C34.c", HEADER}, [])
        for source in (include + "#define ARR unknown_02\nvoid f(void) { *(" + SYMBOL + ".ARR + 0x3A) = a; }\n",
                       include + "#define AT &\nvoid f(void) { p = AT " + SYMBOL + ".display; }\n",
                       include + "#define ADDR(x) &x\nvoid f(void) { p = ADDR(" + SYMBOL + ".display); }\n",
                       include + "#define MASK(x) ((x) & 1)\nvoid f(void) { a = 1; }\n",
                       include + "#define BYTE u8\nvoid f(void) { a = 1; }\n"):
            with self.subTest(source=source):
                self.assertIn("volatile-allowlist", self.rules(source, relpath="src/08028C34.c",
                                                               closure=closure))
        # a file that does not use the object keeps its macros
        self.assertEqual(self.rules("#define MASK(x) ((x) & 1)\nvoid f(void) { a = 1; }\n",
                                    relpath="src/08037428.c", closure=({"src/08037428.c"}, [])), [])
        for statement in ("k(a &&&" + SYMBOL + ".display);", SYMBOL + ".unknown_02[0100] = a;",
                          SYMBOL + ".unknown_02[0x3Au] = a;", "k((u32)&" + SYMBOL + ".unknown_3E);"):
            with self.subTest(statement=statement):
                self.assertIn("volatile-allowlist", self.rules("void f(void) { " + statement + " }\n",
                                                               relpath="src/08028C34.c"))
        for statement in (SYMBOL + ".unknown_02[010] = a;", "k(" + SYMBOL + ".unknown_3C & a);",
                          "x = " + SYMBOL + ".unknown_3D & b[1];"):
            with self.subTest(statement=statement):
                self.assertEqual(self.rules("void f(void) { " + statement + " }\n",
                                            relpath="src/08028C34.c"), [])

    def test_round_four_ampersands_casts_forged_lines_and_header_macros(self):
        # any `&` before the symbol, binary included (write `symbol.x & a`)
        for statement in ("k(a & " + SYMBOL + ".unknown_3C);", "k(a &&&" + SYMBOL + ".unknown_3C);",
                          "p = __extension__ &" + SYMBOL + ".unknown_3E;",
                          "(*(u8 (*)[0x4E])&" + SYMBOL + ".display)[0x3C] = a;",
                          "((struct { u8 unknown_00[0x3C]; u8 x; } *)&" + SYMBOL + ".display)->x = a;",
                          "q = (struct { u8 b[2]; } *)p; x = " + SYMBOL + ".unknown_3C;",
                          "f = (void (*)(void))p; x = " + SYMBOL + ".unknown_3C;"):
            with self.subTest(statement=statement):
                self.assertIn("volatile-allowlist", self.rules("void f(void) { " + statement + " }\n",
                                                               relpath="src/08028C34.c"))
        # a forged linemarker through a macro (c5)
        for source in ("#define H #\nH 1 \"include/fake.h\"\n", "#define H #define\n",
                       "#define H x # y\n"):
            with self.subTest(source=source):
                self.assertIn("volatile-allowlist", self.rules(source, relpath="src/08000001.c", mapping=MAPPING))
        for source in ("#define STR(x) \"(\" #x \")\"\n", "#define S(x) #x\n"):
            with self.subTest(source=source):
                self.assertEqual(self.rules(source, relpath="src/a.c"), [])
        self.assertEqual(self.rules("void f(void) { k(a && " + SYMBOL + ".unknown_3C); }\n",
                                    relpath="src/08028C34.c"), [])
        # a header in a user's include closure may not define such macros (c4)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "config").mkdir()
            (root / "src").mkdir()
            (root / "include").mkdir()
            (root / "config" / "data_symbols.json").write_text(json.dumps(MAPPING))
            (root / HEADER).write_text(DECLARATION)
            (root / "src" / "m.h").write_text("#define ARR unknown_02\n")
            source = root / "src" / "08028C34.c"
            source.write_text('#include "control_flags.h"\n#include "m.h"\n' + ACCESS)
            with mock.patch.object(plausible, "volatile_allow_entries", return_value=[ENTRY]):
                findings = plausible.check_file(source)
            self.assertTrue(any("m.h" in message for _, _, _, message in findings), findings)

    def test_hash_outside_a_directive_line_is_refused(self):
        # round 5 (f1): `F(#) pragma ...` pastes a directive together
        for source in ("#define F(x) x\nF(#) pragma pack(1)\n", "int a; # 1 \"x\"\n",
                       "void f(void) { k(#x); }\n"):
            with self.subTest(source=source):
                self.assertIn("volatile-allowlist", self.rules(source, relpath="src/08000001.c"))
        for source in ("#define S(x) #x\nconst char *s = \"#\";\nchar c = '#';\n",
                       "  #  define A 1\n", "#define LONG \\\n  1\n"):
            with self.subTest(source=source):
                self.assertEqual(self.rules(source, relpath="src/08000001.c"), [])

    def test_provenance_rules_bind_only_users_of_the_object(self):
        # A source that neither names the symbol nor includes the header keeps
        # ordinary C: function-pointer casts, struct casts, `&` and __extension__.
        other = ("typedef void (*Fn)(void);\n"
                 "void f(int a, int b) { ((void (*)(void))a)(); x = (struct { int y; } *)0; "
                 "x = __extension__ a; }\n")
        self.assertEqual(self.rules(other, relpath="src/08011EBC.c", closure=({"src/08011EBC.c"}, [])), [])
        self.assertEqual(self.rules(other, relpath="src/08011EBC.c"), [])
        # Including the header without naming the symbol cannot reach the object
        # when no closure is known.
        self.assertEqual(self.rules('#include "control_flags.h"\nint g(int a) { return a; }\n',
                                    relpath="src/08011EBC.c"), [])
        # The same text in a user of the object is still refused.
        self.assertIn("volatile-allowlist", self.rules(
            '#include "control_flags.h"\n' + other, relpath="src/08028C34.c",
            closure=({"src/08028C34.c", HEADER}, [])))
        self.assertIn("volatile-allowlist", self.rules(
            other + "void g(void) { " + SYMBOL + ".unknown_3C = 1; }\n", relpath="src/08028C34.c"))

    def test_round_six_extension_and_parenthesised_address_of(self):
        for statement in ("p = &(0, " + SYMBOL + ".unknown_3E);", "p = &(c ? " + SYMBOL + ".unknown_3E : x);",
                          "k(*(u16 *)&(0, " + SYMBOL + ".unknown_02[0x39]));",
                          "x = __extension__ " + SYMBOL + ".unknown_3C;"):
            with self.subTest(statement=statement):
                self.assertIn("volatile-allowlist", self.rules("void f(void) { " + statement + " }\n",
                                                               relpath="src/08028C34.c"))
        self.assertEqual(self.rules("void f(void) { x = (" + SYMBOL + ".unknown_3C & a); }\n",
                                    relpath="src/08028C34.c"), [])

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
        guarded = dict(ENTRY, guard="CONTROL_FLAGS_H")
        for source in ("#define CONTROL_FLAGS_H\n", "#undef CONTROL_FLAGS_H\n"):
            with self.subTest(source=source):
                self.assertIn("volatile-allowlist", self.rules(
                    source, relpath="src/08028C34.c", entries=(guarded,)))
        self.assertEqual(plausible.volatile_allow_entries()[0]["guard"], "CONTROL_FLAGS_H")
        header = "#ifndef CONTROL_FLAGS_H\n#define CONTROL_FLAGS_H\n" + DECLARATION + "#endif\n"
        self.assertEqual(self.rules(header, entries=(guarded,)), [])
        for source in (header.replace("#define CONTROL_FLAGS_H", "#define CONTROL_FLAGS_H 1"),
                       header + "#undef CONTROL_FLAGS_H\n",
                       header + "#define CONTROL_FLAGS_H\n"):
            with self.subTest(source=source):
                self.assertIn("volatile-allowlist", self.rules(source, entries=(guarded,)))
        self.assertIn("volatile-allowlist", self.rules(
            "#define CONTROL_FLAGS_H\n", relpath="include/other.h", entries=(guarded,)))
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
            self.assertEqual(uses('#include "control_flags.h"\nvoid f(void) {}\n'), [record()])
            (root / "include" / "wrapper.h").write_text('#include <control_flags.h>\n')
            self.assertEqual(uses('#include "wrapper.h"\nvoid f(void) {}\n'), [record()])
            self.assertEqual(uses('/* #include "wrapper.h" */\nvoid f(void) {}\n'), [])
            self.assertEqual(uses("extern void g(int " + SYMBOL + ");\n" + ACCESS), [record()])
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
