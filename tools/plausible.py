#!/usr/bin/env python3
"""
plausible.py - reject decompiled C that only exists to make bytes match.

A matching decomp is supposed to reconstruct the source a developer actually
wrote.  Byte-matching by trickery is worthless: inline asm, pragma surgery and
padding that exists purely to steer the compiler all produce a "match" that
proves nothing and cannot be maintained.

So every function is also checked for implausibility.  Anything that trips a
rule is IMPLAUSIBLE and does not count as a match, however well the bytes line
up.

    python tools/plausible.py src/08017514.c        # check files
    python tools/plausible.py --quiet src/          # just the exit status

Rules
------
error   the construct has no plausible reading as original source
suspect the construct is legitimate *somewhere*, but must be justified here

A suspect finding is cleared by a comment containing `plausible:` on the same
line or the line above. Volatile additionally requires a direct I/O access or
a pointer used only for member access to an external symbol mapped into the
GBA I/O register window:

    /* plausible: hardware register, volatile is required here */
    *(volatile u16 *)0x04000000 = v;

Proposed (kit#90, pending maintainer decision): volatile RAM is allowed only
for objects on the maintainer's volatile allow list (tools/volatile_allow.json),
and only inside the one listed header's anonymous `extern struct { ... }
symbol;` declaration, which must equal the pinned text, as qualifiers of
bit-field members of listed types, while config/data_symbols.json maps the
symbol to the listed address.  Source files never qualify.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

JUSTIFY = "plausible:"

# id, severity, pattern, message
RULES = [
    # --- constructs that are a codegen hack by definition
    ("inline-asm", "error", r"__asm__|\basm\s*(?:__volatile__|volatile|goto|inline)?\s*\(",
     "inline assembly: the point of a matching decomp is C that compiles to the "
     "original code, not asm pasted into a C file"),
    ("asm-include", "error", r'#\s*include\s+"[^"]*\.(s|S)"',
     "including an assembly file"),
    ("optimize-pragma", "error",
     r"#\s*pragma\s+(?:GCC\s+)?optimize\b|__attribute__\s*\(\(?[^)]*optimize",
     "optimisation pragma/attribute: changes code generation outside the source"),
    ("target-pragma", "error",
     r"#\s*pragma\s+(?:GCC\s+)?target\b|__attribute__\s*\(\(?[^)]*target",
     "target pragma/attribute: retargets code generation from inside the source"),
    ("stringised-pragma", "error", r"\b_Pragma\s*\(|\bpragma\s*\(\s*[A-Za-z_]",
     "_Pragma / stringised pragma: a banned directive written so that it does "
     "not read as one - say what it does, or drop it"),
    ("no-standard-errors", "error", r"#\s*pragma\s+GCC\s+diagnostic",
     "disabling diagnostics to silence warnings the original would not have"),
    ("dead-code", "error", r"\bif\s*\(\s*0\s*\)|\bwhile\s*\(\s*0\s*\)|#\s*if\s+0\b",
     "dead code whose only purpose is to steer the compiler"),
    ("empty-body", "error", r"\)\s*\{\s*\}",
     "empty function body"),
    ("placeholder", "error", r"\?\?\?|\bTODO\b|\bFIXME\b|\bUNIMPLEMENTED\b|not implemented",
     "placeholder body"),
    ("volatile", "error", r"\bvolatile\b",
     "volatile: it suppresses reordering, which is the classic way to force a "
     "byte match (real I/O code is the only legitimate use - justify it)"),
    ("attribute-steering", "error",
     r"__attribute__\s*\(\(\s*_?+(used|section|alias|weak|naked|constructor|destructor|retain|common)",
     "attribute that only affects code placement or emission"),
    ("emission-pragma", "error",
     r"#\s*pragma\s+(?:GCC\s+)?_?(used|weak|section|retain|common|extern_weak)\b",
     "pragma that forces a symbol to exist or where it lands: code placement "
     "and emission are not the programmer's business in a decompilation"),

    # --- legitimate somewhere, must be justified here
    ("noinline", "suspect", r"\bnoinline\b|\balways_inline\b",
     "inlining attribute: fine in real code, but it is also a way to force a "
     "codegen difference"),
    ("pragma-pack", "suspect", r"#\s*pragma\s+pack",
     "struct packing: changes field offsets, which can be legitimate - say why"),
    ("pad-named", "suspect", r"\b(?:pad|padding|_pad)\s*\[",
     "padding named 'pad': if the real members are unknown, name them "
     "'unknown' and say so, rather than leaving steering padding"),
    ("rom-address", "suspect", r"0x0[89][0-9A-Fa-f]{6}\b(?![^;]*\))",
     "an address inside ROM used as a value: ROM is not writable, so this is "
     "usually a hack rather than a pointer"),
    ("hack-vocabulary", "suspect", r"\bhack\b|\bworkaround\b|force the compiler|"
     r"so the compiler will|to make (?:it|the) (?:match|compile)|codegen hack",
     "the comment admits the source exists to steer the compiler"),
]


def strip_comments_and_strings(text):
    """replace comments and string/char literals with spaces, keeping offsets"""
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "/":
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
        elif c == "/" and i + 1 < n and text[i + 1] == "*":
            while i < n and not (text[i] == "*" and i + 1 < n and text[i + 1] == "/"):
                out[i] = " "
                i += 1
            for k in range(i, min(i + 2, n)):
                out[k] = " "
            i += 2
        elif c in "\"'":
            q = c
            out[i] = " "
            i += 1
            while i < n and text[i] != q:
                if text[i] == "\\":
                    out[i] = " "
                    if i + 1 < n:
                        out[i + 1] = " "
                    i += 2
                    continue
                out[i] = " "
                i += 1
            if i < n:
                out[i] = " "
                i += 1
        else:
            i += 1
    return "".join(out)


def justified(text, line_no):
    """True if a comment containing `plausible:` covers this line"""
    lines = text.split("\n")
    for idx in (line_no - 1, line_no - 2):
        if 0 <= idx < len(lines) and JUSTIFY in lines[idx]:
            return True
    return False


def hardware_volatile_offsets(text, code, data_symbols):
    """Recognize documented, directly bound MMIO qualifiers, not local steering."""
    allowed = set()
    if not re.search(r"\bvolatile\b", code):
        return allowed
    comments = []
    tokens = r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|//[^\n]*|/\*[\s\S]*?\*/'
    for token in re.finditer(tokens, text):
        if token[0].startswith(("//", "/*")) and JUSTIFY in token[0]:
            comments.append(text.count("\n", 0, token.end()) + 1)

    def justified_io(offset, address):
        line = text.count("\n", 0, offset) + 1
        return 0x04000000 <= address < 0x04000400 and any(
            comment in (line, line - 1) for comment in comments)

    ctype = r"(?:struct\s+|union\s+)?[A-Za-z_]\w*(?:\s+[A-Za-z_]\w*)*"
    direct = (r"\*\s*\(\s*(?P<v>volatile)\s+" + ctype +
              r"\s*\*\s*\)\s*(?P<address>0x[0-9a-fA-F]+)[uUlL]*\b(?=\s*(?:[;=),]|$))")
    for match in re.finditer(direct, code):
        if justified_io(match.start("v"), int(match["address"], 16)):
            allowed.add(match.start("v"))

    bound = (r"\b(?P<v>volatile)\s+" + ctype +
             r"\s*\*\s*(?:const\s+)?(?P<local>[A-Za-z_]\w*)\s*=\s*"
             r"&\s*(?P<symbol>[A-Za-z_]\w*)\s*;")
    bindings = list(re.finditer(bound, code))
    for match in bindings:
        symbol = match["symbol"]
        value = data_symbols.get(symbol)
        try:
            address = int(value, 0) if isinstance(value, str) else int(value)
        except (TypeError, ValueError):
            continue
        declaration = re.search(r"(?m)^\s*extern\s+" + ctype + r"\s+" +
                                re.escape(symbol) + r"\s*;", code)
        if declaration is None:
            continue
        # Reject shadow declarations, pointer retargeting and pointer escapes.
        references = list(re.finditer(r"\b" + re.escape(symbol) + r"\b", code))
        if any(not declaration.start() <= ref.start() < declaration.end() and
               not re.search(r"&\s*$", code[:ref.start()]) for ref in references):
            continue
        local_uses = re.finditer(r"\b" + re.escape(match["local"]) + r"\b", code)
        declarations = [item.span("local") for item in bindings
                        if item["local"] == match["local"]]
        def conditional_dereference(before):
            prefix = before.rstrip()
            if not prefix.endswith("*"):
                return False
            prefix = prefix[:-1].rstrip()
            if re.search(r"\belse$", prefix):
                return True
            if not prefix.endswith(")"):
                return False
            depth = 0
            for index in range(len(prefix) - 1, -1, -1):
                if prefix[index] == ")":
                    depth += 1
                elif prefix[index] == "(":
                    depth -= 1
                    if depth == 0:
                        return re.search(r"\bif\s*$", prefix[:index]) is not None
            return False

        def direct_access(ref):
            before, after = code[:ref.start()], code[ref.end():]
            if re.match(r"\s*->", after):
                return not re.search(r"&\s*$", before)
            return ((re.search(r"(?:^|[=(:,;{}!~?&|^<>+\-/%\[\]])\s*\*\s*$|\breturn\s+\*\s*$", before) is not None or
                     conditional_dereference(before)) and
                    re.search(r"&\s*\*\s*$", before) is None and
                    re.match(r"\s*(?:\[|\+\+|--|\+=|-=|->|\.)", after) is None)

        if any(ref.span() not in declarations and not direct_access(ref)
               for ref in local_uses):
            continue
        if justified_io(match.start("v"), address):
            allowed.add(match.start("v"))
    return allowed


def volatile_allow_path():
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), "volatile_allow.json")


def volatile_allow_entries():
    """the maintainer's volatile allow list; unreadable or malformed is empty"""
    try:
        doc = json.loads(Path(volatile_allow_path()).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return []
    entries = doc.get("entries") if isinstance(doc, dict) else None
    return entries if isinstance(entries, list) else []


def declaration_tokens(code):
    """C tokens of a declaration, so the pinned text ignores only whitespace"""
    return re.findall(r"[A-Za-z_]\w*|0[xX][0-9A-Fa-f]+|[0-9]+|\S", code)


def declares_symbol(code, symbol):
    """a file that declares the symbol itself cannot also see the volatile one"""
    return re.search(r"\bextern\b(?:[^;{}]|\{[^{}]*\})*\b" + re.escape(symbol) + r"\b",
                     code) is not None


def active_volatile_entries(data_symbols, entries):
    """entries whose symbol the data map binds to exactly the listed address"""
    active = []
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        symbol, address, header, types, declaration = (
            entry.get("symbol"), entry.get("address"), entry.get("header"),
            entry.get("member_types"), entry.get("declaration"))
        if not (isinstance(symbol, str) and re.fullmatch(r"[A-Za-z_]\w*", symbol) and
                isinstance(address, str) and isinstance(header, str) and
                isinstance(declaration, str) and
                isinstance(types, list) and types and
                all(isinstance(t, str) and re.fullmatch(r"[A-Za-z_]\w*", t) for t in types)):
            continue
        mapped = data_symbols.get(symbol)
        try:
            if int(mapped, 0) != int(address, 0):
                continue
        except (TypeError, ValueError):
            continue
        active.append(entry)
    return active


def allowlisted_volatile(code, relpath, data_symbols, entries):
    """(exempt volatile offsets, findings) for the volatile allow list.

    Only the listed header may hold the listed object's declaration, and its
    tokens must equal the entry's pinned `declaration`: one file-scope
    anonymous `extern struct { ... } symbol;`.  Inside its braces, `volatile`
    may only begin a bit-field member `volatile T name : N;` with T a listed
    member type.  Bit-fields have no address, and the braces hold no nested,
    tagged or parenthesized types, so the qualifier cannot reach any other
    object.  While the entry is active, in every file: other headers may not
    name the symbol (a macro could hide a use), a file that does not declare
    the symbol itself may not take its address (pointer arithmetic would
    carry the qualifier elsewhere), typeof is
    refused (it would copy the qualifier onto locals), and no identifier of
    the pinned declaration may be #defined or #undefined (that would change
    what the pinned text declares).
    """
    allowed, findings = set(), []

    def finding(offset, message):
        findings.append((code.count("\n", 0, offset) + 1, "volatile-allowlist", "error", message))

    joined = re.sub(r"\\\r?\n", "", code)
    for entry in active_volatile_entries(data_symbols, entries):
        symbol, header = entry["symbol"], entry["header"]
        pinned = declaration_tokens(entry["declaration"])
        for typeof in re.finditer(r"\b(?:typeof|__typeof|__typeof__)\b", code):
            finding(typeof.start(), f"typeof while {symbol} is an allowlisted volatile "
                    "object: it would copy the qualifier onto other objects")
        own = declares_symbol(code, symbol)
        for address in re.finditer(r"(?<!&)&(?!&)(?:\s|\()*" + re.escape(symbol) + r"\b", code):
            if own:
                break
            finding(address.start(), f"the address of allowlisted volatile {symbol} may not "
                    "be taken: pointer arithmetic would carry the qualifier to other memory")
        names = {token for token in pinned if re.fullmatch(r"[A-Za-z_]\w*", token)}
        for directive in re.finditer(r"(?m)^[ \t]*#[ \t]*(?:define|undef)[ \t]+([A-Za-z_]\w*)", joined):
            if directive[1] in names:
                finding(min(directive.start(), len(code)),
                        f"`{directive[1]}` is part of the pinned {symbol} declaration and "
                        "may not be redefined while it is allowlisted")
        references = list(re.finditer(r"\b" + re.escape(symbol) + r"\b", code))
        if relpath is None or not relpath.endswith(".h"):
            continue
        if relpath != header:
            for reference in references:
                finding(reference.start(), f"{symbol} is declared volatile only in {header}; "
                        "other headers may not name it")
            continue
        declarations = list(re.finditer(
            r"(?m)^[ \t]*extern\s+struct\s*\{(?P<body>[^{}]*)\}\s*" + re.escape(symbol) +
            r"\s*;", code))
        if len(declarations) != 1 or len(references) != 1 or \
                not declarations[0].start() <= references[0].start() < declarations[0].end() or \
                re.search(r"\\\r?\n", code):
            for reference in references or [None]:
                finding(reference.start() if reference else 0,
                        f"{header} must declare {symbol} exactly once as a file-scope "
                        f"`extern struct {{ ... }} {symbol};` and name it nowhere else")
            continue
        body = declarations[0]
        if declaration_tokens(body[0]) != pinned:
            finding(body.start(), f"the {symbol} declaration differs from the one pinned in "
                    "tools/volatile_allow.json; only the maintainer may change it")
            continue
        if re.search(r"\b(?:struct|union|enum|typedef|extern|static)\b|[#()\[\]=]",
                     re.sub(r"\[\s*(?:0x[0-9A-Fa-f]+|[0-9]+)\s*\]", "", body["body"])):
            finding(body.start(), f"the {symbol} declaration may only hold plain members")
            continue
        types = "|".join(re.escape(t) for t in entry["member_types"])
        member = re.compile(r"volatile\s+(?:" + types + r")\s+[A-Za-z_]\w*"
                            r"\s*:\s*[0-9]+\s*;")
        for qualifier in re.finditer(r"\bvolatile\b", body["body"]):
            offset = body.start("body") + qualifier.start()
            prefix = code[body.start("body"):offset]
            if re.search(r"(?:^|;)\s*$", prefix) and member.match(code, offset):
                allowed.add(offset)
    return allowed, findings


def allowlisted_volatile_uses(root, address, entries=None):
    """report records for allowlisted volatile objects the addressed source uses.

    A use is the source naming the symbol without declaring it itself: the
    only declaration it can then compile against is the listed header's.
    Each record binds the header's current SHA-256; an unreadable header
    raises OSError, which callers treat as a failure.
    """
    root = Path(root)
    try:
        data_symbols = json.loads((root / "config" / "data_symbols.json").read_text())
    except (OSError, ValueError):
        data_symbols = {}
    if not isinstance(data_symbols, dict):
        data_symbols = {}
    entries = volatile_allow_entries() if entries is None else entries
    sources = sorted((root / "src").rglob(f"{address:08X}.c"))
    records = []
    for entry in active_volatile_entries(data_symbols, entries):
        symbol = re.escape(entry["symbol"])
        for source in sources:
            code = strip_comments_and_strings(source.read_text(encoding="utf-8", errors="replace"))
            if re.search(r"\b" + symbol + r"\b", code) and not declares_symbol(code, entry["symbol"]):
                digest = hashlib.sha256((root / entry["header"]).read_bytes()).hexdigest()
                records.append(f"* allowlisted volatile: `{entry['symbol']}` at "
                               f"`{entry['address']}` declared in `{entry['header']}` "
                               f"(SHA-256 `{digest}`)")
                break
    return records


def inert_control_flow(text):
    """find `if (c) X; else X;` - identical arms, so the test means nothing.

    This is the shape that appeared in a rejected match: the branches store the
    same value, so the only effect is to make the compiler keep a frame it
    would otherwise drop.  Semantically it is `X;`, and nobody writes that.
    """
    hits = []
    pat = re.compile(
        r"\bif\s*\((?P<cond>[^()]*)\)(?P<a>[^;{}]*?)\s*;?\s*else"
        r"\s*(?P<b>[^;{}]*?)\s*;")
    for m in pat.finditer(text):
        a = " ".join(m.group("a").split())
        b = " ".join(m.group("b").split())
        if a and a == b:
            line = text.count("\n", 0, m.start()) + 1
            hits.append((line, "inert-control-flow", "suspect",
                         f"`if ({m.group('cond').strip()}) {a}; else {b};` - both "
                         f"arms do the same thing, so the test exists only to "
                         f"change the generated code"))
    return hits


def hardware_polling_bodies(code, hardware_qualifiers):
    """Empty while bodies may poll a documented, fixed volatile MMIO macro.

    Only one object-like direct-access definition and a nonzero constant mask
    qualify. Function bodies, RAM reads, calls and mutable aliases still fail.
    """
    bodies = set()
    if re.search(r"\\\r?\n", code):
        return bodies
    definitions = list(re.finditer(
        r"(?m)^[ \t]*#[ \t]*define[ \t]+(?P<name>[A-Za-z_]\w*)[ \t]+"
        r"\(\s*\*\s*\(\s*(?P<v>volatile)\s+(?:u8|u16|u32)\s*\*\s*\)"
        r"\s*0x[0-9a-fA-F]+[uUlL]*\s*\)[ \t]*$", code))
    for definition in definitions:
        name = re.escape(definition['name'])
        directives = list(re.finditer(
            r"(?m)^[ \t]*#[ \t]*(?:define|undef)[ \t]+" + name + r"\b", code))
        if definition.start('v') not in hardware_qualifiers or len(directives) != 1:
            continue
        masked = name + r"\s*&\s*(?P<mask>0x[0-9a-fA-F]+|[0-9]+)[uUlL]*"
        condition = r"(?:" + masked + r"|!\s*\(\s*" + masked.replace('?P<mask>', '?P<negated_mask>') + r"\s*\))"
        for loop in re.finditer(r"\bwhile\s*\(\s*" + condition +
                                r"\s*(?P<body>\)\s*\{\s*\})", code):
            mask = loop['mask'] or loop['negated_mask']
            if loop.start() > definition.end() and int(mask, 16 if mask.lower().startswith('0x') else 10):
                bodies.add(loop.start('body'))
    return bodies


def statement_macro_tails(code):
    """Offsets of `while (0)` closing complete, nonempty do-statement macros.

    Such a macro executes its body once. Only its closing condition is exempt;
    the body is still scanned for dead code and every other forbidden construct.
    Comments and literals have already been blanked without changing offsets.
    """
    logical = re.sub(r"\\\r?\n", lambda match: " " * len(match[0]), code)
    tails = set()
    headers = re.finditer(
        r"(?m)^[ \t]*#[ \t]*define[ \t]+[A-Za-z_]\w*(?:\([^()\r\n]*\))?", logical)
    for header in headers:
        end = logical.find("\n", header.end())
        if end < 0:
            end = len(logical)
        opener = re.match(r"\s*do\b\s*\{", logical[header.end():end])
        if opener is None:
            continue
        opening = header.end() + opener.end() - 1
        depth = 1
        closing = opening + 1
        while closing < end and depth:
            if logical[closing] == "{":
                depth += 1
            elif logical[closing] == "}":
                depth -= 1
            closing += 1
        if depth or not logical[opening + 1:closing - 1].strip(" \t\r\n;"):
            continue
        body = code[opening + 1:closing - 1]
        joined_body = re.sub(r"\\\r?\n", "", body)
        # Do not let a newly accepted wrapper conceal a forbidden token split
        # across physical lines; the ordinary rule scan retains source offsets.
        if any(re.search(pattern, joined_body) and not re.search(pattern, body)
               for _, _, pattern, _ in RULES) or \
                (inert_control_flow(joined_body) and not inert_control_flow(body)):
            continue
        tail = re.fullmatch(r"\s*(while\s*\(\s*0\s*\))\s*;?\s*", logical[closing:end])
        if tail is not None:
            tails.add(closing + tail.start(1))
    return tails


def check_text(text, origin="", data_symbols=None, relpath=None, volatile_allow=None):
    """returns list of findings: (line, rule, severity, message)

    relpath is the file's path relative to the project root; only the header
    an allowlisted volatile object names can be exempted, so None never is.
    """
    code = strip_comments_and_strings(text)
    macro_tails = statement_macro_tails(code)
    hardware_qualifiers = hardware_volatile_offsets(text, code, data_symbols or {})
    listed_qualifiers, findings = allowlisted_volatile(
        code, relpath, data_symbols or {},
        volatile_allow_entries() if volatile_allow is None else volatile_allow)
    polling_bodies = hardware_polling_bodies(code, hardware_qualifiers)
    for rid, sev, pat, msg in RULES:
        for m in re.finditer(pat, code):
            if rid == "volatile" and m.start() in hardware_qualifiers | listed_qualifiers:
                continue
            if rid == "dead-code" and m.start() in macro_tails:
                continue
            if rid == "empty-body" and m.start() in polling_bodies:
                continue
            line = code.count("\n", 0, m.start()) + 1
            if sev == "suspect" and justified(text, line):
                continue
            # an inline-asm-looking thing inside a comment is not code
            findings.append((line, rid, sev, msg))
    findings += inert_control_flow(code)
    # comments are where hackiness gets admitted, so scan them raw too
    for i, raw in enumerate(text.split("\n"), 1):
        if JUSTIFY in raw:
            continue
        for rid, sev, pat, msg in RULES:
            if rid == "hack-vocabulary" and re.search(pat, raw):
                findings.append((i, rid, sev, msg))
    findings.sort(key=lambda f: (f[0], f[1]))
    return findings


def check_file(path):
    try:
        text = open(path, encoding="utf-8", errors="replace").read()
    except OSError as e:
        return [(0, "unreadable", "error", str(e))]
    data_symbols = {}
    relpath = None
    for parent in Path(path).resolve().parents:
        mapping = parent / "config" / "data_symbols.json"
        if mapping.is_file():
            try:
                value = json.loads(mapping.read_text())
                if isinstance(value, dict):
                    data_symbols = value
            except (OSError, ValueError):
                pass
            parts = Path(path).resolve().relative_to(parent).parts
            # Replays lint byte copies of the project's sources captured under
            # build/<capture>/; the copy's own layout is the relative path.
            if len(parts) > 2 and parts[0] == "build":
                relpath = Path(*parts[2:]).as_posix()
            else:
                relpath = Path(*parts).as_posix()
            break
    return check_text(text, os.path.basename(path), data_symbols, relpath)


def asm_allow_path():
    return os.environ.get("FFTA_ASM_ALLOW") or os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "asm_allow.json")


def asm_allowed(addr):
    """is this address on the maintainer's hand-asm allow list?

    The list exists so that a function which provably cannot come from
    plausible C can still be solved, by hand-written assembly, *by decision*
    rather than by an agent quietly hacking its way to a match.  Only the
    repository maintainer may add entries; nothing here writes the file.
    """
    path = asm_allow_path()
    if not addr:
        return None
    try:
        doc = json.load(open(path, encoding="utf-8"))
    except (OSError, ValueError):
        return None
    for entry in doc.get("entries", []):
        if str(entry.get("address", "")).upper() == str(addr).upper():
            return entry
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--strict", action="store_true",
                    help="treat suspect findings as errors too (default: "
                         "suspect findings also fail unless justified)")
    ap.add_argument("--addr", default=None,
                    help="the ROM address these sources implement, so the "
                         "hand-asm allow list can be consulted")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    total = 0
    all_findings = []
    for p in args.paths:
        files = sorted(
            str(q) for q in Path(p).rglob("*")
            if q.is_file() and q.suffix in (".c", ".h")) \
            if os.path.isdir(p) else [p]
        for f in files:
            findings = check_file(f)
            if not findings:
                continue
            total += len(findings)
            all_findings.extend(
                {"file": f, "line": l, "rule": r, "severity": s, "message": m}
                for l, r, s, m in findings)
            if not args.json:
                print(f"{f}:")
                for line, rid, sev, msg in findings:
                    print(f"  {os.path.basename(f)}:{line}: {sev.upper()}: {rid}")
                    print(f"      {msg}")

    allowed = asm_allowed(args.addr) if total else None
    if args.json:
        print(json.dumps({"findings": all_findings, "total": total,
                          "addr": args.addr,
                          "hand_asm_allowed": bool(allowed),
                          "allow_entry": allowed}, indent=2))
        return 1 if total else 0

    if total:
        print(f"\n{total} finding(s): the code does not look like something a "
              f"developer would have written", file=sys.stderr)
        print("A byte-identical compile is not a match if the source is "
              "implausible.", file=sys.stderr)
        if args.addr:
            if allowed:
                print(f"\n{args.addr} IS on the hand-asm allow list "
                      f"({allowed.get('reason', 'no reason recorded')}).",
                      file=sys.stderr)
                print("A match here is HAND-ASM, not a decompilation.",
                      file=sys.stderr)
            else:
                print(f"\n{args.addr} is NOT on the hand-asm allow list, so a "
                      f"match that needs hand asm is not acceptable here.",
                      file=sys.stderr)
                print("Park it and say so; only the maintainer may add an "
                      "entry to tools/asm_allow.json.", file=sys.stderr)
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main())
