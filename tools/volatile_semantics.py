"""Semantic check for allowlisted volatile objects (kit#90).

An allowlisted declaration (tools/volatile_allow.json) may qualify byte
bit-fields of one RAM object as volatile, because the ROM shows the
qualifier's effect: a dead `ldrb` of the byte before every `strb` to it.
That alone does not stop a source from using the qualifier to plant code: a
statement such as `(sym.x, 0);`, `if (sym.x) ;`, an unused local or
`sym.x |= 0;` emits loads under the qualifier that an ordinary declaration
would not.

So match.py compiles the source twice: as written ("real") and with
`volatile` removed from exactly the pinned declaration in the preprocessed
text ("stripped").  The two function bodies are then compared here.  A
textual diff is not enough: removing the qualifier also changes register
allocation and address arithmetic, and a chained `a = (b = v)` re-reads `b`.
The comparison is therefore value-level: both bodies are executed
symbolically along every path, and the check requires

1. the same observable behaviour on every path: the same stores to
   non-stack memory with the same values, in the same order, the same calls
   with the same arguments, the same branch conditions and, for a non-void
   function, the same return value.  Memory is modelled as ordinary memory
   for both compiles, so this says the qualifier changed nothing that the
   program computes.  When a stack address escapes (a call argument or a
   stored value), every local frame byte, with the stores applied in order,
   joins the behaviour (incoming-argument slots included).  Every callee
   needs a file-scope prototype with a fixed list of one-word arguments;
   no prototype, `()`, `...`, indirect calls and wider arguments fail
   closed.  A call reads only the argument registers its prototype names
   when that prototype agrees with the callee's own matched definition in
   src/; any other prototype could lie, so then all of r0-r3 count as read;
2. every access to the object to be `symbol + constant` inside it; variable
   offsets, out-of-object offsets, multi-register transfers and the
   object's address reaching a call argument or a stored value fail closed;
3. every load of the object in the real compile to be one of
   * a read-modify-write load: an `ldrb` of a pinned byte whose destination
     is overwritten before any use, followed by its `strb` to the same byte
     with only immediate moves and copies or literal loads into the store's
     operand registers in between (read_modify_write_store);
   * a chained re-read for `a = (b = v)`: the forwarding `strb` is the
     immediately preceding memory access and the value feeds, through copies
     only, the next store, an `strb` to a pinned byte (chained_reread);
   * a counterpart of the stripped compile's loads of the object, matched
     in order with the same address and width;
4. every store overlapping a pinned byte to be an `strb` of exactly that
   byte with its own read-modify-write load;
5. no store to write back the value just loaded from the same byte (an
   `ldrb`/`strb` self-assignment, `sym.x = sym.x` or `sym.x |= 0`).

plausible.py makes the paired store a volatile lvalue: a pinned byte can be
reached only through its member, since array members take only in-bounds
literal subscripts and no `&` may precede the symbol.  compare() repeats
those token rules (plausible.member_provenance) on the preprocessed text, so
macros cannot spell around them.  This check alone
cannot tell `(void)sym.x; *(sym.array + k) = v;` from `sym.x = v;`; they
compile identically.

A planted read therefore either vanishes from the stripped compile, so the
real compile has a load the rules cannot explain, or it stays, which shows
the qualifier did not produce it; then it is ordinary code that the stripped
compile emits too.  Anything the symbolic executor does not model - ARM
code, computed jumps, symbolic loops beyond the path bound, unknown
instructions - fails closed with a reason.

Known limits (false refusals, never false acceptance of a qualifier
effect): reading a pinned byte twice where an ordinary declaration would
reuse the first value (`if (x) ...; if (x) ...`) is refused, as are loops
whose exit depends on unknown values, stripped compiles that legally reorder
accesses around a pinned one, and equivalent code that the expression
normaliser cannot prove equal.
"""

import re

from plausible import declaration_tokens

MASK = 0xFFFFFFFF
SP = ("sp",)
MAX_PATHS = 256
MAX_STEPS = 20000
MAX_DECISIONS = 32
RUNTIME_ARITY = {"__divsi3": 2, "__udivsi3": 2, "__modsi3": 2, "__umodsi3": 2}
TYPE_SIZES = {"u8": 1, "s8": 1, "char": 1, "vu8": 1, "vs8": 1,
              "u16": 2, "s16": 2, "short": 2, "vu16": 2, "vs16": 2,
              "u32": 4, "s32": 4, "int": 4, "long": 4, "vu32": 4, "vs32": 4,
              "bool8": 1, "bool32": 4}
REGISTER_ALIASES = {"sb": "r9", "sl": "r10", "fp": "r11", "ip": "r12"}
INVERSE = {"eq": "ne", "ne": "eq", "cs": "cc", "cc": "cs", "hs": "lo", "lo": "hs",
           "mi": "pl", "pl": "mi", "vs": "vc", "vc": "vs", "hi": "ls", "ls": "hi",
           "ge": "lt", "lt": "ge", "gt": "le", "le": "gt"}


class SemanticError(ValueError):
    """the real and stripped compiles differ in a way the rules do not permit"""


# ---------------------------------------------------------------- declaration

def object_layout(declaration):
    """(object size, {offset of each volatile byte}) of the pinned declaration.

    The allow list restricts the declaration to plain members `T name;`,
    `T name[N];`, `T *name;` and full-width bit-fields `volatile T name : W;`
    of known integer types; anything else fails closed.
    """
    tokens = declaration_tokens(declaration)
    if tokens[:3] != ["extern", "struct", "{"] or tokens[-3:-2] != ["}"] or tokens[-1] != ";":
        raise SemanticError("pinned declaration is not `extern struct { ... } symbol;`")
    body, members, current = tokens[3:-3], [], []
    for token in body:
        if token == ";":
            members.append(current)
            current = []
        else:
            current.append(token)
    if current:
        raise SemanticError("pinned declaration has an unterminated member")
    offset, align, pinned = 0, 1, set()
    for member in members:
        qualified = member[:1] == ["volatile"]
        member = member[1:] if qualified else member
        if not member or member[0] not in TYPE_SIZES:
            raise SemanticError(f"pinned declaration member `{' '.join(member)}` has an unknown type")
        size, rest = TYPE_SIZES[member[0]], member[1:]
        if rest[:1] == ["*"]:
            size, rest = 4, rest[1:]
        count = 1
        if len(rest) == 4 and rest[1] == "[" and rest[3] == "]":
            count, rest = int(rest[2], 0), rest[:1]
        elif len(rest) == 3 and rest[1] == ":":
            if int(rest[2], 0) != 8 * size:
                raise SemanticError("only full-width bit-fields can be modelled")
            rest = rest[:1]
        if len(rest) != 1 or not re.fullmatch(r"[A-Za-z_]\w*", rest[0]):
            raise SemanticError(f"pinned declaration member `{' '.join(member)}` is not plain")
        offset = (offset + size - 1) // size * size
        align = max(align, size)
        if qualified:
            if size != 1 or count != 1:
                raise SemanticError("only volatile byte members can be modelled")
            pinned.add(offset)
        offset += size * count
    return (offset + align - 1) // align * align, pinned


def strip_pinned_volatile(preprocessed, declaration):
    """the preprocessed text with `volatile` removed from the pinned declaration only.

    The declaration's tokens must occur exactly once (the preprocessor-bypass
    rules in plausible.py keep macros, pasting and computed includes from
    changing them); otherwise the stripping cannot be trusted.
    """
    pattern = r"\s*".join(r"\b" + re.escape(token) + r"\b" if re.match(r"\w", token)
                          else re.escape(token) for token in declaration_tokens(declaration))
    found = list(re.finditer(pattern, preprocessed))
    if len(found) != 1:
        raise SemanticError(f"the pinned declaration occurs {len(found)} times in the preprocessed "
                            "source; it must occur exactly once to be stripped")
    start, end = found[0].span()
    body = re.sub(r"\bvolatile\b", lambda match: " " * len(match[0]), preprocessed[start:end])
    return preprocessed[:start] + body + preprocessed[end:]


SCALAR_TYPES = {"u8", "s8", "u16", "s16", "u32", "s32", "vu8", "vs8", "vu16", "vs16", "vu32",
                "vs32", "bool8", "bool16", "bool32", "int", "char", "short", "long", "unsigned",
                "signed", "float"}
QUALIFIERS = {"const", "volatile", "register", "extern", "static", "inline", "__inline__"}


def file_scope(preprocessed):
    """file-scope text: directives and linemarkers dropped, brace bodies folded to `;`"""
    text = re.sub(r"(?m)^[ \t]*#.*$", ";", preprocessed)
    while True:
        folded = re.sub(r"\{[^{}]*\}", ";", text)
        if folded == text:
            return text
        text = folded


def argument_words(declaration):
    """argument words of one parameter or return type, or None if not one word"""
    tokens = [t for t in re.findall(r"[A-Za-z_]\w*|\*|\S", declaration) if t not in QUALIFIERS]
    if "*" in tokens:
        return 1 if "(" not in tokens and "[" not in tokens else None
    names = [t for t in tokens if re.fullmatch(r"[A-Za-z_]\w*", t)]
    types = [t for t in names if t in SCALAR_TYPES]
    if not types or types.count("long") > 1 or len(names) - len(types) > 1:
        return None
    return 1


def function_signature(scope, name):
    """(returns a value, argument words or None) for a name.

    Every file-scope declaration or definition must agree.  The argument
    count is None (unknown) without a prototype, for `()` or `...`; a
    parameter or return value that is not a scalar or pointer of one word
    fails closed.
    """
    found = set()
    for match in re.finditer(r"(?:^|;)([^;]*?)\b" + re.escape(name) + r"\s*\(([^;]*?)\)\s*(?=;)", scope):
        prefix, parameters = match[1], match[2].strip()
        if "(" in parameters or ")" in parameters or "(" in prefix:
            raise SemanticError(f"the declaration of {name} is too complex to read its signature")
        returns = prefix.split() and [t for t in prefix.split() if t not in QUALIFIERS] != ["void"]
        if returns and argument_words(prefix) is None:
            raise SemanticError(f"{name} returns a value that is not one scalar or pointer word")
        if parameters == "void":
            arity = 0
        elif not parameters or "..." in parameters:
            arity = None
        else:
            words = [argument_words(parameter) for parameter in parameters.split(",")]
            if None in words:
                raise SemanticError(f"a parameter of {name} is not one scalar or pointer word")
            arity = sum(words)
        found.add((bool(returns), arity))
    if len(found) > 1:
        raise SemanticError(f"the file-scope declarations of {name} disagree")
    return found.pop() if found else (True, None)


# ---------------------------------------------------------------- expressions

def contains(expression, atom):
    """does atom occur anywhere in expression, including linear terms?"""
    if expression == atom:
        return True
    if not isinstance(expression, tuple):
        return False
    if expression[0] == "lin":
        return any(contains(term, atom) for term, _ in expression[2])
    return any(contains(part, atom) for part in expression[1:])


def carries(value, atom):
    """does value compute with atom as an address?  A load's value is the
    memory's content, not its address, so loads are not searched."""
    if value == atom:
        return True
    if not isinstance(value, tuple) or value[0] == "load":
        return False
    if value[0] == "lin":
        return any(carries(term, atom) for term, _ in value[2])
    return any(carries(part, atom) for part in value[1:])


def linear(expression):
    """(constant, {term: coefficient}) of an expression"""
    if isinstance(expression, int):
        return expression & MASK, {}
    if expression[0] == "lin":
        return expression[1], dict(expression[2])
    return 0, {expression: 1}


def make_linear(constant, terms):
    terms = {term: coefficient & MASK for term, coefficient in terms.items() if coefficient & MASK}
    constant &= MASK
    if not terms:
        return constant
    if constant == 0 and len(terms) == 1 and next(iter(terms.values())) == 1:
        return next(iter(terms))
    return ("lin", constant, tuple(sorted(terms.items(), key=repr)))


def add(a, b, sign=1):
    ca, ta = linear(a)
    cb, tb = linear(b)
    for term, coefficient in tb.items():
        ta[term] = ta.get(term, 0) + sign * coefficient
    return make_linear(ca + sign * cb, ta)


def scale(a, factor):
    constant, terms = linear(a)
    return make_linear(constant * factor, {term: c * factor for term, c in terms.items()})


def operation(name, a, b):
    if isinstance(a, int) and isinstance(b, int):
        return {"and": a & b, "orr": a | b, "eor": a ^ b, "mul": a * b}[name] & MASK
    if name == "mul":
        if isinstance(a, int) or isinstance(b, int):
            return scale(b, a) if isinstance(a, int) else scale(a, b)
    elif isinstance(b, int) or isinstance(a, int):
        constant, other = (a, b) if isinstance(a, int) else (b, a)
        if name == "and" and constant == 0:
            return 0
        if (name == "and" and constant == MASK) or (name in ("orr", "eor") and constant == 0):
            return other
        if name == "and" and is_zero_extended(other, constant):
            return other
    elif a == b:
        return 0 if name == "eor" else a
    return (name,) + tuple(sorted((a, b), key=repr))


def is_zero_extended(value, mask):
    widths = {0xFF: 8, 0xFFFF: 16}
    if mask not in widths or not isinstance(value, tuple):
        return False
    if value[0] == "load" and value[1] * 8 <= widths[mask]:
        return True
    return value[0] == "trunc" and value[1] <= widths[mask]


def shift(name, value, amount):
    if not isinstance(amount, int):
        return (name, value, amount)
    amount &= 0xFF
    if amount == 0:
        return value
    if isinstance(value, int):
        if name == "lsl":
            return (value << amount) & MASK if amount < 32 else 0
        if name == "lsr":
            return value >> amount if amount < 32 else 0
        if name == "asr":
            signed = value - (1 << 32) if value & 0x80000000 else value
            return (signed >> min(amount, 31)) & MASK
        amount %= 32
        return ((value >> amount) | (value << (32 - amount))) & MASK
    if name == "lsl":
        return scale(value, 1 << amount) if amount < 32 else 0
    return (name, value, amount)


def truncate(value, bits):
    if bits == 32:
        return value
    if isinstance(value, int):
        return value & ((1 << bits) - 1)
    if is_zero_extended(value, (1 << bits) - 1):
        return value
    if isinstance(value, tuple) and value[0] == "trunc" and value[1] >= bits:
        return ("trunc", bits, value[2])
    return ("trunc", bits, value)


def sign_extend(value, bits):
    if isinstance(value, int):
        value &= (1 << bits) - 1
        return (value - (1 << bits)) & MASK if value >> (bits - 1) else value
    return ("sext", bits, value)


def show(value):
    if isinstance(value, int):
        return hex(value)
    if value == SP:
        return "sp"
    if value[0] == "sym":
        return value[1]
    if value[0] == "lin":
        parts = [show(term) if coefficient == 1 else f"{show(term)}*{hex(coefficient)}"
                 for term, coefficient in value[2]]
        return "(" + " + ".join(parts + ([hex(value[1])] if value[1] else [])) + ")"
    return value[0] + "(" + ", ".join(show(part) if isinstance(part, (int, tuple)) else str(part)
                                      for part in value[1:]) + ")"


# ---------------------------------------------------------------- assembly

def split_operands(text):
    parts, depth, current = [], 0, ""
    for character in text:
        if character in "[{":
            depth += 1
        elif character in "]}":
            depth -= 1
        if character == "," and depth == 0:
            parts.append(current.strip())
            current = ""
        else:
            current += character
    if current.strip():
        parts.append(current.strip())
    return parts


def parse_word(text):
    text = text.strip()
    if re.fullmatch(r"-?(?:0[xX][0-9A-Fa-f]+|[0-9]+)", text):
        return int(text, 0) & MASK
    found = re.fullmatch(r"([A-Za-z_.$][\w.$]*)\s*(?:([+-])\s*(0[xX][0-9A-Fa-f]+|[0-9]+))?", text)
    if found is None:
        raise SemanticError(f"unsupported literal word `{text}`")
    if found[1].startswith(".L"):
        return ("code", found[1])
    offset = int(found[3], 0) * (-1 if found[2] == "-" else 1) if found[3] else 0
    return make_linear(offset, {("sym", found[1]): 1})


def parse_assembly(text):
    """({function name: (instructions, labels, pools)}, lines outside functions)

    instructions are (mnemonic, operands, text); labels map a code label to
    the index of the next instruction; pools map a label to the `.word`
    values from it to the next instruction or directive.
    """
    functions, outside, current, thumb_func, name = {}, [], None, False, None
    for raw in text.splitlines():
        line = raw.split("@", 1)[0].strip()
        if not line:
            continue
        if re.match(r"\.(?:code\s+32|arm)\b", line):
            raise SemanticError("ARM-mode code is not modelled")
        label = re.fullmatch(r"([A-Za-z_.$][\w.$]*):", line)
        if current is None:
            if label and thumb_func:
                if label[1] in functions:
                    raise SemanticError(f"function {label[1]} is defined twice")
                name, thumb_func, pending, owners = label[1], False, [], []
                current = functions[name] = ([], {}, {})
                continue
            if line == ".thumb_func":
                thumb_func = True
            outside.append(re.sub(r"\s+", " ", line))
            continue
        instructions, labels, pools = current
        if re.match(r"\.size\s+" + re.escape(name) + r"\s*,", line):
            current = None
            outside.append(re.sub(r"\s+", " ", line))
            continue
        if label:
            pending.append(label[1])
            labels[label[1]] = len(instructions)
            continue
        if line.startswith(".word"):
            for owner in pending:
                pools[owner] = []
            owners, pending = owners + pending, []
            if not owners:
                raise SemanticError("literal word without a label")
            word = parse_word(line[len(".word"):])
            for owner in owners:
                pools[owner].append(word)
            continue
        pending, owners = [], []
        if line.startswith("."):
            if not re.match(r"\.(?:align|pool|ltorg)\b", line):
                raise SemanticError(f"unsupported directive inside a function: `{line}`")
            continue
        mnemonic, _, operands = re.sub(r"\s+", " ", line).partition(" ")
        instructions.append((mnemonic.lower(), split_operands(operands), line))
    if current is not None:
        raise SemanticError("unterminated function in the compiler output")
    return functions, outside


# ---------------------------------------------------------------- execution

class NeedDecision(Exception):
    pass


class Record:
    """one executed instruction, for the dataflow rules"""

    def __init__(self, index, text, kind="alu", reads=(), writes=(), **fields):
        self.index, self.text, self.kind = index, text, kind
        self.reads, self.writes = set(reads), set(writes)
        self.address = self.width = self.value_register = None
        self.signed = self.forwarded = self.copy = self.constant = self.self_assignment = False
        self.guarded = set()
        self.__dict__.update(fields)


class Path:
    def __init__(self, decisions, conditions, trace, records):
        self.decisions, self.conditions = decisions, conditions
        self.trace, self.records = trace, records


def register(operand):
    operand = REGISTER_ALIASES.get(operand.lower(), operand.lower())
    if re.fullmatch(r"r(?:[0-9]|1[0-2])|sp|lr|pc", operand):
        return operand
    return None


def immediate(operand):
    found = re.fullmatch(r"#\s*(-?(?:0[xX][0-9A-Fa-f]+|[0-9]+))", operand.strip())
    return int(found[1], 0) & MASK if found else None


def register_list(operand):
    found = re.fullmatch(r"\{([^{}]*)\}", operand.strip())
    if found is None:
        raise SemanticError(f"unsupported register list `{operand}`")
    names = []
    for part in found[1].split(","):
        part = part.strip()
        bounds = re.fullmatch(r"r([0-7])\s*-\s*r([0-7])", part)
        if bounds:
            names += [f"r{n}" for n in range(int(bounds[1]), int(bounds[2]) + 1)]
        elif register(part):
            names.append(register(part))
        else:
            raise SemanticError(f"unsupported register list `{operand}`")
    order = [f"r{n}" for n in range(13)] + ["sp", "lr", "pc"]
    return sorted(set(names), key=order.index)


def is_stack(address):
    return set(linear(address)[1]) == {SP} and linear(address)[1][SP] == 1


def global_symbol(address):
    terms = linear(address)[1]
    if len(terms) == 1:
        (term, coefficient), = terms.items()
        if coefficient == 1 and isinstance(term, tuple) and term[0] == "sym":
            return term[1]
    return None


def signed32(value):
    return value - (1 << 32) if value & 0x80000000 else value


def evaluate(code, flags):
    """True/False when the flags decide the condition, else None"""
    kind, n, z, c, v = flags[0], None, None, None, None
    if kind == "cmp" and flags[1] == flags[2]:
        n, z, c, v = False, True, True, False
    elif kind in ("cmp", "cmn") and isinstance(flags[1], int) and isinstance(flags[2], int):
        a, b = flags[1], flags[2]
        if kind == "cmp":
            result = (a - b) & MASK
            c, v = a >= b, bool(((a ^ b) & (a ^ result)) >> 31)
        else:
            result = (a + b) & MASK
            c, v = a + b > MASK, bool((~(a ^ b) & (a ^ result) & MASK) >> 31)
        n, z = bool(result >> 31), result == 0
    elif kind == "nz" and isinstance(flags[1], int):
        n, z = bool(flags[1] >> 31), flags[1] == 0
    else:
        return None

    def negate(value):
        return None if value is None else not value

    def both(a, b):
        return None if a is None or b is None else a and b

    table = {"eq": z, "ne": negate(z), "mi": n, "pl": negate(n), "cs": c, "hs": c,
             "cc": negate(c), "lo": negate(c), "vs": v, "vc": negate(v),
             "hi": both(c, negate(z)), "ls": negate(both(c, negate(z))),
             "ge": None if v is None else n == v, "lt": None if v is None else n != v,
             "gt": None if v is None else both(negate(z), n == v),
             "le": None if v is None else negate(both(negate(z), n == v))}
    return table.get(code)


class Executor:
    """symbolic execution of one agbcc Thumb function along one path"""

    def __init__(self, name, function, signatures, label, layout, definitions=None):
        self.name, self.label = name, label
        self.instructions, self.labels, self.pools = function
        self.signatures = signatures
        self.definitions = definitions or {}
        self.symbol, self.size = layout

    def check_address(self, address, width, text, multiple=False):
        """fail closed unless an access to the object is `symbol + constant` inside it"""
        atom = ("sym", self.symbol)
        if not contains(address, atom):
            return
        constant, terms = linear(address)
        if multiple:
            self.fail(text, f"a multi-register transfer touches {self.symbol}")
        if terms != {atom: 1}:
            self.fail(text, f"the address {show(address)} combines {self.symbol} with other "
                      "terms; only constant member offsets are modelled")
        offset = signed32(constant)
        if offset < 0 or offset + width > self.size:
            self.fail(text, f"the access at {self.symbol}{offset:+#x} lies outside the object")

    def fail(self, record_text, message):
        where = f" at `{record_text}`" if record_text else ""
        raise SemanticError(f"{self.label} compile of {self.name}: {message}{where}")

    def value(self, operand, text):
        name = register(operand)
        if name == "pc":
            self.fail(text, "pc-relative arithmetic is not modelled")
        if name:
            return self.regs[name]
        constant = immediate(operand)
        if constant is None:
            self.fail(text, f"unsupported operand `{operand}`")
        return constant

    def target(self, operand, text):
        if operand not in self.labels:
            self.fail(text, f"branch to unknown label `{operand}`")
        return self.labels[operand]

    def run(self, decisions):
        self.regs = {f"r{n}": (("arg", n) if n < 4 else ("entry", f"r{n}")) for n in range(13)}
        self.regs.update(sp=SP, lr=("entry", "lr"))
        self.flags = ("entry",)
        self.memory, self.trace, self.records = [], [], []
        self.escaped, self.known, self.conditions = False, {}, []
        self.frame_base = None
        self.decisions = list(decisions)
        pc, steps = 0, 0
        while True:
            steps += 1
            if steps > MAX_STEPS:
                raise SemanticError(f"{self.label} compile of {self.name}: path exceeds {MAX_STEPS} "
                                    "instructions (loops with unknown exit conditions are not modelled)")
            if pc >= len(self.instructions):
                raise SemanticError(f"{self.label} compile of {self.name}: execution runs off the end")
            result = self.step(pc, *self.instructions[pc])
            if result == "return":
                return Path(list(decisions), self.conditions, self.trace, self.records)
            pc = pc + 1 if result is None else result

    def decide(self, code, text):
        condition = (code, self.flags)
        known = evaluate(code, self.flags)
        if known is not None:
            return known
        if condition in self.known:
            return self.known[condition]
        if (INVERSE[code], self.flags) in self.known:
            return not self.known[(INVERSE[code], self.flags)]
        if len(self.conditions) >= len(self.decisions):
            if len(self.decisions) >= MAX_DECISIONS:
                raise SemanticError(f"{self.label} compile of {self.name}: more than {MAX_DECISIONS} "
                                    "unknown branch conditions on one path (loops with unknown exit "
                                    "conditions are not modelled)")
            raise NeedDecision()
        taken = self.decisions[len(self.conditions)]
        self.conditions.append(condition)
        self.known[condition] = taken
        return taken

    # memory ---------------------------------------------------------------

    def relation(self, a, width_a, b, width_b, private=False):
        ca, ta = linear(a)
        cb, tb = linear(b)
        if ta == tb:
            distance = signed32((ca - cb) & MASK)
            if distance == 0 and width_a == width_b:
                return "same"
            if distance >= width_b or -distance >= width_a:
                return "disjoint"
            return "overlap"
        if is_stack(a) != is_stack(b) and (not self.escaped or private):
            return "disjoint"
        ga, gb = global_symbol(a), global_symbol(b)
        if ga and gb and ga != gb:
            return "disjoint"
        return "overlap"

    def load(self, width, signed, address, text):
        # Saved-register slots stay private even after the frame escapes:
        # the escaping pointer addresses locals, not the push area.
        saved = is_stack(address) and any(entry[0] == "store" and entry[5] and entry[2] == address
                                          for entry in self.memory)
        stack = is_stack(address) and (not self.escaped or saved)
        version, forwarded = "entry", None
        for entry in reversed(self.memory):
            if entry[0] == "call":
                if not stack:
                    version = ("call", entry[1])
                    break
                continue
            _, stored_width, stored_address, stored, event, _ = entry
            relation = self.relation(address, width, stored_address, stored_width, saved)
            if relation == "same":
                forwarded = stored
                break
            if relation == "overlap":
                if event is None:
                    self.fail(text, "partially overlapping stack access")
                version = ("store", event)
                break
        if forwarded is not None:
            value = forwarded
        else:
            value = ("load", width, self.observed(address), version)
        if signed:
            value = sign_extend(value, width * 8)
        return value, forwarded is not None

    def current(self, width, address):
        return self.load(width, False, address, "")[0]

    def observed(self, address):
        """an address as the trace records it: escaped stack slots relative to the escape"""
        if is_stack(address) and self.frame_base is not None:
            return ("frame", signed32(linear(address)[0]) - self.frame_base)
        return address

    def escape(self, values, text):
        """the frame becomes visible to other code through a pointer in values.

        The contents of every local (non-saved) frame byte at that moment
        join the trace, relative to the first escaping pointer, with the
        stores applied byte by byte in program order; each escape takes a
        new snapshot.  So two compiles cannot hand over different stack data,
        on either side of the pointer.  From then on stack stores are
        observable and calls may change the frame.
        """
        pointers = [value for value in values if carries(value, SP)]
        if not pointers:
            return
        for pointer in pointers:
            if not is_stack(pointer):
                self.fail(text, f"a stack address escapes as {show(pointer)}")
        if self.frame_base is None:
            self.frame_base = min(signed32(linear(pointer)[0]) for pointer in pointers)
        self.escaped = True
        frame = {}
        for entry in self.memory:
            if entry[0] != "store" or not is_stack(entry[2]) or entry[5]:
                continue
            offset, width, value = signed32(linear(entry[2])[0]), entry[1], entry[3]
            for byte in range(width):
                if width == 1:
                    part = value
                elif isinstance(value, int):
                    part = (value >> (8 * byte)) & 0xFF
                else:
                    part = ("byte", byte, value)
                frame[offset + byte - self.frame_base] = part
        self.trace.append(("escape", tuple(sorted(frame.items()))))

    def store(self, width, address, value, saved=False, text=""):
        value = truncate(value, width * 8)
        if carries(value, ("sym", self.symbol)):
            self.fail(text, f"the address of {self.symbol} is stored to memory")
        event = None
        if not is_stack(address):
            self.escape([value], text)
        if not is_stack(address) or self.escaped:
            event = len(self.trace)
            self.trace.append(("store", width, self.observed(address), value))
        self.memory.append(("store", width, address, value, event, saved))
        return value

    def call(self, target, text, record):
        if isinstance(target, str) and target in RUNTIME_ARITY:
            count, trusted = RUNTIME_ARITY[target], True
        elif isinstance(target, tuple) and target[0] == "swi":
            count, trusted = 4, False        # BIOS calls take r0-r3 only
        elif isinstance(target, str) and self.signatures.get(target, (None, None))[1] is not None:
            count = self.signatures[target][1]
            trusted = self.definitions.get(target) == self.signatures[target]
        else:
            self.fail(text, "the callee has no prototype with a fixed argument list, so its "
                      "arguments cannot be compared")
        arguments = [self.regs[f"r{n}"] for n in range(min(count, 4))]
        for n in range(4, count):
            arguments.append(self.load(4, False, add(self.regs["sp"], 4 * (n - 4)), text)[0])
        # A call reads the argument registers its prototype names only when
        # that prototype agrees with the callee's own matched definition in
        # src/: any other prototype could lie, and a dead load into an
        # unnamed argument register could then be a hidden argument, so every
        # argument register counts as read.
        named = {f"r{n}" for n in range(min(count, 4))}
        record.guarded = set() if trusted else {"r0", "r1", "r2", "r3"} - named
        record.reads = named | record.guarded | (record.reads - {"r0", "r1", "r2", "r3"})
        if any(carries(argument, ("sym", self.symbol)) for argument in arguments):
            self.fail(text, f"the address of {self.symbol} is passed to a call")
        self.escape(arguments, text)
        event = len(self.trace)
        self.trace.append(("call", target, tuple(arguments)))
        self.memory.append(("call", event))
        self.regs["r0"] = ("ret", event)
        for name in ("r1", "r2", "r3", "r12", "lr"):
            self.regs[name] = ("clobber", event, name)
        self.flags = ("clobber", event)
        self.records.append(record)

    def finish(self, text, record):
        returns = self.signatures.get(self.name, (True,))[0]
        if self.regs["sp"] != SP:
            self.fail(text, "the stack is not balanced at return")
        self.trace.append(("return",) + ((self.regs["r0"],) if returns else ()))
        if returns:
            record.reads.add("r0")
        self.records.append(record)
        return "return"

    # instructions ---------------------------------------------------------

    def memory_operand(self, operand, text):
        found = re.fullmatch(r"\[\s*([^,\]]+?)\s*(?:,\s*([^\]]+?)\s*)?\]", operand)
        if found is None:
            self.fail(text, f"unsupported memory operand `{operand}`")
        base = register(found[1])
        if base is None or base == "pc":
            self.fail(text, f"unsupported base register `{found[1]}`")
        reads = {base}
        offset = 0
        if found[2]:
            index = register(found[2])
            if index:
                reads.add(index)
            offset = self.value(found[2], text)
        return add(self.regs[base], offset), reads

    def step(self, pc, mnemonic, operands, text):
        record = Record(pc, text)
        alu = ("mov", "add", "sub", "neg", "mvn", "and", "orr", "eor", "bic", "mul",
               "lsl", "lsr", "asr", "ror")
        if mnemonic.endswith("s") and mnemonic[:-1] in alu:
            mnemonic = mnemonic[:-1]      # unified syntax spells the flag-setting forms `adds`
        regs = self.regs
        if mnemonic in alu:
            destination = register(operands[0]) if operands else None
            if destination is None or destination == "pc" or len(operands) not in (2, 3):
                if mnemonic == "mov" and destination == "pc" and len(operands) == 2:
                    return self.jump_register(operands[1], text, record)
                self.fail(text, "unsupported instruction form")
            # two-operand forms read their destination: `orr rd, rm` is rd = rd | rm
            sources = operands[1:] if len(operands) == 3 or mnemonic in ("mov", "neg", "mvn") else operands
            record.reads = {register(o) for o in sources if register(o)}
            record.writes = {destination}
            values = [self.value(o, text) for o in sources]
            sets_flags = destination not in ("sp",) and not any(register(o) in ("sp",) for o in sources)
            if mnemonic == "mov":
                result = values[0]
                record.copy = register(sources[0]) is not None
                low = [f"r{n}" for n in range(8)]
                if immediate(sources[0]) is not None:
                    self.flags = ("nz", result)
                    record.constant = True
                elif destination in low and register(sources[0]) in low:
                    # a low-register `mov` assembles as `adds rd, rm, #0`
                    self.flags = ("cmn", result, 0)
            elif mnemonic in ("add", "sub"):
                sign = 1 if mnemonic == "add" else -1
                result = add(values[0], values[1], sign)
                record.copy = mnemonic == "add" and values[1] == 0 and register(sources[0]) is not None \
                    and immediate(sources[1]) is not None
                high = len(operands) == 2 and register(operands[1]) and \
                    (destination not in [f"r{n}" for n in range(8)] or
                     register(operands[1]) not in [f"r{n}" for n in range(8)])
                if sets_flags and not high:
                    self.flags = ("cmp", values[0], values[1]) if sign < 0 else ("cmn", values[0], values[1])
            elif mnemonic == "neg":
                result = scale(values[0], -1)
                self.flags = ("cmp", 0, values[0])
            elif mnemonic == "mvn":
                result = add(scale(values[0], -1), 1, -1)
                self.flags = ("nz", result)
            elif mnemonic in ("lsl", "lsr", "asr", "ror"):
                amount = values[1]
                if not isinstance(amount, int):
                    amount = operation("and", amount, 0xFF)
                result = shift(mnemonic, values[0], amount)
                self.flags = ("shift", mnemonic, values[0], amount)
            else:
                b = values[1]
                if mnemonic == "bic":
                    b = add(scale(b, -1), 1, -1)
                result = operation({"bic": "and"}.get(mnemonic, mnemonic), values[0], b)
                self.flags = ("nz", result)
            regs[destination] = result
            self.records.append(record)
            return None
        if mnemonic in ("cmp", "cmn", "tst"):
            if len(operands) != 2:
                self.fail(text, "unsupported instruction form")
            record.reads = {register(o) for o in operands if register(o)}
            a, b = self.value(operands[0], text), self.value(operands[1], text)
            self.flags = ("nz", operation("and", a, b)) if mnemonic == "tst" else (mnemonic, a, b)
            self.records.append(record)
            return None
        if mnemonic in ("ldr", "ldrb", "ldrh", "ldrsb", "ldrsh", "str", "strb", "strh"):
            if len(operands) != 2 or register(operands[0]) in (None, "pc"):
                self.fail(text, "unsupported instruction form")
            subject = register(operands[0])
            width = 1 if mnemonic.endswith("b") else 2 if mnemonic.endswith("h") else 4
            pool = re.fullmatch(r"(\.L\w+)(?:\s*\+\s*([0-9]+))?", operands[1])
            if pool and mnemonic == "ldr":
                words = self.pools.get(pool[1])
                offset = int(pool[2] or 0)
                if words is None or offset % 4 or offset // 4 >= len(words):
                    self.fail(text, "literal load outside a pool")
                record.kind, record.writes = "literal", {subject}
                regs[subject] = words[offset // 4]
                self.records.append(record)
                return None
            address, reads = self.memory_operand(operands[1], text)
            self.check_address(address, width, text)
            record.address, record.width = address, width
            if mnemonic.startswith("ldr"):
                record.kind, record.reads, record.writes = "load", reads, {subject}
                record.signed = mnemonic in ("ldrsb", "ldrsh")
                regs[subject], record.forwarded = self.load(width, record.signed, address, text)
                record.value = regs[subject]
            else:
                record.kind, record.reads, record.value_register = "store", reads | {subject}, subject
                value = truncate(regs[subject], width * 8)
                record.self_assignment = isinstance(value, tuple) and value[0] == "load" and \
                    value == self.current(width, address)
                record.value = self.store(width, address, regs[subject], text=text)
            self.records.append(record)
            return None
        if mnemonic in ("push", "stmia", "stm", "pop", "ldmia", "ldm"):
            if mnemonic in ("push", "pop"):
                if len(operands) != 1:
                    self.fail(text, "unsupported instruction form")
                base, names, writeback = "sp", register_list(operands[0]), True
            else:
                if len(operands) != 2 or not operands[0].endswith("!"):
                    self.fail(text, "unsupported instruction form")
                base, names, writeback = register(operands[0][:-1]), register_list(operands[1]), True
                if base is None or base in ("sp", "pc"):
                    self.fail(text, "unsupported base register")
            storing = mnemonic in ("push", "stmia", "stm")
            start = add(regs[base], -4 * len(names)) if mnemonic == "push" else regs[base]
            record.kind = "push" if storing else "pop"
            record.reads = {base} | (set(names) if storing else set())
            record.writes = {base} | (set() if storing else set(names) - {"pc"})
            loaded = {}
            for n, name in enumerate(names):
                address = add(start, 4 * n)
                self.check_address(address, 4, text, multiple=True)
                if storing:
                    self.store(4, address, regs[name], saved=mnemonic == "push", text=text)
                else:
                    loaded[name] = self.load(4, False, address, text)[0]
            if writeback:
                regs[base] = start if mnemonic == "push" else add(regs[base], 4 * len(names))
            for name, value in loaded.items():
                if name != "pc":
                    regs[name] = value
            if "pc" in loaded:
                if loaded["pc"] != ("entry", "lr"):
                    self.fail(text, "pop into pc of something other than the return address")
                return self.finish(text, record)
            self.records.append(record)
            return None
        if mnemonic == "b" or (mnemonic[:1] == "b" and mnemonic[1:] in INVERSE):
            if len(operands) != 1:
                self.fail(text, "unsupported branch form")
            record.kind = "branch"
            self.records.append(record)
            if mnemonic == "b" or self.decide(mnemonic[1:], text):
                return self.target(operands[0], text)
            return None
        if mnemonic == "bl":
            if len(operands) != 1:
                self.fail(text, "unsupported call form")
            record.kind = "call"
            record.reads, record.writes = {"r0", "r1", "r2", "r3"}, {"r0", "r1", "r2", "r3", "r12", "lr"}
            via = re.fullmatch(r"_call_via_(r[0-9]|r1[0-2]|ip|fp|sl|sb|lr)", operands[0])
            target = operands[0]
            if via:
                name = register(via[1])
                record.reads.add(name)
                target = ("via", regs[name])
            self.call(target, text, record)
            return None
        if mnemonic == "bx":
            if len(operands) != 1:
                self.fail(text, "unsupported instruction form")
            return self.jump_register(operands[0], text, record)
        if mnemonic in ("swi", "svc"):
            record.kind = "call"
            record.reads, record.writes = {"r0", "r1", "r2", "r3"}, {"r0", "r1", "r2", "r3", "r12", "lr"}
            self.call(("swi", operands[0] if operands else ""), text, record)
            return None
        if mnemonic == "nop":
            self.records.append(record)
            return None
        self.fail(text, f"unsupported instruction `{mnemonic}`")

    def jump_register(self, operand, text, record):
        name = register(operand)
        if name is None:
            self.fail(text, "unsupported jump operand")
        record.kind, record.reads = "return", {name}
        if self.regs[name] == ("entry", "lr"):
            return self.finish(text, record)
        self.fail(text, "computed jumps are not modelled")


# ---------------------------------------------------------------- comparison

def explore(name, function, signatures, label, layout, definitions=None):
    paths, pending = [], [[]]
    while pending:
        decisions = pending.pop()
        try:
            path = Executor(name, function, signatures, label, layout, definitions).run(decisions)
        except NeedDecision:
            pending += [decisions + [False], decisions + [True]]
            continue
        paths.append(path)
        if len(paths) > MAX_PATHS:
            raise SemanticError(f"{name} has more than {MAX_PATHS} paths; the semantic check is bounded")
    return paths


def replay(name, function, signatures, label, decisions, layout, definitions=None):
    try:
        return Executor(name, function, signatures, label, layout, definitions).run(decisions)
    except NeedDecision:
        raise SemanticError(f"{name}: the stripped compile branches where the real one does not")


def describe(record):
    return f"`{record.text}` (instruction {record.index + 1})"


def object_offset(address, symbol, size):
    constant, terms = linear(address)
    if terms == {("sym", symbol): 1}:
        offset = signed32(constant)
        return offset if -4 < offset < size else None
    return None


def dead(records, position, destination):
    """True if overwritten before any use, False if used, or the call record
    whose source-supplied prototype leaves the register's use unknown"""
    for record in records[position + 1:]:
        if destination in record.guarded:
            return record
        if destination in record.reads:
            return False
        if destination in record.writes:
            return True
    return True


def read_modify_write_store(records, position, address):
    """the position of the `strb` this dead load belongs to, or None.

    agbcc computes a volatile byte store's value before the read-modify-write
    load; the only instructions it leaves between that load and the `strb`
    are immediate `mov`s (its own value, or a later store's hoisted constant
    in 08050D50) and register copies or literal loads that write a register
    the `strb` reads (08122C6C copies the address).  Anything else in
    between - arithmetic, another memory access, a call or a branch - means
    the load was not emitted by the store.
    """
    between = []
    for later in range(position + 1, len(records)):
        record = records[later]
        if record.kind == "store":
            if record.width != 1 or record.address != address:
                return None
            if any(not step.constant and not record.reads >= step.writes for step in between):
                return None
            return later
        if not (record.kind == "literal" or record.copy or record.constant):
            return None
        between.append(record)
    return None


def chained_reread(records, position, pinned_address):
    """is this load the re-read of `a = (b = v)` with volatile `b`?

    The forwarding `strb` to the same byte must be the immediately preceding
    memory access, with only register arithmetic in between, and the value
    must reach (through register copies) the next store, which is an `strb`
    to a pinned byte; apart from that store's own read-modify-write load no
    memory access, call or branch may intervene, and the value is used
    nowhere else.
    """
    load = records[position]
    earlier = position - 1
    while earlier >= 0 and records[earlier].kind in ("alu", "literal"):
        earlier -= 1
    if earlier < 0 or records[earlier].kind != "store" or records[earlier].width != 1 or \
            records[earlier].address != load.address:
        return False
    tracked, store, loads = set(load.writes), None, []
    for record in records[position + 1:]:
        if store is None:
            if record.kind == "store":
                if record.width != 1 or record.value_register not in tracked or \
                        not pinned_address(record.address) or \
                        (record.reads - {record.value_register}) & tracked or \
                        any(address != record.address for address in loads) or len(loads) > 1:
                    return False
                store = record
                continue
            if record.kind == "load" and not record.reads & tracked:
                loads.append(record.address)
            elif record.kind not in ("alu", "literal"):
                return False
            elif record.reads & tracked and not (record.copy and record.reads <= tracked):
                return False
            elif record.copy and record.reads & tracked:
                tracked |= record.writes
                continue
        elif record.reads & tracked:
            return False
        tracked -= record.writes
        if not tracked:
            break
    return store is not None


def compare_function(name, real_function, stripped_function, signatures, symbol, size, pinned,
                     definitions=None):
    def pinned_address(address):
        offset = object_offset(address, symbol, size)
        return offset in pinned

    def where(address):
        offset = object_offset(address, symbol, size)
        return f"{symbol}+{offset:#x}" if offset is not None else show(address)

    paths = explore(name, real_function, signatures, "real", (symbol, size), definitions)
    read_modify_write, chained = set(), set()
    for number, path in enumerate(paths, 1):
        records = path.records
        # 4. a store must not write back the value it read from the same byte
        for record in records:
            if record.kind == "store" and pinned_address(record.address) and record.self_assignment:
                raise SemanticError(f"{name}: {describe(record)} writes back the value it read "
                                    f"from {where(record.address)} (an ldrb/strb self-assignment)")
        # 2. classify every load of the object in the real compile
        counterparts, explained_stores = [], set()
        for position, record in enumerate(records):
            if record.kind != "load" or object_offset(record.address, symbol, size) is None:
                continue
            destination = next(iter(record.writes))
            if record.width == 1 and not record.signed and pinned_address(record.address):
                verdict = dead(records, position, destination)
                if isinstance(verdict, Record):
                    raise SemanticError(
                        f"{name}: {describe(record)} loads {where(record.address)} into "
                        f"{destination}, which {describe(verdict)} might take as an argument its "
                        "prototype does not name; only a prototype that agrees with the callee's "
                        "matched definition in src/ is trusted to list every argument")
                if verdict:
                    store = read_modify_write_store(records, position, record.address)
                    if store is None:
                        raise SemanticError(
                            f"{name}: {describe(record)} is a dead load of {where(record.address)} "
                            "that is not directly followed by a store to the same byte (only immediate "
                            "moves and the store's own operand copies may sit between them); only the "
                            "read-modify-write load of a byte store is the qualifier's documented effect")
                    explained_stores.add(store)
                    read_modify_write.add(record.index)
                    continue
                if record.forwarded and chained_reread(records, position, pinned_address):
                    chained.add(record.index)
                    continue
            counterparts.append((record.width, record.signed, where(record.address), record))
        # 3. every store to a pinned byte carries its read-modify-write load
        for position, record in enumerate(records):
            if record.kind != "store":
                continue
            offset = object_offset(record.address, symbol, size)
            if offset is None or not any(offset <= byte < offset + record.width for byte in pinned):
                continue
            if record.width != 1 or position not in explained_stores:
                raise SemanticError(f"{name}: {describe(record)} stores to {where(record.address)} "
                                    "without the read-modify-write load of a volatile byte store")
        # 1. the stripped compile behaves the same on this path
        other = replay(name, stripped_function, signatures, "stripped", path.decisions, (symbol, size),
                       definitions)
        if other.conditions != path.conditions:
            raise SemanticError(f"{name}: the real and stripped compiles branch on different "
                                f"conditions (path {number})")
        if other.trace != path.trace:
            for index, (mine, theirs) in enumerate(zip(path.trace + [None] * len(other.trace),
                                                       other.trace + [None] * len(path.trace))):
                if mine != theirs:
                    break
            raise SemanticError(f"{name}: the real and stripped compiles differ in observable "
                                f"behaviour (path {number}, event {index + 1}: real "
                                f"{show_event(mine)}, stripped {show_event(theirs)})")
        theirs = [(r.width, r.signed, where(r.address)) for r in other.records
                  if r.kind == "load" and object_offset(r.address, symbol, size) is not None]
        mine = [entry[:3] for entry in counterparts]
        if mine != theirs:
            index = next((i for i, (a, b) in enumerate(zip(mine, theirs)) if a != b), min(len(mine), len(theirs)))
            if index < len(mine):
                raise SemanticError(f"{name}: {describe(counterparts[index][3])} loads "
                                    f"{counterparts[index][2]}, which the stripped compile does not "
                                    "load there; the qualifier added a read")
            raise SemanticError(f"{name}: the stripped compile loads {theirs[index][2]} where the real "
                                "one does not")
    return len(paths), sorted(read_modify_write), sorted(chained)


def show_event(event):
    if event is None:
        return "nothing"
    if event[0] == "store":
        return f"store{event[1] * 8} {show(event[2])} <- {show(event[3])}"
    if event[0] == "call":
        target = event[1] if isinstance(event[1], str) else show(event[1][1]) if event[1][0] == "via" \
            else str(event[1])
        return f"call {target}({', '.join(show(a) for a in event[2])})"
    if event[0] == "escape":
        return "frame escape {" + ", ".join(f"{offset:+#x}: {show(value)}" for offset, value in event[1]) + "}"
    return "return" + (f" {show(event[1])}" if len(event) > 1 else "")


def normalised(lines):
    names = {}
    return [re.sub(r"\.L\d+\b", lambda m: names.setdefault(m[0], f".L#{len(names)}"), line)
            for line in lines]


def compare(real_assembly, stripped_assembly, preprocessed, symbol, declaration, definition=None):
    """[(function, paths, read-modify-write instructions, chained re-reads)].

    definition(name) gives a callee's (returns, words) from its own matched
    source, or None; only a prototype that agrees with it is trusted to name
    every argument register the callee reads.

    Raises SemanticError with the reason when the real compile differs from
    the stripped one by anything but the qualifier's documented effect.
    """
    size, pinned = object_layout(declaration)
    from plausible import member_provenance, strip_comments_and_strings
    for _, message in member_provenance(strip_comments_and_strings(preprocessed),
                                        {"symbol": symbol, "declaration": declaration}):
        raise SemanticError(f"after preprocessing: {message}")
    real, real_outside = parse_assembly(real_assembly)
    stripped, stripped_outside = parse_assembly(stripped_assembly)
    if sorted(real) != sorted(stripped):
        raise SemanticError("the real and stripped compiles define different functions")
    if normalised(real_outside) != normalised(stripped_outside):
        raise SemanticError("the real and stripped compiles differ outside their functions")
    names = set(real)
    for function in real.values():
        for mnemonic, operands, _ in function[0]:
            if mnemonic == "bl" and operands:
                names.add(operands[0])
    scope = file_scope(preprocessed)
    signatures = {name: function_signature(scope, name) for name in names}
    definitions = {}
    if definition is not None:
        for callee in names - set(real):
            found = definition(callee)
            if found is not None:
                definitions[callee] = found
    return [(name,) + compare_function(name, real[name], stripped[name], signatures, symbol, size, pinned,
                                       definitions)
            for name in sorted(real)]


def record(symbol, results):
    """the report record for a passed semantic check"""
    parts = []
    for name, paths, read_modify_write, chained in results:
        parts.append(f"`{name}` agrees on {paths} path{'s' if paths != 1 else ''}; "
                     f"read-modify-write loads at {list(n + 1 for n in read_modify_write)}, "
                     f"chained re-reads at {list(n + 1 for n in chained)}")
    return (f"* allowlisted volatile semantics: `{symbol}` stripped of volatile compiles to the same "
            f"behaviour; " + "; ".join(parts))
