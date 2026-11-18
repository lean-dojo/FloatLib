"""A conservative parser for quoted HOL real expressions in Flyspeck.

Only explicit source definitions are unfolded. Hilbert choice, generated OCaml
terms, recursive definitions and unrecognized functions are refusals. This
does not execute HOL Light or infer bounds from names such as 'hminus'.
"""
from __future__ import annotations
import re
from pathlib import Path
from sexpr import Refusal, number, rational

TOKEN = re.compile(
    r"\s+|<=>|==>|/\\|\\/|<=|>=|--|"
    r"[A-Za-z_][A-Za-z_0-9']*|#?\d+(?:\.\d+)?|"
    r"[()\[\],.;:+*/=<>!?'\\~&@-]")
PREC = {"<=>": 1, "==>": 2, "\\/": 3, "/\\": 4, "=": 5,
        "<": 5, "<=": 5, ">": 5, ">=": 5, "+": 6, "-": 6,
        "*": 7, "/": 7, "pow": 8}
SYMBOL = {"<=>": "↔", "==>": "→", "\\/": "∨", "/\\": "∧",
          "<=": "≤", ">=": "≥"}
UNARY = {"sqrt": "Real.sqrt", "sin": "Real.sin", "cos": "Real.cos",
         "tan": "Real.tan", "acs": "Real.arccos", "asn": "Real.arcsin",
         "atn": "Real.arctan", "exp": "Real.exp", "log": "Real.log",
         "abs": "abs"}


def uncomment(text):
    """Nested OCaml comments, preserving line numbers and quoted strings."""
    output, depth, i, quoted = [], 0, 0, False
    while i < len(text):
        if not quoted and text[i:i+2] == "(*":
            depth += 1
            output.extend("  ")
            i += 2
        elif depth and text[i:i+2] == "*)":
            depth -= 1
            output.extend("  ")
            i += 2
        else:
            ch = text[i]
            if not depth and ch == '"' and (i == 0 or text[i-1] != "\\"):
                quoted = not quoted
            output.append(ch if not depth or ch == "\n" else " ")
            i += 1
    if depth:
        raise Refusal("Unclosed OCaml comment")
    return "".join(output)


class Parser:
    def __init__(self, text):
        self.tokens, end = [], 0
        for match in TOKEN.finditer(text):
            if match.start() != end:
                raise Refusal(f"Unsupported HOL token at byte {end}: {text[end:end+30]}")
            end = match.end()
            if not match.group().isspace():
                self.tokens.append(match.group())
        if end != len(text):
            raise Refusal(f"Unsupported HOL text at byte {end}")
        self.i = 0

    def peek(self):
        return self.tokens[self.i] if self.i < len(self.tokens) else None

    def pop(self, expected=None):
        token = self.peek()
        if token is None or expected is not None and token != expected:
            raise Refusal(f"Expected HOL {expected}, found {token}")
        self.i += 1
        return token

    def expr(self, minimum=0):
        token = self.pop()
        if token in ("!", "?", "\\"):
            names = []
            while self.peek() != ".":
                name = self.pop()
                if not re.fullmatch(r"[a-zA-Z_]\w*", name):
                    raise Refusal("Typed or patterned HOL binder is not implemented")
                names.append(name)
            self.pop(".")
            left = (token, names, self.expr())
        elif token == "(":
            left = self.expr()
            if self.peek() == ",":
                items = [left]
                while self.peek() == ",":
                    self.pop(",")
                    items.append(self.expr())
                left = ("tuple", items)
            if self.peek() == ":":
                self.pop(":")
                if self.pop() != "real":
                    raise Refusal("Only real HOL type annotations are implemented")
            self.pop(")")
        elif token == "[":
            items = []
            while self.peek() != "]":
                item = self.expr()
                if self.peek() == ",":
                    parts = [item]
                    while self.peek() == ",":
                        self.pop(",")
                        parts.append(self.expr())
                    item = ("tuple", parts)
                items.append(item)
                if self.peek() != ";":
                    break
                self.pop(";")
            self.pop("]")
            left = ("list", items)
        elif token in ("--", "~", "&"):
            left = (token, self.expr(9))
        elif token == "let":
            pattern = self.expr(6)
            self.pop("=")
            value = self.expr()
            self.pop("in")
            left = ("let", pattern, value, self.expr())
        elif token in ("if", "@"):
            raise Refusal(f"HOL construct is not implemented: {token}")
        else:
            left = ("atom", token)
        while self.peek() is not None:
            op = self.peek()
            if op in PREC:
                if PREC[op] < minimum:
                    break
                self.pop()
                left = (op, left, self.expr(PREC[op] + (op != "==>")))
            elif minimum <= 10 and (op == "(" or op == "[" or op == "&" or
                                     re.fullmatch(r"#?\w+(?:\.\d+)?", op)):
                if op in ("in", "then", "else"):
                    break
                left = ("apply", left, self.expr(11))
            else:
                break
        return left

    def all(self):
        node = self.expr()
        if self.peek() is not None:
            raise Refusal("Trailing HOL tokens: " + " ".join(self.tokens[self.i:self.i+8]))
        return node


def applications(node):
    args = []
    while node[0] == "apply":
        args.insert(0, node[2])
        node = node[1]
    return node, args


def pattern_names(pattern):
    if pattern[0] == "atom" and re.fullmatch(r"[a-zA-Z_]\w*'?", pattern[1]):
        return [pattern[1]]
    if pattern[0] == "tuple":
        names = [name for part in pattern[1] for name in pattern_names(part)]
        if len(set(names)) != len(names):
            raise Refusal("Repeated name in HOL tuple pattern")
        return names
    raise Refusal("Unsupported HOL binding pattern")


def bind_pattern(pattern, value):
    pattern_names(pattern)
    if pattern[0] == "atom":
        return {pattern[1]: value}
    if value[0] != "tuple" or len(pattern[1]) != len(value[1]):
        raise Refusal("HOL tuple argument does not match its pattern")
    return {name: term for p, v in zip(pattern[1], value[1])
            for name, term in bind_pattern(p, v).items()}


def definitions(paths):
    result = {}
    for path in paths:
        if not path.exists():
            continue
        text = uncomment(path.read_text())
        for match in re.finditer(r"\b(?:new_definition|define)\s*\(?\s*`([^`]+)`", text):
            try:
                node = Parser(match.group(1)).all()
                if node[0] != "=":
                    continue
                head, args = applications(node[1])
                if head[0] != "atom":
                    continue
                for arg in args:
                    pattern_names(arg)
                name = head[1]
                entry = (args, node[2], str(path), match.start())
                if name in result and (result[name] is None or result[name][:2] != entry[:2]):
                    result[name] = None
                else:
                    result[name] = entry
            except Refusal:
                continue
    return result


class Translator:
    def __init__(self, defs):
        self.defs = defs
        self.used = set()
        self.free = set()
        self.binders = 0

    def expand(self, node, env, stack=(), bound=()):
        if len(stack) > 80:
            raise Refusal("HOL definition expansion depth exceeded")
        head, args = applications(node)
        if head[0] == "atom":
            name = head[1]
            if name in bound or name == "ineq":
                # ineq is the audited list-of-closed-intervals connective.
                return node
            if name in env:
                replacement = env[name]
                for arg in args:
                    replacement = ("apply", replacement, arg)
                if replacement != node:
                    return self.expand(replacement, {}, stack, bound)
            if name in self.defs:
                if self.defs[name] is None:
                    raise Refusal("Conflicting HOL definitions: " + name)
                params, rhs, _, _ = self.defs[name]
                if name in stack:
                    raise Refusal("Recursive HOL definition: " + name)
                if len(args) != len(params):
                    raise Refusal(f"Partial HOL application: {name}/{len(args)}")
                self.used.add(name)
                # Substitute without permitting capture of source free variables.
                bindings = {key: value for p, a in zip(params, args)
                            for key, value in bind_pattern(p, a).items()}
                rhs = substitute(rhs, bindings)
                return self.expand(rhs, env, (*stack, name), bound)
        if head[0] == "\\":
            params, rhs = head[1:]
            if len(params) != len(args):
                raise Refusal("Partial HOL lambda application")
            return self.expand(substitute(rhs, dict(zip(params, args))), env, stack, bound)
        return node

    def real(self, node, env=None, stack=()):
        env = {} if env is None else env
        node = self.expand(node, {}, stack, tuple(env))
        op = node[0]
        if op == "atom":
            name = node[1]
            if name in env:
                return env[name]
            if name == "pi":
                return "Real.pi"
            if name in ("T", "F"):
                return "True" if name == "T" else "False"
            try:
                return rational(number(name.removeprefix("#")), "ℝ")
            except ValueError:
                if re.fullmatch(r"[xy][0-9]*", name):
                    self.free.add(name)
                    return name
                raise Refusal("Unexpanded HOL symbol: " + name) from None
        if op == "let":
            bindings = bind_pattern(node[1], node[2])
            # Sequential Lean lets retain lexical scope and evaluate every RHS
            # in the outer scope. The HOL tuple value is a literal tuple here.
            clauses, scope = [], dict(env)
            for name, value in bindings.items():
                fresh = f"v{self.binders}"
                self.binders += 1
                clauses.append(f"let {fresh} : ℝ := {self.real(value, env, stack)}; ")
                scope[name] = fresh
            return "(" + "".join(clauses) + self.real(node[3], scope, stack) + ")"
        if op in ("!", "?"):
            names = node[1]
            scope = {**env, **{name: f"v{self.binders+i}" for i, name in enumerate(names)}}
            self.binders += len(names)
            q = "∀" if op == "!" else "∃"
            return f"({q} ({' '.join(scope[n] for n in names)} : ℝ), {self.real(node[2], scope)})"
        if op == "&":
            # Natural subtraction and division do not have their real meanings.
            # Admit literal casts only, after source definitions are expanded.
            operand = self.expand(node[1], {}, stack, tuple(env))
            if operand[0] != "atom" or not operand[1].isdigit():
                raise Refusal("Only literal natural-to-real HOL coercions are implemented")
            return rational(number(operand[1]), "ℝ")
        if op in ("--", "~"):
            value = self.real(node[1], env)
            return f"({'-' if op == '--' else '¬'}{value})"
        if op in PREC:
            if op == "pow":
                exponent = node[2]
                if exponent[0] != "atom" or not exponent[1].isdigit():
                    raise Refusal("Only natural HOL exponents are implemented")
                return f"({self.real(node[1], env)} ^ {int(exponent[1])})"
            return f"({self.real(node[1], env)} {SYMBOL.get(op, op)} {self.real(node[2], env)})"
        if op == "apply":
            head, args = applications(node)
            if head == ("atom", "ineq") and len(args) == 2:
                domain = self.expand(args[0], {}, bound=tuple(env))
                if domain[0] != "list":
                    raise Refusal("Flyspeck domain did not reduce to a bound list")
                premises = []
                for item in domain[1]:
                    if item[0] != "tuple" or len(item[1]) != 3:
                        raise Refusal("Malformed Flyspeck domain tuple")
                    lo, var, hi = item[1]
                    x = self.real(var, env)
                    premises.extend([f"{self.real(lo, env)} ≤ {x}",
                                     f"{x} ≤ {self.real(hi, env)}"])
                return "(" + " → ".join(premises + [self.real(args[1], env)]) + ")"
            if head[0] == "atom" and head[1] in UNARY and len(args) == 1:
                return f"({UNARY[head[1]]} {self.real(args[0], env)})"
            if head[0] == "atom" and head[1] in ("min", "max") and len(args) == 2:
                return f"({head[1]} {self.real(args[0], env)} {self.real(args[1], env)})"
            raise Refusal("Unexpanded HOL application: " + repr(head))
        raise Refusal("Unsupported HOL expression: " + op)

    def goal(self, text):
        node = Parser(text).all()
        value = self.real(node)
        if self.free:
            value = f"∀ ({' '.join(sorted(self.free))} : ℝ), {value}"
        return value


def substitute(node, env):
    if node[0] == "atom":
        return env.get(node[1], node)
    if node[0] in ("!", "?", "\\"):
        if env:
            # Capture checks are essential even for an untrusted source translator.
            text = repr(list(env.values()))
            if any(re.search(r"\b" + re.escape(name) + r"\b", text) for name in node[1]):
                raise Refusal("HOL substitution would capture a bound variable")
        return (node[0], node[1], substitute(node[2], {
            k: v for k, v in env.items() if k not in node[1]}))
    if node[0] == "let":
        names = pattern_names(node[1])
        if env:
            text = repr(list(env.values()))
            if any(re.search(r"\b" + re.escape(name) + r"\b", text) for name in names):
                raise Refusal("HOL let substitution would capture a bound variable")
        return ("let", node[1], substitute(node[2], env),
                substitute(node[3], {k: v for k, v in env.items() if k not in names}))
    if node[0] in ("list", "tuple"):
        return (node[0], [substitute(item, env) for item in node[1]])
    return (node[0], *(substitute(item, env) for item in node[1:]))


def records(path):
    """Inventory record literals, including skipped/generated records, without executing OCaml."""
    text = uncomment(path.read_text())
    # Source records contain no nested records; reject a nested brace conservatively.
    for match in re.finditer(r"\{([^{}]*\bineq\s*=[^{}]*)\}", text, re.DOTALL):
        record = match.group(1)
        ident = re.search(r'\bidv\s*=\s*"([^"]*)"', record)
        name = ident.group(1) if ident else f"generated-at-{text[:match.start()].count(chr(10))+1}"
        field = re.search(r"\bineq\s*=\s*(.*?)(?:;\s*(?:idv|doc|tags)\s*=|$)", record, re.DOTALL)
        # An OCaml function applied to a quoted template can change the term.
        # Accept only the literal or the source's universal-closure wrapper.
        literal = re.fullmatch(r"\s*(?:all_forall\s+)?`([^`]+)`\s*;?\s*",
                               field.group(1)) if field else None
        prefix = text[max(0, match.start()-60):match.start()].strip()
        status = "skipped" if prefix.endswith("skip") else "record"
        if "Deprecated" in record:
            status = "deprecated"
        yield name, literal.group(1) if literal else None, status, match.start()


def examples(path):
    """The official formal verifier's named, quoted Flyspeck examples."""
    text = uncomment(path.read_text())
    for match in re.finditer(r"\badd_example\s*\{([^{}]*)\}", text, re.DOTALL):
        record = match.group(1)
        name = re.search(r'\bid\s*=\s*"([^"]*)"', record)
        term = re.search(r"\bineq_tm\s*=\s*`([^`]+)`\s*;?\s*$", record, re.DOTALL)
        if not name:
            raise Refusal("Unnamed Flyspeck formal-verifier example")
        yield name[1], term[1] if term else None, "formal-verifier-example", match.start()
