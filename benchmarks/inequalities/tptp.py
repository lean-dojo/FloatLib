"""Translate the real, first-order TPTP fragment used by MetiTarski.

This is a parser, not textual substitution. It preserves quantifiers, connectives,
strict inequalities and exact decimal constants. Uninterpreted functions are refused.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "suites"))
from sexpr import Refusal, number, rational


TOKENS = re.compile(
    r"\s+|%[^\n]*|/\*.*?\*/|'(?:\\.|[^'\\])*'|"
    r"<=>|<~>|=>|<=|>=|!=|~\||~&|"
    r"[A-Za-z_$][A-Za-z0-9_$]*|"
    r"\d+(?:\.\d+)?(?:[eE][+-]?\d+)?|[()\[\],.:!?\+\-*/^&|~=<>]",
    re.DOTALL,
)
PRECEDENCE = {"<=>": 1, "=>": 2, "|": 3, "&": 4,
              "=": 5, "!=": 5, "<": 5, "<=": 5, ">": 5, ">=": 5,
              "+": 6, "-": 6, "*": 7, "/": 7, "^": 8}


class Parser:
    def __init__(self, text: str):
        self.tokens = []
        end = 0
        for match in TOKENS.finditer(text):
            if match.start() != end:
                raise Refusal(f"Unrecognized TPTP text at byte {end}")
            end = match.end()
            token = match.group()
            if not token.isspace() and not token.startswith(("%", "/*")):
                self.tokens.append(token)
        if end != len(text):
            raise Refusal(f"Unrecognized TPTP text at byte {end}")
        self.index = 0

    def peek(self):
        return self.tokens[self.index] if self.index < len(self.tokens) else None

    def pop(self, expected=None):
        token = self.peek()
        if token is None or expected is not None and token != expected:
            raise Refusal(f"Expected {expected}, found {token}")
        self.index += 1
        return token

    def expression(self, minimum=0):
        token = self.pop()
        if token in ("!", "?"):
            self.pop("[")
            names = []
            while True:
                names.append(self.pop())
                if self.peek() != ",":
                    break
                self.pop(",")
            self.pop("]")
            self.pop(":")
            # TPTP quantifiers bind a unit formula. Parentheses extend that scope.
            left = (token, names, self.expression(5))
        elif token == "(":
            left = self.expression()
            self.pop(")")
        elif token in ("-", "+", "~"):
            left = ("unary" + token, self.expression(5 if token == "~" else 8))
        else:
            left = ("atom", token)
            if self.peek() == "(":
                self.pop("(")
                args = []
                if self.peek() != ")":
                    while True:
                        args.append(self.expression())
                        if self.peek() != ",":
                            break
                        self.pop(",")
                self.pop(")")
                left = ("call", token, args)
        while self.peek() in PRECEDENCE and PRECEDENCE[self.peek()] >= minimum:
            op = self.pop()
            precedence = PRECEDENCE[op]
            right = self.expression(precedence if op in ("^", "=>") else precedence + 1)
            left = (op, left, right)
        return left

    def file(self):
        forms = []
        includes = []
        while self.peek() is not None:
            kind = self.pop()
            self.pop("(")
            name = self.pop()
            if kind == "include":
                if self.peek() != ")":
                    raise Refusal("Selective TPTP includes are unsupported")
                includes.append(name.strip("'"))
                self.pop(")")
                self.pop(".")
                continue
            if kind != "fof":
                raise Refusal(f"Unsupported TPTP language: {kind}")
            self.pop(",")
            role = self.pop()
            self.pop(",")
            expression = self.expression()
            if self.peek() != ")":
                raise Refusal("TPTP inference annotations are unsupported")
            self.pop(")")
            self.pop(".")
            forms.append((name.strip("'"), role, expression))
        return forms, includes


UNARY = {
    "exp": "Real.exp", "ln": "Real.log", "log": "Real.log", "sqrt": "Real.sqrt",
    "sin": "Real.sin", "cos": "Real.cos", "tan": "Real.tan", "arctan": "Real.arctan",
    "atan": "Real.arctan", "arcsin": "Real.arcsin", "asin": "Real.arcsin",
    "arccos": "Real.arccos", "acos": "Real.arccos", "sinh": "Real.sinh",
    "cosh": "Real.cosh", "tanh": "Real.tanh", "abs": "abs", "absolute": "abs",
}
OPERATORS = {
    "+": "+", "-": "-", "*": "*", "/": "/", "^": "^",
    "=": "=", "!=": "≠", "<": "<", "<=": "≤", ">": ">", ">=": "≥",
    "&": "∧", "|": "∨", "=>": "→", "<=>": "↔",
}
BUILTINS = {
    "$sum": "+", "$difference": "-", "$product": "*", "$quotient": "/",
    "$less": "<", "$lesseq": "<=", "$greater": ">", "$greatereq": ">=",
}


def free_variables(node, bound=frozenset()) -> set[str]:
    if node[0] == "atom":
        value = node[1]
        return {value} if value[0].isupper() and value not in bound else set()
    if node[0] in ("!", "?"):
        return free_variables(node[2], bound | set(node[1]))
    if node[0] == "call":
        return set().union(*(free_variables(arg, bound) for arg in node[2]))
    return set().union(*(free_variables(arg, bound) for arg in node[1:]))


def translate(node, env=None) -> str:
    env = {} if env is None else env
    op = node[0]
    if op == "atom":
        value = node[1]
        if value in env:
            return env[value]
        if value in ("pi", "$pi"):
            return "Real.pi"
        if value == "$true":
            return "True"
        if value == "$false":
            return "False"
        try:
            return rational(number(value), "ℝ")
        except ValueError:
            raise Refusal(f"Uninterpreted TPTP atom: {value}") from None
    if op in ("!", "?"):
        new_env = dict(env)
        names = []
        for index, var in enumerate(node[1]):
            name = f"v{len(env) + index}"
            while name in new_env.values():
                name += "_"
            new_env[var] = name
            names.append(name)
        quantifier = "∀" if op == "!" else "∃"
        return f"({quantifier} ({' '.join(names)} : ℝ), {translate(node[2], new_env)})"
    if op in ("unary-", "unary+", "unary~"):
        symbol = {"unary-": "-", "unary+": "+", "unary~": "¬"}[op]
        if symbol == "+":
            return translate(node[1], env)
        return f"({symbol}{translate(node[1], env)})"
    if op in OPERATORS:
        if op == "^":
            rhs = node[2]
            if rhs[0] == "atom" and rhs[1].isdigit():
                exponent = str(int(rhs[1]))
            elif rhs[0] == "unary-" and rhs[1][0] == "atom" and rhs[1][1].isdigit():
                exponent = f"(-{int(rhs[1][1])} : ℤ)"
            else:
                raise Refusal("Only integer TPTP exponents are implemented")
            return f"({translate(node[1], env)} ^ {exponent})"
        return f"({translate(node[1], env)} {OPERATORS[op]} {translate(node[2], env)})"
    if op == "call":
        name, args = node[1:]
        if name in UNARY and len(args) == 1:
            return f"({UNARY[name]} {translate(args[0], env)})"
        if name in BUILTINS and len(args) == 2:
            return translate((BUILTINS[name], *args), env)
        if name in ("pow", "power") and len(args) == 2:
            return translate(("^", *args), env)
        if name in ("min", "max") and len(args) == 2:
            return f"({name} {translate(args[0], env)} {translate(args[1], env)})"
        raise Refusal(f"Uninterpreted TPTP function: {name}/{len(args)}")
    raise Refusal(f"Unsupported TPTP node: {op}")


def goal(node) -> str:
    variables = sorted(free_variables(node))
    env = {var: f"v{i}" for i, var in enumerate(variables)}
    result = translate(node, env)
    if env:
        result = f"∀ ({' '.join(env.values())} : ℝ), {result}"
    return result
