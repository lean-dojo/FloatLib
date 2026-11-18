"""Lossless S-expression reader for the textual FPCore benchmark language."""

from __future__ import annotations

import re
from dataclasses import dataclass
from fractions import Fraction


class Refusal(ValueError):
    """An unsupported input, with an explanation suitable for a results row."""


@dataclass(frozen=True)
class Quoted:
    text: str


TOKEN = re.compile(r'\s+|;[^\n]*|"(?:\\.|[^"\\])*"|[()[\]]|[^\s()[\]";]+')


def parse(text: str) -> list:
    """Read all forms, reject unmatched delimiters and never discard unknown text."""
    tokens = []
    position = 0
    for match in TOKEN.finditer(text):
        if match.start() != position:
            raise Refusal(f"Unrecognized text at byte {position}")
        position = match.end()
        token = match.group()
        if not token.isspace() and not token.startswith(";"):
            tokens.append(token)
    if position != len(text):
        raise Refusal(f"Unrecognized text at byte {position}")
    stack = []
    forms = []
    for token in tokens:
        if token in ("(", "["):
            stack.append((token, []))
        elif token in (")", "]"):
            if not stack:
                raise Refusal("Unmatched closing delimiter")
            opening, node = stack.pop()
            if (opening, token) not in (("(", ")"), ("[", "]")):
                raise Refusal("Mismatched delimiters")
            (stack[-1][1] if stack else forms).append(node)
        else:
            atom = Quoted(token[1:-1]) if token.startswith('"') else token
            (stack[-1][1] if stack else forms).append(atom)
    if stack:
        raise Refusal("Unclosed delimiter")
    return forms


def render(node) -> str:
    if isinstance(node, list):
        return "(" + " ".join(map(render, node)) + ")"
    if isinstance(node, Quoted):
        return '"' + node.text + '"'
    return str(node)


def number(text: str) -> Fraction:
    """Read decimal, rational, and hexadecimal numbers without binary64 conversion."""
    if not isinstance(text, str):
        raise ValueError("not a numeric atom")
    if re.fullmatch(r"[+-]?0[xX][0-9a-fA-F]+(?:\.[0-9a-fA-F]*)?[pP][+-]?\d+", text):
        sign = -1 if text.startswith("-") else 1
        mantissa, exponent = re.split("[pP]", text.lstrip("+-"))
        digits = mantissa[2:].split(".")
        frac = digits[1] if len(digits) == 2 else ""
        return sign * Fraction(int(digits[0] + frac, 16), 16 ** len(frac)) * (
            Fraction(2) ** int(exponent)
        )
    return Fraction(text)


def rational(q: Fraction, scalar: str = "ℚ") -> str:
    return f"({q.numerator} / {q.denominator} : {scalar})"


def properties(items: list) -> tuple[dict, list]:
    result = {}
    i = 0
    while i < len(items) and isinstance(items[i], str) and items[i].startswith(":"):
        if i + 1 == len(items):
            raise Refusal(f"Missing value for {items[i]}")
        result[items[i]] = items[i + 1]
        i += 2
    return result, items[i:]
