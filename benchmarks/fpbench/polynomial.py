"""Overflow guard for the integer polynomial contract explained in suites/PROOF.md."""
import re

from numeric import source_box
from sexpr import Refusal, number


def polynomial_guard(args, attrs, body, precision):
    """Return the largest checked pre-rounding magnitude, or refuse."""
    if not all(re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name) for name in args):
        raise Refusal("Polynomial audit requires ordinary scalar identifiers")
    if len(set(args)) != len(args):
        raise Refusal("Polynomial audit requires distinct input identifiers")
    boxes = source_box(attrs[":pre"], args)
    integer_limit = 1 << 24
    limit = 1 << ({"binary32": 127, "binary64": 1023}[precision] - 1)
    maximum = 0

    def integer(value):
        if value.denominator != 1 or abs(value) > integer_limit:
            raise Refusal("Polynomial audit requires integers of magnitude at most 2^24")
        return int(value)

    env = {}
    for name, endpoints in boxes.items():
        lo, hi = map(integer, endpoints)
        env[name] = 2 * max(1, abs(lo), abs(hi))

    def magnitude(node, names):
        nonlocal maximum
        if isinstance(node, str):
            if node in names:
                return names[node]
            value = number(node)
            if not value and node.startswith("-"):
                raise Refusal("Negative-zero literals need a separate exporter audit")
            return max(1, abs(integer(value)))
        op, *values = node
        if op == "let":
            bindings, result = values
            scope = dict(names)
            bound_names = []
            for name, term in bindings:
                if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name):
                    raise Refusal("Polynomial audit requires ordinary bound identifiers")
                if name in bound_names:
                    raise Refusal("Polynomial audit refuses duplicate simultaneous bindings")
                bound_names.append(name)
                scope[name] = magnitude(term, names)
            return magnitude(result, scope)
        if op not in ("+", "-", "*"):
            raise Refusal("Gappa polynomial audit supports only +, -, *, and parallel let")
        operands = [magnitude(value, names) for value in values]
        if op == "-" and len(operands) == 1:
            return operands[0]
        if len(operands) != 2:
            raise Refusal("Polynomial audit requires binary arithmetic")
        a, b = operands
        before = a * b if op == "*" else a + b
        maximum = max(maximum, before)
        if before > limit:
            raise Refusal("Conservative polynomial magnitude guard cannot exclude overflow")
        return 2 * before

    magnitude(body, env)
    return maximum
