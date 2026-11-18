"""Translate scalar FPCore programs while preserving rounding and evaluation order.

Unknown operations, unimplemented precision families, and loops fail explicitly. An
annotation changes the context of operations in its body; a variable is not rounded
merely by being read. Operands of different precisions are explicitly converted.
"""

from __future__ import annotations

import hashlib
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "suites"))
from sexpr import Quoted, Refusal, number, parse, properties, rational, render


MODES = {
    "nearestEven": "nearest",
    "nearestAway": "nearestAway",
    "toPositive": "up",
    "toNegative": "down",
    "toZero": "towardZero",
    "awayZero": "away",
}
FORMATS = {"binary32": (8, 23), "binary64": (11, 52)}
CR = {"exp": "exp", "log": "log", "expm1": "expm1", "log1p": "logp1"}


@dataclass(frozen=True)
class Context:
    precision: str
    mode: str = "nearestEven"

    def annotated(self, attrs: dict) -> "Context":
        precision = attrs.get(":precision", self.precision)
        mode = attrs.get(":round", self.mode)
        if not isinstance(precision, str) or precision not in FORMATS:
            raise Refusal(f"Unsupported precision attribute: {render(precision)}")
        if not isinstance(mode, str) or mode not in MODES:
            raise Refusal(f"Unsupported rounding attribute: {render(mode)}")
        return Context(precision, mode)

    @property
    def fmt(self) -> str:
        return "FloatFormat." + self.precision

    @property
    def value_type(self) -> str:
        # The library aliases have already discharged the descriptor proof arguments.
        return {"binary32": "Binary32", "binary64": "Binary64"}[self.precision]


@dataclass(frozen=True)
class Value:
    lean: str
    precision: str


def cast(value: Value, ctx: Context, *, explicit=False) -> str:
    if value.precision == ctx.precision:
        return value.lean
    if not explicit and FORMATS[value.precision][1] > FORMATS[ctx.precision][1]:
        raise Refusal(
            "Mixed-precision operation needs one rounding after exact arithmetic; "
            "narrowing the operand first would change FPCore semantics"
        )
    return (
        "(ExecFloat.Binary.ofModel (Model.cast "
        f"FloatFormat.{value.precision} {ctx.fmt} "
        f"(ExecFloat.Binary.toModel {value.lean}) .{MODES[ctx.mode]}) : {ctx.value_type})"
    )


class Translator:
    def __init__(self):
        self.counter = 0
        self.rounding_attributes = set()
        self.precision_attributes = set()

    def fresh(self) -> str:
        self.counter += 1
        return f"v{self.counter}"

    def expr(self, node, env: dict[str, Value], ctx: Context) -> Value:
        if isinstance(node, str):
            if node in env:
                return env[node]
            try:
                q = number(node)
            except (ValueError, ZeroDivisionError):
                raise Refusal(f"Unsupported constant or free variable: {node}") from None
            if q == 0 and node.startswith("-"):
                return Value(f"(ExecFloat.Binary.zero true : {ctx.value_type})", ctx.precision)
            return Value(
                f"(ExecFloat.Binary.ofRat {rational(q)} .{MODES[ctx.mode]} "
                f": {ctx.value_type})", ctx.precision
            )
        if not isinstance(node, list) or not node or not isinstance(node[0], str):
            raise Refusal("Expected scalar expression: " + render(node))
        op, *args = node
        if op == "!":
            attrs, body = properties(args)
            if len(body) != 1:
                raise Refusal("Annotation must contain exactly one expression")
            for key, dest in [(":round", self.rounding_attributes),
                              (":precision", self.precision_attributes)]:
                if key in attrs:
                    dest.add(render(attrs[key]))
            return self.expr(body[0], env, ctx.annotated(attrs))
        if op in ("let", "let*"):
            if len(args) != 2 or not isinstance(args[0], list):
                raise Refusal(f"Malformed {op}")
            scope = dict(env)
            bindings = []
            for binding in args[0]:
                if len(binding) != 2 or not isinstance(binding[0], str):
                    raise Refusal(f"Malformed {op} binding")
                value = self.expr(binding[1], scope if op == "let*" else env, ctx)
                name = self.fresh()
                bindings.append(f"let {name} := {value.lean}; ")
                scope[binding[0]] = Value(name, value.precision)
            body = self.expr(args[1], scope, ctx)
            return Value("(" + "".join(bindings) + body.lean + ")", body.precision)
        if op == "if":
            if len(args) != 3:
                raise Refusal("Malformed if")
            cond = self.boolean(args[0], env, ctx)
            yes = self.expr(args[1], env, ctx)
            no = self.expr(args[2], env, ctx)
            if yes.precision != no.precision:
                raise Refusal("Branches return different precisions; no implicit result cast")
            return Value(
                f"(if {cond} then {yes.lean} else {no.lean})", yes.precision
            )
        if op in ("while", "while*", "for", "for*", "tensor", "tensor*", "array"):
            raise Refusal(f"Scalar straight-line translator does not implement {op}")
        if op == "cast" and len(args) == 1:
            return Value(cast(self.expr(args[0], env, ctx), ctx, explicit=True), ctx.precision)
        values = [cast(self.expr(x, env, ctx), ctx) for x in args]
        mode = MODES[ctx.mode]
        if op in ("+", "-", "*", "/") and len(values) == 2:
            if mode == "nearest":
                return Value(f"({values[0]} {op} {values[1]})", ctx.precision)
            method = {"+": "add", "-": "sub", "*": "mul", "/": "div"}[op]
            decoded = " ".join(f"(ExecFloat.Binary.toModel {v})" for v in values)
            return Value(
                f"(ExecFloat.Binary.ofModel (Model.{method} {decoded} .{mode}) "
                f": {ctx.value_type})",
                ctx.precision,
            )
        if op == "-" and len(values) == 1:
            return Value(f"(-{values[0]})", ctx.precision)
        if op == "fabs" and len(values) == 1:
            return Value(f"(abs {values[0]})", ctx.precision)
        if op == "fma" and len(values) == 3:
            decoded = " ".join(f"(ExecFloat.Binary.toModel {v})" for v in values)
            return Value(
                f"(ExecFloat.Binary.ofModel (Model.fma {decoded} .{mode}) "
                f": {ctx.value_type})", ctx.precision
            )
        if op == "sqrt" and len(values) == 1:
            return Value(
                "(ExecFloat.Binary.ofModel (Model.sqrt "
                f"(ExecFloat.Binary.toModel {values[0]}) .{mode}) "
                f": {ctx.value_type})", ctx.precision
            )
        if op in CR and len(values) == 1:
            if mode != "nearest":
                raise Refusal(f"CorrectlyRounded.{CR[op]} has no {ctx.mode} API")
            return Value(
                f"(ExecFloat.Binary.CorrectlyRounded.{CR[op]} {values[0]})", ctx.precision
            )
        raise Refusal(f"No semantics-preserving FloatLib translation for {op}/{len(args)}")

    def boolean(self, node, env, ctx) -> str:
        if node == "TRUE":
            return "True"
        if node == "FALSE":
            return "False"
        if not isinstance(node, list) or not node:
            raise Refusal("Unsupported Boolean expression: " + render(node))
        op, *args = node
        if op in ("and", "or") and args:
            symbol = " ∧ " if op == "and" else " ∨ "
            return "(" + symbol.join(self.boolean(a, env, ctx) for a in args) + ")"
        if op == "not" and len(args) == 1:
            return "(¬ " + self.boolean(args[0], env, ctx) + ")"
        if op in ("<", "<=", ">", ">=", "==") and len(args) > 2:
            return "(" + " ∧ ".join(
                self.boolean([op, left, right], env, ctx)
                for left, right in zip(args, args[1:])) + ")"
        if op in ("<", "<=", ">", ">=", "==", "!=") and len(args) == 2:
            operands = [self.expr(a, env, ctx) for a in args]
            widest = max(operands, key=lambda a: FORMATS[a.precision][1]).precision
            x, y = [cast(a, Context(widest)) for a in operands]
            # Compare stored IEEE values; Model.compare is unordered on NaNs.
            cmp = f"Model.compare (ExecFloat.Binary.toModel {x}) (ExecFloat.Binary.toModel {y})"
            if op == "!=":
                return f"({cmp} ≠ some .eq)"
            tests = {"<": [".lt"], "<=": [".lt", ".eq"], ">": [".gt"],
                     ">=": [".gt", ".eq"], "==": [".eq"]}[op]
            return "(" + " ∨ ".join(f"{cmp} = some {t}" for t in tests) + ")"
        raise Refusal("Unsupported Boolean expression: " + render(node))


def cores(path: Path):
    for index, form in enumerate(parse(path.read_text())):
        if not isinstance(form, list) or not form or form[0] != "FPCore":
            raise Refusal("Top-level form is not FPCore")
        rest = form[1:]
        ident = None
        if rest and isinstance(rest[0], str):
            ident = rest.pop(0)
        if not rest or not isinstance(rest[0], list):
            raise Refusal("Missing FPCore arguments")
        args, *rest = rest
        attrs, body = properties(rest)
        if len(body) != 1:
            raise Refusal("FPCore requires exactly one body")
        name = attrs.get(":name", ident or str(index))
        name = name.text if isinstance(name, Quoted) else render(name)
        yield index, name, args, attrs, body[0]


def translate(args: list, attrs: dict, body, precision: str, method: str, case_id: str) -> dict:
    """Return commands and metadata; scalar argument annotations remain authoritative."""
    translator = Translator()
    # Both requested experiments specialize unannotated operations to their format.
    # Explicit source annotations override that specialization.
    ctx = Context(precision).annotated(attrs)
    if ":round" in attrs:
        translator.rounding_attributes.add(render(attrs[":round"]))
    if ":precision" in attrs:
        translator.precision_attributes.add(render(attrs[":precision"]))
    env = {}
    binders = []
    for index, arg in enumerate(args):
        arg_ctx = ctx
        if isinstance(arg, list):
            if not arg or arg[0] != "!":
                raise Refusal("Tensor and array arguments are unsupported")
            arg_attrs, tail = properties(arg[1:])
            if len(tail) != 1:
                raise Refusal("Malformed argument annotation")
            arg_ctx = ctx.annotated(arg_attrs)
            arg = tail[0]
        if not isinstance(arg, str):
            raise Refusal("Argument name must be a symbol")
        name = f"x{index}"
        env[arg] = Value(name, arg_ctx.precision)
        binders.append(f"({name} : {arg_ctx.value_type})")
    value = translator.expr(body, env, ctx)
    declaration = "case_" + hashlib.sha256(case_id.encode()).hexdigest()[:20]
    prefix = {"forward": "roundoff mixed", "closed": "roundoff closed",
              "backward": "roundoff (backward := true)"}[method]
    computation = f"ExecFloat.Binary.toReal {value.lean}"
    if binders:
        computation = "fun " + " ".join(binders) + " => " + computation
    return {
        "id": case_id,
        "declaration": declaration,
        "commands": [f"{prefix} theorem {declaration} := {computation}"],
        "effective_precision": ctx.precision,
        "rounding": ctx.mode,
        "rounding_attributes": sorted(translator.rounding_attributes),
        "precision_attributes": sorted(translator.precision_attributes),
        "precondition": render(attrs.get(":pre", "TRUE")),
    }
