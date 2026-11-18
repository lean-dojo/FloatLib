"""Source-domain goals and untrusted rational candidates for numeric closure.

The candidate calculation is a search heuristic. It cannot establish a bound:
the generated Lean implication must close, including every range premise.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import math

from sexpr import Refusal, number, properties, rational, render
from translate import Context, FORMATS, Translator, Value


class RealExpression:
    """The exact real interpretation used for preconditions and references."""
    def __init__(self):
        self.next = 0

    def expr(self, node, env):
        if isinstance(node, str):
            if node in env:
                return env[node]
            if node in ("TRUE", "FALSE"):
                return {"TRUE": "True", "FALSE": "False"}[node]
            try:
                return rational(number(node), "ℝ")
            except (ValueError, ZeroDivisionError):
                raise Refusal("Unsupported real constant: " + node) from None
        if not isinstance(node, list) or not node:
            raise Refusal("Expected a real FPCore expression")
        op, *args = node
        if op == "!":
            _, body = properties(args)
            if len(body) != 1:
                raise Refusal("Malformed real annotation")
            return self.expr(body[0], env)
        if op in ("let", "let*"):
            if len(args) != 2 or not isinstance(args[0], list):
                raise Refusal("Malformed real binding")
            scope, clauses = dict(env), []
            for name, term in args[0]:
                value = self.expr(term, scope if op == "let*" else env)
                fresh = f"r{self.next}"
                self.next += 1
                clauses.append(f"let {fresh} : ℝ := {value}; ")
                scope[name] = fresh
            return "(" + "".join(clauses) + self.expr(args[1], scope) + ")"
        if op == "if":
            raise Refusal("Numeric closure needs a proof that rounded and real branches agree")
        values = [self.expr(arg, env) for arg in args]
        if op in ("+", "-", "*", "/") and len(values) == 2:
            return f"({values[0]} {op} {values[1]})"
        if op == "-" and len(values) == 1:
            return f"(-{values[0]})"
        if op == "cast" and len(values) == 1:
            return values[0]
        if op == "fma" and len(values) == 3:
            return f"({values[0]} * {values[1]} + {values[2]})"
        if op in ("sqrt", "exp", "log", "fabs") and len(values) == 1:
            function = "abs" if op == "fabs" else "Real." + op
            return f"({function} {values[0]})"
        if op == "expm1" and len(values) == 1:
            return f"(Real.exp {values[0]} - 1)"
        if op == "log1p" and len(values) == 1:
            return f"(Real.log (1 + {values[0]}))"
        if op in ("and", "or"):
            if not values:
                return "True" if op == "and" else "False"
            return "(" + (" ∧ " if op == "and" else " ∨ ").join(values) + ")"
        if op == "not" and len(values) == 1:
            return f"(¬ {values[0]})"
        if op in ("<", "<=", ">", ">=", "==", "!=") and len(values) >= 2:
            symbol = {"<=": "≤", ">=": "≥", "==": "=", "!=": "≠"}.get(op, op)
            pairs = ([(x, y) for i, x in enumerate(values) for y in values[i + 1:]]
                     if op == "!=" else list(zip(values, values[1:])))
            return "(" + " ∧ ".join(f"{x} {symbol} {y}" for x, y in pairs) + ")"
        raise Refusal(f"Unsupported real operator for numeric closure: {op}/{len(args)}")


def source_box(pre, names):
    """Extract only conjunctive variable/constant bounds; never strengthen a disjunction."""
    boxes = {name: [None, None] for name in names}

    def endpoint(node):
        try:
            return number(node) if isinstance(node, str) else None
        except (ValueError, ZeroDivisionError):
            return None

    def update(name, side, value):
        if value is None:
            return
        previous = boxes[name][side]
        boxes[name][side] = value if previous is None else (
            max(previous, value) if side == 0 else min(previous, value))

    def visit(node):
        if not isinstance(node, list) or not node:
            return
        if node[0] == "and":
            for part in node[1:]:
                visit(part)
        elif node[0] in ("<", "<=", ">", ">=", "=="):
            for left, right in zip(node[1:], node[2:]):
                op = node[0]
                if op in (">", ">="):
                    left, right, op = right, left, "<="
                if isinstance(left, str) and left in boxes:
                    update(left, 1, endpoint(right))
                    if op == "==":
                        update(left, 0, endpoint(right))
                if isinstance(right, str) and right in boxes:
                    update(right, 0, endpoint(left))
                    if op == "==":
                        update(right, 1, endpoint(left))
    visit(pre)
    if any(lo is None or hi is None or lo > hi for lo, hi in boxes.values()):
        raise Refusal("Candidate search needs a finite nonempty box implied by source conjuncts")
    return boxes


@dataclass
class Estimate:
    lower: Fraction
    upper: Fraction
    error: Fraction = Fraction(0)

    @property
    def magnitude(self):
        return max(abs(self.lower), abs(self.upper))

    @property
    def min_magnitude(self):
        return 0 if self.lower <= 0 <= self.upper else min(abs(self.lower), abs(self.upper))


def candidate(node, env, ctx):
    """Rational arithmetic plus approximate elementary values proposes, never proves."""
    exponent, fraction = FORMATS[ctx.precision]
    unit = Fraction(2) ** -(fraction + (ctx.mode in ("nearestEven", "nearestAway")))
    eta = Fraction(2) ** (1 - ((1 << (exponent - 1)) - 1) - fraction)

    def rounded(lo, hi, error=Fraction(0)):
        return Estimate(lo, hi, error + unit * (max(abs(lo), abs(hi)) + error) + eta)

    if isinstance(node, str):
        if node in env:
            return env[node]
        try:
            value = number(node)
        except (ValueError, ZeroDivisionError):
            raise Refusal("Candidate search cannot evaluate: " + node) from None
        return rounded(value, value)
    op, *args = node
    if op == "!":
        attrs, body = properties(args)
        return candidate(body[0], env, ctx.annotated(attrs))
    if op in ("let", "let*"):
        scope = dict(env)
        for name, value in args[0]:
            scope[name] = candidate(value, scope if op == "let*" else env, ctx)
        return candidate(args[1], scope, ctx)
    values = [candidate(arg, env, ctx) for arg in args]
    if op == "-" and len(values) == 1:
        a = values[0]
        return Estimate(-a.upper, -a.lower, a.error)
    if op == "fabs" and len(values) == 1:
        a = values[0]
        return Estimate(a.min_magnitude, a.magnitude, a.error)
    if op == "cast" and len(values) == 1:
        a = values[0]
        return rounded(a.lower, a.upper, a.error)
    if op in ("+", "-", "*", "/", "fma") and len(values) in (2, 3):
        a, b = values[:2]
        if op == "+":
            return rounded(a.lower + b.lower, a.upper + b.upper, a.error + b.error)
        if op == "-":
            return rounded(a.lower - b.upper, a.upper - b.lower, a.error + b.error)
        if op in ("*", "fma"):
            products = [x * y for x in (a.lower, a.upper) for y in (b.lower, b.upper)]
            lo, hi = min(products), max(products)
            error = a.magnitude * b.error + b.magnitude * a.error + a.error * b.error
            if op == "fma":
                c = values[2]
                lo, hi, error = lo + c.lower, hi + c.upper, error + c.error
            return rounded(lo, hi, error)
        margin = b.min_magnitude - b.error
        if margin <= 0:
            raise Refusal("Candidate denominator enclosure contains zero")
        quotients = [x / y for x in (a.lower, a.upper) for y in (b.lower, b.upper)]
        lo, hi = min(quotients), max(quotients)
        error = (a.error + max(abs(lo), abs(hi)) * b.error) / margin
        return rounded(lo, hi, error)
    if op in ("sqrt", "exp", "expm1", "log", "log1p") and len(values) == 1:
        a = values[0]
        function = getattr(math, op)
        try:
            lo, hi = Fraction(function(float(a.lower))), Fraction(function(float(a.upper)))
            if op in ("log", "log1p"):
                margin = a.lower + (op == "log1p") - a.error
                if margin <= 0:
                    raise ValueError("Logarithm domain includes zero")
                error = a.error / margin
            elif op == "sqrt":
                if a.lower <= a.error:
                    error = Fraction(math.sqrt(float(a.error)))
                else:
                    denominator = Fraction(math.sqrt(float(a.lower - a.error)))
                    error = a.error / denominator
            else:
                error = Fraction(math.exp(float(a.upper + a.error))) * a.error
            return rounded(lo, hi, error)
        except (ValueError, OverflowError, ZeroDivisionError):
            raise Refusal(f"Candidate {op} range is not supported") from None
    raise Refusal(f"Candidate search does not implement {op}")


def pre_leaves(node):
    if isinstance(node, list) and node and node[0] == "and":
        return [part for arg in node[1:] for part in pre_leaves(arg)]
    if isinstance(node, list) and node and node[0] in ("<", "<=", ">", ">=", "==") and len(node) > 3:
        return [[node[0], x, y] for x, y in zip(node[1:], node[2:])]
    return [node]


def numeric_case(args, attrs, body, precision, method, original):
    if method == "backward":
        raise Refusal("Backward bounds concern input perturbations; no absolute-error ratio")
    ctx = Context(precision).annotated(attrs)
    env, real_env, binders, finite, names = {}, {}, [], [], []
    for index, arg in enumerate(args):
        context = ctx
        if isinstance(arg, list):
            properties_, tail = properties(arg[1:])
            context = ctx.annotated(properties_)
            arg = tail[0]
        name = f"x{index}"
        names.append(arg)
        env[arg] = Value(name, context.precision)
        real_env[arg] = f"(ExecFloat.Binary.toReal {name})"
        binders.append(f"({name} : {context.value_type})")
        finite.append(f"(hf{index} : ExecFloat.Binary.isFinite {name} = true)")
    pre = attrs.get(":pre", "TRUE")
    box = source_box(pre, names)
    estimate = candidate(body, {name: Estimate(*box[name]) for name in names}, ctx)
    # Round the positive proposal up to one binary significant bit. This small
    # inflation also avoids pretending the heuristic is an optimized bound.
    error = estimate.error
    if error <= 0:
        proposed = Fraction(0)
    else:
        shift = error.numerator.bit_length() - error.denominator.bit_length()
        proposed = Fraction(2) ** shift
        if proposed < error:
            proposed *= 2
    translator = RealExpression()
    reference = translator.expr(body, real_env)
    hypotheses = [translator.expr(part, real_env) for part in pre_leaves(pre)]
    pre_binders = [f"(hp{i} : {part})" for i, part in enumerate(hypotheses)]
    value = Translator().expr(body, env, ctx)
    ident = original["id"] + ":numeric"
    declaration = original["declaration"] + "_numeric"
    application = original["declaration"] + " " + " ".join(f"x{i}" for i in range(len(args)))
    if method == "forward":
        # Split the conjunction only: on Lean v4.36.0 `constructor` also applies to `a ≤ b` on the reals.
        premises = "repeat' apply And.intro\n    all_goals suite_range"
        first = f"({application} (by\n    {premises})).2.bound"
    else:
        premises = "roundoff\n    all_goals suite_range"
        first = f"({application} (by\n    {premises}))"
    normalize = "norm_num only at " + " ".join(f"hp{i}" for i in range(len(hypotheses)))
    # The premises of a binary64 theorem need a recursion depth between 4,000 and 10,000 on Lean v4.36.0
    # (the default 512 was enough on v4.35.0).
    command = f"""set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem {declaration} {' '.join(binders + finite + pre_binders)} :
    |ExecFloat.Binary.toReal {value.lean} - {reference}| ≤ {rational(proposed, 'ℝ')} := by
  {normalize}
  have hbound := {first}
  have hfinal := le_trans hbound (show _ ≤ {rational(proposed, 'ℝ')} from by
    suite_format <;> interval)
  simpa only [div_one] using hfinal"""
    return {
        "id": ident, "declaration": declaration,
        "commands": [*original["commands"], command],
        "proposed_bound": str(proposed),
        "proposal_policy": "Untrusted propagated estimate, rounded up to a power of two",
        "numeric_contract": "Absolute error from real source expression on finite stored source-domain inputs",
        "source_precondition": render(pre),
        "source_box": {name: [str(value) for value in bounds] for name, bounds in box.items()},
    }
