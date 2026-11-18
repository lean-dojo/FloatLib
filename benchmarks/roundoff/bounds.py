#!/usr/bin/env python3
"""Forward bounds of `roundoff` against measured errors, in binary32.

For each benchmark program this script runs the program in binary32 (numpy `float32` for the
arithmetic, a correctly rounded exponential and logarithm from mpmath), computes the exact
reference with rational or 300-bit arithmetic, and evaluates three bounds:

* the bound that `roundoff mixed theorem` states, by following its recurrences;
* for a summation loop, the closed form `List.abs_sub_le_of_sumFold` of that bound;
* the closed form that `roundoff closed theorem` states: each term weighted by the bound of its
  own perturbation.

It reports each bound over the measured error. The bounds are transcribed from the statements
that `benchmarks/roundoff/Programs.lean` prints. Nothing here is checked by Lean: the numbers
are the script's.

Three more tables measure the tightness work on cancellation and on constants:

* a scaled difference `(x - y) * z` whose subtraction is exact (Sterbenz), with the bound that
  charges the subtraction a rounding and the bound that recognizes it from the hypotheses;
* the linear constants `(n - 1) u` of a sum (Rump 2012) and `n u` of an inner product (Jeannerod
  and Rump 2013), proved in `Analysis/Summation.lean`, against the powers `(1 + u) ^ k - 1`, in
  binary32 and in a format with eight bits of precision;
* a relative entropy of two close distributions as the sum of `p * (log p - log q)`, whose
  terms cancel, and as the sum of `p * expm1x (log q - log p)`, whose terms are nonnegative.

Two more measure the rounding attributes and the closed form of a correctly rounded function:

* the lower endpoint of `x * y + z`, both operations rounded toward negative infinity, whose
  bound uses the unit roundoff `2 u` of a directed attribute, and the same endpoint by one
  fused multiply-add rounded toward negative infinity;
* one call of `expm1x` near zero, with the closed forward bound that spreads the rounding of the
  function over the three terms of `exp x - 1 - x` and the bound that keeps it on its value.
"""

from __future__ import annotations

import argparse
import json
import statistics
from fractions import Fraction

import mpmath as mp
import numpy as np

mp.mp.prec = 300

U = mp.mpf(2) ** -24               # unit roundoff of binary32
ETA = mp.mpf(2) ** -150            # half the subnormal spacing
ZERO = mp.mpf(0)


def exact(value):
    """The exact value of a binary32 number, as a 300-bit float."""
    return mp.mpf(float(value))


def round32(q: Fraction) -> np.float32:
    """Round a rational to binary32, to nearest with ties to even."""
    if q == 0:
        return np.float32(0)
    sign = -1 if q < 0 else 1
    q = abs(q)
    exponent = q.numerator.bit_length() - q.denominator.bit_length()
    if Fraction(2) ** exponent > q:
        exponent -= 1
    ulp = Fraction(2) ** max(exponent - 23, -149)
    scaled = q / ulp
    floor = scaled.numerator // scaled.denominator
    rest = scaled - floor
    if rest > Fraction(1, 2) or (rest == Fraction(1, 2) and floor % 2 == 1):
        floor += 1
    return np.float32(float(sign * floor * ulp))


def round_bits(q: Fraction, precision: int, emin: int) -> Fraction:
    """Round a rational to nearest, ties to even, in a binary format with `precision` bits and
    least subnormal `2 ** emin`. No overflow."""
    if q == 0:
        return Fraction(0)
    sign = -1 if q < 0 else 1
    q = abs(q)
    exponent = q.numerator.bit_length() - q.denominator.bit_length()
    if Fraction(2) ** exponent > q:
        exponent -= 1
    ulp = Fraction(2) ** max(exponent - (precision - 1), emin)
    scaled = q / ulp
    floor = scaled.numerator // scaled.denominator
    rest = scaled - floor
    if rest > Fraction(1, 2) or (rest == Fraction(1, 2) and floor % 2 == 1):
        floor += 1
    return sign * floor * ulp


def to_fraction(value) -> Fraction:
    """An mpf as a Fraction (mpf values are dyadic)."""
    man, exp = mp.frexp(value)
    return Fraction(int(mp.ldexp(man, 400))) * Fraction(2) ** (int(exp) - 400)


def exp32(x: np.float32) -> np.float32:
    return round32(to_fraction(mp.exp(mp.mpf(float(x)))))


def log32(x: np.float32) -> np.float32:
    return round32(to_fraction(mp.log(mp.mpf(float(x)))))


def expm1x32(x: np.float32) -> np.float32:
    """`exp x - 1 - x`, correctly rounded to binary32."""
    value = mp.mpf(float(x))
    return round32(to_fraction(mp.exp(value) - 1 - value))


# ---------------------------------------------------------------------------------------------
# The recurrences of the generated theorems. Each returns (reference, relative, absolute): the
# theorem states |computed - reference| <= relative * |reference| + absolute.
# `tight` evaluates what the bound would be if the analysis treated the first step of a loop from
# zero as exact (`0 + t` does not round). The analysis does not do that: the column measures what
# it would gain.


def fold_sum(terms, budgets, tight=False):
    """A summation loop `s := s + t` from zero: `terms` are the exact terms, `budgets` the absolute
    error of each computed term. Returns the exact sum and the loop's (relative, absolute)."""
    s, r, a = ZERO, ZERO, ZERO
    first = True
    for p, c in zip(terms, budgets):
        if tight and first:
            # The first addition, to an exact zero, does not round.
            a, r = c, ZERO
        else:
            a = (1 + U) * (r * abs(s) + a + c)
            r = U
        first = False
        s = s + p
    return s, r, a


def bound_sum(x, tight=False):
    xs = [exact(v) for v in x]
    s, r, a = fold_sum(xs, [ZERO] * len(xs), tight)
    return s, r, a


def bound_dot(x, y, tight=False):
    ps = [exact(a) * exact(b) for a, b in zip(x, y)]
    s, r, a = fold_sum(ps, [U * abs(p) + ETA for p in ps], tight)
    return s, r, a


def bound_horner(coefficients, x, tight=False):
    xr = exact(x)
    s, r, a = ZERO, ZERO, ZERO
    first = True
    for c in coefficients:
        if tight and first:
            # `0 * x + c` is exact.
            a, r = ZERO, ZERO
        else:
            a = (1 + U) * (((1 + U) * r + U) * abs(s * xr) + ((1 + U) * (a * abs(xr)) + ETA))
            r = U
        first = False
        s = s * xr + exact(c)
    return s, r, a


def bound_linear(w, x, b, tight=False):
    s, r, a = bound_dot(w, x, tight)
    carried = r * abs(s) + a
    return s + exact(b), U, (1 + U) * carried


def bound_mlp(W, b, v, c, x, active, tight=False):
    sigma, rho, alpha = ZERO, ZERO, ZERO
    first = True
    for k in range(len(v)):
        S, R, A = bound_dot(W[k], x, tight)
        vk = exact(v[k])
        if active[k]:
            hidden = S + exact(b[k])
            hidden_relative = U
            hidden_absolute = (1 + U) * (R * abs(S) + A)
        else:
            hidden, hidden_relative, hidden_absolute = ZERO, ZERO, ZERO
        term = vk * hidden
        budget = ((1 + U) * hidden_relative + U) * abs(term) + \
            ((1 + U) * (hidden_absolute * abs(vk)) + ETA)
        if tight and first:
            alpha, rho = budget, ZERO
        else:
            alpha = (1 + U) * (rho * abs(sigma) + alpha + budget)
            rho = U
        first = False
        sigma = sigma + term
    return sigma + exact(c), U, (1 + U) * (rho * abs(sigma) + alpha)


def closed_sum(terms, budgets):
    """`List.abs_sub_le_of_sumFold`: ((1 + u)^n - 1) * sum |p| + (1 + u)^n * sum c."""
    n = len(terms)
    growth = (1 + U) ** n
    return (growth - 1) * mp.fsum(abs(p) for p in terms) + growth * mp.fsum(budgets)


def backward_sum(terms, own, absolute):
    """The forward bound from the backward theorem of a summation loop: the term at index j of n
    is weighted by (1 + u)^(n - 1 - j + own) - 1, and `absolute` is the step's absolute error."""
    n = len(terms)
    weighted = mp.fsum(((1 + U) ** (n - 1 - j + own) - 1) * abs(p) for j, p in enumerate(terms))
    return weighted + absolute * mp.fsum((1 + U) ** k for k in range(n))


def closed_horner(coefficients, x):
    """`horner_closed`: the changes of the coefficients accumulated through the exact loop, plus
    the underflow term."""
    n = len(coefficients)
    xr = abs(exact(x))
    e = ZERO
    for j, c in enumerate(coefficients):
        e = e * xr + abs(exact(c)) * ((1 + U) ** (2 * (n - 1 - j) + 1) - 1)
    return e + ETA * (1 + U) * mp.fsum((xr * (1 + U) * (1 + U)) ** k for k in range(n))


def closed_mlp(W, b, v, c, x, active):
    """`mlp_closed`: a sum over the hidden units of sums over their weights, under the branch
    each rectifier takes, plus the accumulated underflow of the products."""
    h, n = len(v), len(x)
    inner_underflow = ETA * (1 + U) * mp.fsum((1 + U) ** k for k in range(n)) * (1 + U)
    total, accumulated = ZERO, ZERO
    for k in range(h):
        vk = abs(exact(v[k]))
        if active[k]:
            hidden = abs(mp.fsum(exact(W[k][j]) * exact(x[j]) for j in range(n)) + exact(b[k]))
            change = mp.fsum(abs(exact(W[k][j])) * ((1 + U) ** (n - 1 - j + 3) - 1) *
                             abs(exact(x[j])) for j in range(n)) + abs(exact(b[k])) * U
            underflow = inner_underflow
        else:
            hidden, change, underflow = ZERO, ZERO, ZERO
        total += vk * ((1 + U) ** (h - 1 - k + 3) - 1) * (hidden + change) + vk * change
        accumulated = (1 + U) * accumulated + (vk * underflow * (1 + U) + ETA) * (1 + U)
    return total + abs(exact(c)) * U + accumulated * (1 + U)


def exponential_changes(x):
    """What the perturbations change in a sum of exponentials, and its accumulated underflow."""
    n = len(x)
    change = mp.fsum(mp.exp(exact(v)) * ((1 + U) ** (n - 1 - i + 2) - 1) for i, v in enumerate(x))
    underflow = ETA * (1 + U) * mp.fsum((1 + U) ** k for k in range(n))
    return change, underflow


def closed_softmax(x, computed_first, computed_sum):
    """`softmax_closed`: the first exponential over the sum of all, with a perturbed divisor."""
    first = mp.exp(exact(x[0]))
    total = mp.fsum(mp.exp(exact(v)) for v in x)
    change, underflow = exponential_changes(x)
    e0, s = abs(exact(computed_first)), abs(exact(computed_sum))
    assert change < total and underflow < s
    main = (first * ((1 + U) ** 2 - 1) * total + first * change) / (total * (total - change))
    return main + ((ETA * s + e0 * underflow) / (s * (s - underflow)) * (1 + U) + ETA)


def closed_logsumexp(x, computed_sum):
    """`logSumExp_closed`: the logarithm of a perturbed sum, then its own rounding."""
    total = mp.fsum(mp.exp(exact(v)) for v in x)
    change, underflow = exponential_changes(x)
    s = exact(computed_sum)
    assert change < total and underflow < s
    inner = change / (total - change)
    return inner + (abs(mp.log(total)) + inner) * U + (underflow / (s - underflow) * (1 + U) + ETA)


def closed_forms(kind, *arguments):
    """(closed form of a summation loop, generated closed form) of a program, as absolute bounds.
    Only a sum, a dot product and a linear layer have the first."""
    if kind == "softmax":
        return None, closed_softmax(*arguments)
    if kind == "logsumexp":
        return None, closed_logsumexp(*arguments)
    if kind == "horner":
        return None, closed_horner(*arguments)
    if kind == "mlp":
        return None, closed_mlp(*arguments)
    if kind == "sum":
        terms = [exact(v) for v in arguments[0]]
        return closed_sum(terms, [ZERO] * len(terms)), backward_sum(terms, 1, ZERO)
    x, y = arguments[0], arguments[1]
    terms = [exact(a) * exact(b) for a, b in zip(x, y)]
    loop = closed_sum(terms, [U * abs(p) + ETA for p in terms])
    if kind == "dot":
        return loop, backward_sum(terms, 2, ETA * (1 + U))
    # A linear layer: the bias addition rounds once more.
    bias = exact(arguments[2])
    reference = mp.fsum(terms) + bias
    generated = mp.fsum(((1 + U) ** (len(terms) - 1 - j + 3) - 1) * abs(p)
                    for j, p in enumerate(terms)) \
        + U * abs(bias) + ETA * (1 + U) * mp.fsum((1 + U) ** k for k in range(len(terms))) * (1 + U)
    return U * abs(reference) + (1 + U) * loop, generated


def fold_expsum(x, tight=False):
    """The loop `s := s + exp x_i` of nonnegative terms: a relative error weighted by the terms."""
    s, r, a = ZERO, ZERO, ZERO
    u, eta = U, ETA
    first = True
    for v in x:
        e = mp.exp(mp.mpf(float(v)))
        if tight and first:
            r, a = u, eta
        else:
            r = (1 + u) * ((r * abs(s) + u * e) / abs(s + e)) + u
            a = (1 + u) * (a + eta)
        first = False
        s = s + e
    return s, r, a


def bound_softmax(x, computed_first=None, computed_sum=None, tight=False):
    u, eta = U, ETA
    term, relative_error, absolute_error = fold_expsum(x, tight)
    magnitude = abs(term)
    quotient = absolute_error / magnitude
    total = relative_error + quotient
    difference = 1 - total
    reference = mp.exp(mp.mpf(float(x[0]))) / term
    relative = (1 + u) * ((u + total) / difference) + u
    absolute = (1 + u) * (eta / (difference * magnitude)) + eta
    return reference, relative, absolute


def bound_logsumexp(x, computed_sum, tight=False):
    u, eta = U, ETA
    term, relative_error, absolute_error = fold_expsum(x, tight)
    minimum = min(mp.mpf(float(computed_sum)), term)
    quotient = (relative_error * abs(term) + absolute_error) / minimum
    return mp.log(term), u, (1 + u) * quotient + eta


def bound_gradient_difference(s):
    u, eta = U, ETA
    sr = mp.mpf(float(s))
    quotient = 1 / (1 + sr)
    total = ((1 + u) * (u / (1 - u)) + u) * abs(quotient) + eta
    return quotient - 1, u, (1 + u) * total


def bound_gradient_quotient(s):
    u, eta = U, ETA
    sr = mp.mpf(float(s))
    return -(sr / (1 + sr)), (1 + u) * (u / (1 - u)) + u, eta


# ---------------------------------------------------------------------------------------------
# The programs, in binary32.


def run_sum(x):
    s = np.float32(0)
    for v in x:
        s = np.float32(s + v)
    return s


def run_dot(x, y):
    s = np.float32(0)
    for a, b in zip(x, y):
        s = np.float32(s + np.float32(a * b))
    return s


def run_horner(coefficients, x):
    s = np.float32(0)
    for c in coefficients:
        s = np.float32(np.float32(s * x) + c)
    return s


def run_expsum(x):
    s = np.float32(0)
    for v in x:
        s = np.float32(s + exp32(v))
    return s


def run_mlp(W, b, v, c, x):
    s = np.float32(0)
    active = []
    for k in range(len(v)):
        z = np.float32(run_dot(W[k], x) + b[k])
        active.append(bool(z > 0))
        h = z if z > 0 else np.float32(0)
        s = np.float32(s + np.float32(v[k] * h))
    return np.float32(s + c), active


# ---------------------------------------------------------------------------------------------


def ratio(computed, reference, relative, absolute):
    """Bound over measured error, and the measured error; `None` when the result is exact."""
    error = abs(mp.mpf(float(computed)) - reference)
    bound = relative * abs(reference) + absolute
    assert error <= bound, (error, bound)
    return (None if error == 0 else float(bound / error)), error, bound


def cases(rng, trials):
    """The benchmark cases: name, size, and a function from a trial to its ratios of bound over
    error."""
    def both(run, bound, kind=None):
        def trial():
            computed, arguments = run()
            stated = ratio(computed, *bound(*arguments, tight=False))
            first = ratio(computed, *bound(*arguments, tight=True))
            closed = None
            if kind is not None and stated[0] is not None:
                loop, generated = closed_forms(kind, *arguments)
                error = stated[1]
                assert (loop is None or error <= loop) and error <= generated
                closed = (None if loop is None else float(loop / error),
                          float(generated / error))
            return stated, first, closed
        return trial

    def normal(n):
        return rng.standard_normal(n).astype(np.float32)

    def positive(n):
        return rng.uniform(0.5, 1.5, n).astype(np.float32)

    result = []
    for n in (4, 16, 256, 4096):
        def sum_case(draw=normal, n=n):
            x = draw(n)
            return run_sum(x), (x,)
        result.append(("sum, mixed signs", n, both(sum_case, bound_sum, "sum")))
        result.append(("sum, positive terms", n,
                       both(lambda n=n: sum_case(positive, n), bound_sum, "sum")))

        def worst_case(n=n):
            # One, then n - 1 terms of half an ulp of one: every addition is a tie that rounds
            # back to one, so the errors add up.
            x = np.array([1.0] + [2.0 ** -24] * (n - 1), dtype=np.float32)
            return run_sum(x), (x,)
        result.append(("sum, worst case", n, both(worst_case, bound_sum, "sum")))

        def worst_dot(n=n):
            # The same sum from exact products: 1 * 1, then n - 1 products 2^-12 * 2^-12.
            x = np.array([1.0] + [2.0 ** -12] * (n - 1), dtype=np.float32)
            return run_dot(x, x), (x, x)
        result.append(("dot product, worst case", n, both(worst_dot, bound_dot, "dot")))

        def dot_case(n=n):
            x, y = normal(n), normal(n)
            return run_dot(x, y), (x, y)
        result.append(("dot product", n, both(dot_case, bound_dot, "dot")))

        def matmul_case(n=n):
            A, B = rng.standard_normal((3, n)).astype(np.float32), \
                rng.standard_normal((n, 3)).astype(np.float32)
            return run_dot(A[1], B[:, 2]), (A[1], B[:, 2])
        result.append(("matrix product entry", n, both(matmul_case, bound_dot, "dot")))

        def linear_case(n=n):
            w, x, b = normal(n) / np.float32(np.sqrt(n)), normal(n), normal(1)[0]
            return np.float32(run_dot(w, x) + b), (w, x, b)
        result.append(("linear layer output", n, both(linear_case, bound_linear, "linear")))
    for n in (4, 16, 64):
        def horner_case(n=n):
            coefficients, x = normal(n), np.float32(rng.uniform(-1.0, 1.0))
            return run_horner(coefficients, x), (coefficients, x)
        result.append(("Horner's rule", n, both(horner_case, bound_horner, "horner")))
    for n in (4, 16, 256):
        def softmax_case(n=n):
            x = (3 * rng.standard_normal(n)).astype(np.float32)
            first, total = exp32(x[0]), run_expsum(x)
            return np.float32(first / total), (x, first, total)
        result.append(("softmax weight", n, both(softmax_case, bound_softmax, "softmax")))

        def logsumexp_case(n=n):
            x = (3 * rng.standard_normal(n)).astype(np.float32)
            total = run_expsum(x)
            return log32(total), (x, total)
        result.append(("log-sum-exp", n, both(logsumexp_case, bound_logsumexp, "logsumexp")))
    for n, h in ((16, 8), (64, 32), (256, 64)):
        def mlp_case(n=n, h=h):
            W = (rng.standard_normal((h, n)) / np.sqrt(n)).astype(np.float32)
            b, v = normal(h), (rng.standard_normal(h) / np.sqrt(h)).astype(np.float32)
            c, x = normal(1)[0], normal(n)
            computed, active = run_mlp(W, b, v, c, x)
            return computed, (W, b, v, c, x, active)
        result.append(("perceptron output", n * 1000 + h, both(mlp_case, bound_mlp, "mlp")))
    return result


def gradient_rows():
    """The two schedules of the target gradient at fixed `s`: measured error, bound, and the part
    of the bound that does not shrink with the exact result."""
    rows = []
    for text in ("1e-2", "1e-4", "1e-6", "3.0459e-8", "1e-9"):
        s = np.float32(float(text))
        one = np.float32(1)
        difference = np.float32(np.float32(one / np.float32(one + s)) - one)
        quotient = np.float32(-np.float32(s / np.float32(one + s)))
        exact_value = -(mp.mpf(float(s)) / (1 + mp.mpf(float(s))))
        row = {"s": text, "exact": float(exact_value)}
        for name, computed, bound in (("difference", difference, bound_gradient_difference(s)),
                                      ("quotient", quotient, bound_gradient_quotient(s))):
            reference, relative, absolute = bound
            error = abs(mp.mpf(float(computed)) - reference)
            total = relative * abs(reference) + absolute
            assert error <= total
            row[name] = {"computed": float(computed), "error": float(error),
                         "bound": float(total), "relative_error": float(error / abs(exact_value)),
                         "bound_over_exact": float(total / abs(exact_value))}
        rows.append(row)
    return rows


def sterbenz_rows(rng, trials):
    """`(x - y) * z` with `y / 2 <= x <= 2 y`: the subtraction is exact. `charged` is the bound of
    the statement without that fact (the subtraction charged a rounding), `exact` the bound of
    `scaledDifference_forward` and `scaledDifference_closed`."""
    rows = []
    for name, spread in (("within a factor of two", None), ("within 1e-3", 1e-3),
                         ("within 1e-6", 1e-6)):
        ratios = {"mixed_charged": [], "mixed_exact": [], "closed_charged": [], "closed_exact": []}
        for _ in range(trials):
            y = np.float32(rng.uniform(0.5, 1.5))
            factor = rng.uniform(0.5, 2.0) if spread is None else 1 + spread * rng.uniform(-1, 1)
            x = np.float32(y * np.float32(factor))
            if not (y / np.float32(2) <= x <= np.float32(2) * y):
                continue
            z = np.float32(rng.standard_normal())
            computed = np.float32(np.float32(x - y) * z)
            xr, yr, zr = exact(x), exact(y), exact(z)
            assert exact(np.float32(x - y)) == xr - yr
            reference = (xr - yr) * zr
            error = abs(exact(computed) - reference)
            if error == 0:
                continue
            bounds = {
                "mixed_charged": ((1 + U) * U + U) * abs(reference) + ETA,
                "mixed_exact": U * abs(reference) + ETA,
                "closed_charged": (abs(xr) + abs(yr)) * ((1 + U) ** 2 - 1) * abs(zr) + ETA,
                "closed_exact": (abs(xr) + abs(yr)) * U * abs(zr) + ETA}
            for key, bound in bounds.items():
                assert error <= bound
                ratios[key].append(float(bound / error))
        rows.append({"case": name, "trials": len(ratios["mixed_exact"]),
                     **{key: statistics.median(values) for key, values in ratios.items()}})
    return rows


def constant_rows(rng, trials):
    """The linear constants of a sum and of an inner product against the powers, as constants and
    over measured errors. `precision` 24 is binary32 and 8 is the significand of bfloat16."""
    rows = []
    for precision, emin in ((24, -149), (8, -133)):
        u = Fraction(1, 2 ** precision)
        for n in (16, 256, 1024):
            power = (1 + u) ** (n - 1) - 1
            linear = (n - 1) * u
            results = {"sum": [], "dot": []}
            # Exact rational arithmetic: a few trials suffice for a median.
            for _ in range(min(trials, 5)):
                x = [round_bits(Fraction(float(v)), precision, emin)
                     for v in rng.uniform(0.5, 1.5, n)]
                y = [round_bits(Fraction(float(v)), precision, emin)
                     for v in rng.uniform(0.5, 1.5, n)]
                for kind in ("sum", "dot"):
                    terms = x if kind == "sum" else [a * b for a, b in zip(x, y)]
                    s = Fraction(0)
                    for index, term in enumerate(terms):
                        rounded = term if kind == "sum" else round_bits(term, precision, emin)
                        s = round_bits(s + rounded, precision, emin)
                    error = abs(s - sum(terms))
                    if error == 0:
                        continue
                    magnitude = sum(abs(t) for t in terms)
                    k = 0 if kind == "sum" else 1
                    # The closed form of `roundoff closed theorem`: term `j` weighted by the
                    # roundings it takes part in.
                    weighted = sum(abs(t) * ((1 + u) ** (n - j + k) - 1)
                                   for j, t in enumerate(terms))
                    classical = ((1 + u) ** (n - 1 + k) - 1) * magnitude
                    published = (n - 1 + k) * u * magnitude
                    assert error <= published and error <= weighted and error <= classical
                    results[kind].append((float(classical / error), float(weighted / error),
                                          float(published / error)))
            row = {"precision": precision, "n": n, "power_over_linear": float(power / linear)}
            for kind, values in results.items():
                row[kind] = {"classical": statistics.median(v[0] for v in values),
                             "weighted": statistics.median(v[1] for v in values),
                             "published": statistics.median(v[2] for v in values)}
            rows.append(row)
    return rows


def entropy_rows(rng, trials):
    """The relative entropy of two close distributions over 16 outcomes, with the logarithms
    computed by the program: `sum p * (log p - log q)`, whose terms cancel, and
    `sum p * expm1x (log q - log p)`, whose terms are nonnegative. Each bound is divided by the
    magnitude of its exact reference: at or above one, the theorem does not fix the sign of the
    result. The recurrences are those of `entropyDifference_forward` and
    `entropyStable_forward`."""
    rows = []
    n = 16
    for spread in (1e-1, 1e-2, 1e-3, 1e-4):
        cells = {"difference": [], "stable": []}
        for _ in range(trials):
            weights = rng.uniform(0.5, 1.5, n)
            p = (weights / weights.sum()).astype(np.float32)
            other = weights * (1 + spread * rng.uniform(-1, 1, n))
            q = (other / other.sum()).astype(np.float32)
            lp = np.array([log32(v) for v in p], dtype=np.float32)
            lq = np.array([log32(v) for v in q], dtype=np.float32)
            for form in ("difference", "stable"):
                s, r, a = ZERO, ZERO, ZERO
                computed = np.float32(0)
                for j in range(n):
                    pr = exact(p[j])
                    log_p, log_q = mp.log(pr), mp.log(exact(q[j]))
                    logs = (U * abs(log_p) + ETA) + (U * abs(log_q) + ETA)
                    if form == "difference":
                        term = pr * (log_p - log_q)
                        value = np.float32(p[j] * np.float32(lp[j] - lq[j]))
                        local = ((1 + U) * U + U) * abs(term) + \
                            ((1 + U) * ((1 + U) * logs * abs(pr)) + ETA)
                    else:
                        d = log_q - log_p
                        term = pr * (mp.exp(d) - 1 - d)
                        value = np.float32(p[j] * expm1x32(np.float32(lq[j] - lp[j])))
                        argument = U * abs(d) + (1 + U) * logs
                        slope = (mp.exp(abs(d) + argument) - 1) * argument
                        local = ((1 + U) * U + U) * abs(term) + \
                            ((1 + U) * (((1 + U) * slope + ETA) * abs(pr)) + ETA)
                    computed = np.float32(computed + value)
                    a = (1 + U) * (r * abs(s) + a + local)
                    r = U
                    s = s + term
                error = abs(exact(computed) - s)
                bound = r * abs(s) + a
                assert error <= bound
                cells[form].append((float(error / abs(s)), float(bound / abs(s)),
                                    float(computed) <= 0))
        row = {"spread": spread}
        for key, values in cells.items():
            row[key] = {"error_over_exact": statistics.median(v[0] for v in values),
                        "bound_over_exact": statistics.median(v[1] for v in values),
                        "bound_over_exact_max": max(v[1] for v in values),
                        "not_positive": sum(v[2] for v in values)}
        rows.append(row)
    return rows


def real(q: Fraction):
    """A rational as an mpf."""
    return mp.mpf(q.numerator) / q.denominator


def round_down32(q: Fraction) -> Fraction:
    """Round a rational toward negative infinity onto the binary32 grid. No overflow."""
    if q == 0:
        return Fraction(0)
    magnitude = abs(q)
    exponent = magnitude.numerator.bit_length() - magnitude.denominator.bit_length()
    if Fraction(2) ** exponent > magnitude:
        exponent -= 1
    ulp = Fraction(2) ** max(exponent - 23, -149)
    scaled = q / ulp
    return (scaled.numerator // scaled.denominator) * ulp


def directed_rows(rng, trials):
    """The lower endpoint of `x * y + z`: the product and the sum are rounded toward negative
    infinity. The bound is that of `lowerAffine_forward`, relative `2 u` and absolute
    `(1 + 2 u) * (2 u |x y| + 2 eta)`. In the second case `z` is within one part in a thousand
    of `-x y`, so the sum cancels. The same endpoint by one fused multiply-add rounded toward
    negative infinity has the bound of `lowerFused_forward`, relative `2 u` and absolute
    `2 eta`."""
    rows = []
    for case in ("z independent", "z within 1e-3 of -x y"):
        ratios, relative, below = [], [], 0
        fused_ratios, fused_relative, fused_below = [], [], 0
        for _ in range(trials):
            x, y = (Fraction(float(np.float32(v))) for v in rng.standard_normal(2))
            if case == "z independent":
                z = Fraction(float(np.float32(rng.standard_normal())))
            else:
                z = Fraction(float(np.float32(float(-x * y) * (1 + 1e-3 * rng.uniform(-1, 1)))))
            product = round_down32(x * y)
            computed = round_down32(product + z)
            reference = x * y + z
            below += computed <= reference
            error = real(abs(computed - reference))
            magnitude = real(abs(reference))
            term = real(abs(x * y))
            bound = 2 * U * magnitude + (1 + 2 * U) * (2 * U * term + 2 * ETA)
            assert error <= bound
            if error > 0:
                ratios.append(float(bound / error))
            if magnitude > 0:
                relative.append(float(bound / magnitude))
            fused = round_down32(reference)
            fused_below += fused <= reference
            fused_error = real(abs(fused - reference))
            fused_bound = 2 * U * magnitude + 2 * ETA
            assert fused_error <= fused_bound
            if fused_error > 0:
                fused_ratios.append(float(fused_bound / fused_error))
            if magnitude > 0:
                fused_relative.append(float(fused_bound / magnitude))
        rows.append({"case": case, "trials": trials, "below": below,
                     "least": min(ratios), "median": statistics.median(ratios),
                     "bound_over_exact": statistics.median(relative),
                     "fused_below": fused_below, "fused_least": min(fused_ratios),
                     "fused_median": statistics.median(fused_ratios),
                     "fused_bound_over_exact": statistics.median(fused_relative)})
    return rows


def function_rows():
    """One call of `expm1x` at `x = 2^-k` in binary32: the closed forward bound over the value
    of the function, with the rounding spread over the three terms of `exp x - 1 - x` (`spread`)
    and kept on the value (`kept`, `expm1xCall_closed`)."""
    rows = []
    for k in (2, 6, 10, 14, 18):
        x = np.float32(2.0 ** -k)
        argument = mp.mpf(float(x))
        value = mp.exp(argument) - 1 - argument
        error = abs(exact(expm1x32(x)) - value)
        spread = (mp.exp(argument) + 1 + abs(argument)) * U + ETA
        kept = value * U + ETA
        assert error <= kept
        rows.append({"k": k, "value": float(value), "error_over_value": float(error / value),
                     "spread_over_value": float(spread / value),
                     "kept_over_value": float(kept / value)})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trials", type=int, default=200)
    parser.add_argument("--seed", type=int, default=20261115)
    parser.add_argument("--json", help="write the results to this file")
    arguments = parser.parse_args()
    rng = np.random.default_rng(arguments.seed)
    rows = []
    for name, size, trial in cases(rng, arguments.trials):
        stated, first, loop, generated, exact_results = [], [], [], [], 0
        count = arguments.trials if size < 4096 else max(arguments.trials // 4, 10)
        if name.endswith("worst case"):
            count = 1
        for _ in range(count):
            (ratio_stated, _, _), (ratio_first, _, _), closed = trial()
            if ratio_stated is None:
                exact_results += 1
                continue
            stated.append(ratio_stated)
            first.append(ratio_first)
            if closed is not None:
                if closed[0] is not None:
                    loop.append(closed[0])
                generated.append(closed[1])
        rows.append({
            "program": name, "size": size, "trials": count, "exact": exact_results,
            "stated_min": min(stated), "stated_median": statistics.median(stated),
            "first_exact_median": statistics.median(first),
            "closed_loop_median": statistics.median(loop) if loop else None,
            "closed_generated_median": statistics.median(generated) if generated else None})
    gradient = gradient_rows()
    sterbenz = sterbenz_rows(rng, arguments.trials)
    constants = constant_rows(rng, arguments.trials)
    entropy = entropy_rows(rng, arguments.trials)
    directed = directed_rows(rng, arguments.trials)
    function = function_rows()
    print("| Program | n | stated bound / error (least, median) | closed form of the loop | "
          "generated closed form | if the first step were exact |")
    print("| --- | --- | --- | --- | --- | --- |")
    for row in rows:
        size = row["size"]
        label = f"{size // 1000} x {size % 1000}" if row["program"].startswith("perceptron") \
            else str(size)
        loop = "" if row["closed_loop_median"] is None else f"{row['closed_loop_median']:.3g}"
        generated = ("" if row["closed_generated_median"] is None
                     else f"{row['closed_generated_median']:.3g}")
        print(f"| {row['program']} | {label} | {row['stated_min']:.3g}, "
              f"{row['stated_median']:.3g} | {loop} | {generated} | "
              f"{row['first_exact_median']:.3g} |")
    print()
    print("| s | exact gradient | 1 / (1 + s) - 1: computed, bound / exact | "
          "-(s / (1 + s)): computed, bound / exact |")
    print("| --- | --- | --- | --- |")
    for row in gradient:
        print(f"| {row['s']} | {row['exact']:.6g} | {row['difference']['computed']:.6g}, "
              f"{row['difference']['bound_over_exact']:.3g} | {row['quotient']['computed']:.6g}, "
              f"{row['quotient']['bound_over_exact']:.3g} |")
    print()
    print("| (x - y) * z, x and y | trials | mixed, subtraction charged | "
          "mixed, subtraction exact | closed, subtraction charged | closed, subtraction exact |")
    print("| --- | ---: | ---: | ---: | ---: | ---: |")
    for row in sterbenz:
        print(f"| {row['case']} | {row['trials']} | {row['mixed_charged']:.3g} | "
              f"{row['mixed_exact']:.3g} | {row['closed_charged']:.3g} | "
              f"{row['closed_exact']:.3g} |")
    print()
    print("| precision | n | ((1 + u)^(n-1) - 1) / ((n-1) u) | sum: power, weighted, "
          "(n-1) u | inner product: power, weighted, n u |")
    print("| ---: | ---: | ---: | --- | --- |")
    for row in constants:
        cells = [", ".join(f"{row[kind][key]:.3g}" for key in ("classical", "weighted",
                                                               "published"))
                 for kind in ("sum", "dot")]
        print(f"| {row['precision']} | {row['n']} | {row['power_over_linear']:.6g} | "
              f"{cells[0]} | {cells[1]} |")
    print()
    print("| spread of q around p | p (log p - log q): error / exact | bound / exact (median, "
          "largest) | not positive | p expm1x (log q - log p): error / exact | bound / exact "
          "(median, largest) | not positive |")
    print("| --- | ---: | --- | ---: | ---: | --- | ---: |")
    for row in entropy:
        cells = []
        for key in ("difference", "stable"):
            cell = row[key]
            cells.append(f"{cell['error_over_exact']:.3g} | {cell['bound_over_exact']:.3g}, "
                         f"{cell['bound_over_exact_max']:.3g} | {cell['not_positive']}")
        print(f"| {row['spread']:g} | {cells[0]} | {cells[1]} |")
    print()
    print("| lower endpoint of x * y + z | trials | computed at or below exact | bound / error "
          "(least, median) | bound / exact (median) |")
    print("| --- | ---: | ---: | --- | ---: |")
    for row in directed:
        print(f"| product and sum, {row['case']} | {row['trials']} | {row['below']} | "
              f"{row['least']:.3g}, {row['median']:.3g} | {row['bound_over_exact']:.3g} |")
        print(f"| one fused multiply-add, {row['case']} | {row['trials']} | "
              f"{row['fused_below']} | {row['fused_least']:.3g}, {row['fused_median']:.3g} | "
              f"{row['fused_bound_over_exact']:.3g} |")
    print()
    print("| x | exp x - 1 - x | error / value | closed bound / value, rounding on the terms | "
          "on the value |")
    print("| --- | ---: | ---: | ---: | ---: |")
    for row in function:
        print(f"| 2^-{row['k']} | {row['value']:.3g} | {row['error_over_value']:.3g} | "
              f"{row['spread_over_value']:.3g} | {row['kept_over_value']:.3g} |")
    if arguments.json:
        with open(arguments.json, "w") as handle:
            json.dump({"seed": arguments.seed, "trials": arguments.trials, "rows": rows,
                       "gradient": gradient, "sterbenz": sterbenz, "constants": constants,
                       "entropy": entropy, "directed": directed, "function": function},
                      handle, indent=1)


if __name__ == "__main__":
    main()
