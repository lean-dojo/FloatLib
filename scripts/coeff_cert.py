#!/usr/bin/env python3
"""Sum-of-squares certificates for the coefficient route of `interval`.

`interval` proves a bound on a series over its whole domain from one check per side: for the
target row T of the goal, scaled to `kT T + kc`, it needs a factor h = p + i q of integers with

    kH |h(e^{iu})|^2 <= 2^s (kT T(e^{iu}) + kc)

up to a remainder whose centre coefficient dominates all the others. This script finds h for the
three families the tactic knows:

* a trigonometric polynomial  sum_k a_k cos(k u) + b_k sin(k u)  on the circle (the default; a
  Chebyshev series sum_k a_k T_k(y) on [-1, 1] has the cosine polynomial's certificates),
* a polynomial  sum_k a_k x^k  on an interval [lo, hi] (--interval lo hi),
* a polynomial  sum_k (a_k + i b_k) z^k  on the unit circle of C, with bounds on its norm
  (--laurent).

It builds exactly the integer target the tactic builds, subtracts a margin from its centre,
factors it as |h|^2 by the roots of the polynomial (the Fejer-Riesz spectral factor, with complex
coefficients when the target has sine terms or complex coefficients), rounds h to Gaussian
integers, and checks the result in exact integer arithmetic before it writes it. The real part goes
to one file, the imaginary part, when there is one, to a second file, one integer per line, in the
format that `packed_row ... from` and `interval (lower := "file")` read.

Nothing here is trusted: the kernel checks the certificate, and a wrong one fails the check. That
is also why the numerics can be as quick and loose as they like. A root a little off, or a factor
rounded the wrong way, costs at worst a failed exact check here, never a wrong proof.
python-flint is used for the roots when it is installed, then mpmath, and otherwise plain floats,
which are enough for bounds that are not too tight.

The factor comes from the roots. A trigonometric polynomial T >= 0 of degree n - 1 is, after
multiplying by z^(n-1), an ordinary polynomial of degree 2 n - 2 whose roots come in pairs r and
1 / conj(r). Keeping the n - 1 roots outside the unit circle gives h with |h|^2 = T on the circle,
up to one positive constant, which is the classical construction behind the Fejer-Riesz theorem.

Usage:

    python3 scripts/coeff_cert.py COEFFS --lower LO -o lower.txt
    python3 scripts/coeff_cert.py COEFFS --sin SINES --upper HI -o upper.txt
    python3 scripts/coeff_cert.py COEFFS --abs C -o cert      # cert_lower.txt, cert_upper.txt
    python3 scripts/coeff_cert.py COEFFS --interval 0 2 --lower auto -o lower.txt
    python3 scripts/coeff_cert.py COEFFS --laurent --imag IMAG --upper auto -o upper.txt
    python3 scripts/coeff_cert.py COEFFS --info

COEFFS (and SINES, IMAG) are text files of a_0, a_1, ...: integers, fractions p/q, decimals or
hexadecimal floats such as 0x1.8p-1, separated by white space or commas, with `#` comments. With
`--ieee 64` (or 32, 16) hexadecimal integers are read as the bit patterns of binary64 (binary32,
binary16) values. A bound given as `auto` is placed just below the minimum (or above the maximum),
by `--slack` relative to the l1 norm, rounded to `--digits` significant digits, and printed.
"""

import argparse
import cmath
import math
import re
import struct
import sys
from fractions import Fraction

try:
    import flint  # noqa: F401
    HAVE_FLINT = True
except ImportError:
    HAVE_FLINT = False

try:
    import mpmath
    HAVE_MPMATH = True
except ImportError:
    HAVE_MPMATH = False


# --- input --------------------------------------------------------------------------------------

def parse_number(token, ieee):
    """One coefficient as an exact fraction: an integer, a fraction p/q, a decimal, a hexadecimal
    float such as 0x1.8p-1, or with `ieee` the bit pattern of a binary16, binary32 or binary64
    value written in hexadecimal."""
    t = token.lower()
    if t.startswith(("0x", "-0x", "+0x")):
        if "p" in t:
            parts = re.fullmatch(r"([+-]?)0x([0-9a-f]*)(?:\.([0-9a-f]*))?p([+-]?[0-9]+)", t)
            if parts is None or not (parts[2] or parts[3]):
                raise ValueError(f"{token} is not a hexadecimal float")
            fraction = parts[3] or ""
            numerator = int(parts[2] + fraction, 16)
            if parts[1] == "-":
                numerator = -numerator
            shift = int(parts[4]) - 4 * len(fraction)
            return (Fraction(numerator << shift) if shift >= 0
                    else Fraction(numerator, 1 << -shift))
        bits = int(t, 16)
        if ieee is None:
            return Fraction(bits)
        fmt = {16: ("<H", "<e"), 32: ("<I", "<f"), 64: ("<Q", "<d")}[ieee]
        value = struct.unpack(fmt[1], struct.pack(fmt[0], bits))[0]
        if not math.isfinite(value):
            raise ValueError(f"{token} is not a finite binary{ieee} value")
        return Fraction(value)
    return Fraction(token)


def read_coefficients(path, ieee):
    """The coefficients a_0, a_1, ... of a text file, separated by white space or commas, with `#`
    starting a comment."""
    values = []
    with open(path, encoding="utf-8") as handle:
        for line in handle:
            line = line.split("#", 1)[0]
            for token in line.replace(",", " ").split():
                values.append(parse_number(token, ieee))
    if not values:
        raise ValueError(f"{path} has no coefficients")
    return values


# --- integer rows, exactly as the tactic builds them ---------------------------------------------

def common_denominator(*rows):
    """The least common denominator of the fractions in all the rows, the d of the tactic."""
    d = 1
    for row in rows:
        for a in row:
            d = d * a.denominator // math.gcd(d, a.denominator)
    return d


def mirror(xs, odd=False):
    """The two-sided row of a half row: cosine rows double the centre, sine rows negate the left."""
    if not xs:
        return []
    rest = xs[1:]
    left = [-x for x in reversed(rest)] if odd else list(reversed(rest))
    return left + [0 if odd else 2 * xs[0]] + rest


def centred(n, k, row):
    """A row of a half row of k entries moved up to the centre n - 1 of 2 n - 1 lanes."""
    out = [0] * (n - k) + row
    return out + [0] * (2 * n - 1 - len(out))


def conv(xs, ys):
    """The Cauchy product of two integer rows, as `Packed.conv` defines it."""
    if not xs or not ys:
        return []
    out = [0] * (len(xs) + len(ys) - 1)
    for i, x in enumerate(xs):
        if x:
            for j, y in enumerate(ys):
                out[i + j] += x * y
    return out


def norm_square(n, p, q):
    """The rows (re, im) of |p + i q|^2 centred at n - 1, in the convention re - i im."""
    m = max(len(p), len(q))
    h = [(p[j] if j < len(p) else 0, q[j] if j < len(q) else 0) for j in range(m)]
    re = [0] * (2 * n - 1)
    im = [0] * (2 * n - 1)
    for lag in range(-(m - 1), m):
        sr = si = 0
        for j in range(m):
            k = j + lag
            if 0 <= k < m:
                a, b = h[k]
                c, d = h[j]
                # h_k * conj(h_j)
                sr += a * c + b * d
                si += b * c - a * d
        if sr or si:
            re[n - 1 + lag] += sr
            im[n - 1 + lag] -= si
    return re, im


def compose(a, b, cs):
    """Horner's rule for sum_k cs[k] b^k a^(len - 1 - k), from the last coefficient down."""
    acc, pw = [], [1]
    for c in reversed(cs):
        prod = conv(acc, b)
        scaled = [c * x for x in pw]
        size = max(len(prod), len(scaled))
        prod += [0] * (size - len(prod))
        scaled += [0] * (size - len(scaled))
        acc = [x + y for x, y in zip(prod, scaled)]
        pw = conv(pw, a)
    return acc


class Goal:
    """The target of one family: the rows (T, S) of 2 n - 1 lanes, the scale K, and the value
    function on the circle for the numerical extremum."""

    def __init__(self, family, coeffs, second, interval):
        self.family = family
        self.coeffs = coeffs
        self.second = second
        if family == "power":
            lo, hi = interval
            self.d = common_denominator(coeffs)
            A = [int(a * self.d) for a in coeffs]
            n = len(A)
            mid, rad = (lo + hi) / 2, (hi - lo) / 2
            D = mid.denominator * rad.denominator // math.gcd(mid.denominator, rad.denominator)
            M, R = int(mid * D), int(rad * D)
            self.n = n
            self.T = compose([0, 2 * D], [R, 2 * M, R], A)
            self.T += [0] * (2 * n - 1 - len(self.T))
            self.S = [0] * (2 * n - 1)
            self.K = self.d * (2 * D) ** (n - 1)
            self.mid, self.rad = float(mid), float(rad)
        else:
            self.d = common_denominator(coeffs, second)
            A = [int(a * self.d) for a in coeffs]
            B = [int(b * self.d) for b in second]
            n = max(len(A), len(B), 1)
            self.n = n
            if family == "trig":
                self.T = centred(n, len(A), mirror(A))
                self.S = centred(n, len(B), mirror(B, True))
                self.K = 2 * self.d
            else:
                self.T, self.S = norm_square(n, A, B)
                self.K = self.d ** 2
        self.l1 = float(sum(abs(a) for a in coeffs) + sum(abs(b) for b in second))

    def value(self, u):
        """The value on the circle that the bounds are about: the polynomial, or for --laurent the
        norm of the polynomial (not its square)."""
        if self.family == "trig":
            return (sum(float(a) * math.cos(k * u) for k, a in enumerate(self.coeffs)) +
                    sum(float(b) * math.sin(k * u) for k, b in enumerate(self.second)))
        if self.family == "power":
            x = self.mid + self.rad * math.cos(u)
            return sum(float(a) * x ** k for k, a in enumerate(self.coeffs))
        z = cmath.exp(1j * u)
        p = sum(complex(float(a), 0) * z ** k for k, a in enumerate(self.coeffs))
        p += sum(complex(0, float(b)) * z ** k for k, b in enumerate(self.second))
        return abs(p)


# --- the extremum on the circle -----------------------------------------------------------------

def golden(f, a, b, steps=80):
    """The minimum of f on [a, b] by golden-section search."""
    phi = (math.sqrt(5) - 1) / 2
    c, d = b - phi * (b - a), a + phi * (b - a)
    fc, fd = f(c), f(d)
    for _ in range(steps):
        if fc < fd:
            b, d, fd = d, c, fc
            c = b - phi * (b - a)
            fc = f(c)
        else:
            a, c, fc = c, d, fd
            d = a + phi * (b - a)
            fd = f(d)
    return min(fc, fd)


def extremum(goal, sign):
    """The minimum (sign = 1) or the maximum (sign = -1) of the goal's value, numerically."""
    points = max(4096, 64 * goal.n)
    step = 2 * math.pi / points
    grid = sorted(((sign * goal.value(i * step), i * step) for i in range(points)))
    best = grid[0][0]
    for _, u in grid[:8]:
        best = min(best, golden(lambda t: sign * goal.value(t), u - step, u + step))
    return sign * best


def round_significant(x, digits, down):
    """x rounded to `digits` significant decimal digits, down or up, as an exact fraction, so that
    an `auto` bound stays on the safe side of the extremum."""
    if x == 0:
        return Fraction(0)
    e = math.floor(math.log10(abs(x))) - digits + 1
    q = Fraction(10) ** e
    m = Fraction(x) / q
    m = math.floor(m) if down else math.ceil(m)
    return m * q


# --- spectral factors ---------------------------------------------------------------------------

def aberth(coeffs, prec, start=None, steps=500):
    """All roots of the polynomial sum coeffs[i] z^i, with complex coefficients, by the
    Aberth-Ehrlich iteration in plain complex floats (prec None) or in mpmath with `prec` bits."""
    m = len(coeffs) - 1
    if prec is None:
        num = complex
        cs = [complex(c) for c in coeffs]
        tol = 1e-14
    else:
        num = mpmath.mpc
        cs = [mpmath.mpc(c.real, c.imag) for c in coeffs]
        tol = mpmath.mpf(2) ** (-prec + 16)
    lead = cs[-1]
    cs = [c / lead for c in cs]
    if start is None:
        zs = [num(math.cos(2 * math.pi * k / m + 0.4), math.sin(2 * math.pi * k / m + 0.4)) *
              (1 + 0.01 * k / m) for k in range(m)]
    else:
        zs = [num(z) for z in start]
    dcs = [i * cs[i] for i in range(1, m + 1)]
    for _ in range(steps):
        biggest = 0
        updated = list(zs)
        for i in range(m):
            z = updated[i]
            p = cs[m]
            for c in reversed(cs[:m]):
                p = p * z + c
            dp = dcs[m - 1]
            for c in reversed(dcs[:m - 1]):
                dp = dp * z + c
            if p == 0:
                continue
            ratio = p / dp
            s = sum(1 / (z - w) for j, w in enumerate(updated) if j != i)
            step = ratio / (1 - ratio * s)
            updated[i] = z - step
            size = abs(step) / max(1, abs(z))
            if size > biggest:
                biggest = size
        zs = updated
        if biggest < tol:
            break
    return zs


def roots(pairs, bits):
    """The roots of sum (re_i + i im_i) z^i for integer pairs (re_i, im_i), and the arithmetic to
    use with them: a unit, the modulus of a pair, a square root and the rounding of the real and
    imaginary parts to the nearest integers."""
    if HAVE_FLINT:
        flint.ctx.prec = bits + 64
        found = flint.acb_poly([flint.acb(r, i) for r, i in pairs]).roots()

        def nearest(c):
            return (int((c.real.mid() + flint.arb(0.5)).floor().unique_fmpz()),
                    int((c.imag.mid() + flint.arb(0.5)).floor().unique_fmpz()))
        return found, (flint.acb(1), lambda r, i: abs(flint.acb(r, i)),
                       lambda x: flint.arb(x).sqrt(), nearest, "flint")
    zs = aberth([complex(float(r), float(i)) for r, i in pairs], None)
    if HAVE_MPMATH:
        mpmath.mp.prec = bits + 64
        zs = aberth([mpmath.mpc(r, i) for r, i in pairs], bits + 64, start=zs, steps=60)
        def modulus(r, i):
            return mpmath.sqrt(mpmath.mpf(r) ** 2 + mpmath.mpf(i) ** 2)
        return zs, (mpmath.mpc(1), modulus,
                    lambda x: mpmath.sqrt(mpmath.mpf(x)),
                    lambda c: (int(mpmath.nint(c.real)), int(mpmath.nint(c.imag))), "mpmath")
    return zs, (complex(1), lambda r, i: math.hypot(r, i), math.sqrt,
                lambda c: (int(round(c.real)), int(round(c.imag))), "float")


def spectral_factor(re, im, n, bits):
    """Gaussian-integer rows p and q of n entries with |p + i q|^2 close to the target re - i im:
    the roots of the polynomial outside the unit circle, scaled so that |h|^2 matches on the
    circle, and rounded."""
    if n == 1:
        return [math.isqrt(re[0])], [], "exact"
    pairs = [(r, -s) for r, s in zip(re, im)]
    found, (one, modulus, sqrt, nearest, method) = roots(pairs, bits)
    outside = [r for r in found if abs(r) > 1]
    if len(outside) != n - 1:
        raise ValueError("the target has roots on the unit circle; use a smaller bound")
    poly = [one]
    for r in outside:
        nxt = [0 * one] * (len(poly) + 1)
        for i, c in enumerate(poly):
            nxt[i + 1] += c
            nxt[i] -= c * r
        poly = nxt
    size = modulus(*pairs[-1])
    for r in outside:
        size = size / abs(r)
    scale = sqrt(size)
    rounded = [nearest(c * scale) for c in poly]
    p = [a for a, _ in rounded]
    # a real target has a real factor: its roots come in conjugate pairs, and what is left of
    # the imaginary part is rounding noise
    q = [b for _, b in rounded] if any(im) else []
    if not any(q):
        q = []
    return p, q, method


# --- certificates -------------------------------------------------------------------------------

def check(n, re, im, p, q):
    """The centre of the defect re - i im - |p + i q|^2 and the sum of the absolute values of all
    its other entries, real and imaginary."""
    hr, hi = norm_square(n, p, q)
    er = [a - b for a, b in zip(re, hr)]
    ei = [a - b for a, b in zip(im, hi)]
    c = n - 1
    return er[c], sum(abs(x) for i, x in enumerate(er) if i != c) + sum(abs(x) for x in ei)


def certificate(goal, bound, lower, bits, margin):
    """The factor (p, q) for `bound <= F` (lower) or `F <= bound`, where F is the goal's value
    (its norm square for --laurent), or an error message."""
    sigma = 1 if lower else -1
    kT = sigma * bound.denominator
    kc = -sigma * goal.K * bound.numerator
    n = goal.n
    c = n - 1
    base_re = [kT * t for t in goal.T]
    base_re[c] += kc
    base_im = [kT * s for s in goal.S]
    if base_re[c] <= 0:
        raise ValueError("the bound is on the wrong side of the mean of the polynomial")
    # scale the target up to about `bits` bits, so that rounding the factor to integers costs
    # little next to the margin
    top = max(abs(t) for t in base_re + base_im)
    shift = max(0, bits - top.bit_length())
    re = [t << shift for t in base_re]
    im = [s << shift for s in base_im]
    ext = extremum(goal, sigma)
    value = float(bound) if goal.family != "laurent" else math.sqrt(max(float(bound), 0))
    slack = sigma * (ext - value)
    if slack <= 0:
        raise ValueError(f"the numerical search found no positive margin at the estimated "
                         f"extremum {ext!r}")
    if goal.family == "laurent":
        slack = sigma * (ext * ext - float(bound))
    low = Fraction(slack) * goal.K * bound.denominator * (1 << shift)
    last_error = None
    # factor the target minus a share of the slack, so the rounded factor still leaves a dominant
    # centre; try a few shares before giving up
    for fraction in (margin, margin / 2, margin * 1.5, margin / 4):
        eta = int(low * Fraction(fraction))
        if eta <= 0:
            continue
        shifted = list(re)
        shifted[c] -= eta
        try:
            p, q, method = spectral_factor(shifted, im, n, bits)
        except ValueError as err:
            last_error = str(err)
            continue
        centre, rest = check(n, re, im, p, q)
        if rest <= centre:
            return p, q, {"method": method, "shift": shift, "d": goal.d, "centre": centre,
                          "rest": rest, "extremum": ext}
        last_error = (f"rounded factor fails: centre {centre} below the sum {rest} of the others "
                      f"(try more --bits)")
    raise ValueError(last_error or "no certificate found")


def write_rows(path, row, header):
    """Write one integer per line, after `#` comment lines with the header."""
    with open(path, "w", encoding="utf-8") as out:
        for line in header:
            out.write(f"# {line}\n")
        for x in row:
            out.write(f"{x}\n")


def imaginary_path(path):
    """The file of the imaginary part next to `path`: lower.txt gives lower_im.txt."""
    stem, dot, ext = path.rpartition(".")
    return f"{stem}_im.{ext}" if dot else f"{path}_im"


def main(argv=None):
    """Parse the command line, build the goal, and write one certificate per side."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("coeffs")
    parser.add_argument("--sin", help="sine coefficients b_0, b_1, ... of a trigonometric "
                        "polynomial")
    parser.add_argument("--interval", nargs=2, metavar=("LO", "HI"),
                        help="a polynomial in the power basis on [LO, HI]")
    parser.add_argument("--laurent", action="store_true",
                        help="a polynomial in z on the unit circle, with bounds on its norm")
    parser.add_argument("--imag", help="imaginary parts of the coefficients, with --laurent")
    side = parser.add_mutually_exclusive_group(required=True)
    side.add_argument("--lower")
    side.add_argument("--upper")
    side.add_argument("--abs")
    side.add_argument("--info", action="store_true")
    parser.add_argument("-o", "--out")
    parser.add_argument("--bits", type=int, default=128,
                        help="size of the scaled target in bits (default 128)")
    parser.add_argument("--margin", type=float, default=0.5,
                        help="the share of the slack subtracted before factoring (default 0.5)")
    parser.add_argument("--slack", type=float, default=1e-6,
                        help="for `auto` bounds: the distance from the extremum, relative to l1")
    parser.add_argument("--digits", type=int, default=8,
                        help="for `auto` bounds: significant digits of the printed bound")
    parser.add_argument("--ieee", type=int, choices=(16, 32, 64))
    args = parser.parse_args(argv)
    coeffs = read_coefficients(args.coeffs, args.ieee)
    if args.laurent:
        family = "laurent"
        second = read_coefficients(args.imag, args.ieee) if args.imag else []
    elif args.interval:
        family = "power"
        second = []
    else:
        family = "trig"
        second = read_coefficients(args.sin, args.ieee) if args.sin else []
    interval = tuple(Fraction(x) for x in args.interval) if args.interval else None
    goal = Goal(family, coeffs, second, interval)
    if args.info:
        print(f"n = {goal.n}, l1 = {goal.l1!r}")
        print(f"minimum = {extremum(goal, 1)!r}, maximum = {extremum(goal, -1)!r}")
        return 0

    def bound_of(text, lower):
        """The bound of a side, either as given or placed by `auto` next to the extremum."""
        if text != "auto":
            return Fraction(text)
        ext = extremum(goal, 1 if lower else -1)
        gap = args.slack * goal.l1
        return round_significant(ext - gap if lower else ext + gap, args.digits, lower)

    jobs = []
    if args.lower is not None:
        jobs.append((True, bound_of(args.lower, True), args.out or "lower.txt"))
    elif args.upper is not None:
        jobs.append((False, bound_of(args.upper, False), args.out or "upper.txt"))
    else:
        if family == "laurent":
            print("error: --abs is for real values; a norm takes --upper", file=sys.stderr)
            return 1
        c = bound_of(args.abs, False) if args.abs != "auto" else max(
            -bound_of("auto", True), bound_of("auto", False))
        prefix = args.out or "cert"
        jobs.append((True, -c, f"{prefix}_lower.txt"))
        jobs.append((False, c, f"{prefix}_upper.txt"))
    for lower, bound, path in jobs:
        if family == "laurent" and bound <= 0:
            if not lower and bound < 0:
                print("error: a norm cannot have a negative upper bound", file=sys.stderr)
                return 1
            if lower:
                print(f"lower bound {bound} follows from nonnegativity; no certificate is needed")
                continue
        target = bound * bound if family == "laurent" else bound
        try:
            p, q, info = certificate(goal, target, lower, args.bits, args.margin)
        except ValueError as err:
            print(f"error: {err}", file=sys.stderr)
            return 1
        relation = "<=" if lower else ">="
        what = {"trig": "sum_k a_k cos(k u) + b_k sin(k u)",
                "power": "sum_k a_k x^k on [{}, {}]".format(*(args.interval or ("", ""))),
                "laurent": "|sum_k (a_k + i b_k) z^k| on |z| = 1"}[family]
        header = [
            f"interval factor: {bound} {relation} {what}, {goal.n} coefficients",
            f"denominator {info['d']}, target scaled by 2^{info['shift']}, "
            f"roots by {info['method']}",
            f"exact check: centre {info['centre']} >= sum of the others {info['rest']}",
        ]
        write_rows(path, p, header)
        option = f'"{path}"'
        if q:
            write_rows(imaginary_path(path), q, header[:1] + ["imaginary part of the factor"])
            option = f'("{path}", "{imaginary_path(path)}")'
        name = "lower" if lower else "upper"
        print(f"{path}: {name} bound {bound} (= {float(bound)!r}; extremum "
              f"{info['extremum']!r}), {info['method']}; use ({name} := {option})")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, OverflowError, ZeroDivisionError, struct.error) as err:
        print(f"error: {err}", file=sys.stderr)
        sys.exit(1)
