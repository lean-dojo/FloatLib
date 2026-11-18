/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Logarithm
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Algebraic
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Exponential
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.DirectedEnclosure
public import FloatLib.Numerics.Enclosure.Interval.Elementary
public import FloatLib.Numerics.Exact.RationalPower.Runtime

/-!
# Complex powers with a correct-rounding certificate

`ExecComplex.pow` is C's `cpow` (C23 7.3.8.2 and G.6.5.1): `z ^ w = exp (w log z)`, with the
branch cut of `clog` along the negative real axis of the base. C23 gives `cpow` no table of
special values, and allows `cexp (w clog z)` as an implementation. Here each part of a finite
result is the exact part rounded once, in any rounding direction and for every binary format,
whenever the result is certified, and `powChecked` returns the certificate with the result.

A result is certified in these cases, and `PowerProof` proves it correctly rounded there:

* a zero exponent, where the power is one, and the base one;
* the exponent `1 / 2`: the power is `ExecComplex.sqrt`;
* a real exponent `n / 2 ^ k` and a base whose principal `2 ^ k`-th root is a complex rational,
  with an exact power of moderate size (`gaussRatPow?`): the root comes from `k` exact square
  roots, and its `n`-th power is formed exactly. An integer exponent is the case `k = 0`, and
  `(-4) ^ (1 / 4) = 1 + i` the case `k = 2`;
* a real exponent `c` and a base on the real or the imaginary axis whose power lies on an axis
  again: a positive real base, a negative real base with `2 c` an integer, an imaginary base with
  `c` an integer. One part is zero, and the other is a real power, which
  `RationalPower.compare` compares exactly with every rational;
* a base `±1` or `±i` and a complex exponent `c + i d` with the same condition on `c`: one part
  is zero, and an enclosure decides the other, `±exp (-d θ)`;
* any other finite base and exponent for which an enclosure of each part
  `exp (c L - d θ) cos (d L + c θ)` and `exp (c L - d θ) sin (d L + c θ)`, with `L = log |z|`
  and `θ = arg z`, decides its rounding (Ziv's test, at most `levels` enclosures of doubling
  precision).

The last case cannot certify a part that lies exactly on a rounding boundary: a representable
part in a directed rounding, a midpoint in a rounding to nearest, or a zero. Whether a part of a
complex power is rational is a question of transcendence theory, and the exact cases above are
not proved to be the only ones. A part on a boundary outside them, an exact power of more than
131,072 bits, a part whose sign needs more than `levels` enclosures, and a result whose exponent
`c L - d θ` is beyond `±powExponentCap` are returned without a certificate: each part is the
rounding of the midpoint of its last enclosure, or a NaN without an enclosure.

The sign of a zero imaginary part of the base selects the side of the cut, as for `clog`:
`pow (-1 ± 0 i) (1 / 2) = ±i`. An exactly zero real part of a result is a positive zero, and an
exactly zero imaginary part has the sign bit of the imaginary part of the base, so that
`pow (conj z) (conj w) = conj (pow z w)` for exact results.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open FloatLib.Numerics
open ProductComparison (Trig)
open Model.AlgebraicRounding (roundRat zivRound?)

variable {fmt : FloatFormat}

/--
Enclosures of `log |x + i y|` and of the angle `arg (x + i y)`, negated with `negative`, at
`precision` bits, for a nonzero complex rational.
-/
def logArgEnclosures (x y : Rat) (negative : Bool) (precision : Nat) :
    RationalInterval × RationalInterval :=
  ((ratLogEnclosure (x * x + y * y) precision).scale (1 / 2),
    if negative then (TrigonometricComparison.atan2Interval x y (precision / 2)).neg
    else TrigonometricComparison.atan2Interval x y (precision / 2))

/--
The largest magnitude of the real exponent `c L - d θ` at which a part of a power is enclosed:
`2 ^ 20`, or more for a format whose range needs more.
-/
def powExponentCap (fmt : FloatFormat) : Rat :=
  max 1048576 (4 * (Model.AlgebraicRounding.upperExponent fmt + fmt.fracWidth + 64))

/--
One enclosure of the part `exp (c L - d θ) * trig (d L + c θ)` of `(x + i y) ^ (c + i d)`, from
enclosures of the logarithm `L` and the angle `θ` at `precision` bits and more. With `negative`
the angle is negated: the base is the conjugate of `x + i y`.

The exponential is enclosed at both ends of the enclosure of its argument, on a grid finer by
the number of bits that a small result lies below one, and the cosine or sine by
`ProductComparison.trigBounds?`, which keeps its relative accuracy at an angle of any size. An
exponent beyond `powExponentCap fmt` gives `none`.
-/
def powEnclosure? (fmt : FloatFormat) (trig : Trig) (x y c d : Rat) (negative : Bool)
    (precision : Nat) : Option RationalInterval :=
  let bounds := logArgEnclosures x y negative (precision + ⌈|c| + |d|⌉₊.log2 + 8)
  let exponent := (bounds.1.scale c).sub (bounds.2.scale d)
  if exponent.lo < -powExponentCap fmt ∨ powExponentCap fmt < exponent.hi then none
  else
    let working := precision + ⌈-(exponent.lo * 3 / 2)⌉₊
    (ProductComparison.trigBounds? trig ((bounds.1.scale d).add (bounds.2.scale c))
      precision).map (expBounds exponent (working.sqrt + 8) working).mul

/--
A part of a power in the general case: its rounding and whether an enclosure decided it. A part
that no enclosure decides is the rounding of the midpoint of its last enclosure, or a NaN.
-/
def powPart (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (trig : Trig) (x y c d : Rat)
    (negative : Bool) (levels : Nat) : Model fmt × Bool :=
  match zivRound? fmt mode (powEnclosure? fmt trig x y c d negative) levels
    (fmt.fracWidth + 32) with
  | some result => (result, true)
  | none =>
      (match powEnclosure? fmt trig x y c d negative
          ((fmt.fracWidth + 32) * 2 ^ (levels - 1)) with
        | some interval => roundRat fmt mode ((interval.lo + interval.hi) / 2)
        | none => Model.invalidResult fmt, false)

/-- The exact power `(x + i y) ^ n` of a complex rational, for a natural `n`. -/
def gaussPow (x y : Rat) : Nat → Rat × Rat
  | 0 => (1, 0)
  | n + 1 => ((gaussPow x y n).1 * x - (gaussPow x y n).2 * y,
      (gaussPow x y n).1 * y + (gaussPow x y n).2 * x)

/-- The exact power `(x + i y) ^ n` of a complex rational, for an integer `n`. -/
def gaussZPow (x y : Rat) (n : Int) : Rat × Rat :=
  if 0 ≤ n then gaussPow x y n.natAbs
  else
    ((gaussPow x y n.natAbs).1 /
        ((gaussPow x y n.natAbs).1 * (gaussPow x y n.natAbs).1 +
          (gaussPow x y n.natAbs).2 * (gaussPow x y n.natAbs).2),
      -(gaussPow x y n.natAbs).2 /
        ((gaussPow x y n.natAbs).1 * (gaussPow x y n.natAbs).1 +
          (gaussPow x y n.natAbs).2 * (gaussPow x y n.natAbs).2))

/-- A bound on the number of bits of the parts of `(x + i y) ^ n`. -/
def gaussPowBits (x y : Rat) (n : Nat) : Nat :=
  n * (x.num.natAbs.log2 + x.den.log2 + y.num.natAbs.log2 + y.den.log2 + 4)

/--
A principal square root of the complex rational `x + i y` with rational parts, or `none`. The
candidate comes from three integer square roots, at a precision chosen to hold the root of binary
floating-point parts, and it is checked exactly, so a returned root is the principal square root
(`gaussSqrt?_spec`). No theorem says that a rational root is always found. A returned root lies
in the closed first quadrant, so there is none for a negative `y`.
-/
def gaussSqrt? (x y : Rat) : Option (Rat × Rat) :=
  let precision := x.den.log2 + y.den.log2 + 2
  let norm := (Interval.sqrtPointBounds (x * x + y * y) precision).lo
  let a := (Interval.sqrtPointBounds ((norm + x) / 2) precision).lo
  let b := (Interval.sqrtPointBounds ((norm - x) / 2) precision).lo
  if 0 ≤ a ∧ 0 ≤ b ∧ a * a - b * b = x ∧ 2 * a * b = y then some (a, b) else none

/-- The principal `2 ^ k`-th root of a complex rational by `k` exact square roots, if all exist. -/
def gaussRoot? (x y : Rat) : Nat → Option (Rat × Rat)
  | 0 => some (x, y)
  | k + 1 => (gaussSqrt? x y).bind fun root => gaussRoot? root.1 root.2 k

/--
The exact power `(x + i y) ^ c` of a complex rational, for a rational exponent `c = n / 2 ^ k`,
when the principal `2 ^ k`-th root of the base is a complex rational and its `n`-th power is of
moderate size. An integer exponent is the case `k = 0`.
-/
def gaussRatPow? (x y c : Rat) : Option (Rat × Rat) :=
  if c.den = 2 ^ c.den.log2 then
    (gaussRoot? x y c.den.log2).bind fun root =>
      if gaussPowBits root.1 root.2 c.num.natAbs ≤ 131072 then
        some (gaussZPow root.1 root.2 c.num)
      else none
  else none

/--
The angle of a base on an axis in quarter turns: `0` on the positive real axis, `2` on the
negative real axis and `1` on the positive imaginary axis, negated with `negative`, for the
conjugate base.
-/
def axisTurns (x y : Rat) (negative : Bool) : Int :=
  (if y = 0 then (if 0 < x then 0 else 2) else 1) * (if negative then -1 else 1)

/--
Exact comparators of the two parts of `r ^ c * i ^ quarter` for a positive rational `r`: one part
is zero and the other is the real power `r ^ c` or its negation.
-/
def axisComparators (r c : Rat) (quarter : Int) : (Rat → Ordering) × (Rat → Ordering) :=
  if quarter % 4 = 0 then (RationalPower.compare r c, fun boundary => cmp 0 boundary)
  else if quarter % 4 = 1 then (fun boundary => cmp 0 boundary, RationalPower.compare r c)
  else if quarter % 4 = 2 then
    (fun boundary => (RationalPower.compare r c (-boundary)).swap, fun boundary => cmp 0 boundary)
  else
    (fun boundary => cmp 0 boundary, fun boundary => (RationalPower.compare r c (-boundary)).swap)

/--
The power `(x + i y) ^ (c + i d)` of a nonzero complex rational with `0 ≤ y`, or of its conjugate
with `negative`, and whether it is certified. The exponent is not zero.
-/
def powRat (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (x y c d : Rat) (negative : Bool)
    (levels : Nat) : ExecComplex fmt × Bool :=
  if x = 1 ∧ y = 0 then (⟨roundRat fmt mode 1, Model.zero fmt negative⟩, true)
  else
    match (if d = 0 then gaussRatPow? x y c else none) with
    | some power =>
        (⟨roundRat fmt mode power.1,
          Model.AlgebraicRounding.roundSigned fmt mode
            (fun boundary => cmp (if negative then -power.2 else power.2) boundary) negative⟩,
          true)
    | none =>
        if d = 0 ∧ (x = 0 ∨ y = 0) ∧ (c * axisTurns x y negative).den = 1 then
          (⟨Model.AlgebraicRounding.roundSigned fmt mode
              (axisComparators (|x| + |y|) c (c * axisTurns x y negative).num).1,
            Model.AlgebraicRounding.roundSigned fmt mode
              (axisComparators (|x| + |y|) c (c * axisTurns x y negative).num).2 negative⟩, true)
        else if |x| + |y| = 1 ∧ (x = 0 ∨ y = 0) ∧ (c * axisTurns x y negative).den = 1 then
          if (c * axisTurns x y negative).num % 2 = 0 then
            (⟨(powPart fmt mode .cos x y c d negative levels).1, Model.zero fmt negative⟩,
              (powPart fmt mode .cos x y c d negative levels).2)
          else
            (⟨Model.zero fmt false, (powPart fmt mode .sin x y c d negative levels).1⟩,
              (powPart fmt mode .sin x y c d negative levels).2)
        else
          (⟨(powPart fmt mode .cos x y c d negative levels).1,
            (powPart fmt mode .sin x y c d negative levels).1⟩,
            (powPart fmt mode .cos x y c d negative levels).2 &&
              (powPart fmt mode .sin x y c d negative levels).2)

/--
`cpow` with its certificate: the power `z ^ w`, and whether it is certified. The module
docstring lists the certified cases, and `powChecked_eq` proves a certified result at finite
arguments with a nonzero base correctly rounded in the direction `mode`.

Special values, always certified: `z ^ 0 = 1 ± 0 i` for every `z`, also a NaN, with the sign bit
of the imaginary part of `z`; a zero base gives `+0 + 0 i` for an exponent with positive real
part, `∞ + NaN i` for a negative real part and `NaN + NaN i` for a zero real part; any other
argument with a NaN or an infinite part gives `NaN + NaN i`.
-/
def powChecked (z w : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest)
    (levels : Nat := 4) : ExecComplex fmt × Bool :=
  let nan := if Model.isNaN z.re || Model.isNaN z.im then propagatedNaN z else propagatedNaN w
  let negative := Model.signBit z.im
  match Model.toRat? w.re, Model.toRat? w.im with
  | some c, some d =>
      if c = 0 ∧ d = 0 then (⟨roundRat fmt mode 1, Model.zero fmt negative⟩, true)
      else
        match Model.toRat? z.re, Model.toRat? (if negative then Model.neg z.im else z.im) with
        | some x, some y =>
            if x = 0 ∧ y = 0 then
              (if 0 < c then ⟨Model.zero fmt false, Model.zero fmt false⟩
                else if c < 0 then ⟨Model.posInf fmt, nan⟩
                else ⟨nan, nan⟩, true)
            else if c = 1 / 2 ∧ d = 0 then (sqrt z mode, true)
            else powRat fmt mode x y c d negative levels
        | _, _ => (⟨nan, nan⟩, true)
  | _, _ => (⟨nan, nan⟩, true)

/--
The complex power `cpow` (C23 7.3.8.2 and G.6.5.1): `z ^ w = exp (w log z)`, with the branch cut
of `clog` along the negative real axis of the base.

Each part of a certified result is the exact part rounded once in the direction `mode`
(`pow_eq`). `powCertified` says whether a result is certified, and the module docstring lists the
cases: a zero exponent, the base one, the exponent `1 / 2`, exponents `n / 2 ^ k` of a base with
a complex rational `2 ^ k`-th root (integer exponents among them) of moderate size, a base on an
axis whose power stays on an axis, and every result that an enclosure decides. Special values
are those of `powChecked`.
-/
def pow (z w : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) (levels : Nat := 4) :
    ExecComplex fmt :=
  (powChecked z w mode levels).1

/-- Whether `pow z w mode levels` is certified: correctly rounded by `pow_eq`. -/
def powCertified (z w : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest)
    (levels : Nat := 4) : Bool :=
  (powChecked z w mode levels).2

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
