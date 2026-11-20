/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Logarithm
public import FloatLib.Numerics.Exact.Confocal.Prepared
public import FloatLib.Numerics.Exact.Product.Angle
public import FloatLib.Numerics.Enclosure.Expression.Closed
public import FloatLib.Numerics.Enclosure.Interval.Elementary

/-!
# Correctly rounded complex inverse sines and cosines

`ExecComplex.asinh`, `acosh` and `acos` are C's `casinh`, `cacosh` and `cacos` (C23 7.3.6.2,
7.3.6.1, 7.3.5.1 and G.6.3.2, G.6.3.1, G.6.2.1), and `ExecComplex.asin` is `casin` (7.3.5.2),
defined as C defines it by `casin z = -i casinh (i z)` (G.6.1). Each part of a finite result is
the exact part rounded once, in any rounding direction and for every binary format.

The parts are inverse functions of the confocal coordinates of the argument. With
`M (p, q)` and `m (p, q)` the half sum and the half difference of the distances of `(p, q)` to
`(0, -1)` and `(0, 1)`:

* `asinh (x + i y) = arcosh (M (x, y)) + i arcsin (m (x, y))` where both sign bits are clear;
* `acosh (x + i y) = arcosh (M (y, x)) + i arccos (m (y, x))` where the imaginary sign bit is
  clear;
* `acos (x + i y) = arccos (m (y, x)) - i arcosh (M (y, x))` where the imaginary sign bit is
  clear, which is `-i acosh (x + i y)` there, special values included.

The squares under the roots are formed exactly, so a huge or tiny argument cannot overflow or
underflow before the single rounding. `ConfocalComparison` compares each part with every rational,
and one enclosure of the part answers the comparisons away from it: the table-reduced logarithm of
the correctly rounded real `log` for the inverse hyperbolic cosine, and the binary-grid inverse
sine and cosine. The sign of a zero
part of the argument selects the side of a branch cut: the cuts of `asinh` are the imaginary axis
outside `[-i, i]`, and those of `acosh` and `acos` lie on the real axis.

At a small argument each part of `asinh` and `asin` lies next to a part of the argument, a
representable number. The inverse hyperbolic cosine then works with twice more bits, and the
inverse sine has the enclosure `smallArcsin?` with no cancellation, so that both separate the
part from that number.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open FloatLib.Numerics

variable {fmt : FloatFormat}

/--
The half difference `(√(p² + (q + 1)²) - √(p² + (q - 1)²)) / 2` as a closed expression, clamped
to `[-1, 1]`, where it lies, so that an enclosure of it stays in the domain of the inverse sine.
-/
def minorExpr (p q : Rat) : Interval.Expr :=
  .binary .max (.const (-1)) (.binary .min (.const 1)
    (.binary .div
      (.binary .sub (.unary .sqrt (.const (p ^ 2 + (q + 1) ^ 2)))
        (.unary .sqrt (.const (p ^ 2 + (q - 1) ^ 2))))
      (.const 2)))

/--
Rational bounds `(lower, upper)` of the half sum of the distances, from square roots between
neighbours of the grid of `precision` fractional bits. The lower bound is at least one.
-/
def majorBounds (p q : Rat) (precision : Nat) : Rat × Rat :=
  let near := Interval.sqrtPointBounds (p ^ 2 + (q + 1) ^ 2) precision
  let far := Interval.sqrtPointBounds (p ^ 2 + (q - 1) ^ 2) precision
  (max 1 ((near.lo + far.lo) / 2), (near.hi + far.hi) / 2)

/-- A lower bound of `arcosh y = log (y + √(y² - 1))` from a rational lower bound `1 ≤ x ≤ y`. -/
def arcoshLower (x : Rat) (precision : Nat) : Rat :=
  (ratLogEnclosure (max 1 (x + (Interval.sqrtPointBounds (x ^ 2 - 1) precision).lo))
    precision).lo

/-- An upper bound of `arcosh y = log (y + √(y² - 1))` from a rational upper bound `y ≤ x`. -/
def arcoshUpper (x : Rat) (precision : Nat) : Rat :=
  (ratLogEnclosure (x + (Interval.sqrtPointBounds (x ^ 2 - 1) precision).hi) precision).hi

/--
Enclose the inverse hyperbolic cosine of the half sum of the distances on the grid of
`precision` fractional bits, with the table-reduced logarithm at both bounds of the half sum.
-/
def arcoshEnclosure (p q : Rat) (precision : Nat) : RationalInterval :=
  let bounds := majorBounds p q precision
  ⟨arcoshLower bounds.1 precision, arcoshUpper bounds.2 precision⟩

/--
A rational lower bound of the distance of the half difference of the distances to `±1`:
`max 0 (1 - |q|) + p² / (4 (|p| + |q| + 1)²)`.
-/
def minorGap (p q : Rat) : Rat :=
  max 0 (1 - |q|) + p ^ 2 / (4 * (|p| + |q| + 1) ^ 2)

/--
`2 arctan √((1 - m) / (1 + m))` as a closed expression: the inverse cosine of `m` in `[0, 1]`
(`ConfocalComparison.arccos_eq_two_mul_arctan`). Near `m = 1`, where the inverse cosine is small,
it keeps the relative accuracy of `1 - m`, and it needs no enclosure of `π`.
-/
def halfAngleExpr (m : Interval.Expr) : Interval.Expr :=
  .binary .mul (.const 2) (.unary .atan (.unary .sqrt
    (.binary .div (.binary .sub (.const 1) m) (.binary .add (.const 1) m))))

/--
The inverse cosine of the half difference of the distances as a closed expression: the half-angle
form for `0 ≤ q`, where the half difference is in `[0, 1]`, and `π` minus that form at `-q` for a
negative `q`.
-/
def arccosExpr (p q : Rat) : Interval.Expr :=
  if 0 ≤ q then halfAngleExpr (minorExpr p q)
  else
    .binary .sub (.binary .mul (.const 2) (.unary .asin (.const 1)))
      (halfAngleExpr (minorExpr p (-q)))

/--
The inverse sine of the half difference of the distances as a closed expression: directly where
`minorGap` keeps the half difference `1 / 16` away from `±1`, and as `±(π / 2 - arccos |m|)` in
the half-angle form nearer to them, where the inverse sine is steep.
-/
def arcsinExpr (p q : Rat) : Interval.Expr :=
  if 1 / 16 ≤ minorGap p q then .unary .asin (minorExpr p q)
  else if 0 ≤ q then
    .binary .sub (.unary .asin (.const 1)) (halfAngleExpr (minorExpr p q))
  else .binary .sub (halfAngleExpr (minorExpr p (-q))) (.unary .asin (.const 1))

/--
One binary-grid enclosure of a closed expression, on a grid finer than the working precision of
`fmt` by `extra` bits, for a result that is small or that cancels. The series degree is that of
the working precision: the expressions above need the extra bits in their square roots only.
-/
def exprEnclosure? (fmt : FloatFormat) (e : Interval.Expr) (extra : Nat) :
    Option RationalInterval :=
  refineTwice fmt fun precision => e.gridEnclosure? (precision + extra) (precision / 4 + 8)

/--
One enclosure of `arcsin (m (p, q))` for `0 < q ≤ 1 / 16`, with no cancellation: the half
difference is `q / M (p, q)`, and its inverse sine is `arctan (m / √(1 - m²))`, enclosed by the
Taylor polynomial of the arctangent at both ends of a short interval around the slope
(`dyadicAround`). The half sum and the root are bounded on a
grid finer than the working precision of `fmt` by twice the bits that `p` and `q` lie below
one, so that the enclosure separates the part from `q`, the nearest representable number at a
small argument.
-/
def smallArcsinCore? (fmt : FloatFormat) (p q : Rat) : Option RationalInterval :=
  let precision := fmt.fracWidth + 36 + 2 * bitsBelowOne (max |p| q)
  let bounds := majorBounds p q precision
  let low := q / bounds.2
  let high := q / bounds.1
  let rootHigh := (Interval.sqrtPointBounds (1 - low ^ 2) precision).hi
  let rootLow := (Interval.sqrtPointBounds (1 - high ^ 2) precision).lo
  let slopeLow := (dyadicAround (low / rootHigh) precision).lo
  let slopeHigh := (dyadicAround (high / rootLow) precision).hi
  if 0 < q ∧ q ≤ 1 / 16 ∧ 0 < rootLow ∧ 0 ≤ slopeLow ∧ slopeHigh < 1 then
    tightOnly fmt
      ⟨(Enclosure.atanSmall slopeLow (smallDegree fmt slopeHigh)).lo,
        (Enclosure.atanSmall slopeHigh (smallDegree fmt slopeHigh)).hi⟩
  else none

/-- One enclosure of `arcsin (m (p, q))` for `0 < |q| ≤ 1 / 16`: `smallArcsinCore?`, mirrored
for a negative `q`. -/
def smallArcsin? (fmt : FloatFormat) (p q : Rat) : Option RationalInterval :=
  if |q| ≤ 1 / 16 then
    if 0 < q then smallArcsinCore? fmt p q
    else (smallArcsinCore? fmt p (-q)).map RationalInterval.neg
  else none

/--
The part `arcosh (M (p, q))`, as an exact comparator. It is zero on the segment between the foci,
`p = 0` and `|q| ≤ 1`, and positive elsewhere.

The enclosure works with as many extra bits as `M (p, q) - 1` has leading zeros, by the rational
lower bound `(|q + 1| + |q - 1| - 2) / 2 + p² / (4 (|p| + |q| + 1))` of that difference, and with
twice the bits that `p` and `q` lie below one: at a small argument the part is within
`p² + q²`, relatively, of `|p|`, a representable number, and the enclosure separates the two.
-/
def arcoshPart (fmt : FloatFormat) (p q : Rat) : Part fmt :=
  (Part.real (ConfocalComparison.compareArcosh p q (cacheLevels fmt)) false).within
    (if p = 0 ∧ |q| ≤ 1 then none
      else
        let extra := bitsBelowOne
          ((|q + 1| + |q - 1| - 2) / 2 + p ^ 2 / (4 * (|p| + |q| + 1))) +
            2 * bitsBelowOne (max |p| |q|)
        refineTwice fmt fun precision => some (arcoshEnclosure p q (precision + extra)))

/--
The part `arcsin (m (p, q))`, as an exact comparator. It has the sign of `q`.

The enclosure is `smallArcsin?` for a small `q`. Elsewhere it works with extra bits for a half
difference near `±1`, where the inverse sine is steep.
-/
def arcsinPart (fmt : FloatFormat) (p q : Rat) : Part fmt :=
  (Part.real (ConfocalComparison.compareArcsin p q (cacheLevels fmt)) false).within
    (if q = 0 then none
      else smallArcsin? fmt p q <|> exprEnclosure? fmt (arcsinExpr p q)
        (max (bitsBelowOne (|q| / (|p| + |q| + 1))) (bitsBelowOne (minorGap p q) / 2 + 1)))

/--
The part `arccos (m (p, q))`, as an exact comparator. It is zero on the ray above the upper
focus, `p = 0` and `1 ≤ q`, and positive elsewhere.

The enclosure works with extra bits for a half difference near `±1`, where the result is small
or the inverse cosine is steep.
-/
def arccosPart (fmt : FloatFormat) (p q : Rat) : Part fmt :=
  (Part.real (ConfocalComparison.compareArccos p q (cacheLevels fmt)) false).within
    (if p = 0 ∧ 1 ≤ q then none
      else exprEnclosure? fmt (arccosExpr p q) (bitsBelowOne (minorGap p q)))

/-- `casinh` where both sign bits are clear, before rounding (C23 G.6.3.2). -/
def asinhCore (z : ExecComplex fmt) : Parts fmt :=
  let nan := propagatedNaN z
  let zero := Model.zero fmt false
  let inf := Model.posInf fmt
  match Model.toRat? z.re, Model.toRat? z.im with
  | some x, some y => ⟨arcoshPart fmt x y, arcsinPart fmt x y⟩
  | some _, none =>
      if Model.isNaN z.im then ⟨.exact nan, .exact nan⟩ else ⟨.exact inf, argPart fmt 0 1 1⟩
  | none, some y =>
      if Model.isNaN z.re then
        if y = 0 then ⟨.exact nan, .exact zero⟩ else ⟨.exact nan, .exact nan⟩
      else ⟨.exact inf, .exact zero⟩
  | none, none =>
      if Model.isNaN z.re then
        if Model.isNaN z.im then ⟨.exact nan, .exact nan⟩ else ⟨.exact inf, .exact nan⟩
      else if Model.isNaN z.im then ⟨.exact inf, .exact nan⟩
      else ⟨.exact inf, argPart fmt 1 1 1⟩

/-- `casinh` before rounding, on every input: odd, and `casinh (conj z) = conj (casinh z)`. -/
def asinhParts : ExecComplex fmt → Parts fmt := Parts.ofQuadrant true asinhCore

/--
The complex inverse hyperbolic sine `casinh` (C23 7.3.6.2 and G.6.3.2), with branch cuts along
the imaginary axis outside `[-i, i]` and imaginary part in `[-π / 2, π / 2]`.

For a finite argument each part is the exact part rounded once in the direction `mode`
(`asinh_eq`). The sign of a zero real part selects the side of a cut:
`asinh (±0 + 2 i) = ±arcosh 2 + (π / 2) i`. Special values follow G.6.3.2:
`asinh (+0 + 0 i) = +0 + 0 i`, `asinh (x + ∞ i) = ∞ + (π / 2) i`, `asinh (∞ + i y) = ∞ + 0 i`,
`asinh (∞ + ∞ i) = ∞ + (π / 4) i`, `asinh (NaN + 0 i) = NaN + 0 i`, and
`asinh (NaN + ∞ i) = ∞ + NaN i`, with the angles rounded in the direction `mode`.
-/
def asinh (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (asinhParts z).round mode

/-- `casin` before rounding: `casin z = -i casinh (i z)` (C23 G.6.1). -/
def asinParts (z : ExecComplex fmt) : Parts fmt := (asinhParts (mulI z)).mulNegI

/--
The complex inverse sine `casin` (C23 7.3.5.2), with branch cuts along the real axis outside
`[-1, 1]` and real part in `[-π / 2, π / 2]`. It is `-i casinh (i z)`, as C23 G.6.1 specifies,
with both multiplications by `i` exact: each part of a finite result is the exact part rounded
once in the direction `mode` (`asin_eq`), and the special values are those of `casinh`.
-/
def asin (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (asinParts z).round mode

/-- `cacosh` where the imaginary sign bit is clear, before rounding (C23 G.6.3.1). -/
def acoshCore (z : ExecComplex fmt) : Parts fmt :=
  let nan := propagatedNaN z
  let inf := Model.posInf fmt
  match Model.toRat? z.re, Model.toRat? z.im with
  | some x, some y => ⟨arcoshPart fmt y x, arccosPart fmt y x⟩
  | some x, none =>
      if Model.isNaN z.im then
        if x = 0 then ⟨.exact nan, argPart fmt 0 1 1⟩ else ⟨.exact nan, .exact nan⟩
      else ⟨.exact inf, argPart fmt 0 1 1⟩
  | none, some _ =>
      if Model.isNaN z.re then ⟨.exact nan, .exact nan⟩
      else ⟨.exact inf, argPart fmt (boxed z.re) 0 1⟩
  | none, none =>
      if Model.isNaN z.re then
        if Model.isNaN z.im then ⟨.exact nan, .exact nan⟩ else ⟨.exact inf, .exact nan⟩
      else if Model.isNaN z.im then ⟨.exact inf, .exact nan⟩
      else ⟨.exact inf, argPart fmt (boxed z.re) 1 1⟩

/-- `cacosh` before rounding, on every input: `cacosh (conj z) = conj (cacosh z)`. -/
def acoshParts : ExecComplex fmt → Parts fmt := Parts.ofUpperHalf acoshCore

/--
The complex inverse hyperbolic cosine `cacosh` (C23 7.3.6.1 and G.6.3.1), with the branch cut
along the real axis below one, nonnegative real part and imaginary part in `[-π, π]`.

For a finite argument each part is the exact part rounded once in the direction `mode`
(`acosh_eq`). The sign of a zero imaginary part selects the side of the cut:
`acosh (-2 ± 0 i) = arcosh 2 ± π i`. Special values follow G.6.3.1:
`acosh (±0 + 0 i) = +0 + (π / 2) i`, `acosh (x + ∞ i) = ∞ + (π / 2) i`,
`acosh (-∞ + i y) = ∞ + π i`, `acosh (∞ + i y) = ∞ + 0 i`, `acosh (-∞ + ∞ i) = ∞ + (3 π / 4) i`,
`acosh (∞ + ∞ i) = ∞ + (π / 4) i`, `acosh (0 + NaN i) = NaN + (π / 2) i`, and
`acosh (NaN + ∞ i) = ∞ + NaN i`, with the angles rounded in the direction `mode`.
-/
def acosh (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (acoshParts z).round mode

/--
`cacos` before rounding, on every input: `cacos (conj z) = conj (cacos z)`, and
`cacos z = -i cacosh z` where the imaginary sign bit is clear, special values included (compare
C23 G.6.2.1 with G.6.3.1).
-/
def acosParts : ExecComplex fmt → Parts fmt :=
  Parts.ofUpperHalf fun z => (acoshCore z).mulNegI

/--
The complex inverse cosine `cacos` (C23 7.3.5.1 and G.6.2.1), with branch cuts along the real
axis outside `[-1, 1]` and real part in `[0, π]`.

For a finite argument each part is the exact part rounded once in the direction `mode`
(`acos_eq`). The sign of a zero imaginary part selects the side of a cut:
`acos (2 ± 0 i) = +0 ∓ arcosh 2 i`. Special values follow G.6.2.1:
`acos (±0 + 0 i) = π / 2 - 0 i`, `acos (x + ∞ i) = π / 2 - ∞ i`, `acos (-∞ + i y) = π - ∞ i`,
`acos (∞ + i y) = +0 - ∞ i`, `acos (-∞ + ∞ i) = 3 π / 4 - ∞ i`, `acos (∞ + ∞ i) = π / 4 - ∞ i`,
`acos (±0 + NaN i) = π / 2 + NaN i`, and `acos (NaN + ∞ i) = NaN - ∞ i`, with the angles rounded
in the direction `mode`.
-/
def acos (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (acosParts z).round mode

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
