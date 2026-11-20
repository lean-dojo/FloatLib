/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Small
public import FloatLib.Numerics.Exact.Elementary.Runtime
public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.CorrectlyRounded.Runtime

/-!
# Correctly rounded complex logarithm and inverse tangents

`ExecComplex.log` is C's `clog` (C23 7.3.7.2 and G.6.4.2), `ExecComplex.atanh` is `catanh`
(7.3.6.3 and G.6.3.3), `ExecComplex.atan` is `catan` (7.3.5.3), defined as C defines it by
`catan z = -i catanh (i z)` (G.6.1), and `ExecComplex.log1p` is `clog (1 + z)` with the exact sum.
Each part of a finite result is the exact part rounded once, in any rounding direction and for
every binary format.

The parts of these functions are logarithms and arguments of rationals:

* `log (x + i y) = log (x² + y²) / 2 + i arg (x + i y)`;
* `atanh (x + i y) = log (((1 + x)² + y²) / ((1 - x)² + y²)) / 4 +
  i arg ((1 - x) (1 + x) - y² + 2 i y) / 2` in the first quadrant.

The rationals are formed exactly, so a huge or tiny argument cannot overflow or underflow before
the single rounding, and `ElementaryComparison.prepareLog` and
`TrigonometricComparison.prepareAtan2` compare each part with every rational. One enclosure of
each part, from the table-reduced logarithm of the correctly rounded real `log` and from the
arctangent series, answers the comparisons away from the part (`Part.within`), so the exact
comparators run only for a boundary inside that enclosure. At a small argument, where a part
of `log1p`, `atanh` or `atan` lies next to a part of the argument, the enclosure is a Taylor
enclosure of `Small` that separates the two (`smallLog?`, `smallArg?`), and a rational that a
subnormal part makes thousands of bits long is replaced by a short interval around it
(`coarseLog`, `coarseArg`). The angles of the
special values (`π`, `π / 2`, `π / 4`, `3 π / 4`) are arguments of the direction of an infinite or
zero input, rounded in the requested direction like every other part.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open FloatLib.Numerics

variable {fmt : FloatFormat}

/--
Number of enclosure depths that a comparator shares across the rounding boundaries of one part:
enough to reach the precision of the format. Deeper levels are computed on demand.
-/
def cacheLevels (fmt : FloatFormat) : Nat := (fmt.fracWidth + 1).log2 + 3

/--
Enclose `log q` for a positive rational `q` on the grid of `precision` fractional bits, with the
table reduction of the correctly rounded real logarithm.
-/
def ratLogEnclosure (q : Rat) (precision : Nat) : RationalInterval :=
  let split := Model.Transcendentals.Certified.splitTwoPow q
  Model.Transcendentals.CorrectlyRounded.logEnclosure split.1 split.2 precision

/--
Enclose `log q` for a positive rational `q` on the grid of `precision` fractional bits. For a
`q` that is written with thousands of bits (`isLong`) it is the logarithms at the two ends of a
short interval around `q` (`dyadicAround`), so that the cost does not grow with the length of
`q`.
-/
def coarseLog (q : Rat) (precision : Nat) : RationalInterval :=
  if isLong q (precision + 8) ∧ 0 < (dyadicAround q (precision + 8)).lo then
    ⟨(ratLogEnclosure (dyadicAround q (precision + 8)).lo precision).lo,
      (ratLogEnclosure (dyadicAround q (precision + 8)).hi precision).hi⟩
  else ratLogEnclosure q precision

/--
The degree of the arctangent series at `slope` for `precision` bits: half the precision, and
less for a slope below a quarter, whose series gains twice the bits that the slope lies below
one with each term.
-/
def atanDegree (slope : Rat) (precision : Nat) : Nat :=
  if 3 ≤ bitsBelowOne |slope| then
    min (precision / 2) (precision / (2 * (bitsBelowOne |slope| - 1)) + 4)
  else precision / 2

/--
Enclose `arctan slope` at `precision` bits, with the relative accuracy of a small slope. For a
slope that is written with thousands of bits (`isLong`) it is the arctangent at the two ends of
a short interval around the slope (`dyadicAround`).
-/
def coarseAtan (slope : Rat) (precision : Nat) : RationalInterval :=
  if isLong slope (precision + 8) then
    ⟨(Enclosure.atan (dyadicAround slope (precision + 8)).lo (atanDegree slope precision)).lo,
      (Enclosure.atan (dyadicAround slope (precision + 8)).hi (atanDegree slope precision)).hi⟩
  else Enclosure.atan slope (atanDegree slope precision)

/--
Enclose the principal argument of `x + i y` at `precision` bits: the arctangent of the slope
(`coarseAtan`) with the multiple of `π / 4` of the quadrant.
-/
def coarseArg (x y : Rat) (precision : Nat) : RationalInterval :=
  (coarseAtan (TrigonometricComparison.atan2Reduction x y).1 precision).add
    ((Enclosure.piQuarter (precision / 2)).scale (TrigonometricComparison.atan2Reduction x y).2)

/--
The part `log q / scale` for a positive rational `q` and a positive `scale`, as an exact
comparator. A zero value, at `q = 1`, is a positive zero.

For `q` near one the enclosure is the Taylor enclosure `smallLog?`, which keeps the relative
accuracy of `q - 1`, and elsewhere the table-reduced logarithm `coarseLog`.
-/
def logPart (fmt : FloatFormat) (q scale : Rat) : Part fmt :=
  if hq : 0 < q then
    (Part.real (fun boundary =>
      (ElementaryComparison.prepareLog q (cacheLevels fmt) hq).compare (scale * boundary))
      false).within
        ((smallLog? fmt q).map (fun interval => interval.scale (1 / scale)) <|>
          refineTwice fmt fun precision =>
            some ((coarseLog q precision).scale (1 / scale)))
  else .exact (Model.invalidResult fmt)

/--
The part `arg (x + i y) / scale` for a positive `scale`, as an exact comparator, with the
principal argument in `(-π, π]`. A zero value, on the positive real axis, is a positive zero.

For a small angle from the positive real axis the enclosure is the Taylor enclosure
`smallArg?`, with the degree that the size of the angle needs, and elsewhere `coarseArg`.
-/
def argPart (fmt : FloatFormat) (x y scale : Rat) : Part fmt :=
  (Part.real (fun boundary =>
    (TrigonometricComparison.prepareAtan2 x y (cacheLevels fmt)).compare (scale * boundary))
    false).within
      ((smallArg? fmt x y).map (fun interval => interval.scale (1 / scale)) <|>
        refineTwice fmt fun precision =>
          some ((coarseArg x y precision).scale (1 / scale)))

/--
The direction of one part of an infinite argument: `±1` for an infinite part and `0` for a finite
one, as C23 G.5.2 boxes an infinity.
-/
def boxed (value : Model fmt) : Rat :=
  if Model.isInfinite value then (if Model.signBit value then -1 else 1) else 0

/-- The logarithm of the nonzero complex rational `x + i y`, before rounding. -/
def logRat (fmt : FloatFormat) (x y : Rat) : Parts fmt :=
  ⟨logPart fmt (x * x + y * y) 2, argPart fmt x y 1⟩

/--
The special values of `clog` (C23 G.6.4.2) at an argument with a NaN or an infinite part, where
the imaginary sign bit is clear: the modulus is `+∞`, and the angle is the argument of the
direction of the infinite parts.
-/
def logNonfinite (z : ExecComplex fmt) : Parts fmt :=
  let nan := propagatedNaN z
  if Model.isNaN z.re || Model.isNaN z.im then
    if Model.isInfinite z.re || Model.isInfinite z.im then ⟨.exact (Model.posInf fmt), .exact nan⟩
    else ⟨.exact nan, .exact nan⟩
  else ⟨.exact (Model.posInf fmt), argPart fmt (boxed z.re) (boxed z.im) 1⟩

/-- `clog` where the imaginary sign bit is clear, before rounding. -/
def logCore (z : ExecComplex fmt) : Parts fmt :=
  match Model.toRat? z.re, Model.toRat? z.im with
  | some x, some y =>
      if x = 0 ∧ y = 0 then
        ⟨.exact (Model.negInf fmt), argPart fmt (if Model.signBit z.re then -1 else 1) 0 1⟩
      else logRat fmt x y
  | _, _ => logNonfinite z

/-- `clog` before rounding, on every input: `clog (conj z) = conj (clog z)`. -/
def logParts : ExecComplex fmt → Parts fmt := Parts.ofUpperHalf logCore

/--
The complex natural logarithm `clog` (C23 7.3.7.2 and G.6.4.2), with the branch cut along the
negative real axis and imaginary part in `[-π, π]`.

For a finite nonzero argument each part is the exact part rounded once in the direction `mode`
(`log_eq`): `log |z|`, formed from the exact sum of squares, and the principal argument. The sign
of a zero imaginary part selects the side of the cut: `log (-1 ± 0 i) = 0 ± π i`. Special values
follow G.6.4.2: `log (-0 + 0 i) = -∞ + π i`, `log (+0 + 0 i) = -∞ + 0 i`,
`log (x + ∞ i) = ∞ + (π / 2) i`, `log (-∞ + ∞ i) = ∞ + (3 π / 4) i`, with the angles rounded in
the direction `mode`.
-/
def log (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (logParts z).round mode

/--
`clog (1 + z)` where the imaginary sign bit is clear, before rounding. The sum `1 + z` is exact.
A zero argument is returned unchanged, and `z = -1` is the pole `-∞ + 0 i`.
-/
def log1pCore (z : ExecComplex fmt) : Parts fmt :=
  match Model.toRat? z.re, Model.toRat? z.im with
  | some x, some y =>
      if x = 0 ∧ y = 0 then ⟨.exact z.re, .exact z.im⟩
      else if 1 + x = 0 ∧ y = 0 then
        ⟨.exact (Model.negInf fmt), .exact (Model.zero fmt false)⟩
      else logRat fmt (1 + x) y
  | _, _ => logNonfinite z

/-- `clog (1 + z)` before rounding, on every input, by conjugation. -/
def log1pParts : ExecComplex fmt → Parts fmt := Parts.ofUpperHalf log1pCore

/--
`log (1 + z)` for a complex `z`, with the sum `1 + z` exact: each part of a finite result is the
exact part of the principal logarithm of `1 + z` rounded once in the direction `mode`
(`log1p_eq`), however small `z` is.

A zero argument is returned unchanged, `log1p (-1 ± 0 i) = -∞ ± 0 i`, and an argument with a NaN
or an infinite part takes the special values of `clog` (C23 G.6.4.2).
-/
def log1p (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (log1pParts z).round mode

/--
`catanh` where both sign bits are clear, before rounding: the special values of C23 G.6.3.3 and
the logarithm and argument of a finite argument.
-/
def atanhCore (z : ExecComplex fmt) : Parts fmt :=
  let nan := propagatedNaN z
  let zero := Model.zero fmt false
  match Model.toRat? z.re, Model.toRat? z.im with
  | some x, some y =>
      if x = 1 ∧ y = 0 then ⟨.exact (Model.posInf fmt), .exact zero⟩
      else
        ⟨logPart fmt (((1 + x) * (1 + x) + y * y) / ((1 - x) * (1 - x) + y * y)) 4,
          argPart fmt ((1 - x) * (1 + x) - y * y) (2 * y) 2⟩
  | _, _ =>
      if Model.isNaN z.re then
        if Model.isInfinite z.im then ⟨.exact zero, argPart fmt 0 1 1⟩ else ⟨.exact nan, .exact nan⟩
      else if Model.isNaN z.im then
        if Model.isInfinite z.re || Model.isZero z.re then ⟨.exact zero, .exact nan⟩
        else ⟨.exact nan, .exact nan⟩
      else ⟨.exact zero, argPart fmt 0 1 1⟩

/-- `catanh` before rounding, on every input: odd, and `catanh (conj z) = conj (catanh z)`. -/
def atanhParts : ExecComplex fmt → Parts fmt := Parts.ofQuadrant true atanhCore

/--
The complex inverse hyperbolic tangent `catanh` (C23 7.3.6.3 and G.6.3.3), with branch cuts
outside `[-1, 1]` along the real axis and imaginary part in `[-π / 2, π / 2]`.

For a finite argument other than `±1` each part is the exact part rounded once in the direction
`mode` (`atanh_eq`). The sign of a zero imaginary part selects the side of a cut:
`atanh (2 ± 0 i)` has imaginary part `± π / 2`. Special values follow G.6.3.3:
`atanh (1 + 0 i) = ∞ + 0 i`, `atanh (x + ∞ i) = 0 + (π / 2) i`, `atanh (∞ + y i) = 0 + (π / 2) i`.
-/
def atanh (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (atanhParts z).round mode

/-- `catan` before rounding: `catan z = -i catanh (i z)` (C23 G.6.1). -/
def atanParts (z : ExecComplex fmt) : Parts fmt := (atanhParts (mulI z)).mulNegI

/--
The complex inverse tangent `catan` (C23 7.3.5.3), with branch cuts outside `[-i, i]` along the
imaginary axis and real part in `[-π / 2, π / 2]`. It is `-i catanh (i z)`, as C23 G.6.1
specifies, with both multiplications by `i` exact, so each part of a finite result is the exact
part rounded once in the direction `mode` (`atan_eq`) and the special values are those of
`catanh`.
-/
def atan (z : ExecComplex fmt) (mode : Model.IEEERoundingMode := .nearest) : ExecComplex fmt :=
  (atanParts z).round mode

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
