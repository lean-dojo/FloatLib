/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Rational.Runtime
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Floor

/-!
# Rational enclosures for exponential and logarithm

Taylor polynomials and their remainder bounds are evaluated with exact rational arithmetic.
`exp` reduces the argument by a power of two and restores the scale by repeated squaring.
The reduced logarithm series uses the identity
`log x = log (1 + t) - log (1 - t)`, where `t = (x - 1) / (x + 1)`.
`log` first reduces a positive argument to `[1, 2)`, then restores the removed multiple of
`log 2`. Every series argument satisfies `|t| ≤ 1/3`.

The natural argument controls the polynomial degree, not a floating-point precision or a search
timeout. The endpoint error tends to zero as it increases. These kernels return bounds. A caller
can use them to separate the exact value from rounding boundaries, or show that both endpoints
round to the same result.

The soundness theorems in `Elementary.Proof` use Mathlib's real Taylor remainder bounds.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure

open RationalInterval

/-- The first `n` terms of the exponential series, evaluated exactly. -/
def expTaylor (x : ℚ) (n : Nat) : ℚ :=
  ∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℚ)

/-- Absolute exponential remainder bound for `|x| ≤ 1` and `n > 0`. -/
def expRadius (x : ℚ) (n : Nat) : ℚ :=
  |x| ^ n * ((n + 1 : Nat) : ℚ) / ((n.factorial : ℚ) * n)

/-- Enclose `exp x` on `|x| ≤ 1`, using at least the constant Taylor term. -/
def expSmall (x : ℚ) (degree : Nat) : RationalInterval :=
  around (expTaylor x (degree + 1)) (expRadius x (degree + 1))

/--
A binary reduction scale determined by the integer part of the absolute argument.

Dividing by this power of two puts the absolute argument below one. Using the quotient rather
than the numerator keeps the scale small for high-precision rational inputs close to one.
-/
def expScale (x : ℚ) : Nat :=
  (x.num.natAbs / x.den).log2 + 1

/-- Enclose the exponential of any rational argument by reduction and repeated squaring. -/
def exp (x : ℚ) (degree : Nat) : RationalInterval :=
  let scale := expScale x
  (expSmall (x / (2 : ℚ) ^ scale) degree).squareRepeat scale

/-- The first `n` terms of `-log (1 - x)`, before restoring the sign. -/
def logOneSubTaylor (x : ℚ) (n : Nat) : ℚ :=
  ∑ i ∈ Finset.range n, x ^ (i + 1) / ((i + 1 : Nat) : ℚ)

/-- Absolute logarithm remainder bound on `|x| < 1`. -/
def logOneSubRadius (x : ℚ) (n : Nat) : ℚ :=
  |x| ^ (n + 1) / (1 - |x|)

/-- Enclose `log (1 - x)` for `|x| < 1`. -/
def logOneSub (x : ℚ) (degree : Nat) : RationalInterval :=
  around (-logOneSubTaylor x degree) (logOneSubRadius x degree)

/--
Enclose the natural logarithm of a positive rational with its transformed series.

The change of variable maps every positive argument into `(-1, 1)`. Argument reduction before
this kernel is useful when a value is far from one, since the series then converges slowly.
-/
def logSeries (x : ℚ) (degree : Nat) : RationalInterval :=
  let t := (x - 1) / (x + 1)
  (logOneSub (-t) degree).sub (logOneSub t degree)

/-- Binary logarithm of the integer part, used to reduce arguments at least one. -/
def logScale (x : ℚ) : Nat :=
  (Nat.floor x).log2

/-- Enclose the logarithm after removing an exact power of two from the argument. -/
def logLarge (x : ℚ) (degree : Nat) : RationalInterval :=
  let scale := logScale x
  (logSeries (x / 2 ^ scale) degree).add
    ((logSeries 2 degree).scaleNonnegative scale)

/--
Enclose the logarithm of a positive rational with binary argument reduction.

Inputs below one are inverted first and the resulting interval is negated. Every series is
therefore evaluated in `[1, 2]`, independently of the original input's exponent.
-/
def log (x : ℚ) (degree : Nat) : RationalInterval :=
  if x < 1 then (logLarge x⁻¹ degree).neg else logLarge x degree

end FloatLib.Numerics.Enclosure
