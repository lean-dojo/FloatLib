/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Rational.Runtime
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Rational trigonometric enclosures

The arctangent series is evaluated only for arguments in `(-1, 1)`. Inversion and the
arctangent addition identity at π/4 reduce every rational input to a series argument of magnitude at most
one half. Machin's identity `π / 4 = 4 * atan (1/5) - atan (1/239)` supplies a rational enclosure
of the constant; no rounded approximation to π enters the argument reduction.

The natural argument controls the number of terms. These operations return rational bounds,
not rounded floating-point values. In particular, containment and convergence alone do not
assert termination of a rounding search at an exact rounding boundary.

These kernels provide analytic foundations for the trigonometric functions listed in §5.5 of
the *Posit Standard* (2022); they do not by themselves implement that section's rounding contract.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure

open RationalInterval

/-- The first `n` terms of the arctangent series, evaluated exactly. -/
def atanTaylor (x : ℚ) (n : Nat) : ℚ :=
  ∑ i ∈ Finset.range n, (-1) ^ i * x ^ (2 * i + 1) / ((2 * i + 1 : Nat) : ℚ)

/-- A geometric majorant of the arctangent tail, valid for `|x| < 1`. -/
def atanRadius (x : ℚ) (n : Nat) : ℚ :=
  |x| * (x ^ 2) ^ n / (1 - x ^ 2)

/-- A rational enclosure of the arctangent on its open series domain. -/
def atanSmall (x : ℚ) (degree : Nat) : RationalInterval :=
  around (atanTaylor x (degree + 1)) (atanRadius x (degree + 1))

/-- A rational enclosure of π/4 using Machin's rapidly convergent arctangent identity. -/
def piQuarter (degree : Nat) : RationalInterval :=
  ((atanSmall (1 / 5) degree).scaleNonnegative 4).sub (atanSmall (1 / 239) degree)

/-- Reduce an argument in `[0, 1]` to magnitude at most one half. -/
def atanUnit (x : ℚ) (degree : Nat) : RationalInterval :=
  if x ≤ 1 / 2 then atanSmall x degree
  else (piQuarter degree).add (atanSmall ((x - 1) / (x + 1)) degree)

/-- Inversion reduces a nonnegative rational argument to `[0, 1]`. -/
def atanNonnegative (x : ℚ) (degree : Nat) : RationalInterval :=
  if x ≤ 1 then atanUnit x degree
  else ((piQuarter degree).scaleNonnegative 2).sub (atanUnit x⁻¹ degree)

/-- Enclose the arctangent of any rational argument, using oddness for negative inputs. -/
def atan (x : ℚ) (degree : Nat) : RationalInterval :=
  if x < 0 then (atanNonnegative (-x) degree).neg else atanNonnegative x degree

/-- The `n`th derivative of sine at zero: alternating signs on odd indices and zero otherwise. -/
def sinCoefficient (n : Nat) : ℚ :=
  if n % 2 = 0 then 0 else (-1) ^ (n / 2)

/-- The `n`th derivative of cosine at zero: alternating signs on even indices and zero otherwise. -/
def cosCoefficient (n : Nat) : ℚ :=
  if n % 2 = 0 then (-1) ^ (n / 2) else 0

/-- The sine Taylor polynomial through the requested degree, with exact rational coefficients. -/
def sinTaylor (x : ℚ) (degree : Nat) : ℚ :=
  ∑ i ∈ Finset.range (degree + 1), sinCoefficient i * x ^ i / (i.factorial : ℚ)

/-- The cosine Taylor polynomial through the requested degree. -/
def cosTaylor (x : ℚ) (degree : Nat) : ℚ :=
  ∑ i ∈ Finset.range (degree + 1), cosCoefficient i * x ^ i / (i.factorial : ℚ)

/-- Global Lagrange remainder bound, since every sine and cosine derivative is bounded by one. -/
def trigRadius (x : ℚ) (degree : Nat) : ℚ :=
  |x| ^ (degree + 1) / ((degree + 1).factorial : ℚ)

/-- Intersect a trigonometric enclosure with the known range `[-1, 1]`. -/
def restrictUnit (interval : RationalInterval) : RationalInterval :=
  ⟨max (-1) interval.lo, min 1 interval.hi⟩

/--
Enclose sine at any rational argument using the global Taylor remainder.

The bound is valid even when the degree is too small to be informative. Large arguments can
require large degrees; this baseline performs no reduction by an approximate multiple of π.
-/
def sin (x : ℚ) (degree : Nat) : RationalInterval :=
  restrictUnit (around (sinTaylor x degree) (trigRadius x degree))

/-- Enclose cosine globally and intersect the Taylor bounds with its real range. -/
def cos (x : ℚ) (degree : Nat) : RationalInterval :=
  restrictUnit (around (cosTaylor x degree) (trigRadius x degree))

end FloatLib.Numerics.Enclosure
