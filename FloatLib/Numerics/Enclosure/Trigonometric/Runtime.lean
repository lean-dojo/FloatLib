/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Taylor
public import FloatLib.Numerics.Enclosure.Rational.Runtime

/-!
# Rational trigonometric enclosures

We evaluate the arctangent series only for arguments in `(-1, 1)`. Inversion and the arctangent
addition identity at π/4 reduce every rational input to a series argument of magnitude at most one
half. Machin's identity `π / 4 = 4 * atan (1/5) - atan (1/239)` gives a rational enclosure of the
constant, so no rounded approximation to π enters the argument reduction, and the arctangent partial
sums are evaluated by binary splitting with one final normalization.

Its natural argument controls the number of terms. What comes back are rational bounds and never
rounded floating-point values. Containment and convergence alone don't promise that a rounding
search terminates at an exact rounding boundary.

These kernels are the analytic foundation for the trigonometric functions listed in §5.5 of the
*Posit Standard* (2022), but on their own they don't implement that section's rounding contract.

Taylor coefficients follow the NIST *Digital Library of Mathematical Functions*:
[§4.19.E1](https://dlmf.nist.gov/4.19.E1) for sine, [§4.19.E2](https://dlmf.nist.gov/4.19.E2) for
cosine, and [§4.24.E3](https://dlmf.nist.gov/4.24.E3) for arctangent.

Lean's kernel evaluates these definitions when a proof checks an enclosure by `decide`, so the
ones on its path are written with the functions of `FloatLib.Numerics.Kernel.Q` and `Z`, which
compute the same rationals and integers in fewer kernel steps. Each has a theorem named `…_def`
that states it in ordinary notation, and compiled code runs core's operations as before.

`SinCosProof` proves the remainder bounds using Mathlib's Taylor theorem. `AtanProof` bounds the
arctangent tail by a geometric series and uses Mathlib's Machin identity to enclose π/4.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure

open RationalInterval

/-- Sum of the first `n` terms of the arctangent series, in exact rational arithmetic. -/
def atanTaylor (x : ℚ) (n : Nat) : ℚ := Taylor.atan x n

/-- `atanTaylor x n` is the sum of the first `n` terms of the arctangent series. -/
theorem atanTaylor_def (x : ℚ) (n : Nat) :
    atanTaylor x n =
      ∑ i ∈ Finset.range n, (-1) ^ i * x ^ (2 * i + 1) / ((2 * i + 1 : Nat) : ℚ) :=
  Taylor.atan_eq_sum x n

/-- The arctangent Taylor sum is its evaluation by binary splitting. -/
theorem atanTaylor_eq_binarySplit : atanTaylor = Taylor.atan := rfl

/--
A geometric majorant of the arctangent tail, valid for `|x| < 1`: `atanRadius_def` states it as
`|x| * (x ^ 2) ^ n / (1 - x ^ 2)`.
-/
def atanRadius (x : ℚ) (n : Nat) : ℚ :=
  Kernel.Q.div (Kernel.Q.mul (Kernel.Q.abs x) (Kernel.Q.pow (Kernel.Q.pow x 2) n))
    (Kernel.Q.sub 1 (Kernel.Q.pow x 2))

/-- The arctangent remainder bound, in ordinary notation. -/
theorem atanRadius_def (x : ℚ) (n : Nat) : atanRadius x n = |x| * (x ^ 2) ^ n / (1 - x ^ 2) := by
  unfold atanRadius
  simp only [Kernel.Q.div_eq, Kernel.Q.mul_eq, Kernel.Q.abs_eq, Kernel.Q.pow_eq, Kernel.Q.sub_eq]

/-- A rational enclosure of the arctangent on its open series domain. -/
def atanSmall (x : ℚ) (degree : Nat) : RationalInterval :=
  around (atanTaylor x (degree + 1)) (atanRadius x (degree + 1))

/-- A rational enclosure of π/4 using Machin's rapidly convergent arctangent identity. -/
def piQuarter (degree : Nat) : RationalInterval :=
  ((atanSmall (Kernel.Q.mk 1 5) degree).scaleNonnegative 4).sub
    (atanSmall (Kernel.Q.mk 1 239) degree)

/-- Machin's enclosure, with its two arguments in ordinary notation. -/
theorem piQuarter_def (degree : Nat) :
    piQuarter degree =
      ((atanSmall (1 / 5) degree).scaleNonnegative 4).sub (atanSmall (1 / 239) degree) := by
  have hfive : Kernel.Q.mk 1 5 = (1 / 5 : ℚ) := by
    rw [Kernel.Q.mk_eq, Rat.mkRat_eq_div]
    simp
  have hlarge : Kernel.Q.mk 1 239 = (1 / 239 : ℚ) := by
    rw [Kernel.Q.mk_eq, Rat.mkRat_eq_div]
    simp
  unfold piQuarter
  rw [hfive, hlarge]

/-- Enclose `atan x` for `x` in `[0, 1]`, with a series argument of magnitude at most one half. -/
def atanUnit (x : ℚ) (degree : Nat) : RationalInterval :=
  Bool.casesOn (motive := fun _ => RationalInterval) (Kernel.Q.le x (Kernel.Q.mk 1 2))
    ((piQuarter degree).add
      (atanSmall (Kernel.Q.div (Kernel.Q.sub x 1) (Kernel.Q.add x 1)) degree))
    (atanSmall x degree)

/-- The unit reduction, in ordinary notation. -/
theorem atanUnit_def (x : ℚ) (degree : Nat) :
    atanUnit x degree =
      if x ≤ 1 / 2 then atanSmall x degree
      else (piQuarter degree).add (atanSmall ((x - 1) / (x + 1)) degree) := by
  have hhalf : Kernel.Q.mk 1 2 = (1 / 2 : ℚ) := by
    rw [Kernel.Q.mk_eq, Rat.mkRat_eq_div]
    simp
  unfold atanUnit
  rw [Kernel.Q.casesOn_le, hhalf, Kernel.Q.div_eq, Kernel.Q.sub_eq, Kernel.Q.add_eq]

/-- Enclose `atan x` for nonnegative `x`, inverting arguments above one into `[0, 1]`. -/
def atanNonnegative (x : ℚ) (degree : Nat) : RationalInterval :=
  Bool.casesOn (motive := fun _ => RationalInterval) (Kernel.Q.le x 1)
    (((piQuarter degree).scaleNonnegative 2).sub (atanUnit (Kernel.Q.inv x) degree))
    (atanUnit x degree)

/-- The reduction of arguments above one, in ordinary notation. -/
theorem atanNonnegative_def (x : ℚ) (degree : Nat) :
    atanNonnegative x degree =
      if x ≤ 1 then atanUnit x degree
      else ((piQuarter degree).scaleNonnegative 2).sub (atanUnit x⁻¹ degree) := by
  unfold atanNonnegative
  rw [Kernel.Q.casesOn_le, Kernel.Q.inv_eq]

/-- Enclose the arctangent of any rational argument, using oddness for negative inputs. -/
def atan (x : ℚ) (degree : Nat) : RationalInterval :=
  Bool.casesOn (motive := fun _ => RationalInterval) (Kernel.Q.lt x 0)
    (atanNonnegative x degree) ((atanNonnegative (-x) degree).neg)

/-- The arctangent enclosure, in ordinary notation. -/
theorem atan_def (x : ℚ) (degree : Nat) :
    atan x degree =
      if x < 0 then (atanNonnegative (-x) degree).neg else atanNonnegative x degree := by
  unfold atan
  rw [Kernel.Q.casesOn_lt]

/-- The `n`th derivative of sine at zero: alternating signs on odd indices and zero otherwise. -/
def sinCoefficient (n : Nat) : ℚ :=
  if n % 2 = 0 then 0 else (-1) ^ (n / 2)

/-- The `n`th derivative of cosine at zero: alternating signs on even indices and zero otherwise. -/
def cosCoefficient (n : Nat) : ℚ :=
  if n % 2 = 0 then (-1) ^ (n / 2) else 0

/--
Sine Taylor polynomial through `degree`, with exact rational coefficients: its nonzero terms are
summed by binary splitting (`sinTaylor_def` states the sum over all terms).
-/
def sinTaylor (x : ℚ) (degree : Nat) : ℚ := Taylor.sin x ((degree + 1) / 2)

/-- `sinTaylor x degree` is the sine Taylor polynomial through `degree`. -/
theorem sinTaylor_def (x : ℚ) (degree : Nat) :
    sinTaylor x degree =
      ∑ i ∈ Finset.range (degree + 1), sinCoefficient i * x ^ i / (i.factorial : ℚ) := by
  unfold sinTaylor
  rw [Taylor.sin_eq_sum]
  induction degree with
  | zero => simp [sinCoefficient]
  | succ d ih =>
    rw [Finset.sum_range_succ _ (d + 1), ← ih]
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' d
    · have h₁ : (2 * j + 1 + 1) / 2 = j + 1 := by omega
      have h₂ : (2 * j + 1) / 2 = j := by omega
      have hc : sinCoefficient (2 * j + 1) = (-1) ^ j := by
        unfold sinCoefficient
        rw [ite_eq_right (by omega), h₂]
      rw [h₁, h₂, Finset.sum_range_succ, hc]
    · have h₁ : (2 * j + 1 + 1 + 1) / 2 = j + 1 := by omega
      have h₂ : (2 * j + 1 + 1) / 2 = j + 1 := by omega
      have hc : sinCoefficient (2 * j + 1 + 1) = 0 := by
        unfold sinCoefficient
        rw [ite_eq_left (by omega)]
      rw [h₁, h₂, hc, zero_mul, zero_div, add_zero]

/--
Cosine Taylor polynomial through `degree`: its nonzero terms are summed by binary splitting
(`cosTaylor_def` states the sum over all terms).
-/
def cosTaylor (x : ℚ) (degree : Nat) : ℚ := Taylor.cos x (degree / 2 + 1)

/-- `cosTaylor x degree` is the cosine Taylor polynomial through `degree`. -/
theorem cosTaylor_def (x : ℚ) (degree : Nat) :
    cosTaylor x degree =
      ∑ i ∈ Finset.range (degree + 1), cosCoefficient i * x ^ i / (i.factorial : ℚ) := by
  unfold cosTaylor
  rw [Taylor.cos_eq_sum]
  induction degree with
  | zero => simp [cosCoefficient]
  | succ d ih =>
    rw [Finset.sum_range_succ _ (d + 1), ← ih]
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' d
    · have h₁ : (2 * j + 1) / 2 + 1 = 2 * j / 2 + 1 := by omega
      have hc : cosCoefficient (2 * j + 1) = 0 := by
        unfold cosCoefficient
        rw [ite_eq_right (by omega)]
      rw [h₁, hc, zero_mul, zero_div, add_zero]
    · have h₁ : (2 * j + 1 + 1) / 2 + 1 = j + 1 + 1 := by omega
      have h₂ : (2 * j + 1) / 2 + 1 = j + 1 := by omega
      have hc : cosCoefficient (2 * j + 1 + 1) = (-1) ^ (j + 1) := by
        unfold cosCoefficient
        rw [ite_eq_left (by omega), show (2 * j + 1 + 1) / 2 = j + 1 by omega]
      rw [h₁, h₂, Finset.sum_range_succ, hc, show 2 * (j + 1) = 2 * j + 1 + 1 by omega]

/--
Global Lagrange remainder bound, since every sine and cosine derivative is bounded by one:
`trigRadius_def` states it as `|x| ^ (degree + 1) / (degree + 1)!`. The body builds the numerator
and the denominator from naturals and reduces once.
-/
def trigRadius (x : ℚ) (degree : Nat) : ℚ :=
  Kernel.Q.mk (Int.ofNat (Nat.pow (Kernel.Z.natAbs x.num) (Nat.succ degree)))
    (Nat.mul (Nat.pow x.den (Nat.succ degree)) (Kernel.factorial (Nat.succ degree)))

/-- The trigonometric remainder bound, in ordinary notation. -/
theorem trigRadius_def (x : ℚ) (degree : Nat) :
    trigRadius x degree = |x| ^ (degree + 1) / ((degree + 1).factorial : ℚ) := by
  unfold trigRadius
  rw [Kernel.Q.mk_eq, Rat.mkRat_eq_div, Kernel.Z.natAbs_eq, Kernel.factorial_eq,
    Kernel.Q.abs_eq_natAbs_div, div_pow, div_div]
  change (((x.num.natAbs ^ (degree + 1) : Nat) : Int) : ℚ) /
    ((x.den ^ (degree + 1) * (degree + 1).factorial : Nat) : ℚ) = _
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- Intersect a trigonometric enclosure with the known range `[-1, 1]`. -/
def restrictUnit (interval : RationalInterval) : RationalInterval :=
  ⟨Kernel.Q.max (-1) interval.lo, Kernel.Q.min 1 interval.hi⟩

/-- The endpoints of `restrictUnit`, in ordinary notation. -/
theorem restrictUnit_def (interval : RationalInterval) :
    restrictUnit interval = ⟨max (-1) interval.lo, min 1 interval.hi⟩ := by
  unfold restrictUnit
  rw [Kernel.Q.max_eq, Kernel.Q.min_eq]

/--
Enclose sine at any rational argument using the global Taylor remainder.

The bound is valid even when the degree is too small to be informative. Large arguments can
require large degrees, because this baseline performs no reduction by an approximate multiple of
π.
-/
def sin (x : ℚ) (degree : Nat) : RationalInterval :=
  restrictUnit (around (sinTaylor x degree) (trigRadius x degree))

/-- Enclose cosine globally and intersect the Taylor bounds with its real range. -/
def cos (x : ℚ) (degree : Nat) : RationalInterval :=
  restrictUnit (around (cosTaylor x degree) (trigRadius x degree))

end FloatLib.Numerics.Enclosure
