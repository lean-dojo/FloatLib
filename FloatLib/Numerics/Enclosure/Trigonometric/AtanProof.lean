/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Rational.Proof
public import FloatLib.Numerics.Enclosure.Trigonometric.Runtime
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Containment for rational arctangent enclosures

Mathlib's real arctangent series identifies the exact sum, and its geometric tail estimate bounds
the rational partial sums. The reduction identities hold over the reals, and rational interval
arithmetic keeps their constants exact.
-/

public section

namespace FloatLib.Numerics.Enclosure

/-- Casting the executable polynomial gives the usual real arctangent partial sum. -/
theorem cast_atanTaylor (x : ℚ) (n : Nat) :
    (atanTaylor x n : ℝ) =
      ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (x : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
  simp [atanTaylor_def]

/-- The exact rational radius agrees with its real geometric expression. -/
theorem cast_atanRadius (x : ℚ) (n : Nat) :
    (atanRadius x n : ℝ) = |(x : ℝ)| * ((x : ℝ) ^ 2) ^ n / (1 - (x : ℝ) ^ 2) := by
  simp [atanRadius_def]

/-- The geometric majorant bounds every arctangent series term in absolute value. -/
theorem norm_atan_term_le (x : ℝ) (n : Nat) :
    ‖(-1 : ℝ) ^ n * x ^ (2 * n + 1) / (2 * n + 1)‖ ≤ |x| * (x ^ 2) ^ n := by
  have hden : (1 : ℝ) ≤ 2 * n + 1 := le_add_of_nonneg_left (by positivity)
  calc
    _ = |x| ^ (2 * n + 1) / (2 * n + 1) := by
      simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Real.norm_eq_abs]
      rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * n + 1)]
    _ ≤ |x| ^ (2 * n + 1) := div_le_self (by positivity) hden
    _ = |x| * (x ^ 2) ^ n := by rw [pow_succ, pow_mul, sq_abs, mul_comm]

/-- Every finite-degree arctangent approximation has a valid absolute-error bound. -/
theorem abs_atan_sub_atanTaylor_le (x : ℚ) (n : Nat) (hx : |x| < 1) :
    |Real.arctan (x : ℝ) - (atanTaylor x n : ℝ)| ≤ (atanRadius x n : ℝ) := by
  have hreal : |(x : ℝ)| < 1 := by exact_mod_cast hx
  have hsq : (x : ℝ) ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one _).mpr hreal
  have hseries :
      HasSum (fun i : Nat => (-1 : ℝ) ^ i * (x : ℝ) ^ (2 * i + 1) / (2 * i + 1))
        (Real.arctan (x : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      (Real.hasSum_arctan (x := (x : ℝ)) (by simpa only [Real.norm_eq_abs] using hreal))
  have h := norm_sub_le_of_geometric_bound_of_hasSum hsq
    (norm_atan_term_le (x : ℝ)) hseries n
  simpa only [cast_atanTaylor, cast_atanRadius, Real.norm_eq_abs, abs_sub_comm] using h

/-- The small kernel contains the true arctangent throughout its open series domain. -/
theorem contains_atanSmall (x : ℚ) (degree : Nat) (hx : |x| < 1) :
    (atanSmall x degree).Contains (Real.arctan (x : ℝ)) :=
  RationalInterval.contains_around (abs_atan_sub_atanTaylor_le x (degree + 1) hx)

/-- Machin's formula combines the two arctangent enclosures into an enclosure of π/4. -/
theorem contains_piQuarter (degree : Nat) :
    (piQuarter degree).Contains (Real.pi / 4) := by
  have h := RationalInterval.contains_sub
    (RationalInterval.contains_scaleNonnegative
      (contains_atanSmall (1 / 5) degree (by norm_num)) (factor := 4) (by decide))
    (contains_atanSmall (1 / 239) degree (by decide +kernel))
  simpa [piQuarter_def, one_div, Real.four_mul_arctan_inv_5_sub_arctan_inv_239] using h

/-- The transformed argument has magnitude below one for every positive `x`. -/
theorem abs_atan_unit_argument_lt_one (x : ℚ) (hx : 0 < x) :
    |(x - 1) / (x + 1)| < 1 := by
  rw [abs_div, abs_of_pos (by linarith : (0 : ℚ) < x + 1), div_lt_one (by linarith), abs_lt]
  constructor <;> linarith

/--
On the reduced interval `1/2 ≤ x ≤ 1` of `atanUnit`, the transformed argument `(x - 1) / (x + 1)`
has magnitude at most one third, so the remainder radius `atanRadius` at that argument shrinks by a
factor of at least nine per degree.
-/
theorem abs_atan_unit_argument_le (x : ℚ) (hx : 1 / 2 ≤ x) (hone : x ≤ 1) :
    |(x - 1) / (x + 1)| ≤ 1 / 3 := by
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)),
    ← neg_div, div_le_iff₀ (by linarith : 0 < x + 1)]
  linarith

/-- Adding π/4 to the transformed arctangent recovers the arctangent of any nonnegative input. -/
theorem atan_unit_identity (x : ℚ) (hx : 0 ≤ x) :
    Real.pi / 4 + Real.arctan (((x - 1) / (x + 1) : ℚ) : ℝ) =
      Real.arctan (x : ℝ) := by
  have hreal : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have h := Real.arctan_add (x := (x : ℝ)) (y := -1)
    (show (x : ℝ) * -1 < 1 by linarith)
  simp only [Real.arctan_neg, Real.arctan_one, mul_neg_one, sub_neg_eq_add,
    ← sub_eq_add_neg] at h
  push_cast
  simpa only [add_comm] using (eq_add_of_sub_eq h).symm

/--
Unit reduction retains real containment, including the switch at one half.

Containment holds for every nonnegative input, though the reduction is only fast on `[0, 1]`.
-/
theorem contains_atanUnit (x : ℚ) (degree : Nat) (hx : 0 ≤ x) :
    (atanUnit x degree).Contains (Real.arctan (x : ℝ)) := by
  rw [atanUnit_def]
  split
  · apply contains_atanSmall
    rw [abs_of_nonneg hx]
    linarith
  · simpa only [atan_unit_identity x hx] using RationalInterval.contains_add
      (contains_piQuarter degree)
      (contains_atanSmall ((x - 1) / (x + 1)) degree
        (abs_atan_unit_argument_lt_one x (by linarith)))

/-- Inversion restores the arctangent of every nonnegative rational input. -/
theorem contains_atanNonnegative (x : ℚ) (degree : Nat) (hx : 0 ≤ x) :
    (atanNonnegative x degree).Contains (Real.arctan (x : ℝ)) := by
  rw [atanNonnegative_def]
  split
  · exact contains_atanUnit x degree hx
  · have hpos : 0 < x := by linarith
    have hreal : (0 : ℝ) < x := by exact_mod_cast hpos
    have h := RationalInterval.contains_sub
      (RationalInterval.contains_scaleNonnegative (contains_piQuarter degree)
        (factor := 2) (by decide))
      (contains_atanUnit x⁻¹ degree (inv_nonneg.mpr hx))
    convert h using 1
    push_cast
    rw [Real.arctan_inv_of_pos hreal]
    ring

/-- Every rational input and every finite degree yield a valid arctangent enclosure. -/
theorem contains_atan (x : ℚ) (degree : Nat) :
    (atan x degree).Contains (Real.arctan (x : ℝ)) := by
  rw [atan_def]
  split
  · simpa only [Rat.cast_neg, Real.arctan_neg, neg_neg] using
      RationalInterval.contains_neg (contains_atanNonnegative (-x) degree (by linarith))
  · exact contains_atanNonnegative x degree (not_lt.mp ‹¬x < 0›)

end FloatLib.Numerics.Enclosure
