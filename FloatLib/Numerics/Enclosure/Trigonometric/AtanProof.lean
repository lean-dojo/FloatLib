/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.Runtime
public import FloatLib.Numerics.Enclosure.Rational.Proof
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Containment for rational arctangent enclosures

Mathlib's real arctangent series identifies the exact sum. Its geometric tail estimate bounds
the rational partial sums. The reduction identities hold over the reals; rational interval
arithmetic preserves their exact constants.
-/

public section

namespace FloatLib.Numerics.Enclosure

/-- Casting the executable polynomial gives the usual real arctangent partial sum. -/
theorem cast_atanTaylor (x : ℚ) (n : Nat) :
    (atanTaylor x n : ℝ) =
      ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (x : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
  simp [atanTaylor]

/-- The exact rational radius agrees with its real geometric expression. -/
theorem cast_atanRadius (x : ℚ) (n : Nat) :
    (atanRadius x n : ℝ) = |(x : ℝ)| * ((x : ℝ) ^ 2) ^ n / (1 - (x : ℝ) ^ 2) := by
  simp [atanRadius]

/-- The geometric majorant bounds every arctangent series term in absolute value. -/
theorem norm_atan_term_le (x : ℝ) (n : Nat) :
    ‖(-1 : ℝ) ^ n * x ^ (2 * n + 1) / (2 * n + 1)‖ ≤ |x| * (x ^ 2) ^ n := by
  have hden : (1 : ℝ) ≤ 2 * n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
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
      (contains_atanSmall (1 / 5) degree (by norm_num)) (factor := 4) (by norm_num))
    (contains_atanSmall (1 / 239) degree (by norm_num))
  simpa [piQuarter, one_div, Real.four_mul_arctan_inv_5_sub_arctan_inv_239] using h

/-- The transformed argument has magnitude at most one third for `1/2 ≤ x ≤ 1`. -/
theorem abs_atan_unit_argument_le (x : ℚ) (hx : 1 / 2 ≤ x) (hone : x ≤ 1) :
    |(x - 1) / (x + 1)| ≤ 1 / 3 := by
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)),
    ← neg_div, div_le_iff₀ (by linarith : 0 < x + 1)]
  linarith

/-- Adding π/4 to the transformed arctangent recovers the arctangent of any nonnegative input. -/
theorem atan_unit_identity (x : ℚ) (hx : 0 ≤ x) :
    Real.pi / 4 + Real.arctan (((x - 1) / (x + 1) : ℚ) : ℝ) =
      Real.arctan (x : ℝ) := by
  have hreal : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hden : (x : ℝ) + 1 ≠ 0 := by positivity
  have hlt : (1 : ℝ) * (((x : ℝ) - 1) / ((x : ℝ) + 1)) < 1 := by
    rw [one_mul, div_lt_iff₀ (by positivity : (0 : ℝ) < (x : ℝ) + 1)]
    linarith
  push_cast
  rw [← Real.arctan_one, Real.arctan_add hlt]
  congr 1
  field_simp
  ring

/-- Unit reduction retains real containment, including the switch at one half. -/
theorem contains_atanUnit (x : ℚ) (degree : Nat) (hx : 0 ≤ x) (hone : x ≤ 1) :
    (atanUnit x degree).Contains (Real.arctan (x : ℝ)) := by
  unfold atanUnit
  split
  · apply contains_atanSmall
    rw [abs_of_nonneg hx]
    linarith
  · have ht := abs_atan_unit_argument_le x (by linarith) hone
    simpa only [atan_unit_identity x hx] using RationalInterval.contains_add
      (contains_piQuarter degree)
      (contains_atanSmall ((x - 1) / (x + 1)) degree (by linarith))

/-- Inversion restores the arctangent of every nonnegative rational input. -/
theorem contains_atanNonnegative (x : ℚ) (degree : Nat) (hx : 0 ≤ x) :
    (atanNonnegative x degree).Contains (Real.arctan (x : ℝ)) := by
  unfold atanNonnegative
  split
  · exact contains_atanUnit x degree hx ‹x ≤ 1›
  · have hpos : 0 < x := by linarith
    have hreal : (0 : ℝ) < x := by exact_mod_cast hpos
    have hi : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have h := RationalInterval.contains_sub
      (RationalInterval.contains_scaleNonnegative (contains_piQuarter degree)
        (factor := 2) (by norm_num))
      (contains_atanUnit x⁻¹ degree (inv_nonneg.mpr hx) hi)
    convert h using 1
    push_cast
    rw [Real.arctan_inv_of_pos hreal]
    ring

/-- Every rational input and every finite degree yield a valid arctangent enclosure. -/
theorem contains_atan (x : ℚ) (degree : Nat) :
    (atan x degree).Contains (Real.arctan (x : ℝ)) := by
  unfold atan
  split
  · simpa only [Rat.cast_neg, Real.arctan_neg, neg_neg] using
      RationalInterval.contains_neg (contains_atanNonnegative (-x) degree (by linarith))
  · exact contains_atanNonnegative x degree (by linarith)

end FloatLib.Numerics.Enclosure
