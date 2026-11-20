/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Trigonometric.PiValues.Proof
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Rational tangent values at rational multiples of pi

Niven's cosine theorem and the double-angle identity leave only `-1`, `0`, and `1` as rational
tangent values, because the other cosine cases would make a rational square equal to three. This
also classifies the exact rational values of inverse tangent divided by pi.

The theorem uses Mathlib's total tangent, which is zero at poles, so a format operation with an
invalid-result policy at poles has to check for them before using this totalized value.
-/

public section

namespace FloatLib.Numerics.TrigonometricComparison

private theorem rational_square_ne_three (value : ℚ) : value ^ 2 ≠ 3 := by
  intro hsquare
  have hnot : ¬ IsSquare (3 : ℚ) := by
    exact fun h => (show Nat.Prime 3 by decide).not_isSquare
      (Rat.isSquare_natCast_iff.mp (show IsSquare ((3 : ℕ) : ℚ) from h))
  exact hnot ⟨value, hsquare.symm.trans (pow_two value)⟩

/-- The only rational tangent values at rational multiples of pi are `-1`, `0`, and `1`. -/
theorem rational_tan_pi_mem (argument value : ℚ)
    (hvalue : Real.tan ((argument : ℝ) * Real.pi) = (value : ℝ)) :
    value = -1 ∨ value = 0 ∨ value = 1 := by
  by_cases hcos : Real.cos ((argument : ℝ) * Real.pi) = 0
  · exact Or.inr (Or.inl (Rat.cast_eq_zero.mp
      (hvalue.symm.trans (Real.tan_eq_zero_of_cos_eq_zero hcos))))
  have hdouble :
      Real.cos (((2 * argument : ℚ) : ℝ) * Real.pi) =
        (((1 - value ^ 2) / (1 + value ^ 2) : ℚ) : ℝ) := by
    push_cast
    rw [mul_assoc]
    have hne : Real.cos (2 * ((argument : ℝ) * Real.pi)) ≠ -1 := by
      rw [Real.cos_two_mul]
      have := sq_pos_of_ne_zero hcos
      linarith
    rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq _ hne,
      mul_div_cancel_left₀ _ two_ne_zero, hvalue]
  have hcases := niven ⟨2 * argument, rfl⟩
    ⟨(1 - value ^ 2) / (1 + value ^ 2), hdouble⟩
  rw [hdouble] at hcases
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcases
  have hcasesQ : (1 - value ^ 2) / (1 + value ^ 2) = -1 ∨
      (1 - value ^ 2) / (1 + value ^ 2) = -1 / 2 ∨
      (1 - value ^ 2) / (1 + value ^ 2) = 0 ∨
      (1 - value ^ 2) / (1 + value ^ 2) = 1 / 2 ∨
      (1 - value ^ 2) / (1 + value ^ 2) = 1 := by
    simp only [← Rat.cast_inj (α := ℝ)]
    simpa only [Rat.cast_neg, Rat.cast_one, Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat]
      using hcases
  have hden : (1 : ℚ) + value ^ 2 ≠ 0 := by positivity
  rcases hcasesQ with h | h | h | h | h
  · have := (div_eq_iff hden).mp h
    linarith
  · have := (div_eq_iff hden).mp h
    exact False.elim (rational_square_ne_three value (by linarith))
  · have := (div_eq_iff hden).mp h
    rcases sq_eq_one_iff.mp (show value ^ 2 = 1 by linarith) with hone | hneg
    · exact Or.inr (Or.inr hone)
    · exact Or.inl hneg
  · have := (div_eq_iff hden).mp h
    exact False.elim (rational_square_ne_three (3 * value) (by linarith))
  · have := (div_eq_iff hden).mp h
    exact Or.inr (Or.inl (sq_eq_zero_iff.mp (show value ^ 2 = 0 by linarith)))

/-- Outside the three exact inputs, inverse tangent divided by pi is irrational. -/
theorem irrational_arctan_div_pi_ratCast (argument : ℚ)
    (hnegative : argument ≠ -1) (hzero : argument ≠ 0) (hpositive : argument ≠ 1) :
    Irrational (Real.arctan (argument : ℝ) / Real.pi) := by
  rintro ⟨angle, hangle⟩
  have hscale : (angle : ℝ) * Real.pi = Real.arctan (argument : ℝ) := by
    rw [hangle]
    exact div_mul_cancel₀ _ Real.pi_ne_zero
  have htan : Real.tan ((angle : ℝ) * Real.pi) = (argument : ℝ) := by
    rw [hscale, Real.tan_arctan]
  rcases rational_tan_pi_mem angle argument htan with h | h | h
  · exact hnegative h
  · exact hzero h
  · exact hpositive h

end FloatLib.Numerics.TrigonometricComparison
