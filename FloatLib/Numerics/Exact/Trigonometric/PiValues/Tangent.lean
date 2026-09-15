/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Trigonometric.PiValues.Proof
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Rational tangent values at rational multiples of pi

Niven's cosine theorem and the double-angle identity restrict rational tangent values to
`-1`, `0`, and `1`. The other cosine cases would make a rational square equal to three.
This also classifies the exact rational values of inverse tangent divided by pi.

The theorem uses mathlib's total tangent, which is zero at poles. Format operations with an
invalid-result policy at poles must check for them before using this totalized value.
-/

public section

namespace FloatLib.Numerics.TrigonometricComparison

private theorem rational_square_ne_three (value : ℚ) : value ^ 2 ≠ 3 := by
  intro hsquare
  have hnot : ¬ IsSquare (3 : ℚ) := by
    exact fun h => (show Nat.Prime 3 by decide).not_isSquare
      (Rat.isSquare_natCast_iff.mp (show IsSquare ((3 : ℕ) : ℚ) from h))
  exact hnot ⟨value, by nlinarith⟩

/-- The only rational tangent values at rational multiples of pi are `-1`, `0`, and `1`. -/
theorem rational_tan_pi_mem (argument value : ℚ)
    (hvalue : Real.tan ((argument : ℝ) * Real.pi) = (value : ℝ)) :
    value = -1 ∨ value = 0 ∨ value = 1 := by
  by_cases hcos : Real.cos ((argument : ℝ) * Real.pi) = 0
  · right
    left
    have : (value : ℝ) = 0 := by rw [← hvalue, Real.tan_eq_sin_div_cos, hcos, div_zero]
    exact_mod_cast this
  have hden : (1 : ℝ) + (value : ℝ) ^ 2 ≠ 0 := by positivity
  have hdouble :
      Real.cos (((2 * argument : ℚ) : ℝ) * Real.pi) =
        (((1 - value ^ 2) / (1 + value ^ 2) : ℚ) : ℝ) := by
    push_cast
    rw [mul_assoc, Real.cos_two_mul, ← Real.inv_one_add_tan_sq hcos, hvalue]
    field_simp
    ring
  have hrelation :
      1 - (value : ℝ) ^ 2 =
        Real.cos (((2 * argument : ℚ) : ℝ) * Real.pi) * (1 + (value : ℝ) ^ 2) := by
    rw [hdouble]
    push_cast
    field_simp
  rcases niven ⟨2 * argument, rfl⟩ ⟨(1 - value ^ 2) / (1 + value ^ 2), hdouble⟩ with
    h | h | h | h | h
  · exfalso
    nlinarith
  · exfalso
    apply rational_square_ne_three value
    have : (value : ℝ) ^ 2 = 3 := by nlinarith
    exact_mod_cast this
  · have hsquare : value ^ 2 = 1 := by
      have : (value : ℝ) ^ 2 = 1 := by nlinarith
      exact_mod_cast this
    rcases sq_eq_one_iff.mp hsquare with hone | hneg
    · exact Or.inr (Or.inr hone)
    · exact Or.inl hneg
  · exfalso
    apply rational_square_ne_three (3 * value)
    have : ((3 : ℝ) * value) ^ 2 = 3 := by nlinarith
    exact_mod_cast this
  · right
    left
    change Real.cos (((2 * argument : ℚ) : ℝ) * Real.pi) = 1 at h
    have : (value : ℝ) = 0 := by nlinarith [sq_nonneg (value : ℝ)]
    exact_mod_cast this

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
