/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Enclosure.Runtime
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Principal-branch identities for the complex argument

We apply the inverse tangent only after locating the argument in its open principal branch. They
also cover the real and imaginary axes and Mathlib's totalization at the origin.
-/

public section

namespace FloatLib.Numerics.TrigonometricComparison

/-- A positive real component places the argument in the open arctangent branch. -/
theorem arg_of_pos (x y : ℝ) (hx : 0 < x) :
    Complex.arg ⟨x, y⟩ = Real.arctan (y / x) := by
  have hlo := (Complex.neg_pi_div_two_lt_arg_iff (z := ⟨x, y⟩)).mpr (Or.inl hx : 0 < x ∨ 0 ≤ y)
  have hhi := (Complex.arg_lt_pi_div_two_iff (z := ⟨x, y⟩)).mpr
    (Or.inl hx : 0 < x ∨ y < 0 ∨ (⟨x, y⟩ : ℂ) = 0)
  simpa only [Complex.tan_arg] using (Real.arctan_tan hlo hhi).symm

/-- The upper left quadrant, including the negative real axis, adds π to the arctangent. -/
theorem arg_of_neg_nonneg (x y : ℝ) (hx : x < 0) (hy : 0 ≤ y) :
    Complex.arg ⟨x, y⟩ = Real.arctan (y / x) + Real.pi := by
  have hneg : Complex.arg (-(⟨x, y⟩ : ℂ)) = Real.arctan (y / x) := by
    change Complex.arg ⟨-x, -y⟩ = _
    simpa only [neg_div_neg_eq] using arg_of_pos (-x) (-y) (neg_pos.mpr hx)
  have hshift : Complex.arg (-(⟨x, y⟩ : ℂ)) = Complex.arg ⟨x, y⟩ - Real.pi :=
    Complex.arg_neg_eq_arg_sub_pi_iff.mpr
      (hy.eq_or_lt.elim (fun h => Or.inr ⟨h.symm, hx⟩) Or.inl)
  exact eq_add_of_sub_eq (hshift.symm.trans hneg)

/-- The lower left quadrant subtracts π from the arctangent. -/
theorem arg_of_neg_neg (x y : ℝ) (hx : x < 0) (hy : y < 0) :
    Complex.arg ⟨x, y⟩ = Real.arctan (y / x) - Real.pi := by
  have hneg : Complex.arg (-(⟨x, y⟩ : ℂ)) = Real.arctan (y / x) := by
    change Complex.arg ⟨-x, -y⟩ = _
    simpa only [neg_div_neg_eq] using arg_of_pos (-x) (-y) (neg_pos.mpr hx)
  have hshift : Complex.arg (-(⟨x, y⟩ : ℂ)) = Complex.arg ⟨x, y⟩ + Real.pi :=
    Complex.arg_neg_eq_arg_add_pi_of_im_neg hy
  exact eq_sub_of_add_eq (hshift.symm.trans hneg)

/-- The arctangent formula for the principal argument, including both axes and the origin. -/
theorem arg_formula (x y : ℝ) :
    Complex.arg ⟨x, y⟩ =
      if 0 < x then Real.arctan (y / x)
      else if x < 0 then
        if 0 ≤ y then Real.arctan (y / x) + Real.pi
        else Real.arctan (y / x) - Real.pi
      else if 0 < y then Real.pi / 2
      else if y < 0 then -(Real.pi / 2) else 0 := by
  split
  · exact arg_of_pos x y ‹_›
  · split
    · split
      · exact arg_of_neg_nonneg x y ‹_› ‹_›
      · exact arg_of_neg_neg x y ‹_› (lt_of_not_ge ‹_›)
    · have hx : x = 0 := by linarith
      subst x
      split
      · exact Complex.arg_eq_pi_div_two_iff.mpr ⟨rfl, ‹_›⟩
      · split
        · exact Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨rfl, ‹_›⟩
        · have hy : y = 0 := by linarith
          subst y
          exact Complex.arg_zero

/-- Rational quadrant reduction equals the exact principal complex argument. -/
theorem atan2Reduction_eq_arg (x y : ℚ) :
    Real.arctan ((atan2Reduction x y).1 : ℝ) +
        ((atan2Reduction x y).2 : ℝ) * (Real.pi / 4) =
      Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ := by
  rw [arg_formula]
  simp only [atan2Reduction, Rat.cast_pos, Rat.cast_lt_zero, Rat.cast_nonneg]
  split_ifs <;> norm_num <;> ring

end FloatLib.Numerics.TrigonometricComparison
