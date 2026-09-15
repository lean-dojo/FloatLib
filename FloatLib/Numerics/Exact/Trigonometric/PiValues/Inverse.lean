/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Trigonometric.PiValues.Tangent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Exact inverse trigonometric values divided by pi

On `[-1, 1]`, inverse sine and cosine return rational multiples of pi at five rational inputs.
Inverse tangent has three such inputs. The classifiers return these answers exactly.
Niven's theorem rules out all other rational answers, supplying the termination premise
for interval comparison. Domain checks belong to the numerical operation using the classifier.
-/

public section

namespace FloatLib.Numerics.TrigonometricComparison

/-- Every classified inverse tangent value is exact. -/
theorem arctanPiExact_eq_real (argument value : ℚ)
    (hvalue : arctanPiExact argument = some value) :
    Real.arctan (argument : ℝ) / Real.pi = (value : ℝ) := by
  unfold arctanPiExact at hvalue
  split at hvalue
  · rename_i h
    cases hvalue
    rw [h]
    push_cast
    rw [Real.arctan_neg, Real.arctan_one]
    field_simp
  · split at hvalue
    · rename_i h
      cases hvalue
      simp [h]
    · split at hvalue
      · rename_i h
        cases hvalue
        rw [h]
        push_cast
        rw [Real.arctan_one]
        field_simp
      · cases hvalue

/-- Every unclassified inverse tangent divided by pi is irrational. -/
theorem irrational_arctanPi_of_exact_none (argument : ℚ)
    (hnone : arctanPiExact argument = none) :
    Irrational (Real.arctan (argument : ℝ) / Real.pi) := by
  apply irrational_arctan_div_pi_ratCast argument
  all_goals
    intro h
    norm_num [arctanPiExact, h] at hnone
  all_goals cases hnone

private theorem arcsin_half : Real.arcsin (1 / 2) = Real.pi / 6 := by
  apply Real.arcsin_eq_of_sin_eq Real.sin_pi_div_six
  constructor <;> linarith [Real.pi_pos]

/-- Every classified inverse sine value is exact. -/
theorem arcsinPiExact_eq_real (argument value : ℚ)
    (hvalue : arcsinPiExact argument = some value) :
    Real.arcsin (argument : ℝ) / Real.pi = (value : ℝ) := by
  unfold arcsinPiExact at hvalue
  split at hvalue
  · rename_i h
    cases hvalue
    rw [h]
    push_cast
    rw [Real.arcsin_neg_one]
    field_simp
  · split at hvalue
    · rename_i h
      cases hvalue
      rw [h]
      push_cast
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.arcsin_neg, arcsin_half]
      field_simp
    · split at hvalue
      · rename_i h
        cases hvalue
        simp [h]
      · split at hvalue
        · rename_i h
          cases hvalue
          rw [h]
          push_cast
          rw [arcsin_half]
          field_simp
        · split at hvalue
          · rename_i h
            cases hvalue
            rw [h]
            push_cast
            rw [Real.arcsin_one]
            field_simp
          · cases hvalue

/-- Niven's theorem makes the inverse sine classifier complete on `[-1, 1]`. -/
theorem irrational_arcsinPi_of_exact_none (argument : ℚ)
    (hlower : -1 ≤ argument) (hupper : argument ≤ 1)
    (hnone : arcsinPiExact argument = none) :
    Irrational (Real.arcsin (argument : ℝ) / Real.pi) := by
  rintro ⟨angle, hangle⟩
  have hscale : (angle : ℝ) * Real.pi = Real.arcsin (argument : ℝ) := by
    rw [hangle]
    exact div_mul_cancel₀ _ Real.pi_ne_zero
  have hsin := Real.sin_arcsin (x := (argument : ℝ))
    (by exact_mod_cast hlower) (by exact_mod_cast hupper)
  have hvalues := niven_sin ⟨angle, hscale.symm⟩ ⟨argument, hsin⟩
  rw [hsin] at hvalues
  rcases hvalues with h | h | h | h | h
  · have hq : argument = -1 := by
      apply Rat.cast_injective (α := ℝ)
      push_cast
      linarith
    norm_num [arcsinPiExact, hq] at hnone
    cases hnone
  · have hq : argument = -1 / 2 := by
      apply Rat.cast_injective (α := ℝ)
      push_cast
      linarith
    norm_num [arcsinPiExact, hq] at hnone
    cases hnone
  · have hq : argument = 0 := by
      apply Rat.cast_injective (α := ℝ)
      push_cast
      linarith
    norm_num [arcsinPiExact, hq] at hnone
    cases hnone
  · have hq : argument = 1 / 2 := by
      apply Rat.cast_injective (α := ℝ)
      push_cast
      linarith
    norm_num [arcsinPiExact, hq] at hnone
    cases hnone
  · have hq : argument = 1 := by
      apply Rat.cast_injective (α := ℝ)
      push_cast
      change (argument : ℝ) = 1 at h
      exact h
    norm_num [arcsinPiExact, hq] at hnone
    cases hnone

/-- Every classified inverse cosine value is exact. -/
theorem arccosPiExact_eq_real (argument value : ℚ)
    (hvalue : arccosPiExact argument = some value) :
    Real.arccos (argument : ℝ) / Real.pi = (value : ℝ) := by
  obtain ⟨sineValue, hsine, rfl⟩ := Option.map_eq_some_iff.mp hvalue
  rw [Real.arccos, sub_div, arcsinPiExact_eq_real argument sineValue hsine]
  push_cast
  field_simp

/-- An unclassified inverse cosine divided by pi is irrational on its real domain. -/
theorem irrational_arccosPi_of_exact_none (argument : ℚ)
    (hlower : -1 ≤ argument) (hupper : argument ≤ 1)
    (hnone : arccosPiExact argument = none) :
    Irrational (Real.arccos (argument : ℝ) / Real.pi) := by
  have hsine : arcsinPiExact argument = none := Option.map_eq_none_iff.mp hnone
  have hirr := irrational_arcsinPi_of_exact_none argument hlower hupper hsine
  rintro ⟨angle, hangle⟩
  apply hirr
  refine ⟨1 / 2 - angle, ?_⟩
  push_cast
  rw [hangle, Real.arccos, sub_div]
  field_simp
  ring

end FloatLib.Numerics.TrigonometricComparison
