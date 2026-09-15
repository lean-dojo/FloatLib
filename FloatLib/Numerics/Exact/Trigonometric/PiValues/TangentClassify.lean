/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Trigonometric.PiValues.Tangent

/-!
# Exact tangent values and poles

Reducing the rational angle before introducing pi keeps the pole test exact, even at large
arguments. On the open principal interval tangent is injective. Together with the rational
value theorem, this proves that the three classifier branches exhaust all rational answers
away from poles.
-/

public section

namespace FloatLib.Numerics.TrigonometricComparison

private theorem tanPi_eq_fract (argument : ℚ) :
    Real.tan ((argument : ℝ) * Real.pi) =
      Real.tan ((Int.fract argument : ℚ) * Real.pi) := by
  have hangle : (argument : ℝ) * Real.pi =
      (Int.fract argument : ℚ) * Real.pi + (Int.floor argument : ℝ) * Real.pi := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Int.fract_add_floor argument)
    simp only [Rat.cast_add, Rat.cast_intCast] at h
    linear_combination -h * Real.pi
  rw [hangle, Real.tan_add_int_mul_pi]

/-- Centering the rational angle preserves tangent exactly. -/
theorem tan_centeredPi (argument : ℚ) :
    Real.tan ((centeredPi argument : ℚ) * Real.pi) =
      Real.tan ((argument : ℝ) * Real.pi) := by
  rw [tanPi_eq_fract argument]
  dsimp only [centeredPi]
  split
  · rfl
  · push_cast
    rw [sub_mul, one_mul, Real.tan_sub_pi]

/-- Away from a half-integer pole, the centered angle lies in the open principal interval. -/
theorem centeredPi_mem (argument : ℚ) (hpole : Int.fract argument ≠ 1 / 2) :
    -1 / 2 < centeredPi argument ∧ centeredPi argument < 1 / 2 := by
  have hlower := Int.fract_nonneg argument
  have hupper := Int.fract_lt_one argument
  dsimp only [centeredPi]
  split
  · constructor <;> linarith
  · rename_i h
    have hstrict : 1 / 2 < Int.fract argument :=
      lt_of_le_of_ne (le_of_not_gt h) hpole.symm
    constructor <;> linarith

/-- Half-integer pi-scaled angles are poles of tangent. -/
theorem cosPi_eq_zero_of_fract_half (argument : ℚ)
    (hpole : Int.fract argument = 1 / 2) :
    Real.cos ((argument : ℝ) * Real.pi) = 0 := by
  have h := cosPiExact_eq_real argument 0 (by norm_num [cosPiExact, hpole])
  simpa using h

/-- The executable half-integer test detects every tangent pole. -/
theorem cosPi_eq_zero_iff (argument : ℚ) :
    Real.cos ((argument : ℝ) * Real.pi) = 0 ↔ Int.fract argument = 1 / 2 := by
  constructor
  · intro hzero
    have hclassified : cosPiExact argument = some 0 := by
      cases hvalue : cosPiExact argument with
      | none =>
        exact False.elim ((irrational_cosPi_of_exact_none argument hvalue).ne_rat 0
          (by simpa using hzero))
      | some value =>
        have hcast : (value : ℝ) = 0 := by
          rw [← cosPiExact_eq_real argument value hvalue, hzero]
        have : value = 0 := by exact_mod_cast hcast
        simp [this]
    have hsign : (-1 : ℚ) ^ Int.floor argument ≠ 0 :=
      zpow_ne_zero _ (by norm_num)
    dsimp only [cosPiExact] at hclassified
    rw [halfTurnSign_eq_zpow] at hclassified
    split at hclassified
    · simp_all
    · split at hclassified
      · simp_all
      · split at hclassified
        · assumption
        · split at hclassified <;> simp_all
  · exact cosPi_eq_zero_of_fract_half argument

/-- Every classified tangent value is exact. -/
theorem tanPiExact_eq_real (argument value : ℚ)
    (hvalue : tanPiExact argument = some value) :
    Real.tan ((argument : ℝ) * Real.pi) = (value : ℝ) := by
  rw [← tan_centeredPi]
  dsimp only [tanPiExact] at hvalue
  split at hvalue
  · rename_i h
    cases hvalue
    rw [h]
    push_cast
    rw [show (-1 / 4 : ℝ) * Real.pi = -(Real.pi / 4) by ring,
      Real.tan_neg, Real.tan_pi_div_four]
  · split at hvalue
    · rename_i h
      cases hvalue
      simp [h]
    · split at hvalue
      · rename_i h
        cases hvalue
        rw [h]
        push_cast
        rw [show (1 / 4 : ℝ) * Real.pi = Real.pi / 4 by ring, Real.tan_pi_div_four]
      · cases hvalue

/-- Away from poles, an unclassified tangent value is irrational. -/
theorem irrational_tanPi_of_exact_none (argument : ℚ)
    (hpole : Int.fract argument ≠ 1 / 2) (hnone : tanPiExact argument = none) :
    Irrational (Real.tan ((argument : ℝ) * Real.pi)) := by
  rintro ⟨value, hvalue⟩
  have hbounds := centeredPi_mem argument hpole
  have hangle_lower : -(Real.pi / 2) < (centeredPi argument : ℚ) * Real.pi := by
    have h : (-1 / 2 : ℝ) < (centeredPi argument : ℚ) := by exact_mod_cast hbounds.1
    nlinarith [Real.pi_pos, mul_lt_mul_of_pos_right h Real.pi_pos]
  have hangle_upper : (centeredPi argument : ℚ) * Real.pi < Real.pi / 2 := by
    have h : ((centeredPi argument : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr hbounds.2
    push_cast at h
    nlinarith [Real.pi_pos, mul_lt_mul_of_pos_right h Real.pi_pos]
  have htan : Real.tan ((centeredPi argument : ℚ) * Real.pi) = (value : ℝ) := by
    rw [tan_centeredPi, ← hvalue]
  rcases rational_tan_pi_mem argument value hvalue.symm with h | h | h
  · have hsame : (centeredPi argument : ℚ) * Real.pi = -(Real.pi / 4) := by
      apply Real.tan_inj_of_lt_of_lt_pi_div_two hangle_lower hangle_upper
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      simp [htan, h, Real.tan_neg, Real.tan_pi_div_four]
    have hcenter : centeredPi argument = -1 / 4 := by
      have : ((centeredPi argument : ℚ) : ℝ) = -1 / 4 := by
        nlinarith [Real.pi_pos]
      exact_mod_cast this
    norm_num [tanPiExact, hcenter] at hnone
    cases hnone
  · have hsame : (centeredPi argument : ℚ) * Real.pi = 0 := by
      apply Real.tan_inj_of_lt_of_lt_pi_div_two hangle_lower hangle_upper
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      simp [htan, h]
    have hcenter : centeredPi argument = 0 := by
      have := (mul_eq_zero.mp hsame).resolve_right Real.pi_ne_zero
      exact_mod_cast this
    norm_num [tanPiExact, hcenter] at hnone
    cases hnone
  · have hsame : (centeredPi argument : ℚ) * Real.pi = Real.pi / 4 := by
      apply Real.tan_inj_of_lt_of_lt_pi_div_two hangle_lower hangle_upper
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      simp [htan, h, Real.tan_pi_div_four]
    have hcenter : centeredPi argument = 1 / 4 := by
      have : ((centeredPi argument : ℚ) : ℝ) = 1 / 4 := by nlinarith [Real.pi_pos]
      apply Rat.cast_injective (α := ℝ)
      push_cast
      exact this
    norm_num [tanPiExact, hcenter] at hnone
    cases hnone

end FloatLib.Numerics.TrigonometricComparison
