/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Trigonometric.PiValues.Runtime
public import Mathlib.NumberTheory.Niven

/-!
# Complete rational-value classification for pi-scaled sine and cosine

Niven's theorem supplies completeness, including thirds as well as the more familiar integer
and half-integer angles. Every unclassified value is irrational, so converging rational
enclosures eventually separate it from any rational rounding boundary.
-/

public section

namespace FloatLib.Numerics.TrigonometricComparison

/-- The parity computation is the exact sign from the integer-angle cosine identity. -/
theorem halfTurnSign_eq_zpow (turns : ℤ) :
    halfTurnSign turns = (-1 : ℚ) ^ turns := by
  simp [halfTurnSign, neg_one_zpow_eq_ite, Int.even_iff]

private theorem cosPi_eq_fract (argument : ℚ) :
    Real.cos ((argument : ℝ) * Real.pi) =
      ((-1 : ℚ) ^ Int.floor argument : ℚ) *
        Real.cos ((Int.fract argument : ℚ) * Real.pi) := by
  have hangle : (argument : ℝ) * Real.pi =
      (Int.fract argument : ℚ) * Real.pi + (Int.floor argument : ℝ) * Real.pi := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Int.fract_add_floor argument)
    simp only [Rat.cast_add, Rat.cast_intCast] at h
    linear_combination -h * Real.pi
  rw [hangle, Real.cos_add_int_mul_pi]
  push_cast
  rfl

/-- Every reported rational cosine value is exact. -/
theorem cosPiExact_eq_real (argument value : ℚ) (hvalue : cosPiExact argument = some value) :
    Real.cos ((argument : ℝ) * Real.pi) = (value : ℝ) := by
  rw [cosPi_eq_fract]
  dsimp only [cosPiExact] at hvalue
  rw [halfTurnSign_eq_zpow] at hvalue
  split at hvalue
  · rename_i hzero
    cases hvalue
    simp [hzero]
  · split at hvalue
    · rename_i hthird
      cases hvalue
      simp only [hthird]
      push_cast
      rw [show (1 / 3 : ℝ) * Real.pi = Real.pi / 3 by ring, Real.cos_pi_div_three]
      ring
    · split at hvalue
      · rename_i hhalf
        cases hvalue
        simp only [hhalf]
        push_cast
        rw [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring, Real.cos_pi_div_two]
        ring
      · split at hvalue
        · rename_i hthird
          cases hvalue
          simp only [hthird]
          push_cast
          rw [show (2 / 3 : ℝ) * Real.pi = Real.pi - Real.pi / 3 by ring,
            Real.cos_pi_sub, Real.cos_pi_div_three]
          ring
        · cases hvalue

/-- An unclassified cosine value is irrational, so refinement cannot stall at a boundary. -/
theorem irrational_cosPi_of_exact_none (argument : ℚ)
    (hnone : cosPiExact argument = none) :
    Irrational (Real.cos ((argument : ℝ) * Real.pi)) := by
  rintro ⟨value, hvalue⟩
  rcases niven_fract_angle_div_pi_eq ⟨value, hvalue.symm⟩ with h | h | h | h
  all_goals
    change Int.fract argument = _ at h
    norm_num [cosPiExact, h] at hnone
    cases hnone

private theorem cosPi_complement (argument : ℚ) :
    Real.cos (((1 / 2 - argument : ℚ) : ℝ) * Real.pi) =
      Real.sin ((argument : ℝ) * Real.pi) := by
  push_cast
  rw [show ((1 / 2 : ℝ) - argument) * Real.pi =
    Real.pi / 2 - (argument : ℝ) * Real.pi by ring, Real.cos_pi_div_two_sub]

/-- Every reported rational sine value is exact. -/
theorem sinPiExact_eq_real (argument value : ℚ) (hvalue : sinPiExact argument = some value) :
    Real.sin ((argument : ℝ) * Real.pi) = (value : ℝ) := by
  rw [← cosPi_complement]
  exact cosPiExact_eq_real _ value hvalue

/-- An unclassified sine value is irrational. -/
theorem irrational_sinPi_of_exact_none (argument : ℚ)
    (hnone : sinPiExact argument = none) :
    Irrational (Real.sin ((argument : ℝ) * Real.pi)) := by
  rw [← cosPi_complement]
  exact irrational_cosPi_of_exact_none _ hnone

end FloatLib.Numerics.TrigonometricComparison
