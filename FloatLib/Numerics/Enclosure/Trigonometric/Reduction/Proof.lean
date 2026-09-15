/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.Reduction.Runtime
public import FloatLib.Numerics.Enclosure.Trigonometric.Proof
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Correctness of rational trigonometric period reduction

The approximate remainder is bounded independently of the input. Its distance from a true
period translate is bounded by the explicit rational reduction error. Periodicity and the
Lipschitz estimates then transfer the Taylor enclosure to the original argument.
-/

public section

namespace FloatLib.Numerics.Enclosure

/-- The rational quarter period is at least one half. -/
theorem half_le_trigQuarter (degree : Nat) : 1 / 2 ≤ trigQuarter degree :=
  le_max_left _ _

/-- The rational quarter period is at most one. -/
theorem trigQuarter_le_one (degree : Nat) : trigQuarter degree ≤ 1 := by
  exact max_le (by norm_num) (min_le_left _ _)

/-- The rational quarter period lies below the true quarter period. -/
theorem trigQuarter_le_pi_quarter (degree : Nat) :
    (trigQuarter degree : ℝ) ≤ Real.pi / 4 := by
  have hlo := (contains_piQuarter degree).1
  have hpi := Real.pi_gt_three
  simp only [trigQuarter, Rat.cast_max, Rat.cast_min, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_one]
  exact max_le (by linarith) ((min_le_right _ _).trans hlo)

/-- The upper quarter-period endpoint lies above the clamped lower approximation. -/
theorem trigQuarter_le_hi (degree : Nat) : trigQuarter degree ≤ (piQuarter degree).hi := by
  exact_mod_cast (trigQuarter_le_pi_quarter degree).trans (contains_piQuarter degree).2

/-- Rounding to the nearest integer leaves at most half a period. -/
theorem abs_trig_turns_residual_le (x : ℚ) (degree : Nat) :
    |x / (8 * trigQuarter degree) - (trigTurns x degree : ℚ)| ≤ 1 / 2 := by
  have hlo := Int.floor_le (x / (8 * trigQuarter degree) + 1 / 2)
  have hhi := Int.lt_floor_add_one (x / (8 * trigQuarter degree) + 1 / 2)
  rw [abs_le]
  dsimp [trigTurns]
  constructor <;> linarith

/-- Every reduced rational argument lies in `[-4, 4]`, regardless of input magnitude. -/
theorem abs_trigReducedArgument_le (x : ℚ) (degree : Nat) :
    |trigReducedArgument x degree| ≤ 4 := by
  have hc := half_le_trigQuarter degree
  have hcone := trigQuarter_le_one degree
  have hpos : 0 < 8 * trigQuarter degree := by linarith
  have hid : trigReducedArgument x degree =
      (x / (8 * trigQuarter degree) - (trigTurns x degree : ℚ)) *
        (8 * trigQuarter degree) := by
    dsimp [trigReducedArgument]
    field_simp
  rw [hid, abs_mul, abs_of_pos hpos]
  calc
    _ ≤ (1 / 2) * (8 * trigQuarter degree) :=
      mul_le_mul_of_nonneg_right (abs_trig_turns_residual_le x degree) hpos.le
    _ ≤ 4 := by linarith

/-- The number of removed periods has a uniform bound as the degree varies. -/
theorem abs_trigTurns_le (x : ℚ) (degree : Nat) :
    |(trigTurns x degree : ℚ)| ≤ |x| + 1 := by
  have hc := half_le_trigQuarter degree
  have hp : 0 < 8 * trigQuarter degree := by linarith
  have hdiv : |x / (8 * trigQuarter degree)| ≤ |x| := by
    rw [abs_div, abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr (by nlinarith [abs_nonneg x])
  calc
    |(trigTurns x degree : ℚ)| =
        |x / (8 * trigQuarter degree) -
          (x / (8 * trigQuarter degree) - (trigTurns x degree : ℚ))| := by ring_nf
    _ ≤ |x / (8 * trigQuarter degree)| +
        |x / (8 * trigQuarter degree) - (trigTurns x degree : ℚ)| := abs_sub _ _
    _ ≤ |x| + 1 := by linarith [abs_trig_turns_residual_le x degree]

/-- The accumulated rational period error is nonnegative. -/
theorem trigReductionError_nonneg (x : ℚ) (degree : Nat) :
    0 ≤ trigReductionError x degree := by
  exact mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))
    (sub_nonneg.mpr (trigQuarter_le_hi degree))

/-- An input-dependent constant times the quarter-period width bounds the reduction error. -/
theorem trigReductionError_le (x : ℚ) (degree : Nat) :
    trigReductionError x degree ≤
      8 * (|x| + 1) * ((piQuarter degree).hi - trigQuarter degree) := by
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (abs_trigTurns_le x degree) (by norm_num))
    (sub_nonneg.mpr (trigQuarter_le_hi degree))

/-- The approximate remainder is close to an exact integer translate by `2π`. -/
theorem abs_trigReducedArgument_sub_period_le (x : ℚ) (degree : Nat) :
    |(trigReducedArgument x degree : ℝ) -
      ((x : ℝ) - (trigTurns x degree : ℝ) * (2 * Real.pi))| ≤
        (trigReductionError x degree : ℝ) := by
  have hlo := trigQuarter_le_pi_quarter degree
  have hhi := (contains_piQuarter degree).2
  have hid : (trigReducedArgument x degree : ℝ) -
      ((x : ℝ) - (trigTurns x degree : ℝ) * (2 * Real.pi)) =
      8 * (trigTurns x degree : ℝ) * (Real.pi / 4 - (trigQuarter degree : ℝ)) := by
    push_cast [trigReducedArgument]
    ring
  rw [hid, abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hlo)]
  push_cast [trigReductionError]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hhi _)
    (mul_nonneg (by norm_num) (abs_nonneg _))

/-- The sine error introduced by rational period reduction is explicitly bounded. -/
theorem abs_sin_sub_reduced_le (x : ℚ) (degree : Nat) :
    |Real.sin (x : ℝ) - Real.sin (trigReducedArgument x degree : ℝ)| ≤
      (trigReductionError x degree : ℝ) := by
  have h := Real.abs_sin_sub_sin_le (trigReducedArgument x degree : ℝ)
    ((x : ℝ) - (trigTurns x degree : ℝ) * (2 * Real.pi))
  rw [Real.sin_sub_int_mul_two_pi, abs_sub_comm] at h
  exact h.trans (abs_trigReducedArgument_sub_period_le x degree)

/-- The cosine error introduced by rational period reduction is explicitly bounded. -/
theorem abs_cos_sub_reduced_le (x : ℚ) (degree : Nat) :
    |Real.cos (x : ℝ) - Real.cos (trigReducedArgument x degree : ℝ)| ≤
      (trigReductionError x degree : ℝ) := by
  have h := Real.abs_cos_sub_cos_le (trigReducedArgument x degree : ℝ)
    ((x : ℝ) - (trigTurns x degree : ℝ) * (2 * Real.pi))
  rw [Real.cos_sub_int_mul_two_pi, abs_sub_comm] at h
  exact h.trans (abs_trigReducedArgument_sub_period_le x degree)

/-- Combined period and Taylor errors bound the sine polynomial at the reduced argument. -/
theorem abs_sin_sub_reducedTaylor_le (x : ℚ) (degree : Nat) :
    |Real.sin (x : ℝ) - (sinTaylor (trigReducedArgument x degree) degree : ℝ)| ≤
      (trigReducedRadius x degree : ℝ) := by
  calc
    _ ≤ |Real.sin (x : ℝ) - Real.sin (trigReducedArgument x degree : ℝ)| +
        |Real.sin (trigReducedArgument x degree : ℝ) -
          (sinTaylor (trigReducedArgument x degree) degree : ℝ)| := abs_sub_le _ _ _
    _ ≤ (trigReducedRadius x degree : ℝ) := by
      have h₁ := abs_sin_sub_reduced_le x degree
      have h₂ := abs_sin_sub_sinTaylor_le (trigReducedArgument x degree) degree
      push_cast [trigReducedRadius]
      linarith

/-- Combined period and Taylor errors bound the cosine polynomial at the reduced argument. -/
theorem abs_cos_sub_reducedTaylor_le (x : ℚ) (degree : Nat) :
    |Real.cos (x : ℝ) - (cosTaylor (trigReducedArgument x degree) degree : ℝ)| ≤
      (trigReducedRadius x degree : ℝ) := by
  calc
    _ ≤ |Real.cos (x : ℝ) - Real.cos (trigReducedArgument x degree : ℝ)| +
        |Real.cos (trigReducedArgument x degree : ℝ) -
          (cosTaylor (trigReducedArgument x degree) degree : ℝ)| := abs_sub_le _ _ _
    _ ≤ (trigReducedRadius x degree : ℝ) := by
      have h₁ := abs_cos_sub_reduced_le x degree
      have h₂ := abs_cos_sub_cosTaylor_le (trigReducedArgument x degree) degree
      push_cast [trigReducedRadius]
      linarith

/-- The reduced sine enclosure contains the exact sine at every rational input and degree. -/
theorem contains_sinReduced (x : ℚ) (degree : Nat) :
    (sinReduced x degree).Contains (Real.sin (x : ℝ)) :=
  contains_restrictUnit (RationalInterval.contains_around
    (abs_sin_sub_reducedTaylor_le x degree)) (Real.abs_sin_le_one _)

/-- The reduced cosine enclosure contains the exact cosine at every rational input and degree. -/
theorem contains_cosReduced (x : ℚ) (degree : Nat) :
    (cosReduced x degree).Contains (Real.cos (x : ℝ)) :=
  contains_restrictUnit (RationalInterval.contains_around
    (abs_cos_sub_reducedTaylor_le x degree)) (Real.abs_cos_le_one _)

end FloatLib.Numerics.Enclosure
