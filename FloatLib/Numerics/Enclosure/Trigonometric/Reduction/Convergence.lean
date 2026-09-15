/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.Reduction.Proof
public import FloatLib.Numerics.Enclosure.Trigonometric.Convergence
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Convergence with rational period reduction

The integer quotient need not stabilize. Its magnitude has an input-dependent bound, so the
vanishing quarter-period uncertainty still makes the reduction error tend to zero. Meanwhile
the Taylor radius is uniformly bounded by `4^(n+1)/(n+1)!`. These estimates prove endpoint
convergence for the executable reduced kernels at every rational input.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter
open scoped Topology

/-- Clamping the approximate quarter period preserves its limit. -/
theorem tendsto_trigQuarter :
    Tendsto (fun n : Nat => (trigQuarter n : ℝ)) atTop (𝓝 (Real.pi / 4)) := by
  have hlo : (1 / 2 : ℝ) ≤ Real.pi / 4 := by linarith [Real.pi_gt_three]
  have hhi : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]
  have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).max
    ((tendsto_const_nhds (x := (1 : ℝ))).min tendsto_piQuarter_lo)
  rw [min_eq_right hhi, max_eq_right hlo] at h
  simpa only [trigQuarter, Rat.cast_max, Rat.cast_min, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat] using h

/-- The accumulated period error tends to zero without requiring quotient stability. -/
theorem tendsto_trigReductionError (x : ℚ) :
    Tendsto (fun n : Nat => (trigReductionError x n : ℝ)) atTop (𝓝 0) := by
  have herr : Tendsto (fun n : Nat =>
      ((piQuarter n).hi : ℝ) - (trigQuarter n : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_piQuarter_hi.sub tendsto_trigQuarter
  have hbound := herr.const_mul (8 * (|(x : ℝ)| + 1))
  apply squeeze_zero (fun n => by exact_mod_cast trigReductionError_nonneg x n)
    (fun n => ?_)
    (by simpa using hbound)
  exact_mod_cast trigReductionError_le x n

/-- The bounded reduced arguments give a uniform factorial majorant for the Taylor error. -/
theorem trigRadius_reduced_le (x : ℚ) (degree : Nat) :
    trigRadius (trigReducedArgument x degree) degree ≤ trigRadius 4 degree := by
  unfold trigRadius
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (abs_nonneg _)
  simpa using abs_trigReducedArgument_le x degree

/-- The reduced Taylor error tends to zero even though its rational argument varies. -/
theorem tendsto_trigRadius_reduced (x : ℚ) :
    Tendsto (fun n : Nat => (trigRadius (trigReducedArgument x n) n : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => ?_) (fun n => ?_) (tendsto_trigRadius 4)
  · have h : (0 : ℚ) ≤ trigRadius (trigReducedArgument x n) n := by
      unfold trigRadius
      positivity
    exact_mod_cast h
  · exact_mod_cast trigRadius_reduced_le x n

/-- The complete radius of the reduced enclosure tends to zero. -/
theorem tendsto_trigReducedRadius (x : ℚ) :
    Tendsto (fun n : Nat => (trigReducedRadius x n : ℝ)) atTop (𝓝 0) := by
  simpa [trigReducedRadius] using
    (tendsto_trigRadius_reduced x).add (tendsto_trigReductionError x)

/-- Reduced sine polynomials converge to the sine of the original argument. -/
theorem tendsto_sinReducedTaylor (x : ℚ) :
    Tendsto (fun n : Nat => (sinTaylor (trigReducedArgument x n) n : ℝ)) atTop
      (𝓝 (Real.sin (x : ℝ))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (tendsto_trigReducedRadius x)
  simpa only [Real.dist_eq, abs_sub_comm] using abs_sin_sub_reducedTaylor_le x n

/-- Reduced cosine polynomials converge to the cosine of the original argument. -/
theorem tendsto_cosReducedTaylor (x : ℚ) :
    Tendsto (fun n : Nat => (cosTaylor (trigReducedArgument x n) n : ℝ)) atTop
      (𝓝 (Real.cos (x : ℝ))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (tendsto_trigReducedRadius x)
  simpa only [Real.dist_eq, abs_sub_comm] using abs_cos_sub_reducedTaylor_le x n

/-- The reduced sine lower endpoints converge at every rational input. -/
theorem tendsto_sinReduced_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((sinReduced x n).lo : ℝ)) atTop
      (𝓝 (Real.sin (x : ℝ))) := by
  apply tendsto_restrictUnit_lo (intervals := fun n => RationalInterval.around
    (sinTaylor (trigReducedArgument x n) n) (trigReducedRadius x n))
  · simpa [RationalInterval.around] using
      (tendsto_sinReducedTaylor x).sub (tendsto_trigReducedRadius x)
  · exact (abs_le.mp (Real.abs_sin_le_one _)).1

/-- The reduced sine upper endpoints converge at every rational input. -/
theorem tendsto_sinReduced_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((sinReduced x n).hi : ℝ)) atTop
      (𝓝 (Real.sin (x : ℝ))) := by
  apply tendsto_restrictUnit_hi (intervals := fun n => RationalInterval.around
    (sinTaylor (trigReducedArgument x n) n) (trigReducedRadius x n))
  · simpa [RationalInterval.around] using
      (tendsto_sinReducedTaylor x).add (tendsto_trigReducedRadius x)
  · exact (abs_le.mp (Real.abs_sin_le_one _)).2

/-- The reduced cosine lower endpoints converge at every rational input. -/
theorem tendsto_cosReduced_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((cosReduced x n).lo : ℝ)) atTop
      (𝓝 (Real.cos (x : ℝ))) := by
  apply tendsto_restrictUnit_lo (intervals := fun n => RationalInterval.around
    (cosTaylor (trigReducedArgument x n) n) (trigReducedRadius x n))
  · simpa [RationalInterval.around] using
      (tendsto_cosReducedTaylor x).sub (tendsto_trigReducedRadius x)
  · exact (abs_le.mp (Real.abs_cos_le_one _)).1

/-- The reduced cosine upper endpoints converge at every rational input. -/
theorem tendsto_cosReduced_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((cosReduced x n).hi : ℝ)) atTop
      (𝓝 (Real.cos (x : ℝ))) := by
  apply tendsto_restrictUnit_hi (intervals := fun n => RationalInterval.around
    (cosTaylor (trigReducedArgument x n) n) (trigReducedRadius x n))
  · simpa [RationalInterval.around] using
      (tendsto_cosReducedTaylor x).add (tendsto_trigReducedRadius x)
  · exact (abs_le.mp (Real.abs_cos_le_one _)).2

end FloatLib.Numerics.Enclosure
