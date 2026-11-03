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

/-- The gap between the upper pi-quarter bound and the clamped quarter period vanishes. -/
theorem tendsto_piQuarter_hi_sub_trigQuarter :
    Tendsto (fun n : Nat => ((piQuarter n).hi : ℝ) - (trigQuarter n : ℝ)) atTop (𝓝 0) := by
  simpa using tendsto_piQuarter_hi.sub tendsto_trigQuarter

/-- The accumulated period error tends to zero without requiring quotient stability. -/
theorem tendsto_trigReductionError (x : ℚ) :
    Tendsto (fun n : Nat => (trigReductionError x n : ℝ)) atTop (𝓝 0) := by
  have hbound := tendsto_piQuarter_hi_sub_trigQuarter.const_mul (8 * (|(x : ℝ)| + 1))
  apply squeeze_zero (fun n => by exact_mod_cast trigReductionError_nonneg x n)
    (fun n => ?_)
    (by simpa using hbound)
  exact_mod_cast trigReductionError_le x n

/-- The bounded reduced arguments give a uniform factorial majorant for the Taylor error. -/
theorem trigRadius_reduced_le (x : ℚ) (degree : Nat) :
    trigRadius (trigReducedArgument x degree) degree ≤ trigRadius 4 degree :=
  trigRadius_le_trigRadius_four (abs_trigReducedArgument_le x degree) degree

/-- The reduced Taylor error tends to zero even though its rational argument varies. -/
theorem tendsto_trigRadius_reduced (x : ℚ) :
    Tendsto (fun n : Nat => (trigRadius (trigReducedArgument x n) n : ℝ))
      atTop (𝓝 0) :=
  tendsto_trigRadius_of_abs_le_four (abs_trigReducedArgument_le x)

/-- The complete radius of the reduced enclosure tends to zero. -/
theorem tendsto_trigReducedRadius (x : ℚ) :
    Tendsto (fun n : Nat => (trigReducedRadius x n : ℝ)) atTop (𝓝 0) := by
  simpa [trigReducedRadius] using
    (tendsto_trigRadius_reduced x).add (tendsto_trigReductionError x)

/-- Reduced sine polynomials converge to the sine of the original argument. -/
theorem tendsto_sinReducedTaylor (x : ℚ) :
    Tendsto (fun n : Nat => (sinTaylor (trigReducedArgument x n) n : ℝ)) atTop
      (𝓝 (Real.sin (x : ℝ))) :=
  RationalInterval.tendsto_of_abs_sub_le (abs_sin_sub_reducedTaylor_le x)
    (tendsto_trigReducedRadius x)

/-- Reduced cosine polynomials converge to the cosine of the original argument. -/
theorem tendsto_cosReducedTaylor (x : ℚ) :
    Tendsto (fun n : Nat => (cosTaylor (trigReducedArgument x n) n : ℝ)) atTop
      (𝓝 (Real.cos (x : ℝ))) :=
  RationalInterval.tendsto_of_abs_sub_le (abs_cos_sub_reducedTaylor_le x)
    (tendsto_trigReducedRadius x)

/-- The reduced sine lower endpoints converge at every rational input. -/
theorem tendsto_sinReduced_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((sinReduced x n).lo : ℝ)) atTop
      (𝓝 (Real.sin (x : ℝ))) :=
  tendsto_restrictUnit_around_lo (tendsto_sinReducedTaylor x) (tendsto_trigReducedRadius x)
    (Real.abs_sin_le_one _)

/-- The reduced sine upper endpoints converge at every rational input. -/
theorem tendsto_sinReduced_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((sinReduced x n).hi : ℝ)) atTop
      (𝓝 (Real.sin (x : ℝ))) :=
  tendsto_restrictUnit_around_hi (tendsto_sinReducedTaylor x) (tendsto_trigReducedRadius x)
    (Real.abs_sin_le_one _)

/-- The reduced cosine lower endpoints converge at every rational input. -/
theorem tendsto_cosReduced_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((cosReduced x n).lo : ℝ)) atTop
      (𝓝 (Real.cos (x : ℝ))) :=
  tendsto_restrictUnit_around_lo (tendsto_cosReducedTaylor x) (tendsto_trigReducedRadius x)
    (Real.abs_cos_le_one _)

/-- The reduced cosine upper endpoints converge at every rational input. -/
theorem tendsto_cosReduced_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((cosReduced x n).hi : ℝ)) atTop
      (𝓝 (Real.cos (x : ℝ))) :=
  tendsto_restrictUnit_around_hi (tendsto_cosReducedTaylor x) (tendsto_trigReducedRadius x)
    (Real.abs_cos_le_one _)

end FloatLib.Numerics.Enclosure
