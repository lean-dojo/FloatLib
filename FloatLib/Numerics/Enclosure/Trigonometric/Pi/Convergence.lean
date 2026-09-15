/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.Pi.Proof
public import FloatLib.Numerics.Enclosure.Trigonometric.Reduction.Convergence

/-!
# Convergence of pi-scaled trigonometric enclosures

The exact rational angle reduction is independent of the refinement degree. Its bounded
remainder multiplies a vanishing uncertainty in pi, while a uniform factorial majorant
controls the Taylor error. Thus both endpoints converge at every rational input, including
special angles where a later comparison must use the exact-value classifier.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter
open scoped Topology

/-- The argument uncertainty vanishes at every rational pi-scaled input. -/
theorem tendsto_piArgumentError (x : ℚ) :
    Tendsto (fun n : Nat => (piArgumentError x n : ℝ)) atTop (𝓝 0) := by
  have herr : Tendsto (fun n : Nat =>
      ((piQuarter n).hi : ℝ) - (trigQuarter n : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_piQuarter_hi.sub tendsto_trigQuarter
  simpa [piArgumentError] using herr.const_mul (4 * |((piReduced x : ℚ) : ℝ)|)

/-- The bounded reduced arguments give a uniform factorial majorant for the Taylor error. -/
theorem trigRadius_piArgument_le (x : ℚ) (degree : Nat) :
    trigRadius (piArgument x degree) degree ≤ trigRadius 4 degree := by
  unfold trigRadius
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (abs_nonneg _)
  simpa using abs_piArgument_le x degree

/-- The reduced Taylor error tends to zero even though its rational argument varies. -/
theorem tendsto_trigRadius_piArgument (x : ℚ) :
    Tendsto (fun n : Nat => (trigRadius (piArgument x n) n : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => ?_) (fun n => ?_) (tendsto_trigRadius 4)
  · have h : (0 : ℚ) ≤ trigRadius (piArgument x n) n := by
      unfold trigRadius
      positivity
    exact_mod_cast h
  · exact_mod_cast trigRadius_piArgument_le x n

/-- The complete radius of the reduced enclosure tends to zero. -/
theorem tendsto_piRadius (x : ℚ) :
    Tendsto (fun n : Nat => (piRadius x n : ℝ)) atTop (𝓝 0) := by
  simpa [piRadius] using
    (tendsto_trigRadius_piArgument x).add (tendsto_piArgumentError x)

/-- Reduced sine polynomials converge to the sine of the original argument. -/
theorem tendsto_sinPiTaylor (x : ℚ) :
    Tendsto (fun n : Nat => (sinTaylor (piArgument x n) n : ℝ)) atTop
      (𝓝 (Real.sin ((x : ℝ) * Real.pi))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (tendsto_piRadius x)
  simpa only [Real.dist_eq, abs_sub_comm] using abs_sinPi_sub_taylor_le x n

/-- Reduced cosine polynomials converge to the cosine of the original argument. -/
theorem tendsto_cosPiTaylor (x : ℚ) :
    Tendsto (fun n : Nat => (cosTaylor (piArgument x n) n : ℝ)) atTop
      (𝓝 (Real.cos ((x : ℝ) * Real.pi))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (tendsto_piRadius x)
  simpa only [Real.dist_eq, abs_sub_comm] using abs_cosPi_sub_taylor_le x n

/-- The reduced sine lower endpoints converge at every rational input. -/
theorem tendsto_sinPi_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((sinPi x n).lo : ℝ)) atTop
      (𝓝 (Real.sin ((x : ℝ) * Real.pi))) := by
  apply tendsto_restrictUnit_lo (intervals := fun n => RationalInterval.around
    (sinTaylor (piArgument x n) n) (piRadius x n))
  · simpa [RationalInterval.around] using
      (tendsto_sinPiTaylor x).sub (tendsto_piRadius x)
  · exact (abs_le.mp (Real.abs_sin_le_one _)).1

/-- The reduced sine upper endpoints converge at every rational input. -/
theorem tendsto_sinPi_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((sinPi x n).hi : ℝ)) atTop
      (𝓝 (Real.sin ((x : ℝ) * Real.pi))) := by
  apply tendsto_restrictUnit_hi (intervals := fun n => RationalInterval.around
    (sinTaylor (piArgument x n) n) (piRadius x n))
  · simpa [RationalInterval.around] using
      (tendsto_sinPiTaylor x).add (tendsto_piRadius x)
  · exact (abs_le.mp (Real.abs_sin_le_one _)).2

/-- The reduced cosine lower endpoints converge at every rational input. -/
theorem tendsto_cosPi_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((cosPi x n).lo : ℝ)) atTop
      (𝓝 (Real.cos ((x : ℝ) * Real.pi))) := by
  apply tendsto_restrictUnit_lo (intervals := fun n => RationalInterval.around
    (cosTaylor (piArgument x n) n) (piRadius x n))
  · simpa [RationalInterval.around] using
      (tendsto_cosPiTaylor x).sub (tendsto_piRadius x)
  · exact (abs_le.mp (Real.abs_cos_le_one _)).1

/-- The reduced cosine upper endpoints converge at every rational input. -/
theorem tendsto_cosPi_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((cosPi x n).hi : ℝ)) atTop
      (𝓝 (Real.cos ((x : ℝ) * Real.pi))) := by
  apply tendsto_restrictUnit_hi (intervals := fun n => RationalInterval.around
    (cosTaylor (piArgument x n) n) (piRadius x n))
  · simpa [RationalInterval.around] using
      (tendsto_cosPiTaylor x).add (tendsto_piRadius x)
  · exact (abs_le.mp (Real.abs_cos_le_one _)).2

end FloatLib.Numerics.Enclosure
