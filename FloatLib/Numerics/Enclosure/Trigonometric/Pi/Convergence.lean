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

Exact rational angle reduction doesn't depend on the refinement degree. Its bounded remainder
multiplies a vanishing uncertainty in pi, while a uniform factorial majorant controls the Taylor
error. So both endpoints converge at every rational input, including the special angles where a
later comparison has to use the exact-value classifier.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter
open scoped Topology

/-- The argument uncertainty vanishes at every rational pi-scaled input. -/
theorem tendsto_piArgumentError (x : ℚ) :
    Tendsto (fun n : Nat => (piArgumentError x n : ℝ)) atTop (𝓝 0) := by
  simpa [piArgumentError] using
    tendsto_piQuarter_hi_sub_trigQuarter.const_mul (4 * |((piReduced x : ℚ) : ℝ)|)

/-- The bounded reduced arguments give a uniform factorial majorant for the Taylor error. -/
theorem trigRadius_piArgument_le (x : ℚ) (degree : Nat) :
    trigRadius (piArgument x degree) degree ≤ trigRadius 4 degree :=
  trigRadius_le_trigRadius_four (abs_piArgument_le x degree) degree

/-- The reduced Taylor error tends to zero even though its rational argument varies. -/
theorem tendsto_trigRadius_piArgument (x : ℚ) :
    Tendsto (fun n : Nat => (trigRadius (piArgument x n) n : ℝ))
      atTop (𝓝 0) :=
  tendsto_trigRadius_of_abs_le_four (abs_piArgument_le x)

/-- The complete radius of the reduced enclosure tends to zero. -/
theorem tendsto_piRadius (x : ℚ) :
    Tendsto (fun n : Nat => (piRadius x n : ℝ)) atTop (𝓝 0) := by
  simpa [piRadius] using
    (tendsto_trigRadius_piArgument x).add (tendsto_piArgumentError x)

/-- Reduced sine polynomials converge to the sine of the original argument. -/
theorem tendsto_sinPiTaylor (x : ℚ) :
    Tendsto (fun n : Nat => (sinTaylor (piArgument x n) n : ℝ)) atTop
      (𝓝 (Real.sin ((x : ℝ) * Real.pi))) :=
  RationalInterval.tendsto_of_abs_sub_le (abs_sinPi_sub_taylor_le x) (tendsto_piRadius x)

/-- Reduced cosine polynomials converge to the cosine of the original argument. -/
theorem tendsto_cosPiTaylor (x : ℚ) :
    Tendsto (fun n : Nat => (cosTaylor (piArgument x n) n : ℝ)) atTop
      (𝓝 (Real.cos ((x : ℝ) * Real.pi))) :=
  RationalInterval.tendsto_of_abs_sub_le (abs_cosPi_sub_taylor_le x) (tendsto_piRadius x)

/-- The reduced sine lower endpoints converge at every rational input. -/
theorem tendsto_sinPi_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((sinPi x n).lo : ℝ)) atTop
      (𝓝 (Real.sin ((x : ℝ) * Real.pi))) :=
  tendsto_restrictUnit_around_lo (tendsto_sinPiTaylor x) (tendsto_piRadius x)
    (Real.abs_sin_le_one _)

/-- The reduced sine upper endpoints converge at every rational input. -/
theorem tendsto_sinPi_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((sinPi x n).hi : ℝ)) atTop
      (𝓝 (Real.sin ((x : ℝ) * Real.pi))) :=
  tendsto_restrictUnit_around_hi (tendsto_sinPiTaylor x) (tendsto_piRadius x)
    (Real.abs_sin_le_one _)

/-- The reduced cosine lower endpoints converge at every rational input. -/
theorem tendsto_cosPi_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((cosPi x n).lo : ℝ)) atTop
      (𝓝 (Real.cos ((x : ℝ) * Real.pi))) :=
  tendsto_restrictUnit_around_lo (tendsto_cosPiTaylor x) (tendsto_piRadius x)
    (Real.abs_cos_le_one _)

/-- The reduced cosine upper endpoints converge at every rational input. -/
theorem tendsto_cosPi_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((cosPi x n).hi : ℝ)) atTop
      (𝓝 (Real.cos ((x : ℝ) * Real.pi))) :=
  tendsto_restrictUnit_around_hi (tendsto_cosPiTaylor x) (tendsto_piRadius x)
    (Real.abs_cos_le_one _)

end FloatLib.Numerics.Enclosure
