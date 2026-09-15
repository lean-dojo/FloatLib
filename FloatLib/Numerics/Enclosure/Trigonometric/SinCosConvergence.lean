/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.SinCosProof
public import FloatLib.Numerics.Enclosure.Rational.Convergence
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Convergence of global rational sine and cosine bounds

For every fixed real argument, the exponential-series terms `|x|^n / n!` tend to zero.
The global Taylor error bound therefore squeezes the rational sine and cosine polynomials
toward their exact values. Intersecting with `[-1, 1]` preserves endpoint convergence.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter
open scoped Topology

/-- The global trigonometric Lagrange radius tends to zero at every rational input. -/
theorem tendsto_trigRadius (x : ℚ) :
    Tendsto (fun n : Nat => (trigRadius x n : ℝ)) atTop (𝓝 0) := by
  simpa [trigRadius, Function.comp_def] using
    (Real.summable_pow_div_factorial |(x : ℝ)|).tendsto_atTop_zero.comp
      (tendsto_add_atTop_nat 1)

/-- The executable sine Taylor polynomials converge at every rational input. -/
theorem tendsto_sinTaylor (x : ℚ) :
    Tendsto (fun n : Nat => (sinTaylor x n : ℝ)) atTop (𝓝 (Real.sin (x : ℝ))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (tendsto_trigRadius x)
  simpa only [Real.dist_eq, abs_sub_comm] using abs_sin_sub_sinTaylor_le x n

/-- The executable cosine Taylor polynomials converge at every rational input. -/
theorem tendsto_cosTaylor (x : ℚ) :
    Tendsto (fun n : Nat => (cosTaylor x n : ℝ)) atTop (𝓝 (Real.cos (x : ℝ))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (tendsto_trigRadius x)
  simpa only [Real.dist_eq, abs_sub_comm] using abs_cos_sub_cosTaylor_le x n

/-- Clamping lower endpoints at `-1` preserves any limit at least `-1`. -/
theorem tendsto_restrictUnit_lo {α : Type*} {l : Filter α}
    {intervals : α → RationalInterval} {x : ℝ}
    (hlo : Tendsto (fun a => ((intervals a).lo : ℝ)) l (𝓝 x)) (hx : -1 ≤ x) :
    Tendsto (fun a => ((restrictUnit (intervals a)).lo : ℝ)) l (𝓝 x) := by
  simpa [restrictUnit, max_eq_right hx] using
    (tendsto_const_nhds (x := (-1 : ℝ))).max hlo

/-- Clamping upper endpoints at `1` preserves any limit at most `1`. -/
theorem tendsto_restrictUnit_hi {α : Type*} {l : Filter α}
    {intervals : α → RationalInterval} {x : ℝ}
    (hhi : Tendsto (fun a => ((intervals a).hi : ℝ)) l (𝓝 x)) (hx : x ≤ 1) :
    Tendsto (fun a => ((restrictUnit (intervals a)).hi : ℝ)) l (𝓝 x) := by
  simpa [restrictUnit, min_eq_right hx] using
    (tendsto_const_nhds (x := (1 : ℝ))).min hhi

/-- The sine lower endpoints converge globally as the degree increases. -/
theorem tendsto_sin_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((sin x n).lo : ℝ)) atTop (𝓝 (Real.sin (x : ℝ))) := by
  apply tendsto_restrictUnit_lo (intervals := fun n =>
    RationalInterval.around (sinTaylor x n) (trigRadius x n))
  · simpa [RationalInterval.around] using (tendsto_sinTaylor x).sub (tendsto_trigRadius x)
  · exact (abs_le.mp (Real.abs_sin_le_one _)).1

/-- The sine upper endpoints converge globally as the degree increases. -/
theorem tendsto_sin_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((sin x n).hi : ℝ)) atTop (𝓝 (Real.sin (x : ℝ))) := by
  apply tendsto_restrictUnit_hi (intervals := fun n =>
    RationalInterval.around (sinTaylor x n) (trigRadius x n))
  · simpa [RationalInterval.around] using (tendsto_sinTaylor x).add (tendsto_trigRadius x)
  · exact (abs_le.mp (Real.abs_sin_le_one _)).2

/-- The cosine lower endpoints converge globally as the degree increases. -/
theorem tendsto_cos_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((cos x n).lo : ℝ)) atTop (𝓝 (Real.cos (x : ℝ))) := by
  apply tendsto_restrictUnit_lo (intervals := fun n =>
    RationalInterval.around (cosTaylor x n) (trigRadius x n))
  · simpa [RationalInterval.around] using (tendsto_cosTaylor x).sub (tendsto_trigRadius x)
  · exact (abs_le.mp (Real.abs_cos_le_one _)).1

/-- The cosine upper endpoints converge globally as the degree increases. -/
theorem tendsto_cos_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((cos x n).hi : ℝ)) atTop (𝓝 (Real.cos (x : ℝ))) := by
  apply tendsto_restrictUnit_hi (intervals := fun n =>
    RationalInterval.around (cosTaylor x n) (trigRadius x n))
  · simpa [RationalInterval.around] using (tendsto_cosTaylor x).add (tendsto_trigRadius x)
  · exact (abs_le.mp (Real.abs_cos_le_one _)).2

end FloatLib.Numerics.Enclosure
