/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.SinCosProof
public import FloatLib.Numerics.Enclosure.Rational.AffineConvergence
public import FloatLib.Numerics.Enclosure.Rational.Convergence

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
    Tendsto (fun n : Nat => (sinTaylor x n : ℝ)) atTop (𝓝 (Real.sin (x : ℝ))) :=
  RationalInterval.tendsto_of_abs_sub_le (abs_sin_sub_sinTaylor_le x) (tendsto_trigRadius x)

/-- The executable cosine Taylor polynomials converge at every rational input. -/
theorem tendsto_cosTaylor (x : ℚ) :
    Tendsto (fun n : Nat => (cosTaylor x n : ℝ)) atTop (𝓝 (Real.cos (x : ℝ))) :=
  RationalInterval.tendsto_of_abs_sub_le (abs_cos_sub_cosTaylor_le x) (tendsto_trigRadius x)

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

/--
Clamping a centred interval to `[-1, 1]` keeps the lower endpoints converging when the centres
converge to a value of absolute value at most one and the radii vanish.
-/
theorem tendsto_restrictUnit_around_lo {α : Type*} {l : Filter α} {center radius : α → ℚ}
    {x : ℝ} (hcenter : Tendsto (fun a => (center a : ℝ)) l (𝓝 x))
    (hradius : Tendsto (fun a => (radius a : ℝ)) l (𝓝 0)) (hx : |x| ≤ 1) :
    Tendsto (fun a =>
      ((restrictUnit (RationalInterval.around (center a) (radius a))).lo : ℝ)) l (𝓝 x) :=
  tendsto_restrictUnit_lo (RationalInterval.tendsto_around_lo hcenter hradius) (abs_le.mp hx).1

/--
Clamping a centred interval to `[-1, 1]` keeps the upper endpoints converging when the centres
converge to a value of absolute value at most one and the radii vanish.
-/
theorem tendsto_restrictUnit_around_hi {α : Type*} {l : Filter α} {center radius : α → ℚ}
    {x : ℝ} (hcenter : Tendsto (fun a => (center a : ℝ)) l (𝓝 x))
    (hradius : Tendsto (fun a => (radius a : ℝ)) l (𝓝 0)) (hx : |x| ≤ 1) :
    Tendsto (fun a =>
      ((restrictUnit (RationalInterval.around (center a) (radius a))).hi : ℝ)) l (𝓝 x) :=
  tendsto_restrictUnit_hi (RationalInterval.tendsto_around_hi hcenter hradius) (abs_le.mp hx).2

/-- An argument bounded by four in absolute value has a Taylor radius below that at four. -/
theorem trigRadius_le_trigRadius_four {argument : ℚ} (hargument : |argument| ≤ 4)
    (degree : Nat) :
    trigRadius argument degree ≤ trigRadius 4 degree := by
  unfold trigRadius
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (abs_nonneg _)
  simpa using hargument

/-- Taylor radii at arguments bounded by four tend to zero, even when the argument varies. -/
theorem tendsto_trigRadius_of_abs_le_four {argument : Nat → ℚ}
    (hargument : ∀ n, |argument n| ≤ 4) :
    Tendsto (fun n : Nat => (trigRadius (argument n) n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => ?_) (fun n => ?_) (tendsto_trigRadius 4)
  · have h : (0 : ℚ) ≤ trigRadius (argument n) n := by
      unfold trigRadius
      positivity
    exact_mod_cast h
  · exact_mod_cast trigRadius_le_trigRadius_four (hargument n) n

/-- The sine lower endpoints converge globally as the degree increases. -/
theorem tendsto_sin_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((sin x n).lo : ℝ)) atTop (𝓝 (Real.sin (x : ℝ))) :=
  tendsto_restrictUnit_around_lo (tendsto_sinTaylor x) (tendsto_trigRadius x)
    (Real.abs_sin_le_one _)

/-- The sine upper endpoints converge globally as the degree increases. -/
theorem tendsto_sin_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((sin x n).hi : ℝ)) atTop (𝓝 (Real.sin (x : ℝ))) :=
  tendsto_restrictUnit_around_hi (tendsto_sinTaylor x) (tendsto_trigRadius x)
    (Real.abs_sin_le_one _)

/-- The cosine lower endpoints converge globally as the degree increases. -/
theorem tendsto_cos_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((cos x n).lo : ℝ)) atTop (𝓝 (Real.cos (x : ℝ))) :=
  tendsto_restrictUnit_around_lo (tendsto_cosTaylor x) (tendsto_trigRadius x)
    (Real.abs_cos_le_one _)

/-- The cosine upper endpoints converge globally as the degree increases. -/
theorem tendsto_cos_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((cos x n).hi : ℝ)) atTop (𝓝 (Real.cos (x : ℝ))) :=
  tendsto_restrictUnit_around_hi (tendsto_cosTaylor x) (tendsto_trigRadius x)
    (Real.abs_cos_le_one _)

end FloatLib.Numerics.Enclosure
