/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.Runtime
public import FloatLib.Numerics.Enclosure.Rational.Proof
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Global rational sine and cosine bounds

The rational polynomials are identified with real Taylor polynomials at zero. Mathlib's
Lagrange remainder theorem applies at every real argument: every iterated derivative of sine
or cosine has absolute value at most one. Thus no domain restriction or unproved reduction
condition enters the containment theorem.
-/

public section

namespace FloatLib.Numerics.Enclosure

open scoped ContDiff

/-- Rational sine coefficients are the exact real derivatives at the origin. -/
theorem cast_sinCoefficient (n : Nat) :
    (sinCoefficient n : ℝ) = iteratedDeriv n Real.sin 0 := by
  have hdecomp := Nat.mod_add_div n 2
  by_cases h : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by omega
    rw [sinCoefficient, ite_eq_left h, hn, Real.iteratedDeriv_even_sin]
    simp
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [sinCoefficient, ite_eq_right h]
    conv_rhs => rw [hn, Real.iteratedDeriv_odd_sin]
    simp

/-- Rational cosine coefficients are the exact real derivatives at the origin. -/
theorem cast_cosCoefficient (n : Nat) :
    (cosCoefficient n : ℝ) = iteratedDeriv n Real.cos 0 := by
  have hdecomp := Nat.mod_add_div n 2
  by_cases h : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by omega
    rw [cosCoefficient, ite_eq_left h]
    conv_rhs => rw [hn, Real.iteratedDeriv_even_cos]
    simp
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [cosCoefficient, ite_eq_right h, hn, Real.iteratedDeriv_odd_cos]
    simp

private theorem taylor_eq_sum (f : ℝ → ℝ) (x : ℝ) (n : Nat)
    (hf : ContDiff ℝ ∞ f) (hx : 0 ≠ x) :
    taylorWithinEval f n (Set.uIcc 0 x) 0 x =
      ∑ i ∈ Finset.range (n + 1), iteratedDeriv i f 0 * x ^ i / (i.factorial : ℝ) := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx)
    (hf.of_le (show (i : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)).contDiffAt Set.left_mem_uIcc]
  simp only [sub_zero, smul_eq_mul]
  ring

private theorem abs_sub_taylor_le (f : ℝ → ℝ) (x : ℝ) (n : Nat)
    (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ i y, |iteratedDeriv i f y| ≤ 1) :
    |f x - ∑ i ∈ Finset.range (n + 1),
      iteratedDeriv i f 0 * x ^ i / (i.factorial : ℝ)| ≤
      |x| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  by_cases hx : 0 = x
  · subst x
    simp [zero_pow_eq, ite_div, Finset.sum_ite_eq', Finset.mem_range]
  · obtain ⟨y, _, hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n) hx
      (hf.of_le (by exact_mod_cast le_top)).contDiffOn
    rw [taylor_eq_sum f x n hf hx] at hy
    rw [hy, abs_div, abs_mul, abs_pow, sub_zero,
      abs_of_pos (by positivity : (0 : ℝ) < (n + 1).factorial)]
    exact div_le_div_of_nonneg_right
      (by
        simpa using mul_le_mul_of_nonneg_right (hbound (n + 1) y)
          (pow_nonneg (abs_nonneg x) (n + 1))) (by positivity)

/-- The executable sine polynomial has a valid remainder bound for every rational input. -/
theorem abs_sin_sub_sinTaylor_le (x : ℚ) (degree : Nat) :
    |Real.sin (x : ℝ) - (sinTaylor x degree : ℝ)| ≤ (trigRadius x degree : ℝ) := by
  simpa [sinTaylor, trigRadius, cast_sinCoefficient] using
    abs_sub_taylor_le Real.sin (x : ℝ) degree Real.contDiff_sin
      Real.abs_iteratedDeriv_sin_le_one

/-- The executable cosine polynomial has the same global remainder guarantee. -/
theorem abs_cos_sub_cosTaylor_le (x : ℚ) (degree : Nat) :
    |Real.cos (x : ℝ) - (cosTaylor x degree : ℝ)| ≤ (trigRadius x degree : ℝ) := by
  simpa [cosTaylor, trigRadius, cast_cosCoefficient] using
    abs_sub_taylor_le Real.cos (x : ℝ) degree Real.contDiff_cos
      Real.abs_iteratedDeriv_cos_le_one

/-- Intersecting with `[-1, 1]` retains containment of any value in that range. -/
theorem contains_restrictUnit {interval : RationalInterval} {x : ℝ}
    (hx : interval.Contains x) (hbound : |x| ≤ 1) :
    (restrictUnit interval).Contains x := by
  rcases abs_le.mp hbound with ⟨hlower, hupper⟩
  constructor
  · simpa [restrictUnit] using max_le hlower hx.1
  · simpa [restrictUnit] using le_min hupper hx.2

/-- Every finite degree provides a sound enclosure of sine on all rational arguments. -/
theorem contains_sin (x : ℚ) (degree : Nat) :
    (sin x degree).Contains (Real.sin (x : ℝ)) :=
  contains_restrictUnit
    (RationalInterval.contains_around (abs_sin_sub_sinTaylor_le x degree))
    (Real.abs_sin_le_one _)

/-- Every finite degree provides a sound enclosure of cosine on all rational arguments. -/
theorem contains_cos (x : ℚ) (degree : Nat) :
    (cos x degree).Contains (Real.cos (x : ℝ)) :=
  contains_restrictUnit
    (RationalInterval.contains_around (abs_cos_sub_cosTaylor_le x degree))
    (Real.abs_cos_le_one _)

end FloatLib.Numerics.Enclosure
