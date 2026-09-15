/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Hyperbolic.Runtime
public import FloatLib.Numerics.Enclosure.Comparison.Proof
public import FloatLib.Numerics.Enclosure.Elementary.Convergence
public import FloatLib.Numerics.Enclosure.Elementary.Transcendental
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Soundness and termination of hyperbolic enclosures

The rational endpoints converge to the mathematical hyperbolic sine and cosine. At a nonzero
rational argument neither result is rational: otherwise its exponential would satisfy a
nonzero quadratic polynomial over the rationals, contradicting transcendence. Thus adaptive
comparison eventually separates every rational boundary.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter Polynomial
open scoped Topology

/-- The rational hyperbolic sine interval contains the exact real value. -/
theorem contains_sinh (x : ℚ) (degree : Nat) :
    (sinh x degree).Contains (Real.sinh (x : ℝ)) := by
  simpa [sinh, Real.sinh_eq, div_eq_mul_inv, mul_comm] using
    RationalInterval.contains_scaleNonnegative
      (RationalInterval.contains_sub (contains_exp x degree) (contains_exp (-x) degree))
      (factor := 1 / 2) (by norm_num)

/-- The rational hyperbolic cosine interval contains the exact real value. -/
theorem contains_cosh (x : ℚ) (degree : Nat) :
    (cosh x degree).Contains (Real.cosh (x : ℝ)) := by
  simpa [cosh, Real.cosh_eq, div_eq_mul_inv, mul_comm] using
    RationalInterval.contains_scaleNonnegative
      (RationalInterval.contains_add (contains_exp x degree) (contains_exp (-x) degree))
      (factor := 1 / 2) (by norm_num)

/-- Lower hyperbolic sine endpoints converge to the exact real value. -/
theorem tendsto_sinh_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((sinh x n).lo : ℝ)) atTop (𝓝 (Real.sinh (x : ℝ))) := by
  simpa [sinh, RationalInterval.scaleNonnegative, RationalInterval.sub,
    RationalInterval.add, RationalInterval.neg, Real.sinh_eq, sub_eq_add_neg,
    div_eq_mul_inv, mul_comm] using
    ((tendsto_exp_lo x).sub (tendsto_exp_hi (-x))).const_mul ((2 : ℝ)⁻¹)

/-- Upper hyperbolic sine endpoints converge to the exact real value. -/
theorem tendsto_sinh_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((sinh x n).hi : ℝ)) atTop (𝓝 (Real.sinh (x : ℝ))) := by
  simpa [sinh, RationalInterval.scaleNonnegative, RationalInterval.sub,
    RationalInterval.add, RationalInterval.neg, Real.sinh_eq, sub_eq_add_neg,
    div_eq_mul_inv, mul_comm] using
    ((tendsto_exp_hi x).sub (tendsto_exp_lo (-x))).const_mul ((2 : ℝ)⁻¹)

/-- Lower hyperbolic cosine endpoints converge to the exact real value. -/
theorem tendsto_cosh_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((cosh x n).lo : ℝ)) atTop (𝓝 (Real.cosh (x : ℝ))) := by
  simpa [cosh, RationalInterval.scaleNonnegative, RationalInterval.add,
    Real.cosh_eq, div_eq_mul_inv, mul_comm] using
    ((tendsto_exp_lo x).add (tendsto_exp_lo (-x))).const_mul ((2 : ℝ)⁻¹)

/-- Upper hyperbolic cosine endpoints converge to the exact real value. -/
theorem tendsto_cosh_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((cosh x n).hi : ℝ)) atTop (𝓝 (Real.cosh (x : ℝ))) := by
  simpa [cosh, RationalInterval.scaleNonnegative, RationalInterval.add,
    Real.cosh_eq, div_eq_mul_inv, mul_comm] using
    ((tendsto_exp_hi x).add (tendsto_exp_hi (-x))).const_mul ((2 : ℝ)⁻¹)

/-- A nonzero rational argument cannot have a rational hyperbolic sine. -/
theorem sinh_ratCast_ne_ratCast (x q : ℚ) (hx : x ≠ 0) :
    Real.sinh (x : ℝ) ≠ (q : ℝ) := by
  intro heq
  apply transcendental_exp_ratCast x hx
  refine ⟨X ^ 2 - C (2 * q) * X - 1, ?_, ?_⟩
  · intro h
    have := congrArg (fun p : ℚ[X] => p.coeff 2) h
    norm_num [coeff_X_pow, coeff_C_mul, coeff_one] at this
  · simp only [map_sub, map_pow, map_mul, map_one, aeval_X, aeval_C]
    change Real.exp (x : ℝ) ^ 2 - 2 * (q : ℝ) * Real.exp (x : ℝ) - 1 = 0
    rw [Real.sinh_eq, Real.exp_neg] at heq
    have hexp := Real.exp_ne_zero (x : ℝ)
    field_simp at heq
    nlinarith [heq]

/-- A nonzero rational argument cannot have a rational hyperbolic cosine. -/
theorem cosh_ratCast_ne_ratCast (x q : ℚ) (hx : x ≠ 0) :
    Real.cosh (x : ℝ) ≠ (q : ℝ) := by
  intro heq
  apply transcendental_exp_ratCast x hx
  refine ⟨X ^ 2 - C (2 * q) * X + 1, ?_, ?_⟩
  · intro h
    have := congrArg (fun p : ℚ[X] => p.coeff 2) h
    norm_num [coeff_X_pow, coeff_C_mul, coeff_one] at this
  · simp only [map_add, map_sub, map_pow, map_mul, map_one, aeval_X, aeval_C]
    change Real.exp (x : ℝ) ^ 2 - 2 * (q : ℝ) * Real.exp (x : ℝ) + 1 = 0
    rw [Real.cosh_eq, Real.exp_neg] at heq
    have hexp := Real.exp_ne_zero (x : ℝ)
    field_simp at heq
    nlinarith [heq]

/-- Doubling the degree eventually separates every rational hyperbolic sine boundary. -/
theorem exists_sinh_separating (argument boundary : ℚ) (hne : argument ≠ 0) :
    ∃ n, Comparison.Separates (sinh argument (2 ^ n)) boundary :=
  Comparison.exists_separating boundary (sinh_ratCast_ne_ratCast argument boundary hne)
    ((tendsto_sinh_lo argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))
    ((tendsto_sinh_hi argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))

/-- Doubling the degree eventually separates every rational hyperbolic cosine boundary. -/
theorem exists_cosh_separating (argument boundary : ℚ) (hne : argument ≠ 0) :
    ∃ n, Comparison.Separates (cosh argument (2 ^ n)) boundary :=
  Comparison.exists_separating boundary (cosh_ratCast_ne_ratCast argument boundary hne)
    ((tendsto_cosh_lo argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))
    ((tendsto_cosh_hi argument).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))

end FloatLib.Numerics.Enclosure
