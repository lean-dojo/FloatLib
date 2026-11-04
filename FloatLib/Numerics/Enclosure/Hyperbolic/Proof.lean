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
rational argument neither result is rational, since otherwise its exponential would satisfy a
nonzero quadratic polynomial over the rationals and contradict transcendence. So adaptive comparison
eventually separates every rational boundary.
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
  simpa [sinh, Real.sinh_eq, div_eq_mul_inv, mul_comm] using
    RationalInterval.tendsto_scaleNonnegative_lo
      (RationalInterval.tendsto_sub_lo (tendsto_exp_lo x) (tendsto_exp_hi (-x))) (1 / 2)

/-- Upper hyperbolic sine endpoints converge to the exact real value. -/
theorem tendsto_sinh_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((sinh x n).hi : ℝ)) atTop (𝓝 (Real.sinh (x : ℝ))) := by
  simpa [sinh, Real.sinh_eq, div_eq_mul_inv, mul_comm] using
    RationalInterval.tendsto_scaleNonnegative_hi
      (RationalInterval.tendsto_sub_hi (tendsto_exp_hi x) (tendsto_exp_lo (-x))) (1 / 2)

/-- Lower hyperbolic cosine endpoints converge to the exact real value. -/
theorem tendsto_cosh_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((cosh x n).lo : ℝ)) atTop (𝓝 (Real.cosh (x : ℝ))) := by
  simpa [cosh, Real.cosh_eq, div_eq_mul_inv, mul_comm] using
    RationalInterval.tendsto_scaleNonnegative_lo
      (RationalInterval.tendsto_add_lo (tendsto_exp_lo x) (tendsto_exp_lo (-x))) (1 / 2)

/-- Upper hyperbolic cosine endpoints converge to the exact real value. -/
theorem tendsto_cosh_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((cosh x n).hi : ℝ)) atTop (𝓝 (Real.cosh (x : ℝ))) := by
  simpa [cosh, Real.cosh_eq, div_eq_mul_inv, mul_comm] using
    RationalInterval.tendsto_scaleNonnegative_hi
      (RationalInterval.tendsto_add_hi (tendsto_exp_hi x) (tendsto_exp_hi (-x))) (1 / 2)

/-- A real root of a monic rational quadratic `y ^ 2 - 2 q y + c` is algebraic over `ℚ`. -/
private theorem isAlgebraic_of_sq_sub_two_mul_add_eq_zero {y : ℝ} (q c : ℚ)
    (hroot : y ^ 2 - 2 * (q : ℝ) * y + (c : ℝ) = 0) : IsAlgebraic ℚ y := by
  refine ⟨X ^ 2 - C (2 * q) * X + C c, ?_, ?_⟩
  · intro h
    have := congrArg (fun p : ℚ[X] => p.coeff 2) h
    norm_num [coeff_X_pow, coeff_C_mul, coeff_C] at this
  · simp only [map_add, map_sub, map_pow, map_mul, aeval_X, aeval_C]
    simpa using hroot

/--
At a nonzero rational `x`, `(exp x + c * exp (-x)) / 2` is not rational for any rational `c`:
a rational value `q` would make `exp x` a root of `y ^ 2 - 2 q y + c`.
-/
private theorem exp_add_mul_exp_neg_ne_ratCast (x q c : ℚ) (hx : x ≠ 0) :
    (Real.exp (x : ℝ) + (c : ℝ) * Real.exp (-(x : ℝ))) / 2 ≠ (q : ℝ) := by
  intro heq
  apply transcendental_exp_ratCast x hx
  refine isAlgebraic_of_sq_sub_two_mul_add_eq_zero q c ?_
  rw [Real.exp_neg] at heq
  have hexp := Real.exp_ne_zero (x : ℝ)
  field_simp at heq
  linear_combination heq

/-- A nonzero rational argument cannot have a rational hyperbolic sine. -/
theorem sinh_ratCast_ne_ratCast (x q : ℚ) (hx : x ≠ 0) :
    Real.sinh (x : ℝ) ≠ (q : ℝ) := by
  have h := exp_add_mul_exp_neg_ne_ratCast x q (-1) hx
  rwa [Rat.cast_neg, Rat.cast_one, neg_one_mul, ← sub_eq_add_neg, ← Real.sinh_eq] at h

/-- A nonzero rational argument cannot have a rational hyperbolic cosine. -/
theorem cosh_ratCast_ne_ratCast (x q : ℚ) (hx : x ≠ 0) :
    Real.cosh (x : ℝ) ≠ (q : ℝ) := by
  have h := exp_add_mul_exp_neg_ne_ratCast x q 1 hx
  rwa [Rat.cast_one, one_mul, ← Real.cosh_eq] at h

/-- Doubling the degree eventually separates every rational hyperbolic sine boundary. -/
theorem exists_sinh_separating (argument boundary : ℚ) (hne : argument ≠ 0) :
    ∃ n, Comparison.Separates (sinh argument (2 ^ n)) boundary :=
  Comparison.exists_separating_two_pow boundary (sinh_ratCast_ne_ratCast argument boundary hne)
    (tendsto_sinh_lo argument)
    (tendsto_sinh_hi argument)

/-- Doubling the degree eventually separates every rational hyperbolic cosine boundary. -/
theorem exists_cosh_separating (argument boundary : ℚ) (hne : argument ≠ 0) :
    ∃ n, Comparison.Separates (cosh argument (2 ^ n)) boundary :=
  Comparison.exists_separating_two_pow boundary (cosh_ratCast_ne_ratCast argument boundary hne)
    (tendsto_cosh_lo argument)
    (tendsto_cosh_hi argument)

end FloatLib.Numerics.Enclosure
