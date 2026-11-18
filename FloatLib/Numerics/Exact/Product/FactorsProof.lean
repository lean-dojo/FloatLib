/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Product.Factors
public import FloatLib.Numerics.Exact.Product.Proof
public import FloatLib.Numerics.Exact.Hyperbolic.Proof
public import FloatLib.Numerics.Enclosure.Elementary.ExponentialSumIrrational
public import FloatLib.Numerics.Enclosure.Elementary.TrigonometricIrrational
public import FloatLib.Numerics.Enclosure.Trigonometric.Reduction.Convergence
public import FloatLib.Numerics.Enclosure.Rational.Converges

/-!
# The products of the complex exponential and hyperbolic functions are irrational

For an admissible pair of factors the product `growth a * trig b` at rational `a` and `b` differs
from every rational (`eval_mul_eval_ne_ratCast`): it is a real exponential sum at nonzero
arguments, which `Enclosure.sum_exp_mul_trig_ne_ratCast` separates from nonzero rationals, and
neither factor is zero. The enclosures of the bounded factor by argument reduction converge
(`Trig.converges_reduced`), so the product comparison terminates at every rational boundary, with
no premise on the boundary (`Admissible.exists_decide?_isSome` in `AngleProof`).
-/

@[expose] public section

namespace FloatLib.Numerics.ProductComparison

open Filter
open scoped Topology

/-- The real unbounded factor. -/
noncomputable def Growth.eval : Growth → ℝ → ℝ
  | .exp => Real.exp
  | .sinh => Real.sinh
  | .cosh => Real.cosh

/-- The real bounded factor. -/
noncomputable def Trig.eval : Trig → ℝ → ℝ
  | .cos => Real.cos
  | .sin => Real.sin

/-- The weights of `exp a` and `exp (-a)` in the unbounded factor. -/
def Growth.weights : Growth → ℚ × ℚ
  | .exp => (1, 0)
  | .sinh => (1 / 2, -1 / 2)
  | .cosh => (1 / 2, 1 / 2)

/-- The weights of `cos b` and `sin b` in the bounded factor. -/
def Trig.weights : Trig → ℚ × ℚ
  | .cos => (1, 0)
  | .sin => (0, 1)

/-- The unbounded factor is a combination of `exp a` and `exp (-a)`. -/
theorem Growth.eval_eq (growth : Growth) (a : ℝ) :
    growth.eval a = growth.weights.1 * Real.exp a + growth.weights.2 * Real.exp (-a) := by
  cases growth
  · simp [Growth.eval, Growth.weights]
  · simp only [Growth.eval, Growth.weights, Real.sinh_eq]
    push_cast
    ring
  · simp only [Growth.eval, Growth.weights, Real.cosh_eq]
    push_cast
    ring

/-- The bounded factor is a combination of `cos b` and `sin b`. -/
theorem Trig.eval_eq (trig : Trig) (b : ℝ) :
    trig.eval b = trig.weights.1 * Real.cos b + trig.weights.2 * Real.sin b := by
  cases trig <;> simp [Trig.eval, Trig.weights]

/-- The comparator of the unbounded factor is exact. -/
theorem Growth.compare_eq_real (growth : Growth) (a boundary : ℚ) :
    growth.compare a boundary = cmp (growth.eval (a : ℝ)) (boundary : ℝ) := by
  cases growth
  · exact ElementaryComparison.compareExp_eq_real a boundary
  · exact HyperbolicComparison.compareSinh_eq_real a boundary
  · exact HyperbolicComparison.compareCosh_eq_real a boundary

/-- The enclosures by argument reduction contain the bounded factor and converge to it. -/
theorem Trig.converges_reduced (trig : Trig) (b : ℚ) :
    RationalInterval.Converges (trig.reduced b) (trig.eval (b : ℝ)) := by
  cases trig
  · exact ⟨fun n => Enclosure.contains_cosReduced b (2 ^ n),
      (Enclosure.tendsto_cosReduced_lo b).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)),
      (Enclosure.tendsto_cosReduced_hi b).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))⟩
  · exact ⟨fun n => Enclosure.contains_sinReduced b (2 ^ n),
      (Enclosure.tendsto_sinReduced_lo b).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)),
      (Enclosure.tendsto_sinReduced_hi b).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))⟩

variable {growth : Growth} {trig : Trig} {a b : ℚ}

/-- An admissible unbounded factor is positive. -/
theorem Admissible.growth_pos (h : Admissible growth trig a b) : 0 < growth.eval (a : ℝ) := by
  cases growth
  · exact Real.exp_pos _
  · exact Real.sinh_pos_iff.mpr (by exact_mod_cast h.1 rfl)
  · exact Real.cosh_pos _

/-- An admissible bounded factor is not zero: no rational is a zero of the cosine or, apart from
zero, of the sine. -/
theorem Admissible.trig_ne_zero (h : Admissible growth trig a b) : trig.eval (b : ℝ) ≠ 0 := by
  cases trig
  · by_cases hb : b = 0
    · simp [Trig.eval, hb]
    · exact (Enclosure.irrational_cos_ratCast b hb).ne_zero
  · exact (Enclosure.irrational_sin_ratCast b (h.2.1 rfl)).ne_zero

/-- An admissible product differs from every rational. -/
theorem Admissible.eval_mul_eval_ne_ratCast (h : Admissible growth trig a b) (boundary : ℚ) :
    growth.eval (a : ℝ) * trig.eval (b : ℝ) ≠ (boundary : ℝ) := by
  by_cases hboundary : boundary = 0
  · rw [hboundary, Rat.cast_zero]
    exact mul_ne_zero h.growth_pos.ne' h.trig_ne_zero
  intro hproduct
  refine Enclosure.sum_exp_mul_trig_ne_ratCast (Finset.univ : Finset Bool)
    (fun k => if k then a else -a) (fun _ => b) ?_
    (fun k => (if k then growth.weights.1 else growth.weights.2) * trig.weights.1)
    (fun k => (if k then growth.weights.1 else growth.weights.2) * trig.weights.2)
    boundary hboundary ?_
  · intro k _ hzero
    refine h.2.2 ⟨?_, hzero.2⟩
    cases k
    · simpa using hzero.1
    · simpa using hzero.1
  · rw [Fintype.sum_bool, ← hproduct, growth.eval_eq, trig.eval_eq]
    push_cast
    simp only [↓reduceIte]
    ring

end FloatLib.Numerics.ProductComparison
