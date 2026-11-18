/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Tanh.Sequences
public import FloatLib.Numerics.Exact.Product.AngleProof
public import FloatLib.Numerics.Enclosure.Rational.Converges
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridProof
public import FloatLib.Numerics.Enclosure.Elementary.Convergence

/-!
# The parts of the complex hyperbolic tangent are irrational

For rational `a > 0` and `b`, the numerators that order the parts of `tanh (a + i b)` against a
rational converge (`converges_reInterval`, `converges_imInterval`) and never vanish
(`reNumerator_ne_zero`, `imNumerator_ne_zero`): each vanishing would be a rational value of a
real exponential sum, which `Enclosure.sum_exp_mul_trig_ne_ratCast` excludes. So the exact
comparisons of the tangent terminate at every rational boundary.
-/

@[expose] public section

namespace FloatLib.Numerics.TanhComparison

open RationalInterval ProductComparison

/-- The exponential ladder converges to the exponential. -/
theorem converges_expLadder (x : ℚ) : Converges (expLadder x) (Real.exp (x : ℝ)) :=
  (Converges.comp_two_pow
    ⟨Enclosure.contains_exp x, Enclosure.tendsto_exp_lo x, Enclosure.tendsto_exp_hi x⟩).prefixed
    fun _ _ => Enclosure.BinaryGrid.contains_exp x _ _

/-- The numerator of the real part: `(1 - t) - (1 + t) exp (-4a) - 2 t exp (-2a) cos 2b`. -/
noncomputable def reNumerator (a b t : ℝ) : ℝ :=
  (1 - t) - (1 + t) * Real.exp (-(4 * a)) - 2 * t * (Real.exp (-(2 * a)) * Real.cos (2 * b))

/-- The numerator of the imaginary part:
`2 exp (-2a) sin 2b - t - t exp (-4a) - 2 t exp (-2a) cos 2b`. -/
noncomputable def imNumerator (a b t : ℝ) : ℝ :=
  2 * (Real.exp (-(2 * a)) * Real.sin (2 * b)) - t - t * Real.exp (-(4 * a)) -
    2 * t * (Real.exp (-(2 * a)) * Real.cos (2 * b))

variable (a b t : ℚ)

/-- The enclosures of `exp (-2a) + cos 2b` converge. -/
theorem converges_unitInterval :
    Converges (fun n => unitInterval (expLadder (-(2 * a)) n) (Trig.cos.intervals (2 * b) n))
      (Real.exp (-(2 * (a : ℝ))) + Real.cos (2 * (b : ℝ))) := by
  have h := (converges_expLadder (-(2 * a))).add (Trig.converges_intervals .cos (2 * b))
  simpa [Trig.eval, unitInterval] using h

/-- The enclosures of the real-part numerator converge. -/
theorem converges_reInterval :
    Converges (fun n => reInterval (expLadder (-(2 * a)) n) (expLadder (-(4 * a)) n)
      (Trig.cos.intervals (2 * b) n) t) (reNumerator a b t) := by
  have h := ((Converges.const (1 - t)).sub ((converges_expLadder (-(4 * a))).scale (1 + t))).sub
    (((converges_expLadder (-(2 * a))).mul (Trig.converges_intervals .cos (2 * b))).scale (2 * t))
  simpa [Trig.eval, reNumerator, reInterval] using h

/-- The enclosures of the imaginary-part numerator converge. -/
theorem converges_imInterval :
    Converges (fun n => imInterval (expLadder (-(2 * a)) n) (expLadder (-(4 * a)) n)
      (Trig.sin.intervals (2 * b) n) (Trig.cos.intervals (2 * b) n) t) (imNumerator a b t) := by
  have hsine := (converges_expLadder (-(2 * a))).mul (Trig.converges_intervals .sin (2 * b))
  have hcosine := (converges_expLadder (-(2 * a))).mul (Trig.converges_intervals .cos (2 * b))
  have h := (((hsine.scale 2).sub (Converges.const t)).sub
    ((converges_expLadder (-(4 * a))).scale t)).sub (hcosine.scale (2 * t))
  simpa [Trig.eval, imNumerator, imInterval] using h

variable {a b t}

private theorem exp_neg_two (a : ℝ) : Real.exp (-(2 * a)) = (Real.exp (2 * a))⁻¹ :=
  Real.exp_neg _

private theorem exp_neg_four (a : ℝ) : Real.exp (-(4 * a)) = ((Real.exp (2 * a))⁻¹) ^ 2 := by
  rw [← Real.exp_neg, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem exp_four (a : ℝ) : Real.exp (4 * a) = Real.exp (2 * a) ^ 2 := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `exp (-2a) + cos 2b` is not zero for a nonzero rational `a`. -/
theorem exp_neg_add_cos_ne_zero (ha : a ≠ 0) :
    Real.exp (-(2 * (a : ℝ))) + Real.cos (2 * (b : ℝ)) ≠ 0 := by
  intro hzero
  have hpos := Real.exp_pos (2 * (a : ℝ))
  refine Enclosure.sum_exp_mul_trig_ne_ratCast (Finset.univ : Finset Unit) (fun _ => 2 * a)
    (fun _ => 2 * b) (fun _ _ h => ha (by linarith [h.1])) (fun _ => 1) (fun _ => 0) (-1)
    (by norm_num) ?_
  rw [exp_neg_two] at hzero
  simp only [Finset.univ_unique, Finset.sum_singleton]
  push_cast
  field_simp at hzero
  linarith

/-- The real-part numerator is not zero, for a nonzero rational `a` and a boundary other than
`-1`. -/
theorem reNumerator_ne_zero (ha : a ≠ 0) (ht : t ≠ -1) : reNumerator a b t ≠ 0 := by
  intro hzero
  have hpos := Real.exp_pos (2 * (a : ℝ))
  refine Enclosure.sum_exp_mul_trig_ne_ratCast (Finset.univ : Finset Bool)
    (fun k => if k then 4 * a else 2 * a) (fun k => if k then 0 else 2 * b) ?_
    (fun k => if k then 1 - t else -(2 * t)) (fun _ => 0) (1 + t)
    (fun h => ht (by linarith)) ?_
  · intro k _ h
    cases k <;> exact ha (by simpa using h.1)
  · rw [reNumerator, exp_neg_two, exp_neg_four] at hzero
    rw [Fintype.sum_bool]
    simp only [↓reduceIte]
    push_cast
    rw [Real.cos_zero, Real.sin_zero, exp_four]
    generalize Real.exp (2 * (a : ℝ)) = E at hzero hpos ⊢
    have h1 : E * E⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
    have h2 : E ^ 2 * E⁻¹ ^ 2 = 1 := by rw [← mul_pow, h1, one_pow]
    have h3 : E ^ 2 * (E⁻¹ * Real.cos (2 * b)) = E * Real.cos (2 * b) := by
      calc E ^ 2 * (E⁻¹ * Real.cos (2 * b)) = E * (E * E⁻¹) * Real.cos (2 * b) := by ring
        _ = E * Real.cos (2 * b) := by rw [h1, mul_one]
    have hscaled : E ^ 2 * (1 - (t : ℝ)) - (1 + t) * (E ^ 2 * E⁻¹ ^ 2) -
        2 * t * (E ^ 2 * (E⁻¹ * Real.cos (2 * b))) = 0 := by
      linear_combination E ^ 2 * hzero
    rw [h2, h3] at hscaled
    linarith

/-- The imaginary-part numerator is not zero, for a nonzero rational `a` and a nonzero
boundary. -/
theorem imNumerator_ne_zero (ha : a ≠ 0) (ht : t ≠ 0) : imNumerator a b t ≠ 0 := by
  intro hzero
  have hpos := Real.exp_pos (2 * (a : ℝ))
  refine Enclosure.sum_exp_mul_trig_ne_ratCast (Finset.univ : Finset Bool)
    (fun k => if k then 4 * a else 2 * a) (fun k => if k then 0 else 2 * b) ?_
    (fun k => if k then -t else -(2 * t)) (fun k => if k then 0 else 2) t ht ?_
  · intro k _ h
    cases k <;> exact ha (by simpa using h.1)
  · rw [imNumerator, exp_neg_two, exp_neg_four] at hzero
    rw [Fintype.sum_bool]
    simp only [↓reduceIte]
    push_cast
    rw [Real.cos_zero, Real.sin_zero, exp_four]
    generalize Real.exp (2 * (a : ℝ)) = E at hzero hpos ⊢
    have h1 : E * E⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
    have h2 : E ^ 2 * E⁻¹ ^ 2 = 1 := by rw [← mul_pow, h1, one_pow]
    have h3 (x : ℝ) : E ^ 2 * (E⁻¹ * x) = E * x := by
      calc E ^ 2 * (E⁻¹ * x) = E * (E * E⁻¹) * x := by ring
        _ = E * x := by rw [h1, mul_one]
    have hscaled : 2 * (E ^ 2 * (E⁻¹ * Real.sin (2 * b))) - E ^ 2 * (t : ℝ) -
        t * (E ^ 2 * E⁻¹ ^ 2) - 2 * t * (E ^ 2 * (E⁻¹ * Real.cos (2 * b))) = 0 := by
      linear_combination E ^ 2 * hzero
    rw [h2, h3, h3] at hscaled
    linarith

end FloatLib.Numerics.TanhComparison
