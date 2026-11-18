/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Probability.Moments.SubGaussian

/-!
# Two-sided stochastic error bounds

The only probability estimate used here is mathlib's sub-Gaussian Chernoff bound.
Applying it to the error and its negative gives the two-sided bound and the usual
square-root logarithmic confidence radius. The positive-variance premise on the
radius theorem avoids treating division by zero as a probability calculation.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X : Ω → ℝ} {c : ℝ≥0}

/-- Two-sided Chernoff bound, with the factor two coming from the union of the two tails. -/
theorem tail_abs (h : HasSubgaussianMGF X c μ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * exp (-ε ^ 2 / (2 * c)) := by
  have heq : {ω | ε ≤ |X ω|} = {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    by_cases hx : 0 ≤ X ω
    · rw [abs_of_nonneg hx]
      constructor
      · exact Or.inl
      · rintro (h | h) <;> linarith
    · rw [abs_of_neg (lt_of_not_ge hx)]
      constructor
      · exact Or.inr
      · rintro (h | h) <;> linarith
  rw [heq]
  have hneg := h.neg.measure_ge_le hε
  have hpos := h.measure_ge_le hε
  calc
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -X ω} := measureReal_union_le _ _
    _ ≤ _ := by simpa only [Pi.neg_apply] using add_le_add hpos hneg |>.trans_eq (by ring)

/-- The standard square-root logarithmic radius at a requested failure probability. -/
theorem tail_delta (h : HasSubgaussianMGF X c μ) (hc : 0 < c)
    (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    μ.real {ω | sqrt (2 * c * log (2 / δ)) ≤ |X ω|} ≤ δ := by
  have hl : 0 ≤ log (2 / δ) := log_nonneg (by
    apply (le_div_iff₀ hδ).mpr
    linarith)
  have hb := tail_abs h (sqrt (2 * c * log (2 / δ))) (sqrt_nonneg _)
  rw [sq_sqrt (by positivity)] at hb
  have he : -(2 * (c : ℝ) * log (2 / δ)) / (2 * c) = -log (2 / δ) := by
    field_simp
  rw [he, exp_neg, exp_log (div_pos (by norm_num) hδ)] at hb
  convert hb using 1
  field_simp

end FloatLib.Numerics.Quantization.Stochastic
