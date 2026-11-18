/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Quantization.Stochastic.Rounder

/-!
# Fixed-scale re-quantization and independent products

Scaling an unbiased rounded value back by the same fixed nonzero scale
preserves the supplied stored value in expectation. A scale may vary by
entry or block, but is fixed with respect to the entropy in this theorem.
Reindexing, including transposition, does not change the argument.
The reference is the stored forward value, not an earlier master weight.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory

/-- Re-quantize a stored rational using a fixed scale and then decode the scale. -/
def scaledRound {E : Type*} (r : Rounder E) (scale x : ℚ) (e : E) : ℚ :=
  scale * r.round e (x / scale)

/-- A nonzero scale chosen independently of this word preserves the stored value's mean. -/
theorem mean_scaledRound {E : Type*} [MeasurableSpace E] {ν : Measure E}
    (r : Rounder E) (hr : r.Law ν) (scale x : ℚ) (hs : scale ≠ 0)
    (hx : r.Admissible (x / scale)) :
    (∫ e, (scaledRound r scale x e : ℝ) ∂ν) = x := by
  simp only [scaledRound, Rat.cast_mul, integral_const_mul, hr.mean _ hx, Rat.cast_div]
  exact mul_div_cancel₀ (x : ℝ) (by exact_mod_cast hs)

/-- Any reindexing preserves entrywise means; different entries may share entropy. -/
theorem mean_reindex {I J E : Type*} [MeasurableSpace E] {ν : Measure E}
    (r : I → Rounder E) (hr : ∀ i, (r i).Law ν) (scale x : I → ℚ) (index : J → I)
    (hs : ∀ i, scale i ≠ 0) (hx : ∀ i, (r i).Admissible (x i / scale i)) (j : J) :
    (∫ e, (scaledRound (r (index j)) (scale (index j)) (x (index j)) e : ℝ) ∂ν) =
      x (index j) :=
  mean_scaledRound _ (hr _) _ _ (hs _) (hx _)

/-- A fixed linear combination needs only entrywise unbiasedness, not independence of entries. -/
theorem mean_linear_combination {I E : Type*} [Fintype I] [Finite E]
    [MeasurableSpace E] [MeasurableSingletonClass E] {ν : Measure E}
    [IsFiniteMeasure ν]
    (X : I → E → ℝ) (reference coefficient : I → ℝ)
    (hX : ∀ i, (∫ e, X i e ∂ν) = reference i) :
    (∫ e, ∑ i, coefficient i * X i e ∂ν) = ∑ i, coefficient i * reference i := by
  rw [integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
  simp only [integral_const_mul, hX]

/-- Rounded products of independent random operands preserve the product of their means.
The operand histories and the product's fresh word have three separate factors. -/
theorem mean_independent_rounded_product {H K E : Type*}
    [Finite H] [Finite K] [Finite E]
    [MeasurableSpace H] [MeasurableSpace K] [MeasurableSpace E]
    [MeasurableSingletonClass H] [MeasurableSingletonClass K] [MeasurableSingletonClass E]
    {μ : Measure H} {ν : Measure K} {ρ : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (r : Rounder E) (hr : r.Law ρ) (X : H → ℚ) (Y : K → ℚ)
    (hs : ∀ h k, r.Admissible (X h * Y k)) :
    (∫ z, (r.round z.2 (X z.1.1 * Y z.1.2) : ℝ) ∂(μ.prod ν).prod ρ) =
      (∫ h, (X h : ℝ) ∂μ) * ∫ k, (Y k : ℝ) ∂ν := by
  rw [integral_prod _ Integrable.of_finite]
  simp_rw [hr.mean _ (hs _ _), Rat.cast_mul]
  exact integral_prod_mul (fun h ↦ (X h : ℝ)) (fun k ↦ (Y k : ℝ))

end FloatLib.Numerics.Quantization.Stochastic
