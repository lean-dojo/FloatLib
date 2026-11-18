/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Stochastic.Sum

/-!
# Append a fresh rounded addition to a certified computation

The accumulated value may depend on its entire entropy history. The new
word is independent of that history; the new rounding error need not be.
This rule handles the final bias addition in an affine layer and composes
already certified arithmetic without repeating the sequential proof.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Append one rounded addition, consuming a word after the previous history. -/
def roundedAdd {H E : Type*} (r : Rounder E) (actual : H → ℚ) (b : ℚ)
    (z : H × E) : ℚ :=
  r.round z.2 (actual z.1 + b)

variable {H E : Type*} [Finite H] [Finite E]
  [MeasurableSpace H] [MeasurableSpace E]
  [MeasurableSingletonClass H] [MeasurableSingletonClass E]
  {μ : Measure H} {ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- A fresh rounded addition preserves the reference mean and adds one local proxy. -/
theorem roundedAdd_certificate (r : Rounder E) (hr : r.Law ν)
    (actual : H → ℚ) (reference : ℝ) (budget : ℝ≥0)
    (hactual : Certificate μ (fun h ↦ (actual h : ℝ)) reference budget)
    (b : ℚ) (c : ℝ≥0)
    (hs : ∀ h, r.Admissible (actual h + b))
    (hc : ∀ h, r.proxy (actual h + b) ≤ c) :
    Certificate (μ.prod ν) (fun z ↦ (roundedAdd r actual b z : ℝ))
      (reference + b) (budget + c) := by
  let X : H → ℝ := fun h ↦ (actual h : ℝ) - reference
  let D : H × E → ℝ := fun z ↦
    (roundedAdd r actual b z : ℝ) - (actual z.1 + b : ℚ)
  have hD : ∀ h, ∫ e, D (h, e) ∂ν = 0 := by
    intro h
    dsimp only [D, roundedAdd]
    rw [integral_sub Integrable.of_finite (integrable_const _), hr.mean _ (hs h)]
    simp
  have hX : ∫ h, X h ∂μ = 0 := by
    dsimp only [X]
    rw [integral_sub Integrable.of_finite (integrable_const _), hactual.mean]
    simp
  have heq :
      (fun z ↦ (roundedAdd r actual b z : ℝ) - (reference + b)) =
      fun z ↦ X z.1 + D z := by
    funext z
    simp only [X, D, Rat.cast_add]
    ring
  refine ⟨?_, ?_, ?_⟩
  · have hm := mean_fresh (μ := μ) (ν := ν) X D hD
    rw [← heq, hX, integral_sub Integrable.of_finite (integrable_const _)] at hm
    simpa using sub_eq_zero.mp hm
  · simp_rw [show ∀ z, (roundedAdd r actual b z : ℝ) - (reference + b) =
        X z.1 + D z from fun z ↦ congrFun heq z]
    have hD₂ : ∀ h, ∫ e, (D (h, e)) ^ 2 ∂ν ≤ (c : ℝ) :=
      fun h ↦ (hr.second _ (hs h)).trans (hc h)
    exact (second_moment_fresh_le X D c hD hD₂).trans
      (add_le_add hactual.second le_rfl)
  · rw [heq]
    exact subgaussian_fresh hactual.mgf
      (fun h ↦ subgaussian_mono (hr.mgf _ (hs h)) (hc h))

/-- The same composition with its local proxy inferred over all prior histories. -/
theorem roundedAdd_certificate_auto (r : Rounder E) (hr : r.Law ν)
    (actual : H → ℚ) (reference : ℝ) (budget : ℝ≥0)
    (hactual : Certificate μ (fun h ↦ (actual h : ℝ)) reference budget)
    (b : ℚ) (hs : ∀ h, r.Admissible (actual h + b)) :
    Certificate (μ.prod ν) (fun z ↦ (roundedAdd r actual b z : ℝ))
      (reference + b) (budget + finiteBudget (fun h ↦ r.proxy (actual h + b))) :=
  roundedAdd_certificate r hr actual reference budget hactual b _ hs
    (le_finiteBudget (fun h ↦ r.proxy (actual h + b)))

end FloatLib.Numerics.Quantization.Stochastic
