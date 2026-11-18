/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Probability.Moments.SubGaussian

/-!
# One fresh finite-entropy step

The previous history and the next entropy word have a product law. The error may depend
on both. Its mean, second moment, and sub-Gaussian MGF compose by integrating over the
fresh coordinate first. Independence of successive errors is not assumed.

The finite measurable carriers cover finite entropy implementations. Exact conditional
centering remains a premise: a biased finite-bit implementation cannot use these rules
without separating its drift.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {H E : Type*} [Finite H] [Finite E]
  [MeasurableSpace H] [MeasurableSpace E]
  [MeasurableSingletonClass H] [MeasurableSingletonClass E]
  {μ : Measure H} {ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- A conditionally centered fresh error does not change the accumulated mean. -/
theorem mean_fresh (X : H → ℝ) (D : H × E → ℝ)
    (hD : ∀ h, ∫ e, D (h, e) ∂ν = 0) :
    ∫ z, (X z.1 + D z) ∂μ.prod ν = ∫ h, X h ∂μ := by
  rw [integral_prod _ Integrable.of_finite]
  apply integral_congr_ae
  filter_upwards [] with h
  rw [integral_add (integrable_const _) Integrable.of_finite, hD]
  simp

/-- The new error is a martingale difference relative to the complete previous history. -/
theorem condExp_fresh (D : H × E → ℝ) (hD : ∀ h, ∫ e, D (h, e) ∂ν = 0) :
    (μ.prod ν)[D | (inferInstance : MeasurableSpace H).comap Prod.fst] =ᵐ[μ.prod ν]
      fun _ ↦ 0 := by
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le
    Integrable.of_finite (fun _ _ _ ↦ (integrable_const _).integrableOn) ?_
    aestronglyMeasurable_const
  intro s hs _
  obtain ⟨t, _, rfl⟩ := hs
  have heq : Prod.fst ⁻¹' t = t ×ˢ (Set.univ : Set E) := by ext; simp
  rw [heq, ← Measure.restrict_prod_eq_prod_univ, integral_zero,
    integral_prod D Integrable.of_finite]
  simp [hD]

/-- The mixed second-moment term vanishes by conditional centering, without independence
of the two errors. -/
theorem second_moment_fresh (X : H → ℝ) (D : H × E → ℝ)
    (hD : ∀ h, ∫ e, D (h, e) ∂ν = 0) :
    ∫ z, (X z.1 + D z) ^ 2 ∂μ.prod ν =
      (∫ h, (X h) ^ 2 ∂μ) + ∫ h, ∫ e, (D (h, e)) ^ 2 ∂ν ∂μ := by
  rw [integral_prod _ Integrable.of_finite, ← integral_add
    Integrable.of_finite Integrable.of_finite]
  apply integral_congr_ae
  filter_upwards [] with h
  simp_rw [add_sq]
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite]
  simp [integral_const_mul, hD]

/-- A uniform conditional second-moment budget adds once per fresh step. -/
theorem second_moment_fresh_le (X : H → ℝ) (D : H × E → ℝ) (v : ℝ)
    (hD : ∀ h, ∫ e, D (h, e) ∂ν = 0)
    (hv : ∀ h, ∫ e, (D (h, e)) ^ 2 ∂ν ≤ v) :
    ∫ z, (X z.1 + D z) ^ 2 ∂μ.prod ν ≤ (∫ h, (X h) ^ 2 ∂μ) + v := by
  rw [second_moment_fresh X D hD]
  gcongr
  calc
    _ ≤ ∫ _ : H, v ∂μ := integral_mono Integrable.of_finite
      (integrable_const _) hv
    _ = v := by simp

/-- Conditional sub-Gaussian budgets add under fresh entropy even for history-dependent
errors. This is the product-space specialization used by executable finite schedules. -/
theorem subgaussian_fresh {X : H → ℝ} {D : H × E → ℝ} {c d : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ)
    (hD : ∀ h, HasSubgaussianMGF (fun e ↦ D (h, e)) d ν) :
    HasSubgaussianMGF (fun z ↦ X z.1 + D z) (c + d) (μ.prod ν) where
  integrable_exp_mul _ := Integrable.of_finite
  mgf_le t := by
    simp_rw [mgf, mul_add, exp_add]
    rw [integral_prod _ Integrable.of_finite]
    simp_rw [integral_const_mul]
    calc
      _ ≤ ∫ h, exp (t * X h) * exp ((d : ℝ) * t ^ 2 / 2) ∂μ := by
        apply integral_mono Integrable.of_finite Integrable.of_finite
        intro h
        exact mul_le_mul_of_nonneg_left ((hD h).mgf_le t) (exp_pos _).le
      _ ≤ exp (↑(c + d) * t ^ 2 / 2) := by
        rw [integral_mul_const, NNReal.coe_add, add_mul, add_div, exp_add]
        exact mul_le_mul_of_nonneg_right (hX.mgf_le t) (exp_pos _).le

end FloatLib.Numerics.Quantization.Stochastic
