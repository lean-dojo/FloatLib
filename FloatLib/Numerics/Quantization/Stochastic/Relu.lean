/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Quantization.Stochastic.MGF

/-!
# Weighted ReLU errors with proved reachable intervals

A centered preactivation error with proxy `c` contributes `a² c` after
ReLU and multiplication by `a`, and incurs at most a factor two in its
exponential moment. A nonnegative reachable interval removes that factor;
a nonpositive interval or zero coefficient removes the whole contribution.
These rules do not assert that ReLU preserves the mean.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- The quadratic proxy of a weighted ReLU error, using its reachable upper bound. -/
noncomputable def reluProxy (a upper c : ℝ) : ℝ :=
  if a = 0 ∨ upper ≤ 0 then 0 else a ^ 2 * c

/-- Only a nonzero contribution whose interval crosses zero needs the factor two. -/
noncomputable def reluPenalty (a lower upper : ℝ) : ℝ :=
  if a = 0 ∨ 0 ≤ lower ∨ upper ≤ 0 then 0 else log 2

/-- A reachable interval selects the exact linear branch or the general contraction bound. -/
theorem weighted_relu {E : Type*} [Finite E] [MeasurableSpace E]
    [MeasurableSingletonClass E] {μ : Measure E} [IsProbabilityMeasure μ]
    {X : E → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ)
    (hmean : ∫ e, X e ∂μ = 0) (a z lower upper : ℝ)
    (hlower : ∀ e, lower ≤ z + X e) (hupper : ∀ e, z + X e ≤ upper) :
    MGFBound (fun e ↦ a * (max (z + X e) 0 - max z 0))
      (reluProxy a upper c) (reluPenalty a lower upper) μ := by
  by_cases ha : a = 0
  · subst a
    simpa [reluProxy, reluPenalty] using
      (MGFBound.of_subgaussian (HasSubgaussianMGF.fun_zero (μ := μ)))
  by_cases hu : upper ≤ 0
  · have hn := MGFBound.relu_of_nonpos hmean z (fun e ↦ (hupper e).trans hu)
    simpa [reluProxy, reluPenalty, hu] using hn.mul_const a
  by_cases hl : 0 ≤ lower
  · have hp := (MGFBound.of_subgaussian h).relu_of_nonneg hmean z
      (fun e ↦ hl.trans (hlower e))
    simpa [reluProxy, reluPenalty, ha, hu, hl] using hp.mul_const a
  · simpa [reluProxy, reluPenalty, ha, hu, hl] using
      ((MGFBound.of_subgaussian h).relu z).mul_const a

/-- Independent hidden rows followed by fresh conditional output error.
The output law may depend on the entire hidden history; only its bound is uniform. -/
theorem relu_fresh {E F : Type*} [Finite E] [Finite F]
    [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSingletonClass E] [MeasurableSingletonClass F]
    {μ : Measure E} {ν : Measure F} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ℕ → E → ℝ) (c : ℕ → ℝ≥0) (a z lower upper : ℕ → ℝ) (n : ℕ)
    (h : ∀ k, k < n → HasSubgaussianMGF (X k) (c k) μ)
    (hmean : ∀ k, k < n → ∫ e, X k e ∂μ = 0)
    (hlower : ∀ k, k < n → ∀ e, lower k ≤ z k + X k e)
    (hupper : ∀ k, k < n → ∀ e, z k + X k e ≤ upper k)
    (D : History E n × F → ℝ) (d q : ℝ)
    (hD : ∀ history, MGFBound (fun e ↦ D (history, e)) d q ν) :
    MGFBound (fun e ↦
      run (fun k s word ↦ s + a k * (max (z k + X k word) 0 - max (z k) 0))
        0 n e.1 + D e)
      ((∑ k ∈ Finset.range n, reluProxy (a k) (upper k) (c k)) + d)
      ((∑ k ∈ Finset.range n, reluPenalty (a k) (lower k) (upper k)) + q)
      ((historyLaw μ n).prod ν) :=
  (MGFBound.independent_sum _ _ _ n (fun k hk ↦ weighted_relu
    (h k hk) (hmean k hk) (a k) (z k) (lower k) (upper k)
    (hlower k hk) (hupper k hk))).fresh hD

end FloatLib.Numerics.Quantization.Stochastic
