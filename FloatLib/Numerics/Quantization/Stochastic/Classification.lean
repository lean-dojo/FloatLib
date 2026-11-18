/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Quantization.Stochastic.Relu
public import FloatLib.Numerics.Quantization.Stochastic.Zero

/-!
# Classification margins from probabilistic gap errors

For each rival, an exponential-moment certificate for the error in its
score minus the candidate score gives a one-sided confidence radius.
If every exact reference margin exceeds that radius, a finite union bound
controls any tie or loss. Scores and rivals are arbitrary: this theorem
does not assume a particular network or unbiased nonlinear activations.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory Real

/-- Simultaneous pairwise margin checks bound the probability of any tie or loss. -/
theorem classification_confidence {E J : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasure μ] (rivals : Finset J)
    (candidate : E → ℝ) (score : J → E → ℝ) (reference : ℝ)
    (refScore c p δ : J → ℝ)
    (hmgf : ∀ j ∈ rivals,
      MGFBound (fun e ↦ (score j e - candidate e) - (refScore j - reference))
        (c j) (p j) μ)
    (hc : ∀ j ∈ rivals, 0 ≤ c j) (hp : ∀ j ∈ rivals, 0 ≤ p j)
    (hδ : ∀ j ∈ rivals, 0 < δ j) (hδ₁ : ∀ j ∈ rivals, δ j < 1)
    (hgap : ∀ j ∈ rivals, refScore j < reference)
    (hmargin : ∀ j ∈ rivals,
      sqrt (2 * c j * (p j + log (1 / δ j))) ≤ reference - refScore j) :
    μ.real {e | ∃ j ∈ rivals, candidate e ≤ score j e} ≤ ∑ j ∈ rivals, δ j := by
  have hpair (j : J) (hj : j ∈ rivals) :
      μ.real {e | candidate e ≤ score j e} ≤ δ j := by
    rcases (hc j hj).eq_or_lt with hz | hcj
    · have hm := hmgf j hj
      rw [← hz] at hm
      have hn : ∀ᵐ e ∂μ, ¬ candidate e ≤ score j e := by
        filter_upwards [hm.exact_of_zero] with e he
        change (score j e - candidate e) - (refScore j - reference) = 0 at he
        have hg := hgap j hj
        linarith
      have hnull : μ {e | candidate e ≤ score j e} = 0 := by
        simpa only [not_not] using ae_iff.mp hn
      rw [(measureReal_eq_zero_iff).mpr hnull]
      exact (hδ j hj).le
    · refine (measureReal_mono (fun e he ↦ ?_)).trans
        ((hmgf j hj).confidence hcj (hp j hj) (δ j) (hδ j hj) (hδ₁ j hj))
      change candidate e ≤ score j e at he
      change sqrt (2 * c j * (p j + log (1 / δ j))) ≤
        (score j e - candidate e) - (refScore j - reference)
      exact (hmargin j hj).trans (by linarith)
  calc
    _ = μ.real (⋃ j ∈ rivals, {e | candidate e ≤ score j e}) := by
      congr 1
      ext e
      simp
    _ ≤ ∑ j ∈ rivals, μ.real {e | candidate e ≤ score j e} :=
      measureReal_biUnion_finset_le rivals _
    _ ≤ ∑ j ∈ rivals, δ j := Finset.sum_le_sum hpair

end FloatLib.Numerics.Quantization.Stochastic
