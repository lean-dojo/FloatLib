/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Stochastic.Cell
public import Mathlib.Probability.Distributions.Uniform

/-!
# Stochastic rounding with finite uniform entropy

`entropyLaw M` samples an integer uniformly below `M`. `hasLaw_finite_choice` is the
common implementation contract: a deterministic predicate on those integers chooses
between two real endpoints, with upper probability equal to its exact finite count.

`count_mod` counts the runtime test `entropy % den < remainder` for every entropy range,
denominator, and remainder. It separates complete residue blocks from the final incomplete
block; `mod_bias` gives the resulting probability bias, without assuming that modulo
reduction preserves uniformity.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The existing uniform finite-set measure on integers in `[0,M)`. -/
noncomputable def entropyLaw (M : ℕ) : Measure ℕ :=
  Measure.uniformOfFinset (Finset.range M)

/-- A nonempty entropy range has total mass one. -/
theorem entropyLaw_probability (M : ℕ) (hM : 0 < M) :
    IsProbabilityMeasure (entropyLaw M) := by
  refine ⟨?_⟩
  simp only [entropyLaw, Measure.uniformOfFinset_apply, Set.mem_univ, Finset.filter_true,
    Finset.card_range]
  exact ENNReal.div_self (by exact_mod_cast hM.ne') (by simp)

/-- Event probabilities under finite uniform entropy are normalized exact counts. -/
theorem entropyLaw_real (M : ℕ) (test : ℕ → Prop) [DecidablePred test] :
    (entropyLaw M).real {e | test e} = (Nat.count test M : ℝ) / M := by
  simp [entropyLaw, measureReal_def, Measure.uniformOfFinset_apply,
    Nat.count_eq_card_filter_range, ENNReal.toReal_div]

/-- Every sampled entropy word lies in the specified range almost surely. -/
theorem ae_entropyLaw_lt (M : ℕ) : ∀ᵐ e ∂entropyLaw M, e < M := by
  rw [ae_iff]
  simp [entropyLaw, Measure.uniformOfFinset_apply]

/-- A deterministic choice on finite entropy realizes its counted Bernoulli law. -/
theorem hasLaw_finite_choice (M : ℕ) (hM : 0 < M) (test : ℕ → Prop)
    [DecidablePred test] (a b : ℝ) :
    HasLaw (fun e ↦ if test e then b else a)
      (bernoulliMeasure b a
        ⟨(Nat.count test M : ℝ) / M,
          div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
          (div_le_one (Nat.cast_pos.mpr hM)).mpr (Nat.cast_le.mpr (Nat.count_le test))⟩)
      (entropyLaw M) := by
  let := entropyLaw_probability M hM
  simpa [entropyLaw_real] using
    hasLaw_choice (entropyLaw M) {e | test e} (by measurability) a b

/-- The common finite implementation contract also gives its exact expected output. -/
theorem integral_finite_choice (M : ℕ) (hM : 0 < M) (test : ℕ → Prop)
    [DecidablePred test] (a b : ℝ) :
    (∫ e, (if test e then b else a) ∂entropyLaw M) =
      (Nat.count test M : ℝ) / M * b + (1 - (Nat.count test M : ℝ) / M) * a := by
  rw [(hasLaw_finite_choice M hM test a b).integral_eq, integral_bernoulliMeasure]
  rfl

private theorem count_mod_small (t d k : ℕ) (ht : t ≤ d) :
    Nat.count (fun e ↦ e % d < k) t = min t k := by
  rw [Nat.count_eq_card_filter_range]
  have h : (Finset.range t).filter (fun e ↦ e % d < k) = Finset.range (min t k) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    constructor
    · rintro ⟨he, hk⟩
      exact ⟨he, by simpa [Nat.mod_eq_of_lt (lt_of_lt_of_le he ht)] using hk⟩
    · rintro ⟨he, hk⟩
      exact ⟨he, by simpa [Nat.mod_eq_of_lt (lt_of_lt_of_le he ht)] using hk⟩
  rw [h, Finset.card_range]

private theorem count_mod_mul (q d k : ℕ) (hk : k ≤ d) :
    Nat.count (fun e ↦ e % d < k) (q * d) = q * k := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Nat.count_add']
    simp only [Nat.add_mod_right]
    rw [ih, count_mod_small d d k le_rfl, min_eq_right hk, Nat.succ_mul]

/-- Every full residue block contributes `k` successes and the last block contributes `min`. -/
theorem count_mod (M d k : ℕ) (hd : 0 < d) (hk : k ≤ d) :
    Nat.count (fun e ↦ e % d < k) M = (M / d) * k + min (M % d) k := by
  have hsplit : M = (M / d) * d + M % d := by
    simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div M d).symm
  calc
    Nat.count (fun e ↦ e % d < k) M =
        Nat.count (fun e ↦ e % d < k) ((M / d) * d + M % d) := congrArg _ hsplit
    _ = (M / d) * k + min (M % d) k := by
      rw [Nat.count_add, count_mod_mul _ _ _ hk]
      simp only [Nat.mul_add_mod_self_right]
      rw [count_mod_small _ _ _ (Nat.mod_lt M hd).le]

/-- Exact probability of the modulo threshold used by the executable stochastic rounder. -/
theorem entropyLaw_mod (M d k : ℕ) (hd : 0 < d) (hk : k ≤ d) :
    (entropyLaw M).real {e | e % d < k} =
      (((M / d) * k + min (M % d) k : ℕ) : ℝ) / M := by
  rw [entropyLaw_real, count_mod M d k hd hk]

/-- Bias of modulo reduction relative to ideal upper probability `k/d`. -/
theorem mod_bias (M d k : ℕ) (hM : 0 < M) (hd : 0 < d) (hk : k ≤ d) :
    (entropyLaw M).real {e | e % d < k} - (k : ℝ) / d =
      ((d : ℝ) * min (M % d) k - (M % d : ℕ) * (k : ℝ)) / (M * d) := by
  rw [entropyLaw_mod M d k hd hk]
  have hm : (M : ℝ) = (M / d : ℕ) * (d : ℝ) + (M % d : ℕ) := by
    exact_mod_cast (by simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div M d).symm)
  rw [div_sub_div _ _ (Nat.cast_ne_zero.mpr hM.ne') (Nat.cast_ne_zero.mpr hd.ne')]
  congr 1
  push_cast
  rw [hm]
  simp only [add_mul]
  rw [mul_right_comm ((M / d : ℕ) : ℝ) (k : ℝ) (d : ℝ),
    add_sub_add_left_eq_sub, mul_comm]

/-- Divisibility eliminates the incomplete residue block and its bias. -/
theorem entropyLaw_mod_of_dvd (M d k : ℕ) (hM : 0 < M) (hd : 0 < d)
    (hk : k ≤ d) (hdiv : d ∣ M) :
    (entropyLaw M).real {e | e % d < k} = (k : ℝ) / d := by
  have h := mod_bias M d k hM hd hk
  simp only [Nat.mod_eq_zero_of_dvd hdiv, zero_le, inf_of_le_left, CharP.cast_eq_zero, mul_zero,
    zero_mul, sub_self, zero_div] at h
  exact sub_eq_zero.mp h

end FloatLib.Numerics.Quantization.Stochastic
