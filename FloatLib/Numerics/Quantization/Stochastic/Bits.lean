/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Stochastic.Finite

/-!
# Adding random bits and truncating

For discarded fraction `k/d` and a uniform integer `e < M`, `addTrunc` adds `e/M`
and truncates. The usual `r`-bit implementation is the instance `M = 2^r`.
Its increment probability is `floor(k*M/d)/M`, with exact bias
`-((k*M) % d)/(d*M)`. This is a pointwise downward bias, not an average over inputs.
The same finite-choice law as modulo rounding supplies the distribution.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory

/-- Integer implementation of adding `e/M` to discarded fraction `k/d` and truncating. -/
def addTrunc (M d k e : ℕ) : ℕ :=
  (k * M + e * d) / (d * M)

private theorem quotient_le (M d k : ℕ) (hk : k ≤ d) :
    k * M / d ≤ M :=
  Nat.div_le_of_le_mul (Nat.mul_le_mul_right M hk)

/-- On the entropy range the executable quotient is a single threshold choice. -/
theorem addTrunc_eq (M d k e : ℕ) (hM : 0 < M) (hd : 0 < d)
    (hk : k ≤ d) (he : e < M) :
    addTrunc M d k e = if M - k * M / d ≤ e then 1 else 0 := by
  have hq := quotient_le M d k hk
  have hdiv : (k * M + e * d) / d = k * M / d + e :=
    Nat.add_mul_div_right _ _ hd
  have htest : d * M ≤ k * M + e * d ↔ M - k * M / d ≤ e := by
    rw [Nat.mul_comm d M, ← Nat.le_div_iff_mul_le hd, hdiv]
    omega
  have hlt : k * M + e * d < 2 * (d * M) := by
    have h₁ := Nat.mul_le_mul_right M hk
    have h₂ := Nat.mul_lt_mul_of_pos_right he hd
    linarith
  unfold addTrunc
  split_ifs with h
  · have h₁ : 1 ≤ (k * M + e * d) / (d * M) :=
      (Nat.le_div_iff_mul_le (Nat.mul_pos hd hM)).mpr (by simpa using htest.mpr h)
    have h₂ : (k * M + e * d) / (d * M) < 2 :=
      (Nat.div_lt_iff_lt_mul (Nat.mul_pos hd hM)).mpr hlt
    omega
  · exact Nat.div_eq_of_lt (lt_of_not_ge (mt htest.mp h))

private theorem count_ge (M t : ℕ) :
    Nat.count (fun e ↦ t ≤ e) M = M - t := by
  rw [Nat.count_eq_card_filter_range]
  have h : (Finset.range M).filter (fun e ↦ t ≤ e) = Finset.Ico t M := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact and_comm
  rw [h, Nat.card_Ico]

/-- Exactly `floor(k*M/d)` entropy words produce a carry. -/
theorem count_addTrunc (M d k : ℕ) (hk : k ≤ d) :
    Nat.count (fun e ↦ M - k * M / d ≤ e) M = k * M / d := by
  rw [count_ge, Nat.sub_sub_self (quotient_le M d k hk)]

/-- Upper probability for the add-and-truncate implementation. -/
theorem entropyLaw_addTrunc (M d k : ℕ) (hk : k ≤ d) :
    (entropyLaw M).real {e | M - k * M / d ≤ e} = (k * M / d : ℕ) / (M : ℝ) := by
  rw [entropyLaw_real, count_addTrunc M d k hk]

/-- The executable integer addition-and-truncation has the common finite-choice law. -/
theorem hasLaw_addTrunc (M d k : ℕ) (hM : 0 < M) (hd : 0 < d) (hk : k ≤ d) :
    HasLaw (fun e ↦ (addTrunc M d k e : ℝ))
      (bernoulliMeasure 1 0
        ⟨(k * M / d : ℕ) / (M : ℝ),
          div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
          (div_le_one (Nat.cast_pos.mpr hM)).mpr
            (Nat.cast_le.mpr (Nat.div_le_of_le_mul (Nat.mul_le_mul_right M hk)))⟩)
      (entropyLaw M) := by
  simpa only [count_addTrunc M d k hk] using
    (hasLaw_finite_choice M hM (fun e ↦ M - k * M / d ≤ e) 0 1).congr
    (show (fun e ↦ (addTrunc M d k e : ℝ)) =ᵐ[entropyLaw M]
      (fun e ↦ if M - k * M / d ≤ e then 1 else 0) from by
        filter_upwards [ae_entropyLaw_lt M] with e he
        simp only [addTrunc_eq M d k e hM hd hk he, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero])

/-- The carry mean is the truncated discarded fraction. -/
theorem addTrunc_mean (M d k : ℕ) (hM : 0 < M) (hd : 0 < d) (hk : k ≤ d) :
    (∫ e, (addTrunc M d k e : ℝ) ∂entropyLaw M) = (k * M / d : ℕ) / (M : ℝ) := by
  rw [(hasLaw_addTrunc M d k hM hd hk).integral_eq, integral_bernoulliMeasure]
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero]

/-- Exact probability bias of random addition, for every entropy width and rational fraction. -/
theorem addTrunc_bias (M d k : ℕ) (hM : 0 < M) (hd : 0 < d) (hk : k ≤ d) :
    (entropyLaw M).real {e | M - k * M / d ≤ e} - (k : ℝ) / d =
      -((k * M) % d : ℕ) / ((d : ℝ) * M) := by
  rw [entropyLaw_addTrunc M d k hk]
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hdr : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hsplit : (k : ℝ) * M = (k * M / d : ℕ) * (d : ℝ) + ((k * M) % d : ℕ) := by
    exact_mod_cast (by simpa [Nat.mul_comm, Nat.add_comm] using
      (Nat.mod_add_div (k * M) d).symm)
  rw [div_sub_div _ _ hMr.ne' hdr.ne', mul_comm (M : ℝ) (k : ℝ),
    hsplit, sub_add_eq_sub_sub, sub_self, zero_sub, mul_comm (M : ℝ) (d : ℝ)]

/-- With `r` random bits, the pointwise probability bias lies in `(-2⁻ʳ,0]`. -/
theorem bits_bias_bounds (r d k : ℕ) (hd : 0 < d) (hk : k ≤ d) :
    let bias := (entropyLaw (2 ^ r)).real {e | 2 ^ r - k * 2 ^ r / d ≤ e} - (k : ℝ) / d;
    -(1 / (2 ^ r : ℝ)) < bias ∧ bias ≤ 0 := by
  dsimp
  rw [addTrunc_bias (2 ^ r) d k (by positivity) hd hk]
  have hdr : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hMr : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have ht : (((k * 2 ^ r) % d : ℕ) : ℝ) < d := Nat.cast_lt.mpr (Nat.mod_lt _ hd)
  have ht₀ : (0 : ℝ) ≤ ((k * 2 ^ r) % d : ℕ) := Nat.cast_nonneg _
  push_cast
  constructor
  · rw [neg_div, neg_lt_neg_iff, div_mul_eq_div_div]
    exact div_lt_div_of_pos_right ((div_lt_one hdr).mpr ht) hMr
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht₀) (mul_pos hdr hMr).le

end FloatLib.Numerics.Quantization.Stochastic
