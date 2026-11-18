/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Quantization.Stochastic.MGF

/-!
# Exactness from a zero quadratic proxy

A uniform finite exponential-moment penalty cannot hide a nonzero error
when the quadratic proxy is zero. Exponential Markov and a countable union
of rational-threshold events prove almost-sure exactness. The penalty need
not vanish, so this also applies after conservative nonlinear composition.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic.MGFBound

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]
  {X : E → ℝ} {p : ℝ}

private theorem measure_pos_zero (h : MGFBound X 0 p μ) :
    μ {e | 0 < X e} = 0 := by
  have hs : {e | 0 < X e} = ⋃ q : {q : ℚ // 0 < q}, {e | (q.val : ℝ) ≤ X e} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists]
    constructor
    · intro he
      obtain ⟨q, hq, hqe⟩ := exists_rat_btwn he
      exact ⟨q, Rat.cast_pos.mp hq, hqe.le⟩
    · rintro ⟨q, hq, he⟩
      exact (Rat.cast_pos.mpr hq).trans_le he
  rw [hs, measure_iUnion_null_iff]
  intro q
  suffices hz : μ.real {e | (q.val : ℝ) ≤ X e} = 0 by
    simpa only [Measure.real, ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false] using hz
  have hl : Tendsto (fun t : ℝ ↦ exp (p - t * q.val)) atTop (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ ↦ t * (q.val : ℝ)) atTop atTop :=
      Tendsto.atTop_mul_const (Rat.cast_pos.mpr q.property) tendsto_id
    have he := (tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul (exp p)
    simpa only [sub_eq_add_neg, exp_add, mul_zero, Function.comp_def] using he
  apply le_antisymm
  · apply ge_of_tendsto hl
    apply eventually_atTop.2
    refine ⟨0, fun t ht ↦ ?_⟩
    simpa only [zero_mul, zero_div, add_zero] using h.chernoff q.val t ht
  · exact measureReal_nonneg

/-- A zero proxy forces almost-sure zero error, even with a nonzero finite penalty. -/
theorem exact_of_zero (h : MGFBound X 0 p μ) : X =ᵐ[μ] 0 := by
  have hn : MGFBound (fun e ↦ -X e) 0 p μ := by simpa using h.mul_const (-1)
  have hp := h.measure_pos_zero
  have hm := hn.measure_pos_zero
  apply nonpos_iff_eq_zero.1
  calc
    μ {e | X e ≠ 0} = μ ({e | -X e > 0} ∪ {e | X e > 0}) := by
      congr 1
      ext e
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · intro hne
        rcases lt_trichotomy (X e) 0 with h | h | h
        · exact Or.inl (by linarith)
        · exact False.elim (hne h)
        · exact Or.inr h
      · rintro (h | h) <;> linarith
    _ ≤ μ {e | -X e > 0} + μ {e | X e > 0} := measure_union_le _ _
    _ = 0 := by rw [hp, hm, add_zero]

end FloatLib.Numerics.Quantization.Stochastic.MGFBound
