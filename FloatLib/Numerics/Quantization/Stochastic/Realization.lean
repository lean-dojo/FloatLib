/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Stochastic.Cell
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Local error rules for realized stochastic rounding

The contract is mathlib's `HasLaw`, applied to the decoded output of the actual
operation. Every implementation that realizes the cell law inherits the same
centered error, exact second moment, and Hoeffding MGF bound. The law must be
proved for the chosen entropy distribution; finite-bit rounding does not
satisfy it merely because its rounding-mode field says `stochastic`.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- A valid MGF proxy may be enlarged: the exponential bound is monotone in it. -/
theorem subgaussian_mono {E : Type*} [MeasurableSpace E] {ν : Measure E}
    {R : E → ℝ} {c d : ℝ≥0} (h : HasSubgaussianMGF R c ν) (hcd : c ≤ d) :
    HasSubgaussianMGF R d ν where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcd (sq_nonneg t))
      (by norm_num)))

variable {E : Type*} [MeasurableSpace E] {ν : Measure E}
  {R : E → ℝ} {a b x : ℝ} {hab : a < b} {hx : x ∈ Set.Icc a b}

/-- A realized ideal cell has the same centered local error as the abstract law. -/
theorem mean_error_of_cell (h : HasLaw R (cellLaw a b x hab hx) ν) :
    ∫ e, R e - x ∂ν = 0 := by
  calc
    _ = ∫ y, y - x ∂cellLaw a b x hab hx := h.integral_comp (by fun_prop)
    _ = 0 := ?_
  have hi : Integrable (fun y : ℝ ↦ y) (cellLaw a b x hab hx) :=
    integrable_bernoulliMeasure _ _ _ _
  rw [integral_sub hi (integrable_const _),
    mean_cellLaw, integral_const, probReal_univ, one_smul, sub_self]

/-- Realization transfers the exact variance, without an independent-error assumption. -/
theorem second_moment_of_cell (h : HasLaw R (cellLaw a b x hab hx) ν) :
    ∫ e, (R e - x) ^ 2 ∂ν = (x - a) * (b - x) := by
  exact (h.integral_comp (f := fun y ↦ (y - x) ^ 2) (by fun_prop)).trans
    (second_moment_cellLaw a b x hab hx)

/-- Hoeffding's lemma uses the full cell width and yields its sharp range-based proxy. -/
theorem subgaussian_of_cell [IsProbabilityMeasure ν]
    (h : HasLaw R (cellLaw a b x hab hx) ν) :
    HasSubgaussianMGF (fun e ↦ R e - x) ((‖b - a‖₊ / 2) ^ 2) ν := by
  have hb : ∀ᵐ e ∂ν, R e - x ∈ Set.Icc (a - x) (b - x) := by
    apply (h.ae_iff (p := fun y ↦ y - x ∈ Set.Icc (a - x) (b - x))
      (measurableSet_Icc.mem.comp (measurable_id.sub_const x))).mpr
    filter_upwards [ae_bernoulli_endpoints a b (upProb a b x hab hx)] with y hy
    rcases hy with rfl | rfl
    · exact ⟨le_rfl, sub_le_sub_right hab.le _⟩
    · exact ⟨sub_le_sub_right hab.le _, le_rfl⟩
  have hg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (h.aemeasurable.sub_const x) hb (mean_error_of_cell h)
  simpa only [sub_sub_sub_cancel_right] using hg

/-- The exact variance is bounded by the same squared half-gap budget. -/
theorem second_moment_of_cell_le (h : HasLaw R (cellLaw a b x hab hx) ν) :
    ∫ e, (R e - x) ^ 2 ∂ν ≤ (b - a) ^ 2 / 4 := by
  rw [second_moment_of_cell h]
  linarith [sq_nonneg (2 * x - a - b)]

end FloatLib.Numerics.Quantization.Stochastic
