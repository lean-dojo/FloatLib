/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Stochastic.Realization
public import FloatLib.Numerics.Quantization.Stochastic.Tail

/-!
# Rounding rules for executable rational arithmetic

The data in `Rounder` describe an actual operation, its admissible exact inputs,
and a rational cell width. `Rounder.Law` records the three local consequences
needed by sequential arithmetic. `law_of_cell` derives this contract directly
from the common `HasLaw` cell interface, for any rational grid or implementation.
The binary adapter separately constructs it from the actual policy runtime.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Executable rational rounding together with the domain and width of its local rule. -/
structure Rounder (E : Type*) where
  /-- Consume one entropy word and round an exact rational. -/
  round : E → ℚ → ℚ
  /-- Exact inputs for which the proved unbiased rule applies. -/
  Admissible : ℚ → Prop
  /-- A rational upper bound for the width of the rounding cell. -/
  width : ℚ → ℚ

/-- Squared half width, expressed as a nonnegative MGF proxy. -/
noncomputable def Rounder.proxy {E : Type*} (r : Rounder E) (x : ℚ) : ℝ≥0 :=
  (‖(r.width x : ℝ)‖₊ / 2) ^ 2

/-- The MGF proxy denotes one quarter of the squared rational width. -/
theorem Rounder.coe_proxy {E : Type*} (r : Rounder E) (x : ℚ) :
    (r.proxy x : ℝ) = (r.width x : ℝ) ^ 2 / 4 := by
  change (‖(r.width x : ℝ)‖ / 2) ^ 2 = _
  rw [Real.norm_eq_abs, div_pow, sq_abs]
  norm_num

/-- An exact rational width check gives a nonnegative real proxy bound. -/
theorem Rounder.proxy_le_of_rat {E : Type*} (r : Rounder E) (x q : ℚ)
    (h : r.width x ^ 2 / 4 ≤ q) :
    r.proxy x ≤ Real.toNNReal (q : ℝ) := by
  apply NNReal.le_toNNReal_of_coe_le
  rw [r.coe_proxy]
  exact_mod_cast h

/-- Local correctness is proved for a named entropy law, never inferred from a mode flag. -/
structure Rounder.Law {E : Type*} [MeasurableSpace E] (r : Rounder E)
    (ν : Measure E) : Prop where
  /-- Conditional mean of the delivered rational. -/
  mean : ∀ x, r.Admissible x → (∫ e, (r.round e x : ℝ) ∂ν) = x
  /-- Conditional second moment of its rounding error. -/
  second : ∀ x, r.Admissible x →
    (∫ e, ((r.round e x : ℝ) - x) ^ 2 ∂ν) ≤ r.proxy x
  /-- Conditional centered exponential-moment bound. -/
  mgf : ∀ x, r.Admissible x →
    HasSubgaussianMGF (fun e ↦ (r.round e x : ℝ) - x) (r.proxy x) ν

/-- Any implementation of the common cell law supplies all local arithmetic rules. -/
theorem Rounder.law_of_cell {E : Type*} [MeasurableSpace E] {ν : Measure E}
    [IsProbabilityMeasure ν] (r : Rounder E) (a b : ℚ → ℝ)
    (hab : ∀ x, r.Admissible x → a x < b x)
    (hx : ∀ x, r.Admissible x → (x : ℝ) ∈ Set.Icc (a x) (b x))
    (hw : ∀ x, r.Admissible x → b x - a x = (r.width x : ℝ))
    (hlaw : ∀ x h, HasLaw (fun e ↦ (r.round e x : ℝ))
      (cellLaw (a x) (b x) x (hab x h) (hx x h)) ν) :
    r.Law ν where
  mean x h := by
    exact (hlaw x h).integral_comp (f := fun y : ℝ ↦ y) (by fun_prop) |>.trans
      (mean_cellLaw _ _ _ _ _)
  second x h := by
    simpa only [r.coe_proxy, ← hw x h] using second_moment_of_cell_le (hlaw x h)
  mgf x h := by
    simpa only [Rounder.proxy, ← hw x h] using subgaussian_of_cell (hlaw x h)

/-- A proved program result: exact mean, additive second-moment budget and centered MGF. -/
structure Certificate {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (actual : E → ℝ) (reference : ℝ) (budget : ℝ≥0) : Prop where
  /-- Mean against the exact deterministic reference. -/
  mean : (∫ e, actual e ∂ν) = reference
  /-- Second moment of the final error. -/
  second : (∫ e, (actual e - reference) ^ 2 ∂ν) ≤ budget
  /-- Centered exponential-moment bound of the final error. -/
  mgf : HasSubgaussianMGF (fun e ↦ actual e - reference) budget ν

/-- A proved larger budget preserves all three parts of the certificate. -/
theorem Certificate.mono {E : Type*} [MeasurableSpace E] {ν : Measure E}
    {actual : E → ℝ} {reference : ℝ} {c d : ℝ≥0}
    (h : Certificate ν actual reference c) (hcd : c ≤ d) :
    Certificate ν actual reference d :=
  ⟨h.mean, h.second.trans (NNReal.coe_le_coe.mpr hcd), subgaussian_mono h.mgf hcd⟩

/-- Every generated certificate proves the explicit two-sided exponential tail. -/
theorem Certificate.tail {E : Type*} [MeasurableSpace E] {ν : Measure E}
    {actual : E → ℝ} {reference : ℝ} {budget : ℝ≥0}
    (h : Certificate ν actual reference budget) (ε : ℝ) (hε : 0 ≤ ε) :
    ν.real {e | ε ≤ |actual e - reference|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * budget)) :=
  tail_abs h.mgf ε hε

/-- Positive-budget certificates prove the requested square-root logarithmic radius. -/
theorem Certificate.confidence {E : Type*} [MeasurableSpace E] {ν : Measure E}
    {actual : E → ℝ} {reference : ℝ} {budget : ℝ≥0}
    (h : Certificate ν actual reference budget) (hc : 0 < budget)
    (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ν.real {e | Real.sqrt (2 * budget * Real.log (2 / δ)) ≤
      |actual e - reference|} ≤ δ :=
  tail_delta h.mgf hc δ hδ hδ₁

/-- A zero budget means exact output almost surely. -/
theorem Certificate.exact_of_zero {E : Type*} [MeasurableSpace E] {ν : Measure E}
    {actual : E → ℝ} {reference : ℝ}
    (h : Certificate ν actual reference 0) :
    actual =ᵐ[ν] fun _ ↦ reference := by
  filter_upwards [h.mgf.ae_eq_zero_of_hasSubgaussianMGF_zero] with e he
  exact sub_eq_zero.mp he

end FloatLib.Numerics.Quantization.Stochastic
