/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Stochastic rounding between two real neighbors

`cellLaw` is mathlib's Bernoulli measure on two endpoints, with probability proportional to
distance from the opposite endpoint. Its mean is the input, its variance is the product of
the two distances, and its error is strictly smaller than the cell width almost surely.
The endpoints may come from any numerical format. Identifying them as consecutive
representable values and refining an executable rounder are separate obligations.

`bias_bernoulli` accounts for a changed upper probability and arbitrary output policies,
including clipping and flushing. It assumes real-valued outputs; infinities and NaNs do
not acquire a real numerical expectation through this theorem.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Probability of the upper endpoint of an in-range cell. -/
noncomputable def upProb (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    unitInterval :=
  ⟨(x - a) / (b - a),
    div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hab.le),
    (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right hx.2 a)⟩

/-- Ideal stochastic rounding on an arbitrary nondegenerate real cell. -/
noncomputable def cellLaw (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    Measure ℝ :=
  bernoulliMeasure b a (upProb a b x hab hx)

/-- The law of one stochastic rounding inside a cell is a probability measure. -/
instance (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    IsProbabilityMeasure (cellLaw a b x hab hx) := by
  unfold cellLaw
  infer_instance

/-- Integrating any observation reduces to its two endpoint values. -/
theorem integral_cellLaw (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b)
    (f : ℝ → ℝ) :
    ∫ y, f y ∂cellLaw a b x hab hx =
      (x - a) / (b - a) * f b + (1 - (x - a) / (b - a)) * f a := by
  exact integral_bernoulliMeasure b a (upProb a b x hab hx) f

/-- Ideal stochastic rounding preserves an in-range input in expectation. -/
theorem mean_cellLaw (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ∫ y, y ∂cellLaw a b x hab hx = x := by
  rw [integral_cellLaw]
  calc
    (x - a) / (b - a) * b + (1 - (x - a) / (b - a)) * a =
        (x - a) / (b - a) * (b - a) + a := by
      rw [sub_mul, one_mul, mul_sub]
      abel
    _ = x := by rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne'), sub_add_cancel]

/-- Exact second central moment, including inputs equal to an endpoint. -/
theorem second_moment_cellLaw (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ∫ y, (y - x) ^ 2 ∂cellLaw a b x hab hx = (x - a) * (b - x) := by
  rw [integral_cellLaw, one_sub_div (sub_ne_zero.mpr hab.ne'),
    sub_sub_sub_cancel_right, div_mul_eq_mul_div, div_mul_eq_mul_div,
    ← add_div, sub_sq_comm a x]
  calc
    ((x - a) * (b - x) ^ 2 + (b - x) * (x - a) ^ 2) / (b - a) =
        ((x - a) * (b - x) * ((b - x) + (x - a))) / (b - a) := by
      congr 1
      rw [mul_add, sq, sq]
      ac_rfl
    _ = (x - a) * (b - x) := by
      rw [sub_add_sub_cancel, mul_div_cancel_right₀ _ (sub_ne_zero.mpr hab.ne')]

/-- The second central moment is the variance in mathlib's measure-theoretic sense. -/
theorem variance_cellLaw (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    variance (fun y : ℝ ↦ y) (cellLaw a b x hab hx) = (x - a) * (b - x) := by
  rw [variance_eq_integral (X := fun y : ℝ ↦ y) (by fun_prop), mean_cellLaw]
  exact second_moment_cellLaw a b x hab hx

/-- The sharp cellwise variance bound is one quarter of the squared gap. -/
theorem variance_cellLaw_le (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    variance (fun y : ℝ ↦ y) (cellLaw a b x hab hx) ≤ (b - a) ^ 2 / 4 := by
  rw [variance_cellLaw]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
  simpa only [mul_assoc, mul_comm, mul_left_comm, sub_add_sub_cancel'] using
    four_mul_le_sq_add (x - a) (b - x)

/-- The upper neighbor has probability equal to the discarded fraction. -/
theorem cellLaw_upper (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    (cellLaw a b x hab hx).real {b} = (x - a) / (b - a) := by
  exact bernoulliMeasure_real_apply_of_mem_of_notMem (upProb a b x hab hx)
    (measurableSet_singleton b) rfl hab.ne

/-- The lower neighbor receives the complementary probability. -/
theorem cellLaw_lower (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    (cellLaw a b x hab hx).real {a} = 1 - (x - a) / (b - a) := by
  exact bernoulliMeasure_real_apply_of_notMem_of_mem (upProb a b x hab hx)
    (measurableSet_singleton a) hab.ne' rfl

/-- A representable lower endpoint is fixed with probability one. -/
theorem cellLaw_left (a b : ℝ) (hab : a < b) :
    cellLaw a b a hab ⟨le_rfl, hab.le⟩ = Measure.dirac a := by
  have h : upProb a b a hab ⟨le_rfl, hab.le⟩ = 0 := by
    apply Subtype.ext
    simp [upProb]
  simp [cellLaw, h]

/-- A representable upper endpoint is fixed with probability one. -/
theorem cellLaw_right (a b : ℝ) (hab : a < b) :
    cellLaw a b b hab ⟨hab.le, le_rfl⟩ = Measure.dirac b := by
  have h : upProb a b b hab ⟨hab.le, le_rfl⟩ = 1 := by
    apply Subtype.ext
    simp [upProb, ne_of_gt (sub_pos.mpr hab)]
  simp [cellLaw, h]

/-- A Bernoulli draw belongs to its pair of endpoints almost surely. -/
theorem ae_bernoulli_endpoints (a b : ℝ) (p : unitInterval) :
    ∀ᵐ y ∂bernoulliMeasure b a p, y = a ∨ y = b := by
  rw [bernoulliMeasure_def, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure (by simp [MeasureTheory.ae_dirac_eq]) _
  · exact Measure.ae_smul_measure (by simp [MeasureTheory.ae_dirac_eq]) _

/-- The strict error bound ignores the zero-mass opposite endpoint at an exact input. -/
theorem ae_error_lt_gap (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ∀ᵐ y ∂cellLaw a b x hab hx, |y - x| < b - a := by
  rcases hx.1.eq_or_lt with h | h
  · subst x
    rw [cellLaw_left]
    simpa [MeasureTheory.ae_dirac_eq] using sub_pos.mpr hab
  rcases hx.2.eq_or_lt with h' | h'
  · subst x
    rw [cellLaw_right]
    simpa [MeasureTheory.ae_dirac_eq] using sub_pos.mpr hab
  filter_upwards [ae_bernoulli_endpoints a b (upProb a b x hab hx)] with y hy
  rcases hy with rfl | rfl
  · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr h)]
    exact sub_lt_sub_right h' _
  · rw [abs_of_pos (sub_pos.mpr h')]
    exact sub_lt_sub_left h _

/-- Exact bias under any finite real-valued output policy and any upper probability. -/
theorem bias_bernoulli (a b x : ℝ) (p : unitInterval) (f : ℝ → ℝ) :
    (∫ y, f y ∂bernoulliMeasure b a p) - x =
      (p : ℝ) * f b + (1 - p) * f a - x := by
  rw [integral_bernoulliMeasure]
  rfl

/-- Changing the upper probability changes the mean by that probability error times the gap. -/
theorem mean_bias (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b)
    (p : unitInterval) :
    (∫ y, y ∂bernoulliMeasure b a p) - x =
      ((p : ℝ) - upProb a b x hab hx) * (b - a) := by
  rw [integral_bernoulliMeasure]
  change (p : ℝ) * b + (1 - p) * a - x =
    ((p : ℝ) - (x - a) / (b - a)) * (b - a)
  rw [sub_mul, sub_mul, one_mul, div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne'), mul_sub]
  abel

/-- A measurable event implements a two-point law with its actual event probability. -/
theorem hasLaw_choice {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Set Ω) [DecidablePred (· ∈ s)] (hs : MeasurableSet s)
    (a b : ℝ) :
    HasLaw (fun ω ↦ if ω ∈ s then b else a)
      (bernoulliMeasure b a ⟨μ.real s, by simp⟩) μ := by
  let p : unitInterval := ⟨μ.real s, by simp⟩
  have h := hasLaw_indicator_one_bernoulliMeasure (M := ℝ) (P := μ)
    hs.nullMeasurableSet
  have hf : HasLaw (fun y : ℝ ↦ a + (b - a) * y) (bernoulliMeasure b a p)
      (bernoulliMeasure 1 0 p) := by
    refine ⟨by fun_prop, ?_⟩
    simp [map_bernoulliMeasure]
  convert hf.comp h using 1
  ext ω
  simp only [Function.comp_apply, Set.indicator_apply]
  split_ifs <;> simp

end FloatLib.Numerics.Quantization.Stochastic
