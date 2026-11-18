/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Quantization.Stochastic.Schedule

/-!
# Exponential moments through nonlinear error bounds

`MGFBound X c p` means `E exp(t X) ≤ exp(p + c t²/2)` for every real `t`.
The penalty `p` permits errors that are not centered. In particular an
absolute contraction of a sub-Gaussian error keeps its proxy and adds
`log 2`, without asserting an unbiased nonlinear output. Fresh conditional
composition adds both proxies and penalties. Chernoff's inequality then
gives a one-sided tail, used for pairwise classification margins.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- A quadratic exponential-moment bound with an explicit multiplicative penalty. -/
structure MGFBound {E : Type*} [MeasurableSpace E] (X : E → ℝ)
    (c p : ℝ) (μ : Measure E) : Prop where
  /-- Every exponential moment of `X` exists. -/
  integrable_exp_mul : ∀ t : ℝ, Integrable (fun e ↦ exp (t * X e)) μ
  /-- The moment generating function is at most `exp (p + c * t ^ 2 / 2)`. -/
  mgf_le : ∀ t : ℝ, mgf X μ t ≤ exp (p + c * t ^ 2 / 2)

namespace MGFBound

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}
  {X Y : E → ℝ} {c p : ℝ}

/-- A centered sub-Gaussian error has no exponential penalty. -/
theorem of_subgaussian {v : ℝ≥0} (h : HasSubgaussianMGF X v μ) :
    MGFBound X v 0 μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := by simpa only [zero_add] using h.mgf_le t

/-- Pointwise equal errors have the same exponential-moment bound. -/
theorem congr (h : MGFBound X c p μ) (he : ∀ e, X e = Y e) :
    MGFBound Y c p μ := by
  have : X = Y := funext he
  rwa [← this]

/-- Scaling changes the quadratic proxy by the square of the scale. -/
theorem mul_const (h : MGFBound X c p μ) (a : ℝ) :
    MGFBound (fun e ↦ a * X e) (a ^ 2 * c) p μ where
  integrable_exp_mul t := by
    simpa only [mul_assoc] using h.integrable_exp_mul (t * a)
  mgf_le t := by
    have hm := h.mgf_le (t * a)
    simpa only [mgf, mul_assoc, show p + c * (t * a) ^ 2 / 2 =
      p + (a ^ 2 * c) * t ^ 2 / 2 by ring] using hm

/-- Outward bounds may enlarge either the quadratic proxy or the exponential penalty. -/
theorem mono {d q : ℝ} (h : MGFBound X c p μ) (hc : c ≤ d) (hp : p ≤ q) :
    MGFBound X d q μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (exp_le_exp.mpr
    (add_le_add hp (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (sq_nonneg t)) (by norm_num))))

/-- An absolute contraction adds at most `log 2`; no mean-preservation premise is used. -/
theorem of_abs_le [Finite E] [MeasurableSingletonClass E] [IsFiniteMeasure μ]
    (h : MGFBound X c p μ) (hY : ∀ e, |Y e| ≤ |X e|) :
    MGFBound Y c (p + log 2) μ where
  integrable_exp_mul _ := Integrable.of_finite
  mgf_le t := by
    have pointwise (e : E) :
        exp (t * Y e) ≤ exp (t * X e) + exp ((-t) * X e) := by
      have hab : t * Y e ≤ |t * X e| := by
        calc
          _ ≤ |t * Y e| := le_abs_self _
          _ = |t| * |Y e| := abs_mul _ _
          _ ≤ |t| * |X e| := mul_le_mul_of_nonneg_left (hY e) (abs_nonneg _)
          _ = |t * X e| := (abs_mul _ _).symm
      refine (exp_le_exp.mpr hab).trans ?_
      by_cases hx : 0 ≤ t * X e
      · rw [abs_of_nonneg hx]
        exact le_add_of_nonneg_right (exp_pos _).le
      · rw [abs_of_neg (lt_of_not_ge hx), neg_mul]
        exact le_add_of_nonneg_left (exp_pos _).le
    calc
      mgf Y μ t ≤ ∫ e, exp (t * X e) + exp ((-t) * X e) ∂μ :=
        integral_mono Integrable.of_finite Integrable.of_finite pointwise
      _ = mgf X μ t + mgf X μ (-t) :=
        integral_add (h.integrable_exp_mul t) (h.integrable_exp_mul (-t))
      _ ≤ exp (p + c * t ^ 2 / 2) + exp (p + c * (-t) ^ 2 / 2) :=
        add_le_add (h.mgf_le t) (h.mgf_le (-t))
      _ = exp (p + log 2 + c * t ^ 2 / 2) := by
        have he : exp (p + log 2 + c * t ^ 2 / 2) =
            2 * exp (p + c * t ^ 2 / 2) := by
          rw [show p + log 2 + c * t ^ 2 / 2 =
            log 2 + (p + c * t ^ 2 / 2) by ring, exp_add, exp_log (by norm_num)]
        rw [neg_sq, he]
        ring

/-- ReLU contracts absolute error even when it changes the mean. -/
theorem relu [Finite E] [MeasurableSingletonClass E] [IsFiniteMeasure μ]
    (h : MGFBound X c p μ) (z : ℝ) :
    MGFBound (fun e ↦ max (z + X e) 0 - max z 0) c (p + log 2) μ := by
  apply h.of_abs_le
  intro e
  have hm := abs_max_sub_max_le_max (z + X e) (0 : ℝ) z 0
  simpa using hm

/-- If every preactivation is nonnegative, ReLU retains the original error and penalty. -/
theorem relu_of_nonneg [Finite E] [MeasurableSingletonClass E] [IsProbabilityMeasure μ]
    (h : MGFBound X c p μ) (hz : ∫ e, X e ∂μ = 0) (z : ℝ)
    (hn : ∀ e, 0 ≤ z + X e) :
    MGFBound (fun e ↦ max (z + X e) 0 - max z 0) c p μ := by
  have hz' : 0 ≤ z := by
    have hi := integral_nonneg_of_ae (μ := μ) (Filter.Eventually.of_forall hn)
    rw [integral_add (integrable_const _) Integrable.of_finite, hz] at hi
    simpa using hi
  apply h.congr
  intro e
  rw [max_eq_left (hn e), max_eq_left hz']
  ring

/-- If every preactivation is nonpositive, its ReLU error is identically zero. -/
theorem relu_of_nonpos [Finite E] [MeasurableSingletonClass E] [IsProbabilityMeasure μ]
    (hz : ∫ e, X e ∂μ = 0) (z : ℝ) (hn : ∀ e, z + X e ≤ 0) :
    MGFBound (fun e ↦ max (z + X e) 0 - max z 0) 0 0 μ := by
  have hz' : z ≤ 0 := by
    have hi := integral_nonpos hn (μ := μ)
    rw [integral_add (integrable_const _) Integrable.of_finite, hz] at hi
    simpa using hi
  have he : (fun e ↦ max (z + X e) 0 - max z 0) = fun _ ↦ (0 : ℝ) := by
    funext e
    rw [max_eq_right (hn e), max_eq_right hz', sub_self]
  rw [he]
  exact of_subgaussian (HasSubgaussianMGF.fun_zero (μ := μ))

/-- A uniform conditional bound composes with the previous history by Fubini. -/
theorem fresh {H : Type*} [Finite H] [Finite E]
    [MeasurableSpace H] [MeasurableSingletonClass H] [MeasurableSingletonClass E]
    {ν : Measure H} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {A : H → ℝ} {D : H × E → ℝ} {a b d q : ℝ}
    (hA : MGFBound A a b ν) (hD : ∀ h, MGFBound (fun e ↦ D (h, e)) d q μ) :
    MGFBound (fun z ↦ A z.1 + D z) (a + d) (b + q) (ν.prod μ) where
  integrable_exp_mul _ := Integrable.of_finite
  mgf_le t := by
    have he : (fun z : H × E ↦ exp (t * (A z.1 + D z))) =
        (fun z ↦ exp (t * A z.1) * exp (t * D z)) := by
      funext z
      rw [mul_add, exp_add]
    rw [mgf, he, integral_prod _ Integrable.of_finite]
    simp_rw [integral_const_mul]
    calc
      _ ≤ ∫ h, exp (t * A h) * exp (q + d * t ^ 2 / 2) ∂ν := by
        apply integral_mono Integrable.of_finite Integrable.of_finite
        intro h
        exact mul_le_mul_of_nonneg_left ((hD h).mgf_le t) (exp_pos _).le
      _ ≤ exp (b + a * t ^ 2 / 2) * exp (q + d * t ^ 2 / 2) := by
        rw [integral_mul_const]
        exact mul_le_mul_of_nonneg_right (hA.mgf_le t) (exp_pos _).le
      _ = exp ((b + q) + (a + d) * t ^ 2 / 2) := by
        rw [← exp_add]
        congr 1
        ring

/-- Two independent errors give a difference with the sum of their proxies and penalties. -/
theorem independent_sub {F : Type*} [Finite E] [Finite F]
    [MeasurableSpace F] [MeasurableSingletonClass E] [MeasurableSingletonClass F]
    {ν : Measure F} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Y : F → ℝ} {d q : ℝ} (hX : MGFBound X c p μ) (hY : MGFBound Y d q ν) :
    MGFBound (fun e : E × F ↦ X e.1 - Y e.2) (c + d) (p + q) (μ.prod ν) := by
  have hn : MGFBound (fun e ↦ -Y e) d q ν := by
    simpa using hY.mul_const (-1)
  simpa only [sub_eq_add_neg] using hX.fresh
    (D := fun e : E × F ↦ -Y e.2) (μ := ν) (fun _ ↦ hn)

/-- Independent row errors add proxies and nonlinear penalties over any finite length. -/
theorem independent_sum [Finite E] [MeasurableSingletonClass E] [IsProbabilityMeasure μ]
    (term : ℕ → E → ℝ) (c p : ℕ → ℝ) (n : ℕ)
    (h : ∀ k, k < n → MGFBound (term k) (c k) (p k) μ) :
    MGFBound (run (fun k s e ↦ s + term k e) 0 n)
      (∑ k ∈ Finset.range n, c k) (∑ k ∈ Finset.range n, p k) (historyLaw μ n) := by
  induction n with
  | zero =>
    constructor
    · intro t
      change Integrable (fun _ : PUnit ↦ exp (t * 0)) (Measure.dirac PUnit.unit)
      exact integrable_const _
    · intro t
      simp [run, historyLaw, mgf]
  | succ n ih =>
    have hs := (ih (fun k hk ↦ h k (by omega))).fresh
      (D := fun z : History E n × E ↦ term n z.2) (μ := μ)
      (fun _ ↦ h n (by omega))
    simpa only [run, historyLaw, Finset.sum_range_succ] using hs

/-- Exponential Markov at any nonnegative parameter, before optimization. -/
theorem chernoff [IsFiniteMeasure μ] (h : MGFBound X c p μ)
    (ε t : ℝ) (ht : 0 ≤ t) :
    μ.real {e | ε ≤ X e} ≤ exp (p + c * t ^ 2 / 2 - t * ε) := by
  have hm := measure_ge_le_exp_mul_mgf ε ht (h.integrable_exp_mul t)
  refine hm.trans ?_
  calc
    _ ≤ exp (-t * ε) * exp (p + c * t ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (h.mgf_le t) (exp_pos _).le
    _ = exp (p + c * t ^ 2 / 2 - t * ε) := by
      rw [← exp_add]
      congr 1
      ring

/-- The optimized one-sided Chernoff bound includes the nonlinear penalty. -/
theorem tail [IsFiniteMeasure μ] (h : MGFBound X c p μ) (hc : 0 < c)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {e | ε ≤ X e} ≤ exp (p - ε ^ 2 / (2 * c)) := by
  have hm := h.chernoff ε (ε / c) (div_nonneg hε hc.le)
  have he : p + c * (ε / c) ^ 2 / 2 - (ε / c) * ε = p - ε ^ 2 / (2 * c) := by
    field_simp [hc.ne']
    ring
  rwa [he] at hm

/-- A confidence radius for one side, with the penalty added inside the logarithmic budget. -/
theorem confidence [IsFiniteMeasure μ] (h : MGFBound X c p μ)
    (hc : 0 < c) (hp : 0 ≤ p) (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    μ.real {e | sqrt (2 * c * (p + log (1 / δ))) ≤ X e} ≤ δ := by
  have hl : 0 ≤ log (1 / δ) := log_nonneg
    ((le_div_iff₀ hδ).mpr (by simpa using hδ₁.le))
  have hm := h.tail hc (sqrt (2 * c * (p + log (1 / δ)))) (sqrt_nonneg _)
  rw [sq_sqrt (by positivity)] at hm
  have he : p - 2 * c * (p + log (1 / δ)) / (2 * c) = -log (1 / δ) := by
    field_simp [hc.ne']
    ring
  rw [he, exp_neg, exp_log (div_pos (by norm_num) hδ)] at hm
  simpa using hm

end MGFBound
end FloatLib.Numerics.Quantization.Stochastic
