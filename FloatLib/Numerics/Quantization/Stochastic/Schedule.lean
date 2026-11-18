/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Stochastic.Fresh
public import FloatLib.Numerics.Quantization.Stochastic.Tail

/-!
# Stateful schedules with fresh finite entropy

`run` evaluates an arbitrary state transition once per entropy word. Its state type can
be a floating encoding, a tuple of registers, or another program state. `error` observes
that execution through a real decoder and compares it to deterministic exact increments.
All probabilistic conclusions are derived from the local errors of this actual evaluator.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u v

/-- Entropy words in execution order, represented by repeated products. -/
@[reducible] def History (E : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => History E n × E

/-- There are finitely many histories of words from a finite type. -/
instance {E : Type u} [Finite E] (n : ℕ) : Finite (History E n) := by
  induction n with
  | zero => exact inferInstanceAs (Finite PUnit)
  | succ n ih =>
    let := ih
    exact inferInstanceAs (Finite (History E n × E))

@[reducible] instance historyMeasurableSpace {E : Type u} [MeasurableSpace E] :
    (n : ℕ) → MeasurableSpace (History E n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n + 1 =>
    letI : MeasurableSpace (History E n) := historyMeasurableSpace (E := E) n
    inferInstanceAs (MeasurableSpace (History E n × E))

/-- A single history is measurable when a single word is. -/
instance {E : Type u} [MeasurableSpace E] [MeasurableSingletonClass E] (n : ℕ) :
    MeasurableSingletonClass (History E n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSingletonClass PUnit)
  | succ n ih =>
    let := ih
    exact inferInstanceAs (MeasurableSingletonClass (History E n × E))

/-- Independent fresh entropy is a product-measure premise of the execution. -/
noncomputable def historyLaw {E : Type u} [MeasurableSpace E] (ν : Measure E) :
    (n : ℕ) → Measure (History E n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => (historyLaw ν n).prod ν

/-- The law of a history of independent words is a probability measure. -/
instance historyLaw_probability {E : Type u} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (historyLaw ν n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | succ n ih =>
    let := ih
    exact inferInstanceAs (IsProbabilityMeasure ((historyLaw ν n).prod ν))

/-- The generic bounded-loop evaluator; no numerical semantics are built into its state. -/
def run {A : Type v} {E : Type u} (step : ℕ → A → E → A) (s : A) :
    (n : ℕ) → History E n → A
  | 0, _ => s
  | n + 1, z => step n (run step s n z.1) z.2

/-- Error in the decoded program output against its specified exact linear schedule. -/
def error {A : Type v} {E : Type u} (decode : A → ℝ) (step : ℕ → A → E → A)
    (s : A) (term : ℕ → ℝ) (n : ℕ) (h : History E n) : ℝ :=
  decode (run step s n h) - (decode s + ∑ i ∈ Finset.range n, term i)

/-- The local error is computed from the actual reachable state and transition. -/
def increment {A : Type v} {E : Type u} (decode : A → ℝ) (step : ℕ → A → E → A)
    (s : A) (term : ℕ → ℝ) (n : ℕ) (z : History E n × E) : ℝ :=
  decode (step n (run step s n z.1) z.2) - decode (run step s n z.1) - term n

/-- No transition has yet introduced an error. -/
@[simp] theorem error_zero {A : Type v} {E : Type u} (decode : A → ℝ)
    (step : ℕ → A → E → A) (s : A) (term : ℕ → ℝ) :
    error decode step s term 0 = 0 := by
  funext h
  simp [error, run]

/-- The exact error recurrence used once for every state type and operation family. -/
theorem error_succ {A : Type v} {E : Type u} (decode : A → ℝ)
    (step : ℕ → A → E → A) (s : A) (term : ℕ → ℝ) (n : ℕ) :
    error decode step s term (n + 1) =
      fun z ↦ error decode step s term n z.1 + increment decode step s term n z := by
  funext z
  simp only [error, increment, run, Finset.sum_range_succ]
  ring

variable {A : Type v} {E : Type u} [Finite E] [MeasurableSpace E]
  [MeasurableSingletonClass E] {ν : Measure E} [IsProbabilityMeasure ν]
  (decode : A → ℝ) (step : ℕ → A → E → A) (s : A) (term : ℕ → ℝ)

/-- Conditional centering of the actual transition implies a centered final error. -/
theorem mean_error (n : ℕ)
    (hm : ∀ k, k < n → ∀ h, ∫ e, increment decode step s term k (h, e) ∂ν = 0) :
    ∫ h, error decode step s term n h ∂historyLaw ν n = 0 := by
  induction n with
  | zero => simp [error, run, historyLaw]
  | succ n ih =>
    simp only [error_succ, historyLaw]
    rw [mean_fresh _ _ (hm n (Nat.lt_succ_self n))]
    exact ih (fun k hk ↦ hm k (Nat.lt_trans hk (Nat.lt_succ_self n)))

/-- The mean of decoded execution is its exact initial value plus the exact increments. -/
theorem mean_run (n : ℕ)
    (hm : ∀ k, k < n → ∀ h, ∫ e, increment decode step s term k (h, e) ∂ν = 0) :
    ∫ h, decode (run step s n h) ∂historyLaw ν n =
      decode s + ∑ i ∈ Finset.range n, term i := by
  have h := mean_error decode step s term n hm
  simp only [error] at h
  rw [integral_sub Integrable.of_finite (integrable_const _)] at h
  simpa only [integral_const, probReal_univ, one_smul] using sub_eq_zero.mp h

/-- Second moments add along the actual loop, with one budget per reached transition. -/
theorem second_moment_error (n : ℕ)
    (hm : ∀ k, k < n → ∀ h, ∫ e, increment decode step s term k (h, e) ∂ν = 0)
    (v : ℕ → ℝ)
    (hv : ∀ k, k < n → ∀ h, ∫ e, (increment decode step s term k (h, e)) ^ 2 ∂ν ≤ v k) :
    ∫ h, (error decode step s term n h) ^ 2 ∂historyLaw ν n ≤
      ∑ i ∈ Finset.range n, v i := by
  induction n with
  | zero => simp [error, run, historyLaw]
  | succ n ih =>
    simp only [error_succ, historyLaw, Finset.sum_range_succ]
    exact (second_moment_fresh_le _ _ (v n) (hm n (Nat.lt_succ_self n))
      (hv n (Nat.lt_succ_self n))).trans (add_le_add
        (ih (fun k hk ↦ hm k (Nat.lt_trans hk (Nat.lt_succ_self n)))
          (fun k hk ↦ hv k (Nat.lt_trans hk (Nat.lt_succ_self n)))) le_rfl)

/-- Conditional MGF budgets compose through the same evaluator. -/
theorem subgaussian_error (c : ℕ → ℝ≥0) (n : ℕ)
    (hc : ∀ k, k < n → ∀ h, HasSubgaussianMGF
      (fun e ↦ increment decode step s term k (h, e)) (c k) ν) :
    HasSubgaussianMGF (error decode step s term n)
      (∑ i ∈ Finset.range n, c i) (historyLaw ν n) := by
  induction n with
  | zero => simpa only [error_zero, Finset.sum_range_zero, historyLaw] using
      (HasSubgaussianMGF.zero (μ := Measure.dirac (PUnit.unit : History E 0)))
  | succ n ih =>
    simpa only [error_succ, historyLaw, Finset.sum_range_succ] using
      subgaussian_fresh
        (ih (fun k hk ↦ hc k (Nat.lt_trans hk (Nat.lt_succ_self n))))
        (hc n (Nat.lt_succ_self n))

end FloatLib.Numerics.Quantization.Stochastic
