/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Stochastic.Rounder
public import FloatLib.Numerics.Quantization.Stochastic.Schedule

/-!
# Sums with fresh stochastic rounding after every addition

`roundedSum` is the actual rational execution, not its reference. Its one loop
proof applies to any `Rounder` with a proved local law. Safety is required only
on reachable states of the finite prefix. A caller may supply uniform local
budgets, or use the finite maximum over those states without enumerating them
in the proof.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- One rounded addition, consuming exactly one fresh word. -/
def sumStep {E : Type*} (r : Rounder E) (term : ℕ → ℚ)
    (k : ℕ) (s : ℚ) (e : E) : ℚ :=
  r.round e (s + term k)

/-- A finite sum with stochastic rounding after every addition. -/
def roundedSum {E : Type*} (r : Rounder E) (term : ℕ → ℚ)
    (initial : ℚ) (n : ℕ) : History E n → ℚ :=
  run (sumStep r term) initial n

/-- Admissibility of exactly the inputs presented by a finite execution. -/
def SumSafe {E : Type*} (r : Rounder E) (term : ℕ → ℚ) (initial : ℚ) (n : ℕ) : Prop :=
  ∀ k, k < n → ∀ h : History E k,
    r.Admissible (roundedSum r term initial k h + term k)

/-- A deterministic proxy valid on all histories of a finite execution. -/
def SumBudget {E : Type*} (r : Rounder E) (term : ℕ → ℚ) (initial : ℚ)
    (n : ℕ) (c : ℕ → ℝ≥0) : Prop :=
  ∀ k, k < n → ∀ h : History E k,
    r.proxy (roundedSum r term initial k h + term k) ≤ c k

/-- The loop's increment is exactly the error of its next rounded addition. -/
theorem sum_increment {E : Type*} (r : Rounder E) (term : ℕ → ℚ) (initial : ℚ)
    (k : ℕ) (h : History E k) (e : E) :
    increment (fun q : ℚ ↦ (q : ℝ)) (sumStep r term) initial (fun i ↦ (term i : ℝ))
      k (h, e) =
      (r.round e (roundedSum r term initial k h + term k) : ℝ) -
        (roundedSum r term initial k h + term k : ℚ) := by
  simp only [increment, sumStep, roundedSum, Rat.cast_add]
  ring

variable {E : Type*} [Finite E] [MeasurableSpace E] [MeasurableSingletonClass E]
  {ν : Measure E} [IsProbabilityMeasure ν]

/-- The local law proves the sum's mean, second moment and MGF in one finite-prefix argument. -/
theorem sum_certificate (r : Rounder E) (hr : r.Law ν) (term : ℕ → ℚ)
    (initial : ℚ) (n : ℕ) (c : ℕ → ℝ≥0)
    (hs : SumSafe r term initial n) (hc : SumBudget r term initial n c) :
    Certificate (historyLaw ν n) (fun h ↦ (roundedSum r term initial n h : ℝ))
      ((initial : ℝ) + ∑ i ∈ Finset.range n, (term i : ℝ))
      (∑ i ∈ Finset.range n, c i) := by
  have hm : ∀ k, k < n → ∀ h,
      ∫ e, increment (fun q : ℚ ↦ (q : ℝ)) (sumStep r term) initial
        (fun i ↦ (term i : ℝ)) k (h, e) ∂ν = 0 := by
    intro k hk h
    simp_rw [sum_increment]
    rw [integral_sub Integrable.of_finite (integrable_const _), hr.mean _ (hs k hk h)]
    simp
  refine ⟨mean_run _ _ _ _ n hm, ?_, ?_⟩
  · have hv : ∀ k, k < n → ∀ h,
        ∫ e, (increment (fun q : ℚ ↦ (q : ℝ)) (sumStep r term) initial
          (fun i ↦ (term i : ℝ)) k (h, e)) ^ 2 ∂ν ≤ (c k : ℝ) := by
      intro k hk h
      simp_rw [sum_increment]
      exact (hr.second _ (hs k hk h)).trans (hc k hk h)
    simpa only [error, roundedSum, NNReal.coe_sum] using
      second_moment_error (fun q : ℚ ↦ (q : ℝ)) (sumStep r term) initial
        (fun i ↦ (term i : ℝ)) n hm (fun i ↦ (c i : ℝ)) hv
  · have hg : ∀ k, k < n → ∀ h, HasSubgaussianMGF
        (fun e ↦ increment (fun q : ℚ ↦ (q : ℝ)) (sumStep r term) initial
          (fun i ↦ (term i : ℝ)) k (h, e)) (c k) ν := by
      intro k hk h
      simp_rw [sum_increment]
      exact subgaussian_mono (hr.mgf _ (hs k hk h)) (hc k hk h)
    exact subgaussian_error _ _ _ _ c n hg

/-- Finite maximum of a nonnegative local proxy; no enumeration is performed by its proof. -/
noncomputable def finiteBudget {H : Type*} [Finite H] (c : H → ℝ≥0) : ℝ≥0 :=
  letI := Fintype.ofFinite H
  Finset.univ.sup c

/-- Every local proxy is bounded by its finite maximum. -/
theorem le_finiteBudget {H : Type*} [Finite H] (c : H → ℝ≥0) (h : H) :
    c h ≤ finiteBudget c := by
  let := Fintype.ofFinite H
  exact Finset.le_sup (f := c) (Finset.mem_univ h)

/-- A canonical, automatically inferred budget, over actual reachable prefix states. -/
noncomputable def sumBudget (r : Rounder E) (term : ℕ → ℚ) (initial : ℚ)
    (k : ℕ) : ℝ≥0 :=
  finiteBudget (fun h : History E k ↦ r.proxy (roundedSum r term initial k h + term k))

/-- The automatic budget needs no numerical inequality supplied by the user. -/
theorem sum_certificate_auto (r : Rounder E) (hr : r.Law ν) (term : ℕ → ℚ)
    (initial : ℚ) (n : ℕ) (hs : SumSafe r term initial n) :
    Certificate (historyLaw ν n) (fun h ↦ (roundedSum r term initial n h : ℝ))
      ((initial : ℝ) + ∑ i ∈ Finset.range n, (term i : ℝ))
      (∑ i ∈ Finset.range n, sumBudget r term initial i) :=
  sum_certificate r hr term initial n _ hs (fun k _ h ↦
    le_finiteBudget (fun h : History E k ↦ r.proxy (roundedSum r term initial k h + term k)) h)

end FloatLib.Numerics.Quantization.Stochastic
