/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Stochastic.Compose

/-!
# Dot products with separately rounded multiplication and addition

Each step consumes two independent fresh words. The product and accumulator
rounders may differ. The local proof conditions on the product word before
rounding the addition, so it does not assume independence of the two errors.
The outer schedule is the same arbitrary-length evaluator used for sums.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Round a term, then add it to the accumulator with a second rounding. -/
def addRoundedTerm {E F : Type*} (rp : Rounder E) (ra : Rounder F)
    (s p : ℚ) (e : E × F) : ℚ :=
  ra.round e.2 (s + rp.round e.1 p)

/-- One step of an ordinary multiply-then-add dot product; the product is rounded first. -/
def dotStep {E F : Type*} (rp : Rounder E) (ra : Rounder F) (x y : ℕ → ℚ)
    (k : ℕ) (s : ℚ) (e : E × F) : ℚ :=
  addRoundedTerm rp ra s (x k * y k) e

/-- Executable dot product with one product and one addition rounding per term. -/
def roundedDot {E F : Type*} (rp : Rounder E) (ra : Rounder F) (x y : ℕ → ℚ)
    (initial : ℚ) (n : ℕ) : History (E × F) n → ℚ :=
  run (dotStep rp ra x y) initial n

/-- All product inputs and reached addition inputs are admissible. -/
def DotSafe {E F : Type*} (rp : Rounder E) (ra : Rounder F) (x y : ℕ → ℚ)
    (initial : ℚ) (n : ℕ) : Prop :=
  ∀ k, k < n →
    rp.Admissible (x k * y k) ∧
      ∀ (h : History (E × F) k) (e : E),
        ra.Admissible (roundedDot rp ra x y initial k h + rp.round e (x k * y k))

/-- The addition proxy is bounded uniformly over past and current product words. -/
def DotBudget {E F : Type*} (rp : Rounder E) (ra : Rounder F) (x y : ℕ → ℚ)
    (initial : ℚ) (n : ℕ) (c : ℕ → ℝ≥0) : Prop :=
  ∀ k, k < n → ∀ (h : History (E × F) k) (e : E),
    ra.proxy (roundedDot rp ra x y initial k h + rp.round e (x k * y k)) ≤ c k

variable {E F : Type*} [Finite E] [Finite F]
  [MeasurableSpace E] [MeasurableSpace F]
  [MeasurableSingletonClass E] [MeasurableSingletonClass F]
  {ν : Measure E} {ρ : Measure F} [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

/-- Two local rounding errors have additive budgets after conditioning on the first word. -/
theorem addRoundedTerm_certificate (rp : Rounder E) (ra : Rounder F)
    (hp : rp.Law ν) (ha : ra.Law ρ) (s p : ℚ) (c : ℝ≥0)
    (hps : rp.Admissible p) (has : ∀ e, ra.Admissible (s + rp.round e p))
    (hac : ∀ e, ra.proxy (s + rp.round e p) ≤ c) :
    Certificate (ν.prod ρ) (fun e ↦ (addRoundedTerm rp ra s p e : ℝ))
      (s + p : ℚ) (rp.proxy p + c) := by
  have hproduct : Certificate ν (fun e ↦ (rp.round e p : ℝ)) p (rp.proxy p) :=
    ⟨hp.mean p hps, hp.second p hps, hp.mgf p hps⟩
  simpa only [roundedAdd, addRoundedTerm, Rat.cast_add, add_comm] using
    roundedAdd_certificate ra ha (fun e ↦ rp.round e p) p (rp.proxy p) hproduct s c
      (fun e ↦ by simpa only [add_comm] using has e)
      (fun e ↦ by simpa only [add_comm] using hac e)

/-- The dot-product increment is the two-rounding local error. -/
theorem dot_increment {E F : Type*} (rp : Rounder E) (ra : Rounder F) (x y : ℕ → ℚ)
    (initial : ℚ) (k : ℕ) (h : History (E × F) k) (e : E × F) :
    increment (fun q : ℚ ↦ (q : ℝ)) (dotStep rp ra x y) initial
      (fun i ↦ ((x i * y i : ℚ) : ℝ)) k (h, e) =
      (addRoundedTerm rp ra (roundedDot rp ra x y initial k h) (x k * y k) e : ℝ) -
        (roundedDot rp ra x y initial k h + x k * y k : ℚ) := by
  simp only [increment, dotStep, roundedDot, Rat.cast_add]
  ring

/-- Every finite multiply-then-add loop has exact mean and additive stochastic budgets. -/
theorem dot_certificate (rp : Rounder E) (ra : Rounder F)
    (hp : rp.Law ν) (ha : ra.Law ρ) (x y : ℕ → ℚ)
    (initial : ℚ) (n : ℕ) (c : ℕ → ℝ≥0)
    (hs : DotSafe rp ra x y initial n) (hc : DotBudget rp ra x y initial n c) :
    Certificate (historyLaw (ν.prod ρ) n)
      (fun h ↦ (roundedDot rp ra x y initial n h : ℝ))
      ((initial : ℝ) + ∑ i ∈ Finset.range n, ((x i * y i : ℚ) : ℝ))
      (∑ i ∈ Finset.range n, (rp.proxy (x i * y i) + c i)) := by
  have hlocal (k : ℕ) (hk : k < n) (h : History (E × F) k) :=
    addRoundedTerm_certificate rp ra hp ha (roundedDot rp ra x y initial k h)
      (x k * y k) (c k) (hs k hk).1 ((hs k hk).2 h) (hc k hk h)
  have hm : ∀ k, k < n → ∀ h,
      ∫ e, increment (fun q : ℚ ↦ (q : ℝ)) (dotStep rp ra x y) initial
        (fun i ↦ ((x i * y i : ℚ) : ℝ)) k (h, e) ∂ν.prod ρ = 0 := by
    intro k hk h
    simp_rw [dot_increment]
    rw [integral_sub Integrable.of_finite (integrable_const _), (hlocal k hk h).mean]
    simp
  refine ⟨mean_run _ _ _ _ n hm, ?_, ?_⟩
  · have hv : ∀ k, k < n → ∀ h,
        ∫ e, (increment (fun q : ℚ ↦ (q : ℝ)) (dotStep rp ra x y) initial
          (fun i ↦ ((x i * y i : ℚ) : ℝ)) k (h, e)) ^ 2 ∂ν.prod ρ ≤
            ((rp.proxy (x k * y k) + c k : ℝ≥0) : ℝ) := by
      intro k hk h
      simpa only [dot_increment] using (hlocal k hk h).second
    simpa only [error, roundedDot, NNReal.coe_sum] using
      second_moment_error (fun q : ℚ ↦ (q : ℝ)) (dotStep rp ra x y) initial
        (fun i ↦ ((x i * y i : ℚ) : ℝ)) n hm
        (fun i ↦ ((rp.proxy (x i * y i) + c i : ℝ≥0) : ℝ)) hv
  · have hg : ∀ k, k < n → ∀ h, HasSubgaussianMGF
        (fun e ↦ increment (fun q : ℚ ↦ (q : ℝ)) (dotStep rp ra x y) initial
          (fun i ↦ ((x i * y i : ℚ) : ℝ)) k (h, e))
        (rp.proxy (x k * y k) + c k) (ν.prod ρ) := by
      intro k hk h
      simpa only [dot_increment] using (hlocal k hk h).mgf
    exact subgaussian_error _ _ _ _ _ n hg

/-- Automatically inferred addition proxy, over actual past states and product outcomes. -/
noncomputable def dotBudget (rp : Rounder E) (ra : Rounder F) (x y : ℕ → ℚ)
    (initial : ℚ) (k : ℕ) : ℝ≥0 :=
  finiteBudget (fun z : History (E × F) k × E ↦
    ra.proxy (roundedDot rp ra x y initial k z.1 + rp.round z.2 (x k * y k)))

/-- The dot-product certificate with an automatic finite maximum as its local budget. -/
theorem dot_certificate_auto (rp : Rounder E) (ra : Rounder F)
    (hp : rp.Law ν) (ha : ra.Law ρ) (x y : ℕ → ℚ)
    (initial : ℚ) (n : ℕ) (hs : DotSafe rp ra x y initial n) :
    Certificate (historyLaw (ν.prod ρ) n)
      (fun h ↦ (roundedDot rp ra x y initial n h : ℝ))
      ((initial : ℝ) + ∑ i ∈ Finset.range n, ((x i * y i : ℚ) : ℝ))
      (∑ i ∈ Finset.range n, (rp.proxy (x i * y i) + dotBudget rp ra x y initial i)) :=
  dot_certificate rp ra hp ha x y initial n _ hs (fun k _ h e ↦
    le_finiteBudget (fun z : History (E × F) k × E ↦
      ra.proxy (roundedDot rp ra x y initial k z.1 + rp.round z.2 (x k * y k))) (h, e))

end FloatLib.Numerics.Quantization.Stochastic
