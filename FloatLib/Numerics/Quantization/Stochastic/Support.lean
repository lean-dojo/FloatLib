/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Quantization.Stochastic.Affine

/-!
# Finite support checks for all execution histories

A scalar support lists every possible output of one rounding without enumerating entropy.
`reach` propagates such lists through a loop: it contains every state the loop can be in after
`n` steps, for every entropy history (`run_mem_reach`). The supports of a rounded sum and of a
rounded dot product are instances. A finite check on these lists then proves the premises of the
arithmetic certificates, `SumSafe`, `DotSafe`, `AffineSafe` and the proxy budgets, for every
history, and `sum_certificate` and `affine_certificate` return a certificate whose budget is a
rational number. Lists may overapproximate and contain duplicates; coverage, rather than an exact
probability distribution, is what matters.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open scoped NNReal
open MeasureTheory

/-- The states a loop can be in after each number of steps, when `next k s` lists the possible
outcomes of step `k` at the state `s`. -/
def reach (next : ℕ → ℚ → List ℚ) (initial : ℚ) : ℕ → List ℚ
  | 0 => [initial]
  | n + 1 => (reach next initial n).flatMap (next n)

/-- A loop whose every step lands in the listed outcomes is, after `n` steps and for every
entropy history, in a listed state. -/
theorem run_mem_reach {E : Type*} (step : ℕ → ℚ → E → ℚ) (next : ℕ → ℚ → List ℚ)
    (hstep : ∀ k s e, step k s e ∈ next k s) (initial : ℚ) (n : ℕ) (h : History E n) :
    run step initial n h ∈ reach next initial n := by
  induction n with
  | zero => simp [run, reach]
  | succ n ih => exact List.mem_flatMap.mpr ⟨_, ih h.1, hstep n _ h.2⟩

/-- A finite enclosure of every scalar output, independently of its probability. -/
structure Rounder.Support {E : Type*} (r : Rounder E) where
  /-- A finite list of candidate outputs at the input `x`. -/
  values : ℚ → List ℚ
  /-- Every output at `x`, whatever the entropy, is in the list. -/
  covers : ∀ x e, r.round e x ∈ values x

namespace Rounder.Support

variable {E F : Type*} {r : Rounder E} {rp : Rounder E} {ra : Rounder F}

/-- All accumulators of a rounded sum that the support lists generate, up to the requested
length. -/
def sum (s : r.Support) (x : ℕ → ℚ) (initial : ℚ) : ℕ → List ℚ :=
  reach (fun k a ↦ s.values (a + x k)) initial

/-- The accumulator of every execution of a rounded sum is in its support. -/
theorem mem_sum (s : r.Support) (x : ℕ → ℚ) (initial : ℚ) (n : ℕ) (h : History E n) :
    roundedSum r x initial n h ∈ s.sum x initial n :=
  run_mem_reach (sumStep r x) _ (fun _ _ _ ↦ s.covers _ _) initial n h

/-- Checking the finitely many support inputs proves the safety of a sum for every entropy
history. -/
theorem sum_safe (s : r.Support) (x : ℕ → ℚ) (initial : ℚ) (n : ℕ)
    (hs : ∀ k : Fin n, ∀ a ∈ s.sum x initial k, r.Admissible (a + x k)) :
    SumSafe r x initial n :=
  fun k hk h ↦ hs ⟨k, hk⟩ _ (s.mem_sum x initial k h)

/-- Rational support checks certify a rounded sum at a supplied rational budget: `c k` bounds
the squared half width of the addition at step `k` on every listed accumulator. -/
theorem sum_certificate [Finite E] [MeasurableSpace E] [MeasurableSingletonClass E]
    {ν : Measure E} [IsProbabilityMeasure ν] (s : r.Support) (hr : r.Law ν)
    (x : ℕ → ℚ) (initial : ℚ) (n : ℕ) (c : ℕ → ℚ) (total : ℚ)
    (hs : ∀ k : Fin n, ∀ a ∈ s.sum x initial k, r.Admissible (a + x k))
    (hc : ∀ k : Fin n, ∀ a ∈ s.sum x initial k, r.width (a + x k) ^ 2 / 4 ≤ c k)
    (ht : ∑ k ∈ Finset.range n, c k ≤ total) :
    Certificate (historyLaw ν n) (fun h ↦ (roundedSum r x initial n h : ℝ))
      ((initial : ℝ) + ∑ k ∈ Finset.range n, (x k : ℝ)) (Real.toNNReal (total : ℝ)) := by
  have hcert := Stochastic.sum_certificate r hr x initial n (fun k ↦ Real.toNNReal (c k : ℝ))
    (s.sum_safe x initial n hs)
    (fun k hk h ↦ r.proxy_le_of_rat _ _ (hc ⟨k, hk⟩ _ (s.mem_sum x initial k h)))
  apply hcert.mono
  apply NNReal.le_toNNReal_of_coe_le
  -- Each `c k` bounds a square on a listed accumulator, and there is one: it is nonnegative.
  have hc0 (k : ℕ) (hk : k ∈ Finset.range n) : (0 : ℝ) ≤ c k := by
    obtain ⟨h⟩ := nonempty_of_isProbabilityMeasure (historyLaw ν k)
    exact_mod_cast (by positivity : (0 : ℚ) ≤ r.width (roundedSum r x initial k h + x k) ^ 2 / 4)
      |>.trans (hc ⟨k, Finset.mem_range.mp hk⟩ _ (s.mem_sum x initial k h))
  rw [NNReal.coe_sum, Finset.sum_congr rfl fun k hk ↦ Real.coe_toNNReal _ (hc0 k hk)]
  exact_mod_cast ht

/-- All accumulators of a rounded dot product that the support lists generate, up to the
requested length. -/
def dot (sp : rp.Support) (sa : ra.Support) (x y : ℕ → ℚ) (initial : ℚ) : ℕ → List ℚ :=
  reach (fun k s ↦ (sp.values (x k * y k)).flatMap fun p ↦ sa.values (s + p)) initial

/-- Coverage of the scalar lists propagates through the actual execution. -/
theorem mem_dot (sp : rp.Support) (sa : ra.Support) (x y : ℕ → ℚ)
    (initial : ℚ) (n : ℕ) (h : History (E × F) n) :
    roundedDot rp ra x y initial n h ∈ sp.dot sa x y initial n :=
  run_mem_reach (dotStep rp ra x y) _
    (fun _ _ _ ↦ List.mem_flatMap.mpr ⟨_, sp.covers _ _, sa.covers _ _⟩) initial n h

/-- Checking the finitely many support inputs proves safety for every entropy history. -/
theorem safe (sp : rp.Support) (sa : ra.Support) (x y : ℕ → ℚ)
    (initial : ℚ) (n : ℕ)
    (hs : ∀ k : Fin n, rp.Admissible (x k * y k) ∧
      ∀ s ∈ sp.dot sa x y initial k, ∀ p ∈ sp.values (x k * y k),
        ra.Admissible (s + p)) :
    DotSafe rp ra x y initial n := by
  intro k hk
  refine ⟨(hs ⟨k, hk⟩).1, ?_⟩
  intro h e
  exact (hs ⟨k, hk⟩).2 _ (sp.mem_dot sa x y initial k h) _ (sp.covers _ e)

/-- Uniform support bounds imply the all-history addition proxy bounds. -/
theorem budget (sp : rp.Support) (sa : ra.Support) (x y : ℕ → ℚ)
    (initial : ℚ) (n : ℕ) (c : ℕ → ℝ≥0)
    (hc : ∀ k : Fin n, ∀ s ∈ sp.dot sa x y initial k,
      ∀ p ∈ sp.values (x k * y k), ra.proxy (s + p) ≤ c k) :
    DotBudget rp ra x y initial n c := by
  intro k hk h e
  exact hc ⟨k, hk⟩ _ (sp.mem_dot sa x y initial k h) _ (sp.covers _ e)

/-- A terminal support check covers the separately rounded bias addition. -/
theorem terminal (sp : rp.Support) (sa : ra.Support) (x y : ℕ → ℚ)
    (initial bias : ℚ) (n : ℕ) (P : ℚ → Prop)
    (hc : ∀ s ∈ sp.dot sa x y initial n, P (s + bias))
    (h : History (E × F) n) :
    P (roundedDot rp ra x y initial n h + bias) :=
  hc _ (sp.mem_dot sa x y initial n h)

/-- Rational support checks certify an affine execution at a supplied rational budget: `p k`
bounds the squared half width of the product at step `k`, `c k` that of its addition on every
listed accumulator and product, and `b` that of the bias addition. -/
theorem affine_certificate [Finite E] [Finite F]
    [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSingletonClass E] [MeasurableSingletonClass F]
    {ν : Measure E} {ρ : Measure F} [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (sp : rp.Support) (sa : ra.Support) (hlp : rp.Law ν) (hla : ra.Law ρ)
    (x y : ℕ → ℚ) (bias : ℚ) (n : ℕ) (p c : ℕ → ℚ) (b total : ℚ)
    (hs : ∀ k : Fin n, rp.Admissible (x k * y k) ∧
      ∀ s ∈ sp.dot sa x y 0 k, ∀ v ∈ sp.values (x k * y k), ra.Admissible (s + v))
    (hbs : ∀ s ∈ sp.dot sa x y 0 n, ra.Admissible (s + bias))
    (hp : ∀ k : Fin n, rp.width (x k * y k) ^ 2 / 4 ≤ p k)
    (hc : ∀ k : Fin n, ∀ s ∈ sp.dot sa x y 0 k,
      ∀ v ∈ sp.values (x k * y k), ra.width (s + v) ^ 2 / 4 ≤ c k)
    (hb : ∀ s ∈ sp.dot sa x y 0 n, ra.width (s + bias) ^ 2 / 4 ≤ b)
    (ht : (∑ k ∈ Finset.range n, (p k + c k)) + b ≤ total) :
    Certificate ((historyLaw (ν.prod ρ) n).prod ρ)
      (fun h ↦ (roundedAffine rp ra x y bias n h : ℝ))
      ((∑ k ∈ Finset.range n, ((x k * y k : ℚ) : ℝ)) + bias)
      (Real.toNNReal (total : ℝ)) := by
  have hcert := Stochastic.affine_certificate rp ra hlp hla x y bias n
    (fun k ↦ Real.toNNReal (c k : ℝ)) (Real.toNNReal (b : ℝ))
    ⟨sp.safe sa x y 0 n hs, sp.terminal sa x y 0 bias n _ hbs⟩
    (sp.budget sa x y 0 n _ (fun k s hs v hv ↦
      ra.proxy_le_of_rat _ _ (hc k s hs v hv)))
    (sp.terminal sa x y 0 bias n (fun q ↦ ra.proxy q ≤ Real.toNNReal (b : ℝ))
      (fun s hs ↦ ra.proxy_le_of_rat _ _ (hb s hs)))
  apply hcert.mono
  -- Each budget bounds a square on a listed input, and there is one: it is nonnegative.
  obtain ⟨e⟩ := nonempty_of_isProbabilityMeasure ν
  have reached (k : ℕ) : ∃ s, s ∈ sp.dot sa x y 0 k :=
    (nonempty_of_isProbabilityMeasure (historyLaw (ν.prod ρ) k)).elim
      fun h ↦ ⟨_, sp.mem_dot sa x y 0 k h⟩
  have hp0 (k : ℕ) (hk : k ∈ Finset.range n) : (0 : ℝ) ≤ p k := by
    exact_mod_cast (by positivity : (0 : ℚ) ≤ rp.width (x k * y k) ^ 2 / 4).trans
      (hp ⟨k, Finset.mem_range.mp hk⟩)
  have hc0 (k : ℕ) (hk : k ∈ Finset.range n) : (0 : ℝ) ≤ c k := by
    obtain ⟨s, hs⟩ := reached k
    exact_mod_cast (by positivity :
      (0 : ℚ) ≤ ra.width (s + rp.round e (x k * y k)) ^ 2 / 4).trans
      (hc ⟨k, Finset.mem_range.mp hk⟩ s hs _ (sp.covers _ e))
  have hb0 : (0 : ℝ) ≤ b := by
    obtain ⟨s, hs⟩ := reached n
    exact_mod_cast (by positivity : (0 : ℚ) ≤ ra.width (s + bias) ^ 2 / 4).trans (hb s hs)
  calc
    _ ≤ (∑ k ∈ Finset.range n,
        (Real.toNNReal (p k : ℝ) + Real.toNNReal (c k : ℝ))) +
          Real.toNNReal (b : ℝ) := by
      apply add_le_add _ le_rfl
      apply Finset.sum_le_sum
      intro k hk
      exact add_le_add (rp.proxy_le_of_rat _ _ (hp ⟨k, Finset.mem_range.mp hk⟩)) le_rfl
    _ ≤ Real.toNNReal (total : ℝ) := by
      apply NNReal.le_toNNReal_of_coe_le
      rw [NNReal.coe_add, NNReal.coe_sum, Real.coe_toNNReal _ hb0,
        Finset.sum_congr rfl fun k hk ↦ show
          ((Real.toNNReal (p k : ℝ) + Real.toNNReal (c k : ℝ) : ℝ≥0) : ℝ) = (p k : ℝ) + c k by
            rw [NNReal.coe_add, Real.coe_toNNReal _ (hp0 k hk), Real.coe_toNNReal _ (hc0 k hk)]]
      exact_mod_cast ht

end Rounder.Support
end FloatLib.Numerics.Quantization.Stochastic
