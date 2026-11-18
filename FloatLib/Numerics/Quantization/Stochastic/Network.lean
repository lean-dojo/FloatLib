/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Quantization.Stochastic.Classification
public import FloatLib.Numerics.Quantization.Stochastic.Rounder

/-!
# Assembled two-layer score errors

Independent certified row programs produce the actual hidden vector.
Two fresh output programs are certified conditionally on that vector.
Their score-gap error has the weighted-ReLU proxy and penalty, plus the
two output proxies. The theorem proves the algebraic connection to the
assembled scores; no separate gap-identity premise is assumed.

The row and output programs may be the executable rounded affine
schedules. Their certificates must cover every reachable history.
No nonlinear mean-preservation claim is made.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization.Stochastic

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- Read a word from a finite entropy history in execution order. -/
def History.get {E : Type*} : {n : ℕ} → History E n → Fin n → E
  | 0, _, i => Fin.elim0 i
  | n + 1, h, i => if hi : i.val < n then History.get h.1 ⟨i.val, hi⟩ else h.2

/-- A word before the last is read from the history without its last word. -/
@[simp] theorem History.get_castSucc {E : Type*} {n : ℕ}
    (h : History E (n + 1)) (i : Fin n) :
    h.get i.castSucc = h.1.get i := by
  simp [History.get, i.isLt]

/-- The last word of a history is its second component. -/
@[simp] theorem History.get_last {E : Type*} {n : ℕ} (h : History E (n + 1)) :
    h.get (Fin.last n) = h.2 := by
  simp [History.get]

/-- The ordered additive loop is the sum of the terms at the corresponding history words. -/
theorem run_add_eq_sum {E : Type*} (term : ℕ → E → ℝ)
    (n : ℕ) (h : History E n) :
    run (fun k s e ↦ s + term k e) 0 n h = ∑ i : Fin n, term i (h.get i) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simpa only [History.get_castSucc, History.get_last, Fin.val_castSucc,
      Fin.val_last, run] using congrArg (fun s ↦ s + term n h.2) (ih h.1)

namespace Network

/-- The actual ReLU outputs, extended by zero beyond the requested row count. -/
def hidden {E : Type*} (row : ℕ → E → ℝ) (n : ℕ) (h : History E n) (k : ℕ) : ℝ :=
  if hk : k < n then max (row k (h.get ⟨k, hk⟩)) 0 else 0

/-- An exact affine reference on any supplied real vector. -/
def affine (x weight : ℕ → ℝ) (bias : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n, weight k * x k) + bias

/-- The weighted hidden error is the same ordered sum used by the independent-row theorem. -/
theorem hidden_error {E : Type*} (row : ℕ → E → ℝ) (z a : ℕ → ℝ)
    (n : ℕ) (h : History E n) :
    (∑ k ∈ Finset.range n, a k * (hidden row n h k - max (z k) 0)) =
      run (fun k s e ↦ s + a k * (max (row k e) 0 - max (z k) 0)) 0 n h := by
  rw [run_add_eq_sum, Finset.sum_range]
  simp only [hidden, Fin.isLt, dite_true]

/-- Adding the two conditional output errors to the hidden error gives the assembled gap. -/
theorem gap_identity {E F : Type*} (row : ℕ → E → ℝ) (z v w : ℕ → ℝ)
    (b d : ℝ) (n : ℕ) (candidate score : History E n → F → ℝ)
    (h : History E n) (e f : F) :
    (score h e - candidate h f) -
        (affine (fun k ↦ max (z k) 0) v b n - affine (fun k ↦ max (z k) 0) w d n) =
      run (fun k s word ↦ s + (v k - w k) * (max (row k word) 0 - max (z k) 0))
        0 n h +
      ((score h e - affine (hidden row n h) v b n) -
        (candidate h f - affine (hidden row n h) w d n)) := by
  rw [← hidden_error row z (fun k ↦ v k - w k)]
  simp only [affine, sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The score-gap bound of two assembled output programs on independent certified hidden rows. -/
theorem gap_mgf {E F : Type*} [Finite E] [Finite F]
    [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSingletonClass E] [MeasurableSingletonClass F]
    {μ : Measure E} {ν : Measure F} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (row : ℕ → E → ℝ) (z : ℕ → ℝ) (c : ℕ → ℝ≥0)
    (lower upper v w : ℕ → ℝ) (b d : ℝ) (n : ℕ)
    (candidate score : History E n → F → ℝ) (dc ds : ℝ≥0)
    (hrow : ∀ k, k < n → Certificate μ (row k) (z k) (c k))
    (hlower : ∀ k, k < n → ∀ e, lower k ≤ row k e)
    (hupper : ∀ k, k < n → ∀ e, row k e ≤ upper k)
    (hcandidate : ∀ h, Certificate ν (candidate h) (affine (hidden row n h) w d n) dc)
    (hscore : ∀ h, Certificate ν (score h) (affine (hidden row n h) v b n) ds) :
    MGFBound (fun e : History E n × (F × F) ↦
      (score e.1 e.2.1 - candidate e.1 e.2.2) -
        (affine (fun k ↦ max (z k) 0) v b n - affine (fun k ↦ max (z k) 0) w d n))
      ((∑ k ∈ Finset.range n, reluProxy (v k - w k) (upper k) (c k)) +
        ((ds : ℝ) + dc))
      (∑ k ∈ Finset.range n, reluPenalty (v k - w k) (lower k) (upper k))
      ((historyLaw μ n).prod (ν.prod ν)) := by
  have hmean (k : ℕ) (hk : k < n) : ∫ e, row k e - z k ∂μ = 0 := by
    rw [integral_sub Integrable.of_finite (integrable_const _), (hrow k hk).mean]
    simp
  have hout (h : History E n) :
      MGFBound (fun e : F × F ↦
        (score h e.1 - affine (hidden row n h) v b n) -
          (candidate h e.2 - affine (hidden row n h) w d n))
        ((ds : ℝ) + dc) 0 (ν.prod ν) := by
    simpa only [zero_add] using
      (MGFBound.of_subgaussian (hscore h).mgf).independent_sub
        (MGFBound.of_subgaussian (hcandidate h).mgf)
  have hg := relu_fresh (μ := μ) (ν := ν.prod ν)
    (fun k e ↦ row k e - z k) c (fun k ↦ v k - w k) z lower upper n
    (fun k hk ↦ (hrow k hk).mgf) hmean
    (fun k hk e ↦ by simpa only [add_sub_cancel] using hlower k hk e)
    (fun k hk e ↦ by simpa only [add_sub_cancel] using hupper k hk e)
    (fun e ↦ (score e.1 e.2.1 - affine (hidden row n e.1) v b n) -
      (candidate e.1 e.2.2 - affine (hidden row n e.1) w d n))
    ((ds : ℝ) + dc) 0 hout
  simp only [add_sub_cancel, add_zero] at hg
  exact hg.congr (fun e ↦ (gap_identity row z v w b d n candidate score e.1 e.2.1 e.2.2).symm)

end Network
end FloatLib.Numerics.Quantization.Stochastic
