/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.ErrorBound.Loop

/-!
# Summation loops in closed form

`roundoff mixed theorem` states the budget of a loop through the recurrences `List.foldRelative` and
`List.foldAbsolute`, which follow the loop's own traversal. For a summation loop `s := s + t v` from
zero, such as a dot product, a sum or a sum of squares, the recurrence has the shape
`List.sumFoldStep`, where each addition contributes relative error `u` and each term its own
absolute budget `c v`.

`List.abs_sub_le_of_sumFold` turns the generated bound into
`((1 + u)^n - 1) * ∑ |p v| + (1 + u)^n * ∑ c v`, a bound by the inputs alone. For exact terms that
is `((1 + u)^n - 1) * ∑ |p v|` (`List.abs_sub_le_of_sumFold_of_exact`). In binary64, where u is
2^-53, a thousand exact terms give a factor of about 1.1 × 10^-13. `List.allSteps_sumFold_of_abs_le`
derives the range conditions from bounds on the terms.
-/

@[expose] public section

namespace List

open FloatLib.Numerics

variable {α β : Type*}

/-- The mixed-error recurrence that `roundoff` generates for a summation loop
`s := s + t v` from zero, when each rounded addition has relative error `u` and the term `t v`
enters with absolute budget `c v` against its real value `p v`: the relative part is `u` after
the first step, and the absolute part absorbs the previous relative part. -/
abbrev sumFoldStep (u : ℝ) (step : α → β → α) (p c : β → ℝ) :=
  mixedFoldStep step (fun reference value => reference + p value) (fun _ _ _ _ _ => u)
    (fun _ reference relative absolute value =>
      (1 + u) * (relative * |reference| + absolute + c value))

/-- **The budget of a summation loop in closed form.** After `n` steps, the bound
`relative * |reference| + absolute` of the recurrence `sumFoldStep` is at most
`((1 + u)^n - 1) * ∑ |p v| + (1 + u)^n * ∑ c v`. -/
theorem sumFoldStep_le (u : ℝ) (hu : 0 ≤ u) (step : α → β → α) (p c : β → ℝ)
    (hc : ∀ v, 0 ≤ c v) (initial : α) (input : List β) :
    let s := input.foldl (sumFoldStep u step p c) (initial, 0, 0, 0)
    s.2.2.1 * |s.2.1| + s.2.2.2 ≤
      ((1 + u) ^ input.length - 1) * (input.map fun v => |p v|).sum +
        (1 + u) ^ input.length * (input.map c).sum := by
  suffices h : ∀ l : List β,
      let s := l.foldl (sumFoldStep u step p c) (initial, 0, 0, 0)
      |s.2.1| ≤ (l.map fun v => |p v|).sum ∧ 0 ≤ (l.map c).sum ∧ 0 ≤ s.2.2.1 ∧ s.2.2.1 ≤ u ∧
        s.2.2.1 * |s.2.1| + s.2.2.2 ≤
          ((1 + u) ^ l.length - 1) * (l.map fun v => |p v|).sum +
            (1 + u) ^ l.length * (l.map c).sum from (h input).2.2.2.2
  intro l
  induction l using List.reverseRecOn with
  | nil => simp [hu]
  | append_singleton l v ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero,
      List.length_append, List.length_cons, List.length_nil, zero_add] at ih ⊢
    generalize l.foldl (sumFoldStep u step p c) (initial, 0, 0, 0) = s at ih ⊢
    obtain ⟨a0, ref, r, a⟩ := s
    obtain ⟨hA, hC, hr0, hru, hE⟩ := ih
    simp only [sumFoldStep, List.mixedFoldStep] at hA hC hr0 hru hE ⊢
    generalize (l.map fun v => |p v|).sum = A at hA hE ⊢
    generalize (l.map c).sum = C at hC hE ⊢
    generalize l.length = k at hE ⊢
    have hpv : 0 ≤ |p v| := abs_nonneg _
    have hcv := hc v
    have hsum : |ref + p v| ≤ A + |p v| := (abs_add_le _ _).trans (by linarith)
    refine ⟨hsum, by linarith, hu, le_rfl, ?_⟩
    have h1u : (1 : ℝ) ≤ 1 + u := by linarith
    have hpow : 1 + u ≤ (1 + u) ^ (k + 1) := le_self_pow₀ h1u (by omega)
    have hp : u * |p v| ≤ ((1 + u) ^ (k + 1) - 1) * |p v| :=
      mul_le_mul_of_nonneg_right (by linarith) hpv
    have hcc : (1 + u) * c v ≤ (1 + u) ^ (k + 1) * c v := mul_le_mul_of_nonneg_right hpow hcv
    have hk : (1 + u) ^ (k + 1) = (1 + u) * (1 + u) ^ k := pow_succ' _ _
    calc u * |ref + p v| + (1 + u) * (r * |ref| + a + c v)
        ≤ u * (A + |p v|) + (1 + u) * ((((1 + u) ^ k - 1) * A + (1 + u) ^ k * C) + c v) :=
          add_le_add (mul_le_mul_of_nonneg_left hsum hu)
            (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
      _ ≤ ((1 + u) ^ (k + 1) - 1) * (A + |p v|) + (1 + u) ^ (k + 1) * (C + c v) := by
          rw [hk]; rw [hk] at hp hcc; nlinarith

/-- The reference component of the recurrence of a summation loop is the plain sum. -/
theorem sumFoldStep_reference (u : ℝ) (step : α → β → α) (p c : β → ℝ) (initial : α)
    (reference relative absolute : ℝ) (input : List β) :
    (input.foldl (sumFoldStep u step p c) (initial, reference, relative, absolute)).2.1 =
      input.foldl (fun reference value => reference + p value) reference := by
  induction input generalizing initial reference relative absolute with
  | nil => rfl
  | cons value rest ih => exact ih _ _ _ _

/-- **A summation loop's generated mixed bound in closed form.** The mixed bound that `roundoff`
generates for `s := s + t v`, where each addition has relative error `u` and the term `t v` has
absolute budget `c v` against `p v`, gives
`|x - ∑ p v| ≤ ((1 + u)^n - 1) * ∑ |p v| + (1 + u)^n * ∑ c v`. For a dot product
`c v = u * |p v| + η`, this is `((1 + u)^(n + 1) - 1) * ∑ |p v| + n (1 + u)^n η`. -/
theorem abs_sub_le_of_sumFold {x : ℝ} (u : ℝ) (hu : 0 ≤ u) (step : α → β → α) (p c : β → ℝ)
    (hc : ∀ v, 0 ≤ c v) (initial : α) (input : List β)
    (h : MixedError x (input.foldl (fun reference value => reference + p value) 0)
      (foldRelative step (fun reference value => reference + p value) (fun _ _ _ _ _ => u)
        (fun _ reference relative absolute value =>
          (1 + u) * (relative * |reference| + absolute + c value)) initial 0 0 0 input)
      (foldAbsolute step (fun reference value => reference + p value) (fun _ _ _ _ _ => u)
        (fun _ reference relative absolute value =>
          (1 + u) * (relative * |reference| + absolute + c value)) initial 0 0 0 input)) :
    |x - input.foldl (fun reference value => reference + p value) 0| ≤
      ((1 + u) ^ input.length - 1) * (input.map fun v => |p v|).sum +
        (1 + u) ^ input.length * (input.map c).sum := by
  have hle := sumFoldStep_le u hu step p c hc initial input
  simp only [sumFoldStep_reference] at hle
  exact h.bound.trans hle

/-- **A recursive sum's generated mixed bound in closed form.** When every term `t v` is exact,
the mixed bound that `roundoff` generates for `s := s + t v` gives
`|x - ∑ p v| ≤ ((1 + u)^n - 1) * ∑ |p v|`. -/
theorem abs_sub_le_of_sumFold_of_exact {x : ℝ} (u : ℝ) (hu : 0 ≤ u) (step : α → β → α)
    (p : β → ℝ) (initial : α) (input : List β)
    (h : MixedError x (input.foldl (fun reference value => reference + p value) 0)
      (foldRelative step (fun reference value => reference + p value) (fun _ _ _ _ _ => u)
        (fun _ reference relative absolute _ => (1 + u) * (relative * |reference| + absolute))
        initial 0 0 0 input)
      (foldAbsolute step (fun reference value => reference + p value) (fun _ _ _ _ _ => u)
        (fun _ reference relative absolute _ => (1 + u) * (relative * |reference| + absolute))
        initial 0 0 0 input)) :
    |x - input.foldl (fun reference value => reference + p value) 0| ≤
      ((1 + u) ^ input.length - 1) * (input.map fun v => |p v|).sum := by
  have hle := abs_sub_le_of_sumFold u hu step p (fun _ => 0) (fun _ => le_rfl) initial input
    (by simpa only [add_zero] using h)
  rwa [show (input.map fun _ => (0 : ℝ)).sum = 0 by simp, mul_zero, add_zero] at hle

/-- **The range conditions of a summation loop from bounds on its terms.** The conditions that
`roundoff` generates at each visited state of `s := s + t v` from zero, that the term and the
enclosure of the next partial sum are at most `M`, hold for `n` terms when each term is at most
`b` in magnitude, its budget at most `u * |p v| + η`, `(1 + u)^(n + 1) ≤ 2` and
`2 (n + 1) (b + η) ≤ M`. -/
theorem allSteps_sumFold_of_abs_le (u η b M : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) (step : α → β → α)
    (p c : β → ℝ) (hc : ∀ v, 0 ≤ c v) (initial : α) (input : List β)
    (hp : ∀ v ∈ input, |p v| ≤ b) (hcp : ∀ v ∈ input, c v ≤ u * |p v| + η)
    (hgrowth : (1 + u) ^ (input.length + 1) ≤ 2) (hrange : 2 * (input.length + 1) * (b + η) ≤ M) :
    AllSteps (sumFoldStep u step p c)
      (fun state value => |p value| ≤ M ∧
        |state.2.1 + p value| + (state.2.2.1 * |state.2.1| + state.2.2.2 + c value) ≤ M)
      (initial, 0, 0, 0) input := by
  have hu1 : u ≤ 1 := by
    have : 1 + u ≤ (1 + u) ^ (input.length + 1) := le_self_pow₀ (by linarith) (by omega)
    linarith
  have sum_eq : ∀ (l : List β) (a : ℝ),
      l.foldl (fun reference value => reference + p value) a = a + (l.map p).sum := by
    intro l; induction l with
    | nil => simp
    | cons v l ih => intro a; simp [ih, add_assoc]
  have abs_sum : ∀ l : List β, |(l.map p).sum| ≤ (l.map fun v => |p v|).sum := by
    intro l; induction l with
    | nil => simp
    | cons v l ih =>
      simp only [List.map_cons, List.sum_cons]; exact (abs_add_le _ _).trans (by linarith)
  suffices h : ∀ l : List β, l.length ≤ input.length → (∀ v ∈ l, |p v| ≤ b) →
      (∀ v ∈ l, c v ≤ u * |p v| + η) →
      AllSteps (sumFoldStep u step p c)
        (fun state value => |p value| ≤ M ∧
          |state.2.1 + p value| + (state.2.2.1 * |state.2.1| + state.2.2.2 + c value) ≤ M)
        (initial, 0, 0, 0) l from h input le_rfl hp hcp
  intro l
  induction l using List.reverseRecOn with
  | nil => intros; trivial
  | append_singleton l v ih =>
    intro hlen hpl hcl
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    rw [allSteps_append_singleton]
    refine ⟨ih (by omega) (fun w hw => hpl w (by simp [hw]))
      (fun w hw => hcl w (by simp [hw])), ?_⟩
    have hpv := hpl v (by simp)
    have hcv := hcl v (by simp)
    have hb : 0 ≤ b := (abs_nonneg _).trans hpv
    have hE := sumFoldStep_le u hu step p c hc initial l
    dsimp only at hE
    have href := sumFoldStep_reference u step p c initial 0 0 0 l
    rw [sum_eq, zero_add] at href
    have hA := abs_sum l
    -- The terms and budgets of the prefix.
    have hAb : (l.map fun v => |p v|).sum ≤ l.length * b := by
      have : ∀ w ∈ l, |p w| ≤ b := fun w hw => hpl w (by simp [hw])
      clear hpl hcl ih hE href hA hlen hcv hpv
      induction l with
      | nil => simp
      | cons w l ihl =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]; push_cast
        linarith [this w (by simp), ihl (fun x hx => this x (by simp [hx]))]
    have hCb : (l.map c).sum ≤ u * (l.map fun v => |p v|).sum + l.length * η := by
      have : ∀ w ∈ l, c w ≤ u * |p w| + η := fun w hw => hcl w (by simp [hw])
      clear hpl hcl ih hE href hA hlen hcv hpv hAb
      induction l with
      | nil => simp
      | cons w l ihl =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]; push_cast
        linarith [this w (by simp), ihl (fun x hx => this x (by simp [hx]))]
    have hk : (l.length : ℝ) + 1 ≤ input.length := by exact_mod_cast hlen
    have hg1 : (1 + u) ^ (l.length + 1) ≤ 2 :=
      (pow_le_pow_right₀ (by linarith) (by omega)).trans hgrowth
    have hg0 : (1 + u) ^ l.length ≤ 2 :=
      (pow_le_pow_right₀ (by linarith) (by omega)).trans hg1
    have hpow : (1 + u) ^ (l.length + 1) = (1 + u) * (1 + u) ^ l.length := pow_succ' _ _
    have hk0 : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
    generalize l.foldl (sumFoldStep u step p c) (initial, 0, 0, 0) = s at href hE ⊢
    rw [href] at hE ⊢
    generalize (l.map fun v => |p v|).sum = A at hA hAb hCb hE
    generalize (l.map c).sum = C at hCb hE
    generalize (l.map p).sum = S at hA hE ⊢
    generalize (l.length : ℝ) = k at hAb hCb hk hk0 hE
    have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
    have hsum : |S + p v| ≤ A + b := (abs_add_le _ _).trans (by linarith)
    have hP0 : 0 ≤ (1 + u) ^ l.length := pow_nonneg (by linarith) _
    have hbudget : ((1 + u) ^ l.length - 1) * A + (1 + u) ^ l.length * C ≤ A + 2 * k * η := by
      have h1 : (1 + u) ^ l.length * C ≤ (1 + u) ^ l.length * (u * A + k * η) :=
        mul_le_mul_of_nonneg_left hCb hP0
      have h2 : (1 + u) ^ l.length * (k * η) ≤ 2 * (k * η) :=
        mul_le_mul_of_nonneg_right hg0 (mul_nonneg hk0 hη)
      nlinarith
    have hcvb : c v ≤ b + η := by nlinarith [abs_nonneg (p v)]
    have hM : 2 * (k + 1) * (b + η) ≤ M := by nlinarith
    refine ⟨by nlinarith, ?_⟩
    nlinarith

end List
