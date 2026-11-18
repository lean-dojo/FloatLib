/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.ErrorBound.Loop

/-!
# Container identities for error propagation

Finite sums, projected folds, and optional computations retain their actual data.
-/

public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

universe u v

/-- The left fold of `+` from zero over the indices of `Fin n` is their finite sum. -/
theorem foldl_finRange_add_eq_sum {β : Type} [AddCommMonoid β] {n : Nat} (f : Fin n → β) :
    (List.finRange n).foldl (fun s i => s + f i) 0 = (Finset.univ : Finset (Fin n)).sum f := by
  classical
  calc
    _ = ((List.finRange n).map f).sum := by
      rw [List.sum_eq_foldl, List.foldl_map]
    _ = _ := by
      simp only [Finset.sum, Finset.val_univ_fin, Multiset.map_coe, Multiset.sum_coe]

/-- A sum of positive terms over the indices of `Fin (n + 1)` is positive. -/
theorem foldl_finRange_add_pos {n : Nat} {f : Fin (n + 1) → ℝ} (h : ∀ i, 0 < f i) :
    0 < (List.finRange (n + 1)).foldl (fun s i => s + f i) 0 := by
  rw [foldl_finRange_add_eq_sum]
  exact Finset.sum_pos (fun i _ => h i) Finset.univ_nonempty

/-- The first component of a left fold whose step computes it from the accumulator's first
component alone is the fold of that component. -/
theorem foldl_fst {α : Type u} {β : Type v} {γ : Type*} (step : α × β → γ → α × β)
    (first : α → γ → α) (h : ∀ state value, (step state value).1 = first state.1 value)
    (initial : α × β) (input : List γ) :
    (input.foldl step initial).1 = input.foldl first initial.1 :=
  (List.foldl_hom Prod.fst (fun state value => (h state value).symm)).symm

/-- Split an actual optional computation without replacing its payload by a fresh input. -/
theorem option_apply_eq_dite {α : Type u} {β : Sort v}
    (program : Option α → β) (source : Option α) :
    program source = if found : source.isSome then
      program (some (source.get found)) else program none := by
  cases source <;> rfl

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
