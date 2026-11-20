/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.KernelOptimize

/-!
# Loops that the kernel runs in a few steps

A left fold over `List.range n` costs Lean's kernel about fifty microseconds for each step: it
builds the list and then steps through the compiled recursion of `List.foldl`. The same loop
written as the recursor of the natural numbers costs about four. `foldl_range` states that the
two are equal, and `foldl_range'` does the same for a fold over `List.range' start n step`, a
range with an offset and a step. Both are tagged `@[kernel_optimize]`, so `float_decide`
runs such a loop as a recursion on its length.

`forall_fin_pairs` turns a statement about all pairs of indices below `n` into one such loop over
the `n * n` pairs. `float_decide` uses it for goals of the form `∀ a b : Fin n, P a b`, an
exhaustive check of a small format. `forall_fin_pairs_test` is the same loop for a Boolean test,
which the kernel runs without unfolding a `Decidable` instance at every pair.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.KernelPath

universe u

/--
A left fold over `List.range n` is the primitive recursion on `n` whose step applies the folded
function to the accumulator and the index.
-/
@[kernel_optimize] theorem foldl_range {α : Type u} (f : α → Nat → α) (init : α) (n : Nat) :
    List.foldl f init (List.range n) =
      Nat.rec (motive := fun _ => α) init (fun index accumulator => f accumulator index) n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.foldl_append, ih]; rfl

/--
A left fold over `List.range' start n step`, the range of `n` indices from `start` in steps of
`step`, is the primitive recursion on `n` whose step applies the folded function to the
accumulator and the index `start + step * k`.
-/
@[kernel_optimize] theorem foldl_range' {α : Type u} (f : α → Nat → α) (init : α)
    (start n step : Nat) :
    List.foldl f init (List.range' start n step) =
      Nat.rec (motive := fun _ => α) init
        (fun index accumulator => f accumulator (Nat.add start (Nat.mul step index))) n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [List.range'_concat, List.foldl_append, ih]; rfl

/--
A Boolean test holds on all pairs of indices below `n` when one loop over the `n * n` pairs
counts no failure. The loop is the recursor of the natural numbers on `count = n * n`, whose
step runs the test on the pair `(i / n, i % n)`, so Lean's kernel checks all pairs in `n * n`
steps of a few natural-number operations each, with no `Decidable` instance to unfold.
-/
theorem forall_fin_pairs_test {n : Nat} (test : Nat → Nat → Bool) (count : Nat)
    (hcount : count = n * n)
    (h : Nat.rec (motive := fun _ => Nat) 0
        (fun index failures =>
          Nat.add failures
            (Bool.rec (motive := fun _ => Nat) 1 0 (test (Nat.div index n) (Nat.mod index n))))
        count = 0) :
    ∀ a b : Fin n, test a.val b.val = true := by
  have hloop : ∀ m : Nat,
      Nat.rec (motive := fun _ => Nat) 0
          (fun index failures =>
            Nat.add failures
              (Bool.rec (motive := fun _ => Nat) 1 0 (test (Nat.div index n) (Nat.mod index n))))
          m = 0 →
        ∀ index < m, test (index / n) (index % n) = true := by
    intro m
    induction m with
    | zero => intro _ index hindex; exact absurd hindex (Nat.not_lt_zero _)
    | succ k ih =>
        intro hk index hindex
        have hsplit := Nat.eq_zero_of_add_eq_zero hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hindex with hlt | rfl
        · exact ih hsplit.1 index hlt
        · have hlast := hsplit.2
          cases htest : test (Nat.div index n) (Nat.mod index n)
          · rw [htest] at hlast
            exact absurd hlast (by decide)
          · rfl
  intro a b
  have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have hindex : a.val * n + b.val < count := by
    rw [hcount]
    calc a.val * n + b.val < a.val * n + n := Nat.add_lt_add_left b.isLt _
      _ = (a.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ n * n := Nat.mul_le_mul_right _ a.isLt
  have hpair := hloop count h (a.val * n + b.val) hindex
  have hdiv : (a.val * n + b.val) / n = a.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt b.isLt, Nat.zero_add]
  have hmod : (a.val * n + b.val) % n = b.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.isLt]
  rw [hdiv, hmod] at hpair
  exact hpair

/--
A decidable relation holds on all pairs of indices below `n` when one loop over the `n * n` pairs
counts no failure. The loop is the recursor of the natural numbers on `count = n * n`, whose
step decides the relation on the pair `(i / n, i % n)`, so Lean's kernel checks all pairs in
`n * n` steps of a few natural-number operations each (`forall_fin_pairs_test` on the decision).
-/
theorem forall_fin_pairs {n : Nat} {relation : Nat → Nat → Prop}
    [decide : ∀ x y, Decidable (relation x y)] (count : Nat) (hcount : count = n * n)
    (h : Nat.rec (motive := fun _ => Nat) 0
        (fun index failures =>
          Nat.add failures
            (Bool.casesOn (motive := fun _ => Nat)
              (Decidable.decide (relation (Nat.div index n) (Nat.mod index n))) 1 0))
        count = 0) :
    ∀ a b : Fin n, relation a.val b.val :=
  fun a b => of_decide_eq_true
    (forall_fin_pairs_test (fun x y => @Decidable.decide (relation x y) (decide x y)) count
      hcount h a b)

end FloatLib.Floats.ExecFloat.KernelPath
