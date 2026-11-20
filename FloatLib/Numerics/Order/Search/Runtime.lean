/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Nat.Find

/-!
# Natural-number search that Lean's kernel can run

`findLeast predicate exists_value` is the least natural number that satisfies a decidable
predicate, given a proof that one does. It is Mathlib's `Nat.find` (`findLeast_eq_find`), with
one difference that matters to Lean's kernel: the kernel evaluates it without reducing the proof.

`Nat.find` recurses on the accessibility of the current number, and that accessibility is read
off the proof `exists_value`. To take a step, the kernel has to reduce the proof to a
constructor, which it cannot do for a proof by real analysis, nor for any theorem of another
module, whose proof it does not see. `accGuard layers` puts
`2 ^ layers - 1` constructors of `Acc` in front of an accessibility proof, built from the number
of layers alone, so a recursion takes `2 ^ layers - 1` steps on these before it reaches the
proof. `findLeast` uses 64 layers.

`findWithPrefix` tests a finite prefix with a list search first and continues with the search
of `findLeastFrom` behind it. The prefix length never restricts the result
(`findWithPrefix_eq_find`).
-/

@[expose] public section

namespace FloatLib.Numerics

universe u

set_option linter.defProp false in
/--
An accessibility proof for every element with `2 ^ layers - 1` constructors in front of `proof`:
a recursion on `accGuard layers proof x` takes `2 ^ layers - 1` steps before it reduces `proof`.
No layer adds no constructor, and one more layer puts one constructor around two uses of the
guard. The constructors are built by recursion on `layers` and do not depend on how `proof` was
obtained.

This is a definition and not a theorem because Lean's kernel has to unfold it in the modules
that import this one, and the proof of a theorem stays in the module that states it.
-/
def accGuard {α : Sort u} {r : α → α → Prop} (layers : Nat) :
    (∀ x : α, Acc r x) → ∀ x : α, Acc r x :=
  Nat.rec (motive := fun _ => (∀ x : α, Acc r x) → ∀ x : α, Acc r x) (fun proof => proof)
    (fun _ guard proof x => Acc.intro x fun y _ => guard (guard proof) y) layers

/--
One step of an upward search: from `current` to `current + 1`, when no number up to `current`
satisfies the predicate.
-/
def SearchStep (predicate : Nat → Prop) (next current : Nat) : Prop :=
  next = current + 1 ∧ ∀ k ≤ current, ¬predicate k

/-- An upward search ends when some number satisfies the predicate. -/
theorem searchStep_acc {predicate : Nat → Prop} (exists_value : ∃ n, predicate n)
    (start : Nat) : Acc (SearchStep predicate) start := by
  obtain ⟨n, hn⟩ := exists_value
  suffices h : ∀ m k, n ≤ k + m → Acc (SearchStep predicate) k from
    h n start (Nat.le_add_left _ _)
  intro m
  induction m with
  | zero => exact fun k kn => ⟨_, fun y r => absurd hn (r.2 _ kn)⟩
  | succ m ih => exact fun k kn => ⟨_, fun y r => r.1 ▸ ih _ (by omega)⟩

set_option linter.defProp false in
/--
The accessibility of `start` for the upward search, with `2 ^ 64 - 1` constructors in front of
the proof that the search ends. It is a definition for the reason given at `accGuard`, and it is
applied to variables only where `findLeastFrom` uses it, so that Lean keeps it in the body of
that definition instead of moving it into an auxiliary theorem.
-/
def searchAcc {predicate : Nat → Prop} (exists_value : ∃ n, predicate n) (start : Nat) :
    Acc (SearchStep predicate) start :=
  accGuard 64 (searchStep_acc exists_value) start

/--
The least natural number that satisfies `predicate`, searched upward from `start`, below which
no number satisfies it. The search recurses on the guarded accessibility proof `searchAcc`, so
Lean's kernel runs `2 ^ 64` steps of it without reducing `exists_value`.
-/
def findLeastFrom (predicate : Nat → Prop) [DecidablePred predicate]
    (exists_value : ∃ n, predicate n) (start : Nat) (below : ∀ k < start, ¬predicate k) :
    { n // predicate n ∧ ∀ m < n, ¬predicate m } :=
  WellFounded.fixF (r := SearchStep predicate)
    (C := fun k => (∀ n < k, ¬predicate n) → { n // predicate n ∧ ∀ m < n, ¬predicate m })
    (fun m search none_below =>
      if holds : predicate m then ⟨m, holds, none_below⟩
      else
        have none_upto : ∀ n ≤ m, ¬predicate n := fun n hn =>
          (Nat.lt_or_eq_of_le hn).elim (none_below n) fun e => e ▸ holds
        search (m + 1) ⟨rfl, none_upto⟩ fun n hn => none_upto n (Nat.le_of_lt_succ hn))
    start (searchAcc exists_value start) below

/--
The least natural number that satisfies `predicate`: `Nat.find` (`findLeast_eq_find`) in a form
that Lean's kernel evaluates without reducing the proof `exists_value`.
-/
def findLeast (predicate : Nat → Prop) [DecidablePred predicate]
    (exists_value : ∃ n, predicate n) : Nat :=
  (findLeastFrom predicate exists_value 0 fun _ h => absurd h (Nat.not_lt_zero _)).1

/--
Find the least satisfying natural, inspecting a finite prefix with a list search before the
search of `findLeastFrom` from the end of the prefix.
-/
def findWithPrefix (predicate : Nat → Prop) [DecidablePred predicate]
    (exists_value : ∃ n, predicate n) (count : Nat) : Nat :=
  match h : (List.range count).find? (fun n => decide (predicate n)) with
  | some n => n
  | none =>
      (findLeastFrom predicate exists_value count fun k hk hpk =>
        absurd (decide_eq_true hpk)
          (List.find?_eq_none.mp h k (List.mem_range.mpr hk))).1

end FloatLib.Numerics
