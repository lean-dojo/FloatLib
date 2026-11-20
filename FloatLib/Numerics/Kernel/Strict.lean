/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Strict application for Lean's kernel

Lean's kernel reduces lazily and remembers the weak head normal form of every term it has reduced,
by the term. So `f (a * b)` and `f (b * a)` are reduced separately, although the kernel would
compute the same number for both arguments. `strict n f` is `f n` with the argument computed
first: the recursor of `Nat` makes the kernel reduce `n` to a literal, and `f` is applied to the
successor of the literal below it. Equal numbers then give the same term, and the kernel reduces
`f` once for each number. This turns a function of a natural number into a table that is filled
on demand, with no data structure.

`strict_eq` states that `strict n f = f n`.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/-- `f n`, with `n` reduced to a literal before `f` is applied (`strict_eq`). -/
noncomputable def strict {α : Sort _} (n : Nat) (f : Nat → α) : α :=
  Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n

/-- `strict n f` is `f n`. -/
theorem strict_eq {α : Sort _} (n : Nat) (f : Nat → α) : strict n f = f n := by
  cases n <;> rfl

end FloatLib.Numerics.Kernel
