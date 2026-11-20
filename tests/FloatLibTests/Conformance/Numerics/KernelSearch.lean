/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Order.Search.Proof

/-!
# The least-witness search in Lean's kernel

`findLeast` and `findWithPrefix` return the least natural number that satisfies a predicate,
given a proof that one does. Lean's kernel evaluates them without reducing that proof: here the
proof is a theorem that the kernel cannot reduce to a witness, the search takes a thousand
steps, and the prefix of `findWithPrefix` is shorter than the search.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.KernelSearch

open FloatLib.Numerics

/-- Some square reaches `bound`. The proof gives no witness that the kernel could read off. -/
theorem exists_square_ge (bound : Nat) : ∃ n, bound ≤ n * n := by
  refine ⟨bound, ?_⟩
  rcases Nat.eq_zero_or_pos bound with h | h
  · simp [h]
  · exact Nat.le_mul_of_pos_left _ h

/-- A search of a thousand steps. -/
theorem findLeast_thousand :
    findLeast (fun n => 1000000 ≤ n * n) (exists_square_ge _) = 1000 := by
  decide +kernel

/-- The search goes on behind a prefix of sixteen numbers, and behind an empty one. -/
theorem findWithPrefix_beyond :
    findWithPrefix (fun n => 1000000 ≤ n * n) (exists_square_ge _) 16 = 1000 ∧
      findWithPrefix (fun n => 250000 ≤ n * n) (exists_square_ge _) 0 = 500 := by
  decide +kernel

/-- A witness inside the prefix is found by the list search. -/
theorem findWithPrefix_within :
    findWithPrefix (fun n => 100 ≤ n * n) (exists_square_ge _) 16 = 10 := by
  decide +kernel

/-- The search from a starting point below which the predicate fails. -/
theorem findLeastFrom_start :
    (findLeastFrom (fun n => 1000000 ≤ n * n) (exists_square_ge _) 900
      (fun k hk => by
        have : k * k < 1000000 := Nat.mul_self_lt_mul_self (m := k) (n := 1000) (by omega)
        omega)).1 = 1000 := by
  decide +kernel

/--
A statement about Mathlib's `Nat.find` is decided after the rewrite to the search that the
kernel runs.
-/
theorem find_thousand : Nat.find (exists_square_ge 1000000) = 1000 := by
  rw [← findLeast_eq_find]
  decide +kernel

/-- info: 'FloatLibTests.Conformance.Numerics.KernelSearch.findWithPrefix_beyond' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms findWithPrefix_beyond

end FloatLibTests.Conformance.Numerics.KernelSearch
