/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Order.Search.Runtime

/-!
# The searches return the least witness

`findLeastFrom`, `findLeast` and `findWithPrefix` all return Mathlib's `Nat.find`, for every
predicate, every starting point and every prefix length.
-/

public section

namespace FloatLib.Numerics

/-- The search from any starting point returns Mathlib's least satisfying natural. -/
theorem findLeastFrom_eq_find (predicate : Nat → Prop) [DecidablePred predicate]
    (exists_value : ∃ n, predicate n) (start : Nat) (below : ∀ k < start, ¬predicate k) :
    (findLeastFrom predicate exists_value start below).1 = Nat.find exists_value :=
  ((Nat.find_eq_iff exists_value).mpr (findLeastFrom predicate exists_value start below).2).symm

/-- The kernel-reducible search returns Mathlib's least satisfying natural. -/
theorem findLeast_eq_find (predicate : Nat → Prop) [DecidablePred predicate]
    (exists_value : ∃ n, predicate n) :
    findLeast predicate exists_value = Nat.find exists_value :=
  findLeastFrom_eq_find predicate exists_value 0 _

/-- Every prefix length returns exactly Mathlib's least satisfying natural. -/
theorem findWithPrefix_eq_find (predicate : Nat → Prop) [DecidablePred predicate]
    (exists_value : ∃ n, predicate n) (count : Nat) :
    findWithPrefix predicate exists_value count = Nat.find exists_value := by
  unfold findWithPrefix
  split
  · rename_i n h
    have hfirst := List.find?_range_eq_some.mp h
    apply Eq.symm
    apply (Nat.find_eq_iff exists_value).mpr
    exact ⟨by simpa using hfirst.1, fun j hj => by simpa using hfirst.2.2 j hj⟩
  · exact findLeastFrom_eq_find predicate exists_value count _

end FloatLib.Numerics
