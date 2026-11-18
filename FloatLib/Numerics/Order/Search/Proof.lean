/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Order.Search.Runtime

/-!
# The finite search prefix preserves the least witness
-/

public section

namespace FloatLib.Numerics

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
  · rfl

end FloatLib.Numerics
