/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Nat.Find

/-!
# Natural-number search with a finite reducible prefix

The finite prefix uses Lean's list search. Its unrestricted fallback is
Mathlib's total search, so the prefix length never restricts the result.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- Find the least satisfying natural, inspecting a finite prefix before the total fallback. -/
def findWithPrefix (predicate : Nat → Prop) [DecidablePred predicate]
    (exists_value : ∃ n, predicate n) (count : Nat) : Nat :=
  match (List.range count).find? (fun n => decide (predicate n)) with
  | some n => n
  | none => Nat.find exists_value

end FloatLib.Numerics
