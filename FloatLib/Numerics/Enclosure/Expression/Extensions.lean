/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Check

/-!
# User enclosure evaluation

An extension supplies rational bounds independently of the endpoint representation. Calls check
their argument count, decode the inputs, and round the result outward with the selected backend.
The checker reevaluates each call on every subdivision; no sampled values or frozen bounds are used.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval.Backend

/-- Add registered rational enclosures to an existing endpoint backend. -/
def withExtensions {α : Type*} (B : Backend α) (config : Config)
    (extensions : List Extension) : Backend α :=
  { B with
    call? := fun index inputs =>
      match extensions[index]? with
      | none => none
      | some E =>
      if inputs.length = E.arity then
        match inputs.mapM (fun (I : Interval α) => I.decode? B.decode) with
        | none => none
        | some decoded =>
          match E.enclose? config decoded with
          | none => none
          | some output => B.encloseInterval? output
      else none }

end FloatLib.Numerics.Interval.Backend
