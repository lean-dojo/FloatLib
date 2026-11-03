/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Rounding
public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff
public import FloatLib.Floats.Formats.BinaryInterchange.Configured

/-!
# Entries of a container that an input option holds

The container `o.get h` of an input option `o` is read as stored: an entry of it is exact, its
reference the decoded stored entry, also in the matcher form `Option.get.match_1` that coordinate
normalization can unfold the getter to, and no finiteness is proved for it, so a mixed theorem
assumes the finiteness of the output. Arithmetic on such an entry is analyzed as usual. A computed
option is not read as stored: the getter of a mapped option is read as the map of the option's
getter, and a match on an input option whose alternative computes is analyzed as the producer it is.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffOptions

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- An entry of the table an option holds. -/
def storedEntry (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2) : Value :=
  (weights.get h)[i]

/-- The entry is exact. -/
roundoff theorem stored_entry_error :=
  fun (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2) =>
    ExecFloat.Binary.toReal (storedEntry weights h i)

/-- The entry is exact in the mixed sense once it is finite. -/
roundoff mixed theorem stored_entry_mixedError :=
  fun (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2) =>
    ExecFloat.Binary.toReal (storedEntry weights h i)

/-- The reference is the decoded stored entry. -/
example (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2) :=
  show |_ - ExecFloat.Binary.toReal (weights.get h)[i]| ≤ 0 from stored_entry_error weights h i

/-- The mixed theorem assumes the finiteness of the entry, which the read does not prove. -/
example (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2)
    (hfinite : ExecFloat.Binary.isFinite (storedEntry weights h i) = true) :=
  show _ ∧ MixedError _ (ExecFloat.Binary.toReal (weights.get h)[i]) 0 0 from
    stored_entry_mixedError weights h i hfinite

set_option linter.auxLemma false in
/-- The same entry, read through the matcher that `Option.get` unfolds to. -/
def matchedEntry (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2) : Value :=
  (Option.get.match_1 (motive := fun _ _ => Vector Value 2) weights h fun x _ => x)[i]

/-- The entry read through the matcher is exact. -/
roundoff theorem matched_entry_error :=
  fun (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2) =>
    ExecFloat.Binary.toReal (matchedEntry weights h i)

/-- The entry read through the matcher is exact in the mixed sense once it is finite. -/
roundoff mixed theorem matched_entry_mixedError :=
  fun (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2) =>
    ExecFloat.Binary.toReal (matchedEntry weights h i)

/-- Its reference is the decoded stored entry too. -/
example (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2) :=
  show |_ - ExecFloat.Binary.toReal (weights.get h)[i]| ≤ 0 from matched_entry_error weights h i

/-- So is the mixed reference, under the finiteness of the entry. -/
example (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2)
    (hfinite : ExecFloat.Binary.isFinite (matchedEntry weights h i) = true) :=
  show _ ∧ MixedError _ (ExecFloat.Binary.toReal (weights.get h)[i]) 0 0 from
    matched_entry_mixedError weights h i hfinite

variable [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

/-- The square of an entry of the table an option holds. -/
def squareEntry (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2) : Value :=
  (weights.get h)[i] * (weights.get h)[i]

/-- On an IEEE format the square is within half an ulp of the square of the stored entry once the
rounded square is finite. -/
roundoff theorem square_entry_error :=
  fun (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2)
      (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (squareEntry weights h i)

/-- On an IEEE format the square has the mixed error of one rounding at the square of the stored
entry once the rounded square is finite. -/
roundoff mixed theorem square_entry_mixedError :=
  fun (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2)
      (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (squareEntry weights h i)

/-- The reference squares the decoded stored entry, under the finiteness of the rounded square. -/
example (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2)
    (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite ((weights.get h)[i] * (weights.get h)[i]) = true) :=
  show |_ - ExecFloat.Binary.toReal (weights.get h)[i] * ExecFloat.Binary.toReal (weights.get h)[i]|
    ≤ _ from square_entry_error weights h i hformat hfinite

/-- The mixed theorem has the same reference and the same premise. -/
example (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2)
    (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite ((weights.get h)[i] * (weights.get h)[i]) = true) :=
  show _ ∧ MixedError _ (ExecFloat.Binary.toReal (weights.get h)[i] *
    ExecFloat.Binary.toReal (weights.get h)[i]) _ _ from
    square_entry_mixedError weights h i hformat hfinite

/-- An entry of the squares of a table, through the getter of a mapped option. -/
def mappedEntry (weights : Option (Vector Value 2))
    (h : (weights.map fun w => w.map fun x => x * x).isSome) (i : Fin 2) : Value :=
  ((weights.map fun w => w.map fun x => x * x).get h)[i]

-- The getter of the mapped option is read as the map of the option's getter, whose squares a read
-- outside a loop has no rule for; they are not read as stored entries.
/--
error: roundoff: no numerical rule for tensor producer Vector.map (fun x => x * x) (weights.get ⋯);
expose its computation or supply an explicit bound
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem mapped_entry_mixedError :=
  fun (weights : Option (Vector Value 2))
      (h : (weights.map fun w => w.map fun x => x * x).isSome) (i : Fin 2)
      (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (mappedEntry weights h i)

/-- An entry of the squares of a table, through a match on the option. -/
def matchedSquares (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2) : Value :=
  (match weights, h with | some w, _ => w.map fun x => x * x)[i]

-- A match on an input option whose alternative computes is not the option's getter.
/--
error: roundoff: no numerical rule for tensor producer match weights, h with
| some w, x => Vector.map (fun x => x * x) w; expose its computation or supply an explicit bound
-/
#guard_msgs (whitespace := lax) in
roundoff mixed theorem matched_squares_mixedError :=
  fun (weights : Option (Vector Value 2)) (h : weights.isSome) (i : Fin 2)
      (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (matchedSquares weights h i)

end FloatLibTests.Conformance.BinaryInterchange.RoundoffOptions
