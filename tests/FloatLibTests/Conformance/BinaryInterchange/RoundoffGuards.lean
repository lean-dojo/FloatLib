/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff
public import FloatLib.Floats.Formats.BinaryInterchange.Configured

/-!
# Branch guards that a registered theorem refutes

A theorem concluding that a Boolean test is false, such as the NaN test of a finite value, decides
a branch guard on that test. These checks read the generated statements: a guard that a registered
theorem refutes from the context leaves one branch, while one it refutes only with an open
obligation leaves both. A refutation whose premise is an automatic argument, as configured theorems
take their format proof, is read as the proposition the premise states. A registered rule stated
like a generated theorem whose finiteness part normalization decides is not indexed by that part,
and a rule whose input premise bounds every entry of the container a read reads is not applied to
that read.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffGuards

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- A finite configured value is not a NaN: a refutation of the guard `isNaN x = true`. -/
theorem isNaN_eq_false_of_isFinite {x : Value} (hx : ExecFloat.Binary.isFinite x = true) :
    ExecFloat.Binary.isNaN x = false :=
  Model.isNaN_eq_false_of_isFinite_eq_true _ hx

/-- The same refutation with its premise an automatic argument. -/
theorem Automatic.isNaN_eq_false_of_isFinite {x : Value}
    (hx : ExecFloat.Binary.isFinite x = true := by assumption) : ExecFloat.Binary.isNaN x = false :=
  Model.isNaN_eq_false_of_isFinite_eq_true _ hx

variable [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

/-- The square of a value, and zero at a NaN. -/
def squareOrZero (x : Value) : Value := if ExecFloat.Binary.isNaN x then 0 else x * x

section Stated

attribute [local roundoff_rule] isNaN_eq_false_of_isFinite

/-- A finite input refutes the guard, so the statement is the square's, with no branch. -/
roundoff mixed theorem square_or_zero_mixedError :=
  fun (x : Value) (hformat : format.isIEEE = true) (hx : ExecFloat.Binary.isFinite x = true) =>
    ExecFloat.Binary.toReal (squareOrZero x)

example (x : Value) (hformat : format.isIEEE = true) (hx : ExecFloat.Binary.isFinite x = true) :=
  show _ → ExecFloat.Binary.isFinite (squareOrZero x) = true ∧
    MixedError (ExecFloat.Binary.toReal (squareOrZero x))
      (ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x) _ _ from
    square_or_zero_mixedError x hformat hx

/-- Without it the refutation would leave the input's finiteness open, so both branches stay. -/
roundoff mixed theorem square_or_zero_open_mixedError :=
  fun (x : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (squareOrZero x)

example (x : Value) (hformat : format.isIEEE = true) :=
  show _ → ExecFloat.Binary.isFinite (squareOrZero x) = true ∧
    MixedError (ExecFloat.Binary.toReal (squareOrZero x))
      (if ExecFloat.Binary.isNaN x = true then 0 else _) _ _ from
    square_or_zero_open_mixedError x hformat

end Stated

section Automatic

attribute [local roundoff_rule] Automatic.isNaN_eq_false_of_isFinite

/-- The refutation with an automatic premise decides the guard from the context as well. -/
roundoff mixed theorem square_or_zero_automatic_mixedError :=
  fun (x : Value) (hformat : format.isIEEE = true) (hx : ExecFloat.Binary.isFinite x = true) =>
    ExecFloat.Binary.toReal (squareOrZero x)

example (x : Value) (hformat : format.isIEEE = true) (hx : ExecFloat.Binary.isFinite x = true) :=
  show _ → ExecFloat.Binary.isFinite (squareOrZero x) = true ∧
    MixedError (ExecFloat.Binary.toReal (squareOrZero x))
      (ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x) _ _ from
    square_or_zero_automatic_mixedError x hformat hx

end Automatic

section Index

omit [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] in
/-- A rule stated like a generated theorem whose finiteness part is its own premise: normalizing
that part with the premise leaves no equality to index it by. -/
theorem entry_mixedError (xs : Array Value) (i : Nat) (h : i < xs.size)
    (hfinite : ExecFloat.Binary.isFinite xs[i] = true) :
    ExecFloat.Binary.isFinite xs[i] = true ∧
      MixedError (ExecFloat.Binary.toReal xs[i]) (ExecFloat.Binary.toReal xs[i]) 0 0 :=
  ⟨hfinite, MixedError.of_eq rfl⟩

attribute [local roundoff_rule] entry_mixedError

/-- Its finiteness part is not indexed, and the mixed analysis of another computation still
succeeds. -/
roundoff mixed theorem index_guard_mixedError :=
  fun (x y : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (x + y)

end Index

section Pointwise

/-- The entries of a pair in the other order. -/
def flip (xs : Vector Value 2) : Vector Value 2 := xs.reverse

omit [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] in
/-- Entry `i` of a flipped pair is within the budget of entry `i.rev` of its input. -/
theorem flip_error (xs : Vector Value 2) (reference error : Fin 2 → ℝ)
    (h : ∀ i : Fin 2, |ExecFloat.Binary.toReal xs[i] - reference i| ≤ error i) (i : Fin 2) :
    |ExecFloat.Binary.toReal (flip xs)[i] - reference i.rev| ≤ error i.rev := by
  simpa [flip, Fin.rev] using h i.rev

omit [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] in
/-- A rule that bounds a read of a vector by a bound on every entry of the same vector. -/
theorem entry_error (xs : Vector Value 2) (reference error : Fin 2 → ℝ)
    (h : ∀ i : Fin 2, |ExecFloat.Binary.toReal xs[i] - reference i| ≤ error i) (i : Fin 2) :
    |ExecFloat.Binary.toReal xs[i] - reference i| ≤ error i :=
  h i

attribute [local roundoff_rule] flip_error

open Lean Elab Command in
-- With `entry_error` registered too, the analysis of a flipped pair's sum rejects it at each read
-- instead of supplying its premise from an analysis of the same read, so it costs about the same.
run_cmd do
  let analyze (name : Name) : CommandElabM Nat := do
    let start ← IO.getNumHeartbeats
    elabCommand (← `(command| roundoff theorem $(mkIdent name) :=
      fun (x : Vector Value 2) =>
        ExecFloat.Binary.toReal ((flip x)[(0 : Fin 2)] + (flip x)[(1 : Fin 2)])))
    return ((← IO.getNumHeartbeats) - start) / 1000
  let alone ← analyze `flip_sum_error
  elabCommand (← `(command| attribute [local roundoff_rule] entry_error))
  let both ← analyze `flip_sum_entry_error
  if both > 2 * alone then
    throwError "flip_sum_entry_error used {both} heartbeats, flip_sum_error {alone}"

/-- Both analyses state the same theorem. -/
example : @flip_sum_error = @flip_sum_entry_error := rfl

end Pointwise

end FloatLibTests.Conformance.BinaryInterchange.RoundoffGuards
