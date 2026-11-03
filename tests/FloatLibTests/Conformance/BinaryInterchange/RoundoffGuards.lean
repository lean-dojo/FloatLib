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
take their format proof, is read as the proposition the premise states.
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

end FloatLibTests.Conformance.BinaryInterchange.RoundoffGuards
