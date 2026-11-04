/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Proof.Arithmetic
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Plan.Dispatch
public import FloatLib.Floats.Formats.Posit.Configured.Type
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Once-rounded posit squares

A posit square is the posit times itself. Neither entry point here adds a rounding step. The
model square reuses exact dyadic multiplication. The public configured square calls whichever
certified multiplication kernel is selected, packed carriers and width-generic fallback included.

`square_eq_mul` and `square_eq_spec` hold for any multiplication capability. For the built-in
storage plans of `ExecFloat.Posit`, `toModel_square` says the decoded result is `Model.square`,
and `square_eq_roundRat` says it is one rounding of the exact rational square.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

/-- Square by exact multiplication followed by one standardized posit rounding. NaR propagates. -/
@[inline] def square {format : Format} (value : Model format) : Model format :=
  DirectDyadicArithmetic.mul value value

/-- Model squaring refines the exact rational multiplication specification. -/
theorem square_eq_spec {format : Format} (value : Model format) :
    square value = Spec.mul value value :=
  DirectDyadicArithmetic.mul_eq_spec value value

/-- The exact rational square is rounded once for every finite posit. -/
theorem square_of_toRat {format : Format} (value : Model format) (q : Rat)
    (hvalue : value.toRat? = some q) :
    square value = roundRat format (q * q) := by
  rw [square_eq_spec]
  simp [Spec.mul, hvalue]

/-- Not-a-Real propagates through squaring. -/
@[simp] theorem square_nar {format : Format} :
    square (nar format) = nar format := by
  rw [square_eq_spec, Spec.mul_nar_left]

end FloatLib.Floats.Formats.Posit.Model

namespace FloatLib.Floats.ExecFloat.Posit

open FloatLib.Floats.Formats.Posit

section AnyCapability

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [FloatLib.Floats.ExecFloat.Mul (Configured.Family format code plan)]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/--
Square through the multiplication capability in scope. For the built-in storage plans this is the
selected certified posit multiplication, rounded once (`square_eq_roundRat`).
-/
@[inline] def square (value : Value) : Value :=
  ExecFloat.mul value value

/-- Public squaring is the call `ExecFloat.mul value value`, the one `value * value` makes. -/
theorem square_eq_mul (value : Value) :
    square value = ExecFloat.mul value value :=
  rfl

/--
Squaring returns the reference result of the multiplication capability in scope.

This holds for any `ExecFloat.Mul` instance and says nothing about posit rounding by itself. The
reference operation is whatever the capability declares. `toModel_square` states the posit result
for the built-in storage plans.
-/
theorem square_eq_spec (value : Value) :
    square value = ExecFloat.Spec.mul value value :=
  ExecFloat.Proof.mul_eq_spec value value

end AnyCapability

section BuiltInPlans

variable {format : Format} {plan : Configured.StoragePlan format}
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Configured.Family format (Configured.Code plan) plan)]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format (Configured.Code plan) plan)

/--
For every built-in storage plan, decoding the configured square gives the model square of the
decoded operand, NaR included.

The selected multiplication capability of each plan, byte table or direct kernel, has the
configured posit multiplication as its reference operation.
-/
@[simp] theorem toModel_square (value : Value) :
    toModel (square value) = Model.square (toModel value) := by
  have hspec : square value = Configured.Spec.mul value value := by
    rw [square_eq_spec]
    cases plan <;> rfl
  rw [hspec, Model.square_eq_spec]
  simp [Configured.Spec.mul, toModel, Configured.Family.toModel]

/-- A finite configured square rounds the exact rational square once. -/
theorem square_eq_roundRat (value : Value) {q : Rat} (hvalue : toRat? value = some q) :
    toModel (square value) = Model.roundRat format (q * q) := by
  rw [toModel_square]
  exact Model.square_of_toRat _ q hvalue

end BuiltInPlans

end FloatLib.Floats.ExecFloat.Posit
