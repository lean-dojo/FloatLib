/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Proof.Arithmetic
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Type

/-!
# Once-rounded posit squares

The model square reuses exact dyadic multiplication. The public configured square reuses the
selected certified multiplication kernel, including its packed carriers and width-generic
fallback. Neither entry point adds a rounding step.
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

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [FloatLib.Floats.ExecFloat.Mul (Configured.Family format code plan)]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Square using the selected certified posit multiplication, with one final rounding. -/
@[inline] def square (value : Value) : Value :=
  ExecFloat.mul value value

/-- Public squaring uses the same certified multiplication call as `value * value`. -/
theorem square_eq_mul (value : Value) :
    square value = ExecFloat.mul value value :=
  rfl

/-- Squaring preserves the selected multiplication capability's reference result. -/
theorem square_eq_spec (value : Value) :
    square value = ExecFloat.Spec.mul value value :=
  ExecFloat.Proof.mul_eq_spec value value

end FloatLib.Floats.ExecFloat.Posit
