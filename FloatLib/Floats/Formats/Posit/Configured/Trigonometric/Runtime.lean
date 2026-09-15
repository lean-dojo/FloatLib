/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Trigonometric.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Configured posit trigonometric operations

The configured operations lift the correctly rounded model functions through the lawful
storage codec. Changing the carrier introduces no additional numerical rounding.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Correctly rounded sine of a radian argument. -/
@[inline] def sin (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.sin value

/-- Correctly rounded cosine of a radian argument. -/
@[inline] def cos (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.cos value

/-- Correctly rounded tangent of a radian argument. -/
@[inline] def tan (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.tan value

/-- Correctly rounded inverse sine; inputs outside `[-1, 1]` produce NaR. -/
@[inline] def arcSin (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.arcSin value

/-- Correctly rounded inverse cosine; inputs outside `[-1, 1]` produce NaR. -/
@[inline] def arcCos (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.arcCos value

/-- Correctly rounded inverse tangent on its principal branch. -/
@[inline] def arcTan (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.arcTan value

end ExecFloat.Posit
end FloatLib.Floats
