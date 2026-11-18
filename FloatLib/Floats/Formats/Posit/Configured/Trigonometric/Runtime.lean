/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime
public import FloatLib.Floats.Formats.Posit.Trigonometric.Runtime

/-!
# Configured posit trigonometric operations

Sine, cosine, and tangent take their arguments in radians, and the inverses return principal
angles. Each call lifts the correctly rounded model result through the lawful storage codec, with
no further rounding.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Posit Standard (2022), §5.5.
Correctly rounded sine of a radian argument. -/
@[inline] def sin (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.sin value

/-- Posit Standard (2022), §5.5.
Correctly rounded cosine of a radian argument. -/
@[inline] def cos (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.cos value

/-- Posit Standard (2022), §5.5.
Correctly rounded tangent of a radian argument. -/
@[inline] def tan (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.tan value

/-- Posit Standard (2022), §5.5.
Correctly rounded inverse sine. Inputs outside `[-1, 1]` produce NaR. -/
@[inline] def arcSin (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.arcSin value

/-- Posit Standard (2022), §5.5.
Correctly rounded inverse cosine. Inputs outside `[-1, 1]` produce NaR. -/
@[inline] def arcCos (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.arcCos value

/-- Posit Standard (2022), §5.5.
Correctly rounded inverse tangent on its principal branch. -/
@[inline] def arcTan (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.arcTan value

end ExecFloat.Posit
end FloatLib.Floats
