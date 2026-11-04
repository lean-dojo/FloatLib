/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Trigonometric.Atan2.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Configured posit two-coordinate arctangent

Both functions take their coordinates in the order `(x, y)`, as the Posit Standard does, so
`arcTan2 x y` is the principal argument of `x + i*y`. The lawful storage codec keeps the model
operations as they are, and the carrier boundary adds no rounding.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Correctly rounded principal argument of `x + i*y` in radians. NaR and the origin are
invalid. -/
@[inline] def arcTan2 (x y : Value) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan) Model.arcTan2 x y

/-- Correctly rounded principal argument of `x + i*y` divided by pi. NaR and the origin are
invalid. -/
@[inline] def arcTan2Pi (x y : Value) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan) Model.arcTan2Pi x y

end ExecFloat.Posit
end FloatLib.Floats
