/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Trigonometric.Pi.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Configured posit pi-scaled trigonometric operations

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

/-- Correctly rounded sine of pi times the input. -/
@[inline] def sinPi (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.sinPi value

/-- Correctly rounded cosine of pi times the input. -/
@[inline] def cosPi (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.cosPi value

/-- Correctly rounded tangent of pi times the input; half-integers produce NaR. -/
@[inline] def tanPi (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.tanPi value

/-- Correctly rounded inverse sine divided by pi; inputs outside `[-1, 1]` produce NaR. -/
@[inline] def arcSinPi (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.arcSinPi value

/-- Correctly rounded inverse cosine divided by pi; inputs outside `[-1, 1]` produce NaR. -/
@[inline] def arcCosPi (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.arcCosPi value

/-- Correctly rounded principal inverse tangent divided by pi. -/
@[inline] def arcTanPi (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.arcTanPi value

end ExecFloat.Posit
end FloatLib.Floats
