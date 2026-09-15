/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Hyperbolic.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Configured posit hyperbolic functions

A lawful model codec changes storage without adding numerical rounding. The operations
inherit the model's NaR propagation and real-domain checks.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Correctly rounded hyperbolic tangent; NaR propagates. -/
@[inline] def tanH (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.tanH value

/-- Correctly rounded inverse hyperbolic tangent, with real domain `-1 < x < 1`. -/
@[inline] def arcTanH (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.arcTanH value

/-- Correctly rounded hyperbolic sine; NaR propagates. -/
@[inline] def sinH (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.sinH value

/-- Correctly rounded hyperbolic cosine; NaR propagates. -/
@[inline] def cosH (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.cosH value

/-- Correctly rounded inverse hyperbolic sine; NaR propagates. -/
@[inline] def arcSinH (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.arcSinH value

/-- Correctly rounded inverse hyperbolic cosine; inputs below `1` produce NaR. -/
@[inline] def arcCosH (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.arcCosH value

end ExecFloat.Posit
end FloatLib.Floats
