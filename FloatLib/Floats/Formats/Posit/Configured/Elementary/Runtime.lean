/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Elementary.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Configured natural posit elementary functions

Every lawful configured carrier uses the same correctly rounded model operation. The codec
changes the storage representation without adding an intermediate numerical rounding.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Correctly rounded natural exponential; NaR propagates. -/
@[inline] def exp (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.exp value

/-- Exact exponential minus one, with a single final posit rounding. -/
@[inline] def expMinus1 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.expMinus1 value

/-- Correctly rounded natural logarithm; NaR and nonpositive inputs produce NaR. -/
@[inline] def log (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.log value

/-- Natural logarithm of exact `1 + x`, with a single final posit rounding. -/
@[inline] def logPlus1 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.logPlus1 value

end ExecFloat.Posit
end FloatLib.Floats
