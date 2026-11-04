/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Logarithm.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Configured base-two and base-ten posit logarithms

Base-two and base-ten logarithms on a configured posit reuse the exact model logarithm through the
carrier's lawful codec, so packed words and wide carriers alike get the once-rounded result and
all of the model's behavior on exceptional inputs.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Correctly rounded base-two logarithm. NaR and nonpositive inputs produce NaR. -/
@[inline] def log2 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.log2 value

/-- Correctly rounded base-ten logarithm. NaR and nonpositive inputs produce NaR. -/
@[inline] def log10 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.log10 value

/-- Base-two logarithm of exact `1 + x`, with one final rounding. -/
@[inline] def log2Plus1 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.log2Plus1 value

/-- Base-ten logarithm of exact `1 + x`, with one final rounding. -/
@[inline] def log10Plus1 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.log10Plus1 value

end ExecFloat.Posit
end FloatLib.Floats
