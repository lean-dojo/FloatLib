/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Posit.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Configured posit and decimal conversion

The selected posit carrier is decoded or encoded through its lawful model codec.
All numerical work is performed by the shared model conversion.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion

open FloatLib.Floats
open FloatLib.Floats.Formats

variable {format : Posit.Format} {plan : Posit.Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Posit.Model format) code]

local notation "Value" => ExecFloat (Posit.Configured.Family format code plan)

/-- Convert a configured posit to decimal through its exact model decoder. -/
@[inline] def fromConfiguredPosit (target : Format) (mode : RoundingMode)
    (x : Value) : Outcome :=
  fromPosit target mode (ExecFloat.Posit.toModel x)

/-- Convert decimal to the configured posit, with one model rounding and exact encoding. -/
@[inline] def toConfiguredPosit (x : Datum) : Value :=
  ExecFloat.Posit.ofModel (toPosit format x)

end FloatLib.Floats.Formats.DecimalInterchange.Conversion
