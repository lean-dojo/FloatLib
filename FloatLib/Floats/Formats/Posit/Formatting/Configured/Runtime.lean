/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Formatting
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Decimal conversion for configured posits

The selected storage codec forwards decimal input and display to the exact-width model. Packing
introduces no additional rounding. This interface works with native and explicit limb carriers.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Exact decimal display through the selected posit storage codec. -/
def display (value : Value) : String :=
  Model.display (toModel value)

/-- Exact decimal input, rounded once and packed into the selected posit storage carrier. -/
def parse (input : String) : Except Model.ParseError Value :=
  (Model.parse format input).map ofModel

end ExecFloat.Posit
end FloatLib.Floats
