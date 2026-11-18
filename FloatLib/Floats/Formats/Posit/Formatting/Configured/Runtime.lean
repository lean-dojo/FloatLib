/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime
public import FloatLib.Floats.Formats.Posit.Formatting

/-!
# Decimal conversion for configured posits

A configured posit reads and prints decimals by handing them to the exact-width model through its
selected storage codec. Packing adds no rounding of its own. Native and limb carriers use the same
interface.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Posit Standard (2022), §6.3: exact decimal display through the selected storage codec. -/
def display (value : Value) : String :=
  Model.display (toModel value)

/-- Posit Standard (2022), §6.3: exact decimal input, rounded once through the selected codec. -/
def parse (input : String) : Except Model.ParseError Value :=
  (Model.parse format input).map ofModel

end ExecFloat.Posit
end FloatLib.Floats
