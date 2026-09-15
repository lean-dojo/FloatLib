/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Formatting.Configured.Runtime
public import FloatLib.Floats.Formats.Posit.Formatting.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Instances
import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Proof

/-!
# Configured posit decimal preservation

Exact model preservation and the codec inverse law imply decimal round trips for every supported
storage carrier and posit width.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Parsing the exact decimal display preserves the complete configured posit value. -/
@[simp] theorem parse_display (value : Value) :
    parse (display value) = .ok value := by
  simp [parse, display, Except.map, ofModel, toModel]

/-- A successful decimal input has precisely the model rounder's result after decoding. -/
theorem toModel_parse (input : String) :
    (parse (format := format) (plan := plan) (code := code) input).map toModel =
      Model.parse format input := by
  cases hparse : Model.parse format input <;>
    simp [parse, hparse, Except.map, toModel, ofModel]

/-- Exact decimal parsing inverts the configured `ToString` display. -/
@[simp] theorem parse_toString (value : Value) :
    parse (toString value) = .ok value :=
  parse_display value

end ExecFloat.Posit
end FloatLib.Floats
