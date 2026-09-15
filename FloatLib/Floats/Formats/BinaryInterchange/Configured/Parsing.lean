/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.BoundedParsing
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof

/-!
# Character input for configured binary values

Configured binary values use the descriptor model's exact character parser. A successful parse
changes only the storage representation; the decoded numerical value is unchanged.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/--
Parse decimal, hexadecimal, dyadic, or special text with nearest-even rounding by default.

Set `rounding` to choose another direction. With `limits := true`, `maxBytes` bounds the
original UTF-8 input and `maxExponent` bounds its adjusted exponent before exact conversion.
Set `status := true` to return the value together with all five IEEE exception flags.
Malformed or oversized input returns `Model.ParseError`.
-/
def parse (input : String) (rounding : Model.IEEERoundingMode := .nearestEven)
    (limits : Bool := false) (maxBytes : Nat := 4096) (maxExponent : Nat := 10000)
    (status : Bool := false) :
    Except Model.ParseError (match status with
      | true => IEEEOutcome (format := format) (plan := plan) (code := code)
      | false => FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  match status with
  | true =>
      (Model.parse format input rounding limits maxBytes maxExponent true).map IEEEOutcome.ofModel
  | false =>
      (Model.parse format input rounding limits maxBytes maxExponent false).map ofModel

/-- Decoding a parsed configured value recovers exactly the descriptor-model result. -/
theorem map_toModel_parse (input : String) (rounding : Model.IEEERoundingMode)
    (limits : Bool) (maxBytes maxExponent : Nat) :
    (parse (format := format) (plan := plan) (code := code)
      input rounding limits maxBytes maxExponent).map toModel =
      Model.parse format input rounding limits maxBytes maxExponent := by
  cases h : Model.parse format input rounding limits maxBytes maxExponent <;>
    simp [parse, h, Except.map]

/-- Requesting status preserves every model bit and IEEE flag across the storage conversion. -/
theorem map_toModel_parse_status (input : String) (rounding : Model.IEEERoundingMode)
    (limits : Bool) (maxBytes maxExponent : Nat) :
    (parse (format := format) (plan := plan) (code := code)
      input rounding limits maxBytes maxExponent (status := true)).map IEEEOutcome.toModel =
      Model.parse format input rounding limits maxBytes maxExponent (status := true) := by
  cases h : Model.parse format input rounding limits maxBytes maxExponent (status := true) <;>
    simp [parse, h, Except.map]

end FloatLib.Floats.ExecFloat.Binary
