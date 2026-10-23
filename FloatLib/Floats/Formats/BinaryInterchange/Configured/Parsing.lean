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
differs from the model's only in storage representation, so the decoded numerical value is the
same.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/--
Parse decimal, hexadecimal, dyadic, or special text with nearest-even rounding by default.

Set `mode` to choose another direction. With `limits := some bounds`, `bounds.maxBytes` bounds the
original UTF-8 input and `bounds.maxExponent` bounds its adjusted exponent before exact conversion,
and `some {}` selects the default bounds. Set `status := true` to return the value together with
all five IEEE exception flags and the ternary value. Malformed or oversized input returns
`Model.ParseError`.
-/
def parse (input : String) (mode : Model.IEEERoundingMode := .nearest)
    (limits : Option Model.ParseLimits := none) (status : Bool := false) :
    Except Model.ParseError (match status with
      | true => IEEEOutcome (format := format) (plan := plan) (code := code)
      | false => FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  match status with
  | true =>
      (Model.parse format input mode limits true).map IEEEOutcome.ofModel
  | false =>
      (Model.parse format input mode limits false).map ofModel

/-- Decoding a parsed configured value gives the descriptor-model result. -/
theorem map_toModel_parse (input : String) (mode : Model.IEEERoundingMode)
    (limits : Option Model.ParseLimits) :
    (parse (format := format) (plan := plan) (code := code)
      input mode limits).map toModel =
      Model.parse format input mode limits := by
  cases h : Model.parse format input mode limits <;>
    simp [parse, h, Except.map]

/--
Requesting status preserves every model bit, IEEE flag, and the ternary value across the storage
conversion.
-/
theorem map_toModel_parse_status (input : String) (mode : Model.IEEERoundingMode)
    (limits : Option Model.ParseLimits) :
    (parse (format := format) (plan := plan) (code := code)
      input mode limits (status := true)).map IEEEOutcome.toModel =
      Model.parse format input mode limits (status := true) := by
  cases h : Model.parse format input mode limits (status := true) <;>
    simp [parse, h, Except.map]

end FloatLib.Floats.ExecFloat.Binary
