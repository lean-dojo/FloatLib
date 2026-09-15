/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.DecimalFormatting

/-! # External character output for configured binary values

Storage selection affects neither the characters nor the exception indicators.
The descriptor model supplies the shared decimal and hexadecimal algorithms.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {fmt : FloatFormat} {plan : Configured.StoragePlan fmt} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model fmt) code]

local notation "Value" => FloatLib.Floats.ExecFloat (Configured.Family fmt code plan)

/-- Decimal or hexadecimal output at exact or requested precision, including rounding status. -/
def formatWithStatus (rounding : Model.IEEERoundingMode) (radix : Model.TextRadix)
    (precision : Model.TextPrecision) (value : Value) : Model.TextOutcome :=
  Model.formatWithStatus rounding radix precision (toModel value)

/-- Exact decimal output, preserving the sign and diagnostic information of special values. -/
def formatDecimal (value : Value) : String := Model.formatDecimal (toModel value)

/-- Exact hexadecimal output with an integral significand and a decimal binary exponent. -/
def formatHex (value : Value) : String := Model.formatHex (toModel value)

/-- Fixed or scientific decimal output, with explicit rounding and exception status. -/
def formatDecimalWithStatus (rounding : Model.IEEERoundingMode) (style : Model.DecimalStyle)
    (value : Value) : Model.TextOutcome :=
  Model.formatDecimalWithStatus rounding style (toModel value)

/-- Nearest-even fixed output with exactly `places` digits after the decimal point. -/
def formatFixed (value : Value) (places : Nat) : String :=
  Model.formatFixed (toModel value) places

/-- Nearest-even scientific output with `places + 1` significant digits. -/
def formatScientific (value : Value) (places : Nat) : String :=
  Model.formatScientific (toModel value) places

/-- Decimal notation and its status flags are independent of the storage representation. -/
@[simp] theorem formatDecimalWithStatus_ofModel (rounding : Model.IEEERoundingMode)
    (style : Model.DecimalStyle) (value : Model fmt) :
    formatDecimalWithStatus rounding style (ofModel (plan := plan) (code := code) value) =
      Model.formatDecimalWithStatus rounding style value := by
  simp [formatDecimalWithStatus]

/-- Repacking a value does not change fixed decimal output. -/
@[simp] theorem formatFixed_ofModel (value : Model fmt) (places : Nat) :
    formatFixed (ofModel (plan := plan) (code := code) value) places =
      Model.formatFixed value places := by
  simp [formatFixed]

/-- Repacking a value does not change scientific decimal output. -/
@[simp] theorem formatScientific_ofModel (value : Model fmt) (places : Nat) :
    formatScientific (ofModel (plan := plan) (code := code) value) places =
      Model.formatScientific value places := by
  simp [formatScientific]

/-- Configured precision output is identical to descriptor-model output, including status. -/
@[simp] theorem formatWithStatus_ofModel (rounding : Model.IEEERoundingMode)
    (radix : Model.TextRadix) (precision : Model.TextPrecision) (value : Model fmt) :
    formatWithStatus rounding radix precision (ofModel (plan := plan) (code := code) value) =
      Model.formatWithStatus rounding radix precision value := by
  simp [formatWithStatus]

/-- Repacking a model word leaves its exact decimal output unchanged. -/
@[simp] theorem formatDecimal_ofModel (value : Model fmt) :
    formatDecimal (ofModel (plan := plan) (code := code) value) = Model.formatDecimal value := by
  simp [formatDecimal]

/-- Repacking a model word leaves its exact hexadecimal output unchanged. -/
@[simp] theorem formatHex_ofModel (value : Model fmt) :
    formatHex (ofModel (plan := plan) (code := code) value) = Model.formatHex value := by
  simp [formatHex]

end FloatLib.Floats.ExecFloat.Binary
