/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# Standard operations for configured binary values

These definitions expose the descriptor-generic operation model on the ordinary
`ExecFloat.Binary` carrier. They add no arithmetic implementation and preserve exception status
exactly across the packing boundary.

The definitions call the descriptor-model operations through the storage codec. The companion
proof module shows that packing changes neither values nor flags.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/-- IEEE remainder, using a nearest-even integral quotient for finite operands. -/
@[inline] def remainder (dividend divisor : Value) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan)
    Model.remainder dividend divisor

/-- IEEE remainder together with its exception indicators. -/
@[inline] def remainderWithStatus
    (dividend divisor : Value) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  IEEEOutcome.ofModel <|
    Model.remainderWithStatus
      (ExecFloat.Binary.toModel dividend)
      (ExecFloat.Binary.toModel divisor)

/--
Round to an integer and encode it in the selected direction. A custom finite-only format can
saturate; use `roundToIntegralExactWithStatus` to detect that overflow.
-/
@[inline] def roundToIntegral
    (value : Value) (rounding : Model.IEEERoundingMode) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (Model.roundToIntegral · rounding) value

/-- Round to an integer, encode it in the same direction, and report fractional loss or overflow. -/
@[inline] def roundToIntegralExactWithStatus
    (value : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  IEEEOutcome.ofModel <|
    Model.roundToIntegralExactWithStatus (ExecFloat.Binary.toModel value) rounding

/-- Multiply by `2^n` and round in the selected direction (IEEE 754 `scaleB`). -/
@[inline] def scale
    (value : Value) (n : Int) (rounding : Model.IEEERoundingMode) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (Model.scale · n rounding) value

/-- Power-of-two scaling with the IEEE exception indicators. -/
@[inline] def scaleWithStatus
    (value : Value) (n : Int) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  IEEEOutcome.ofModel <|
    Model.scaleWithStatus (ExecFloat.Binary.toModel value) n rounding

/-- Leading binary exponent, rounded into the same configured format (IEEE 754 `logB`). -/
@[inline] def binaryExponent (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.binaryExponent value

/-- Return the leading binary exponent and its IEEE exception indicators. -/
@[inline] def binaryExponentWithStatus
    (value : Value) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  IEEEOutcome.ofModel <| Model.binaryExponentWithStatus (ExecFloat.Binary.toModel value)

/-- Copy the numerical sign of `signSource` onto `magnitude`. -/
@[inline] def copySign (magnitude signSource : Value) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan)
    Model.copySign magnitude signSource

/-- Absolute value under the configured encoding policy. -/
@[inline] def abs (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.abs value

/-- Next representable configured value in the positive direction. -/
@[inline] def nextUp (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.nextUp value

/-- Next representable configured value in the negative direction. -/
@[inline] def nextDown (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.nextDown value

/-- IEEE-2008-style `minNum`, retaining the numeric operand against one quiet NaN. -/
@[inline] def minNum (left right : Value) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan) Model.minNum left right

/-- IEEE-2008-style `maxNum`, retaining the numeric operand against one quiet NaN. -/
@[inline] def maxNum (left right : Value) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan) Model.maxNum left right

end FloatLib.Floats.ExecFloat.Binary
