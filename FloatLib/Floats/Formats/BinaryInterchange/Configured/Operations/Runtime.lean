/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# Standard operations for configured binary values

These definitions expose the descriptor-generic operation model on the ordinary
`ExecFloat.Binary` carrier. They add no arithmetic implementation: each one calls the
descriptor-model operation through the storage codec, and `Configured.Operations.Proof` shows
that packing changes neither values, flags, nor ternary values.
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

/--
IEEE remainder, using a nearest-even integral quotient for finite operands. With `status := true`
the result also carries the `invalid` indicator.
-/
@[macro_inline] def remainder (dividend divisor : Value) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.remainder (ExecFloat.Binary.toModel dividend) (ExecFloat.Binary.toModel divisor)
          (status := true)
  | false =>
      ModelCodec.liftBinary (Model := Model format) (plan := plan)
        (fun x y => Model.remainder x y) dividend divisor

/--
Round to an integer and encode it in `mode` (nearest-even by default). With `status := true` the
result also reports fractional loss and, for a custom finite-only format that saturates, overflow.
-/
@[macro_inline] def roundToIntegral (value : Value)
    (mode : Model.IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.roundToIntegral (ExecFloat.Binary.toModel value) mode (status := true)
  | false =>
      ModelCodec.liftUnary (Model := Model format) (plan := plan)
        (fun x => Model.roundToIntegral x mode) value

/--
Multiply by `2^n` and round in `mode` (nearest-even by default), IEEE 754 (C23 draft N3220 Annex
F.3, Table F.2) `scaleB`. With
`status := true` the result also carries the IEEE exception indicators and the ternary value.
-/
@[macro_inline] def scale (value : Value) (n : Int)
    (mode : Model.IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.scale (ExecFloat.Binary.toModel value) n mode (status := true)
  | false =>
      ModelCodec.liftUnary (Model := Model format) (plan := plan)
        (fun x => Model.scale x n mode) value

/-- Exact integer-result IEEE `logB`, with no packing or exponent rounding. -/
@[inline] def logBInt (value : Value) : Model.IntegerExponentOutcome :=
  Model.logBInt (ExecFloat.Binary.toModel value)

/--
Leading binary exponent rounded to nearest-even into the configured format. `logBInt`
is the exact integer version. With `status := true` the result also carries the IEEE exception
indicators and the ternary value.
-/
@[macro_inline] def logB (value : Value) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.logB (ExecFloat.Binary.toModel value) (status := true)
  | false =>
      ModelCodec.liftUnary (Model := Model format) (plan := plan)
        (fun x => Model.logB x) value

/--
The integer that rounds the exact value of a finite configured value in `mode`, toward zero by
default as a C or Python integer cast does, or `none` for a NaN or an infinity.

The integer is unbounded, so no finite value overflows, while `roundToIntegral` keeps the result
in the format.
-/
@[inline] def toInt? (value : Value) (mode : Model.IEEERoundingMode := .towardZero) :
    Option Int :=
  (Model.toDyadic? (ExecFloat.Binary.toModel value)).map (Model.roundDyadicToInt mode)

/-- Copy the numerical sign of `signSource` onto `magnitude`. -/
@[inline] def copySign (magnitude signSource : Value) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan)
    Model.copySign magnitude signSource

/--
IEEE 754-2019 §5.5.1 `copy`: the operand unchanged, with its sign bit and, for a NaN, its
signaling state and payload. No flag is raised.
-/
@[inline] def copy (value : Value) : Value := value

/--
IEEE 754-2019 §5.7.2 `radix` (C23 `FLT_RADIX`, N3220 Table F.2): two, the radix of every
configured binary format.
-/
@[inline] def radix (_ : Value) : Nat := 2

/-- Absolute value under the configured encoding policy. -/
@[inline] def abs (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.abs value

/--
Next representable configured value in the positive direction. With `status := true` the result
also carries the `invalid` indicator of a signaling NaN.
-/
@[macro_inline] def nextUp (value : Value) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true => IEEEOutcome.ofModel <| Model.nextUp (ExecFloat.Binary.toModel value) (status := true)
  | false =>
      ModelCodec.liftUnary (Model := Model format) (plan := plan) (fun x => Model.nextUp x) value

/--
Next representable configured value in the negative direction. With `status := true` the result
also carries the `invalid` indicator of a signaling NaN.
-/
@[macro_inline] def nextDown (value : Value) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <| Model.nextDown (ExecFloat.Binary.toModel value) (status := true)
  | false =>
      ModelCodec.liftUnary (Model := Model format) (plan := plan) (fun x => Model.nextDown x) value

/--
IEEE 754-2019 §9.6 `minimum`, the operation that `min left right` runs: the lesser operand, with
`-0` below `+0`, or a quiet NaN when an operand is a NaN. With `status := true` the result also
carries the `invalid` indicator of a signaling NaN operand.
-/
@[macro_inline] def minimum (left right : Value) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.minimum (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
          (status := true)
  | false =>
      ModelCodec.liftBinary (Model := Model format) (plan := plan)
        (fun x y => Model.minimum x y) left right

/--
IEEE 754-2019 §9.6 `maximum`, the operation that `max left right` runs: the greater operand, with
`+0` above `-0`, or a quiet NaN when an operand is a NaN. With `status := true` the result also
carries the `invalid` indicator of a signaling NaN operand.
-/
@[macro_inline] def maximum (left right : Value) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.maximum (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
          (status := true)
  | false =>
      ModelCodec.liftBinary (Model := Model format) (plan := plan)
        (fun x y => Model.maximum x y) left right

/--
IEEE 754-2019 §9.6 `minimumNumber`: the lesser operand, with `-0` below `+0`, and the number when
the other operand is a NaN, quiet or signaling. Two NaNs give a quiet NaN. With `status := true`
the result also carries the `invalid` indicator that a signaling NaN raises, including when the
other operand is a number and supplies the result.
-/
@[macro_inline] def minimumNumber (left right : Value) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.minimumNumber (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
          (status := true)
  | false =>
      ModelCodec.liftBinary (Model := Model format) (plan := plan)
        (fun x y => Model.minimumNumber x y) left right

/--
IEEE 754-2019 §9.6 `maximumNumber`: the greater operand, with `+0` above `-0`, and the number when
the other operand is a NaN, quiet or signaling. Two NaNs give a quiet NaN. With `status := true`
the result also carries the `invalid` indicator that a signaling NaN raises, including when the
other operand is a number and supplies the result.
-/
@[macro_inline] def maximumNumber (left right : Value) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.maximumNumber (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
          (status := true)
  | false =>
      ModelCodec.liftBinary (Model := Model format) (plan := plan)
        (fun x y => Model.maximumNumber x y) left right

/-! ## Integral rounding and conversion to an integer by the names of the standard -/

ieee_by_direction "IEEE 754-2019 §5.3.1" roundToIntegral (value : Value) : Value :=
  fun mode => roundToIntegral value (mode := mode)

/--
IEEE 754-2019 §5.3.1 `roundToIntegralExact`: `roundToIntegral` in the direction `mode`, the
rounding-direction attribute (nearest-even by default), with its flags: `inexact` is raised
when the result differs from the operand.
-/
@[inline] def roundToIntegralExact (value : Value)
    (mode : Model.IEEERoundingMode := .nearest) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  roundToIntegral value mode (status := true)

ieee_by_direction "IEEE 754-2019 §5.4.1" convertToInteger of toInt? (value : Value) :
    Option Int := fun mode => toInt? value mode

end FloatLib.Floats.ExecFloat.Binary
