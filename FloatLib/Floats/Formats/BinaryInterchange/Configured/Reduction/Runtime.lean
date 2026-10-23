/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Runtime

/-!
# Correctly rounded reductions for configured binary values

These functions lift the format-generic reduction kernel to the ordinary configured
`ExecFloat.Binary` carrier. Operands are decoded into the exact model, reduced there, and the
single final result is packed back into the configured carrier.

For finite operands, `sum` forms the exact mathematical sum and rounds once. `dot` forms every
product exactly, sums those products exactly, and rounds once. The configured type fixes the
source and destination format, and the rounding direction is an optional argument.
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
Correctly rounded sum of configured values in `mode` (nearest-even by default).

Every operand is decoded exactly, the complete sum is accumulated without intermediate rounding,
and the result is rounded once. With `status := true` the result also carries the IEEE exception
indicators and the ternary value. The value form packs the value-only descriptor-model sum, which
computes no exception indicators.
-/
@[macro_inline] def sum (values : Array Value) (mode : Model.IEEERoundingMode := .nearest)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.sum format (values.map ExecFloat.Binary.toModel) mode (status := true)
  | false =>
      ExecFloat.Binary.ofModel (Model.sum format (values.map ExecFloat.Binary.toModel) mode)

/-- List entry point for correctly rounded configured summation, with the options of `sum`. -/
@[macro_inline] def sumList (values : List Value) (mode : Model.IEEERoundingMode := .nearest)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  sum values.toArray mode status

/--
Correctly rounded dot product of configured values in `mode` (nearest-even by default).

Products and their sum are exact until one final rounding. Unequal lengths return
`ReductionError.lengthMismatch`, so no pair is silently dropped. With `status := true` a
successful result also carries the IEEE exception indicators and the ternary value. The value
form packs the value-only descriptor-model dot product, which computes no exception indicators.
-/
@[macro_inline] def dot (left right : Array Value) (mode : Model.IEEERoundingMode := .nearest)
    (status : Bool := false) :
    Except Numerics.ReductionError (match status with
      | true => IEEEOutcome (format := format) (plan := plan) (code := code)
      | false => Value) :=
  match status with
  | true =>
      (Model.dot format
          (left.map ExecFloat.Binary.toModel)
          (right.map ExecFloat.Binary.toModel)
          mode (status := true)).map IEEEOutcome.ofModel
  | false =>
      (Model.dot format
          (left.map ExecFloat.Binary.toModel)
          (right.map ExecFloat.Binary.toModel)
          mode).map ExecFloat.Binary.ofModel

/-- List entry point for a correctly rounded configured dot product, with the options of `dot`. -/
@[macro_inline] def dotList (left right : List Value) (mode : Model.IEEERoundingMode := .nearest)
    (status : Bool := false) :
    Except Numerics.ReductionError (match status with
      | true => IEEEOutcome (format := format) (plan := plan) (code := code)
      | false => Value) :=
  dot left.toArray right.toArray mode status

end FloatLib.Floats.ExecFloat.Binary
