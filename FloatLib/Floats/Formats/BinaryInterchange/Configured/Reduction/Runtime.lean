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
source and destination format, while the rounding direction remains an explicit argument.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/--
Correctly sum configured values and return the result with IEEE exception indicators.

Every operand is decoded exactly, the complete sum is accumulated without intermediate rounding,
and the result is rounded once in `rounding`.
-/
def sumWithStatus (values : Array Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  IEEEOutcome.ofModel <|
    Model.sumWithStatus format (values.map ExecFloat.Binary.toModel) rounding

/-- Correctly sum configured values with one final rounding. -/
@[inline] def sum (values : Array Value) (rounding : Model.IEEERoundingMode) : Value :=
  (sumWithStatus values rounding).1

/-- List entry point for correctly rounded configured summation with status. -/
@[inline] def sumListWithStatus
    (values : List Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  sumWithStatus values.toArray rounding

/-- List entry point for correctly rounded configured summation. -/
@[inline] def sumList (values : List Value) (rounding : Model.IEEERoundingMode) : Value :=
  sum values.toArray rounding

/--
Correctly compute a configured dot product and return IEEE exception indicators.

Products and their sum are exact until one final rounding. Unequal lengths return
`ReductionError.lengthMismatch`; no pair is silently discarded.
-/
def dotWithStatus (left right : Array Value) (rounding : Model.IEEERoundingMode) :
    Except Numerics.ReductionError
      (IEEEOutcome (format := format) (plan := plan) (code := code)) :=
  (Model.dotWithStatus format
      (left.map ExecFloat.Binary.toModel)
      (right.map ExecFloat.Binary.toModel)
      rounding).map IEEEOutcome.ofModel

/-- Correctly compute a configured dot product with one final rounding. -/
@[inline] def dot (left right : Array Value) (rounding : Model.IEEERoundingMode) :
    Except Numerics.ReductionError Value :=
  (dotWithStatus left right rounding).map Prod.fst

/-- List entry point for a correctly rounded configured dot product with status. -/
@[inline] def dotListWithStatus
    (left right : List Value) (rounding : Model.IEEERoundingMode) :
    Except Numerics.ReductionError
      (IEEEOutcome (format := format) (plan := plan) (code := code)) :=
  dotWithStatus left.toArray right.toArray rounding

/-- List entry point for a correctly rounded configured dot product. -/
@[inline] def dotList
    (left right : List Value) (rounding : Model.IEEERoundingMode) :
    Except Numerics.ReductionError Value :=
  dot left.toArray right.toArray rounding

end FloatLib.Floats.ExecFloat.Binary
