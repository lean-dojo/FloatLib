/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime

/-!
# Explicit rounding runtime for configured binary values

The six IEEE arithmetic operations lift from the descriptor model to the ordinary configured
`ExecFloat.Binary` carrier with an explicit rounding direction:

```lean
open scoped FloatLib.IEEERounding

ExecFloat.Binary.add x y (rounding := +∞)
ExecFloat.Binary.div x y (rounding := -∞)
```

Operands come first. The rounding argument is required and may be supplied by name. No global
floating-point environment or rounding-mode instance is changed.

The constructor names `.towardPositiveInfinity` and `.towardNegativeInfinity` are always
available. The shorter `+∞` and `-∞` terms are opt-in so they do not collide with extended-real
notation elsewhere in a development.

These functions round one primitive operation. To evaluate an algebraic expression exactly and
round only its final result, use `ExecFloat.ExactExpression` with `ExecFloat.roundOnceWith` and a
binary conversion context built by `ExecFloat.Binary.Conversion.Context.withRounding`.

The `*WithStatus` variants return the configured value together with the five IEEE exception
indicators computed by the descriptor model. There is no hidden floating-point environment:
applications that need sticky flags combine successive statuses explicitly with
`Numerics.IEEEStatus.union`.

FMA means fused multiply-add. It forms the exact value `x * y + z` and rounds once; ordinary
`x * y + z` rounds the product and then the sum. IEEE 754 specifies FMA as a primitive, including
its exceptional-value and status behavior. `ExactExpression` handles larger finite algebraic
expressions.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/--
A configured binary result paired with the IEEE exception indicators raised by one operation.

This is an alias for a pair rather than another result structure. Pattern matching exposes the
configured value first and its `Model.IEEEStatus` second.
-/
abbrev IEEEOutcome := Value × Model.IEEEStatus

namespace IEEEOutcome

/-- Repack a model outcome without changing any IEEE exception indicator. -/
@[always_inline, inline] def ofModel (outcome : Model.IEEEOutcome format) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  (ExecFloat.Binary.ofModel outcome.value, outcome.status)

/-- Decode the value component of a configured outcome, preserving its status exactly. -/
@[inline] def toModel (outcome : IEEEOutcome (format := format) (plan := plan) (code := code)) :
    Model.IEEEOutcome format :=
  { value := ExecFloat.Binary.toModel outcome.1, status := outcome.2 }

end IEEEOutcome

/-- Add two configured values and round the exact sum in the selected IEEE direction. -/
@[inline] def add
    (left right : Value) (rounding : Model.IEEERoundingMode) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan)
    (Model.addWithRounding rounding) left right

/-- Subtract two configured values and round the exact difference in the selected direction. -/
@[inline] def sub
    (left right : Value) (rounding : Model.IEEERoundingMode) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan)
    (Model.subWithRounding rounding) left right

/-- Multiply two configured values and round the exact product in the selected direction. -/
@[inline] def mul
    (left right : Value) (rounding : Model.IEEERoundingMode) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan)
    (Model.mulWithRounding rounding) left right

/-- Divide two configured values and round the exact quotient in the selected direction. -/
@[inline] def div
    (left right : Value) (rounding : Model.IEEERoundingMode) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan)
    (Model.divWithRounding rounding) left right

/--
Form the exact product-plus-addend and round once in the selected direction.

This is the IEEE fused operation; `mul` followed by `add` rounds twice.
-/
@[inline] def fma
    (left right addend : Value) (rounding : Model.IEEERoundingMode) : Value :=
  ModelCodec.liftTernary (Model := Model format) (plan := plan)
    (Model.fmaWithRounding rounding) left right addend

/-- Take square root and round the exact nonnegative result in the selected direction. -/
@[inline] def sqrt
    (value : Value) (rounding : Model.IEEERoundingMode) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (Model.sqrtWithRounding rounding) value

/-! ## Status-bearing operations -/

/-- Add with an explicit rounding direction and return all IEEE exception indicators. -/
@[inline] def addWithStatus
    (left right : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  IEEEOutcome.ofModel <|
    Model.addWithStatus
      (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) rounding

/-- Subtract with an explicit rounding direction and return all IEEE exception indicators. -/
@[inline] def subWithStatus
    (left right : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  IEEEOutcome.ofModel <|
    Model.subWithStatus
      (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) rounding

/-- Multiply with an explicit rounding direction and return all IEEE exception indicators. -/
@[inline] def mulWithStatus
    (left right : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  IEEEOutcome.ofModel <|
    Model.mulWithStatus
      (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) rounding

/-- Divide with an explicit rounding direction and return all IEEE exception indicators. -/
@[inline] def divWithStatus
    (left right : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  IEEEOutcome.ofModel <|
    Model.divWithStatus
      (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) rounding

/-- Fused multiply-add with an explicit rounding direction and IEEE exception indicators. -/
@[inline] def fmaWithStatus
    (left right addend : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  IEEEOutcome.ofModel <|
    Model.fmaWithStatus
      (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
      (ExecFloat.Binary.toModel addend) rounding

/-- Square root with an explicit rounding direction and return all IEEE exception indicators. -/
@[inline] def sqrtWithStatus
    (value : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  IEEEOutcome.ofModel <|
    Model.sqrtWithStatus (ExecFloat.Binary.toModel value) rounding

end FloatLib.Floats.ExecFloat.Binary
