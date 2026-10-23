/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Dispatch
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Conversion
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime

/-!
# Arithmetic runtime for configured binary values

The six IEEE arithmetic operations lift from the descriptor model to configured binary values with
the model's options, a rounding direction `mode` and `status`:

```lean
open FloatLib.Rounding

ExecFloat.Binary.add x y (mode := up)
ExecFloat.Binary.div x y (mode := down) (status := true)
```

Operands come first, and `mode` defaults to nearest-even. The direction and status are ordinary
arguments and results, and no rounding-mode instance is changed.

The constructor names `.up` and `.down` are always available, and `open FloatLib.Rounding` lets
callers write them bare.

The default call, nearest-even without status, runs the certified implementation selected for the
format, the same `ExecFloat.add` through `ExecFloat.fma` that the operators `+`, `-`, `*`, `/`
run, so `x.add y`, `ExecFloat.Binary.add x y`, and `x + y` compile to the same kernel call. The
other directions, and every call with `status := true`, decode the operands through the
configured codec, run the model operation with the same options, and encode the result. Square
root sends nearest-away rounding to the selected kernel too, since an exact square root is never a
tie.

Each operation is a `@[macro_inline]` selector, so with literal options only the chosen branch is
compiled. Its decoding theorem `toModel_add` and its siblings in `Configured.Rounding.Proof` hold
for every capability whose reference operation is the configured model operation, which is true of
every capability instance this library declares.

These functions round one primitive operation. To evaluate an algebraic expression exactly and
round only its final result, use `ExecFloat.ExactExpression` with `ExecFloat.roundOnce`, which
takes the same `(mode := ...)` option.

With `status := true` an operation returns the configured value together with the five IEEE
exception indicators and the ternary value computed by the descriptor model. There is no hidden
floating-point environment: `IEEEOutcome.bind` feeds one result to the next operation and keeps
the union of their flags, which are sticky in the IEEE sense.

`ofRat q` rounds an exact rational once into the format with the same `mode` and `status` options.
Literals are rounded the same way.

FMA means fused multiply-add. It forms the exact value `x * y + z` and rounds once, while ordinary
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
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/--
A configured binary result with the IEEE exception indicators and the ternary value of one
operation.

The fields mirror `Model.IEEEOutcome`, with the value in configured storage. The numeric
projections `.1`, `.2`, and `.3` select the value, the status, and the ternary value.
-/
structure IEEEOutcome where
  /-- Delivered configured result. -/
  value : Value
  /-- Exception indicators raised while computing `value`. -/
  status : Numerics.IEEEStatus
  /-- The delivered value compared with the exact result, as `Model.IEEEOutcome.ternary`. -/
  ternary : Ordering

namespace IEEEOutcome

/-- Repack a model outcome without changing any IEEE exception indicator or the ternary value. -/
@[always_inline, inline] def ofModel (outcome : Model.IEEEOutcome format) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  { value := ExecFloat.Binary.ofModel outcome.value
    status := outcome.status
    ternary := outcome.ternary }

/--
Decode the value component of a configured outcome, preserving its status and ternary value.
-/
@[inline] def toModel (outcome : IEEEOutcome (format := format) (plan := plan) (code := code)) :
    Model.IEEEOutcome format :=
  { value := ExecFloat.Binary.toModel outcome.value
    status := outcome.status
    ternary := outcome.ternary }

/--
Feed the value of `outcome` to the next operation `next`, keeping the union of both statuses and
the ternary value of `next`.

The flags are sticky: a flag raised by either step is set in the result. The ternary value is not
accumulated. It compares the final value with the exact result of `next` on its rounded input,
not with the exact value of the whole computation.

```lean
(ExecFloat.Binary.div x y (status := true)).bind fun q => ExecFloat.Binary.sqrt q (status := true)
```
-/
@[inline] def bind (outcome : IEEEOutcome (format := format) (plan := plan) (code := code))
    (next : Value → IEEEOutcome (format := format) (plan := plan) (code := code)) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  let result := next outcome.value
  { result with status := outcome.status.union result.status }

/-- `#eval` shows the three fields, displaying the value as its format does. -/
instance [Repr (FloatLib.Floats.ExecFloat (Configured.Family format code plan))] :
    Repr (IEEEOutcome (format := format) (plan := plan) (code := code)) where
  reprPrec outcome _ :=
    Std.Format.bracket "{ "
      (Std.Format.joinSep
        [f!"value := {repr outcome.value}", f!"status := {repr outcome.status}",
          f!"ternary := {repr outcome.ternary}"]
        ("," ++ Std.Format.line))
      " }"

/--
The default outcome has the supplied default value, a clear status, and the ternary value `.eq`.
With the standard configured binary value instance, that value is `+0`.
-/
instance [Inhabited (FloatLib.Floats.ExecFloat (Configured.Family format code plan))] :
    Inhabited (IEEEOutcome (format := format) (plan := plan) (code := code)) where
  default := { value := default, status := .clear, ternary := .eq }

/--
Boolean equality compares the three fields, the value with its own `==`. For configured binary
values that is IEEE numerical comparison, so outcomes holding NaNs are unequal.
-/
instance [BEq (FloatLib.Floats.ExecFloat (Configured.Family format code plan))] :
    BEq (IEEEOutcome (format := format) (plan := plan) (code := code)) where
  beq left right :=
    left.value == right.value && left.status == right.status && left.ternary == right.ternary

/-- Structural equality of the three fields. -/
instance [DecidableEq (FloatLib.Floats.ExecFloat (Configured.Family format code plan))] :
    DecidableEq (IEEEOutcome (format := format) (plan := plan) (code := code)) :=
  fun left right =>
    if h : left.value = right.value ∧ left.status = right.status ∧
        left.ternary = right.ternary then
      isTrue (by
        cases left
        cases right
        obtain ⟨hvalue, hstatus, hternary⟩ := h
        simp_all)
    else
      isFalse (fun hequal => h ⟨congrArg value hequal, congrArg status hequal,
        congrArg ternary hequal⟩)

end IEEEOutcome

/--
Round an exact rational once into the configured format, in `mode` (nearest-even by default). With
`status := true` the result also carries the IEEE exception indicators and the ternary value.

The expected type selects the format, as in `(ExecFloat.Binary.ofRat (1 / 3) (mode := up) :
Binary32)`. Numeric and scientific literals round the same way, to nearest-even.
-/
@[macro_inline] def ofRat (q : Rat) (mode : Model.IEEERoundingMode := .nearest)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true => IEEEOutcome.ofModel (Model.ofRat format q (mode := mode) (status := true))
  | false => ExecFloat.Binary.ofModel (Model.ofRat format q (mode := mode))

/--
Add two configured values, rounding the exact sum in `mode` (nearest-even by default). With
`status := true` the result also carries the IEEE exception indicators and the ternary value.

Nearest-even addition without status is `ExecFloat.add`, the selected kernel that `+` runs.
-/
@[macro_inline] def add [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [ExecFloat.Add (Configured.Family format code plan)]
    (left right : Value) (mode : Model.IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.add (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
          (mode := mode) (status := true)
  | false =>
      match mode with
      | .nearest => ExecFloat.add left right
      | mode =>
          ModelCodec.liftBinary (Model := Model format) (plan := plan)
            (fun x y => Model.add x y (mode := mode)) left right

/--
Subtract two configured values, rounding the exact difference in `mode` (nearest-even by
default). With `status := true` the result also carries the IEEE exception indicators and the
ternary value.

Nearest-even subtraction without status is `ExecFloat.sub`, the selected kernel that `-` runs.
-/
@[macro_inline] def sub [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [ExecFloat.Sub (Configured.Family format code plan)]
    (left right : Value) (mode : Model.IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.sub (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
          (mode := mode) (status := true)
  | false =>
      match mode with
      | .nearest => ExecFloat.sub left right
      | mode =>
          ModelCodec.liftBinary (Model := Model format) (plan := plan)
            (fun x y => Model.sub x y (mode := mode)) left right

/--
Multiply two configured values, rounding the exact product in `mode` (nearest-even by default).
With `status := true` the result also carries the IEEE exception indicators and the ternary value.

Nearest-even multiplication without status is `ExecFloat.mul`, the selected kernel that `*` runs.
-/
@[macro_inline] def mul [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [ExecFloat.Mul (Configured.Family format code plan)]
    (left right : Value) (mode : Model.IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.mul (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
          (mode := mode) (status := true)
  | false =>
      match mode with
      | .nearest => ExecFloat.mul left right
      | mode =>
          ModelCodec.liftBinary (Model := Model format) (plan := plan)
            (fun x y => Model.mul x y (mode := mode)) left right

/--
Divide two configured values, rounding the exact quotient in `mode` (nearest-even by default).
With `status := true` the result also carries the IEEE exception indicators and the ternary value.

Nearest-even division without status is `ExecFloat.div`, the selected kernel that `/` runs.
-/
@[macro_inline] def div [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [ExecFloat.Div (Configured.Family format code plan)]
    (left right : Value) (mode : Model.IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.div (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
          (mode := mode) (status := true)
  | false =>
      match mode with
      | .nearest => ExecFloat.div left right
      | mode =>
          ModelCodec.liftBinary (Model := Model format) (plan := plan)
            (fun x y => Model.div x y (mode := mode)) left right

/--
Form the exact product-plus-addend and round once in `mode` (nearest-even by default). With
`status := true` the result also carries the IEEE exception indicators and the ternary value.

This is the IEEE fused operation, whereas `mul` followed by `add` rounds twice. Nearest-even FMA
without status is `ExecFloat.fma`, the selected kernel.
-/
@[macro_inline] def fma [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [ExecFloat.Fma (Configured.Family format code plan)]
    (left right addend : Value) (mode : Model.IEEERoundingMode := .nearest)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.fma (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
          (ExecFloat.Binary.toModel addend)
          (mode := mode) (status := true)
  | false =>
      match mode with
      | .nearest => ExecFloat.fma left right addend
      | mode =>
          ModelCodec.liftTernary (Model := Model format) (plan := plan)
            (fun x y z => Model.fma x y z (mode := mode)) left right addend

/--
Take the square root of a configured value, rounding the exact result in `mode` (nearest-even by
default). With `status := true` the result also carries the IEEE exception indicators and the
ternary value.

Both nearest modes without status run `ExecFloat.sqrt`, the selected kernel: an exact square root
is never a tie.
-/
@[macro_inline] def sqrt [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [ExecFloat.Sqrt (Configured.Family format code plan)]
    (value : Value) (mode : Model.IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome (format := format) (plan := plan) (code := code)
    | false => Value :=
  match status with
  | true =>
      IEEEOutcome.ofModel <|
        Model.sqrt (ExecFloat.Binary.toModel value)
          (mode := mode) (status := true)
  | false =>
      match mode with
      | .nearest | .nearestAway => ExecFloat.sqrt value
      | mode =>
          ModelCodec.liftUnary (Model := Model format) (plan := plan)
            (fun x => Model.sqrt x (mode := mode)) value

end FloatLib.Floats.ExecFloat.Binary
