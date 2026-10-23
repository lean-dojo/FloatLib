/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime

/-!
# Format-parameterized binary arithmetic runtime

Each of the six IEEE arithmetic operations has one name with two options, a rounding direction
`mode` (nearest-even by default) and `status`, which selects whether the result is the delivered
value or the complete `IEEEOutcome` with the five exception flags and the ternary value:

```
Model.sqrt x
Model.sqrt x (mode := .up)
Model.sqrt x (mode := .up) (status := true)
```

With `open FloatLib.Rounding`, the mode can be written `(mode := up)`.

Each operation is a small `@[macro_inline]` selector. It tests `status` first, so a value call
never computes flags, and then `mode`: nearest-even goes straight to the dispatched kernel in
`Model.Internal.Nearest`, the other directions to `Model.Internal.Directed`, and status calls to
`Model.Internal.Status`. With literal options the compiler keeps only the selected kernel call.
Square root also sends nearest-away to the nearest-even kernel, since an exact square root is
never a tie.

This module contains only executable definitions, and their refinement theorems live in
`Arithmetic.Proof` and `Status.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
IEEE addition, rounded in `mode` (nearest-even by default). With `status := true` the result is
the `IEEEOutcome` carrying the exception flags and the ternary value.
-/
@[macro_inline] def add {fmt : FloatFormat} (x y : Model fmt)
    (mode : IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => Internal.Status.add x y mode
  | false =>
      match mode with
      | .nearest => Internal.Nearest.add x y
      | mode => Internal.Directed.add mode x y

/--
IEEE subtraction, rounded in `mode` (nearest-even by default). With `status := true` the result
is the `IEEEOutcome` carrying the exception flags and the ternary value.
-/
@[macro_inline] def sub {fmt : FloatFormat} (x y : Model fmt)
    (mode : IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => Internal.Status.sub x y mode
  | false =>
      match mode with
      | .nearest => Internal.Nearest.sub x y
      | mode => Internal.Directed.sub mode x y

/--
IEEE multiplication, rounded in `mode` (nearest-even by default). With `status := true` the
result is the `IEEEOutcome` carrying the exception flags and the ternary value.
-/
@[macro_inline] def mul {fmt : FloatFormat} (x y : Model fmt)
    (mode : IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => Internal.Status.mul x y mode
  | false =>
      match mode with
      | .nearest => Internal.Nearest.mul x y
      | mode => Internal.Directed.mul mode x y

/--
IEEE division, rounded in `mode` (nearest-even by default). With `status := true` the result is
the `IEEEOutcome` carrying the exception flags and the ternary value.
-/
@[macro_inline] def div {fmt : FloatFormat} (x y : Model fmt)
    (mode : IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => Internal.Status.div x y mode
  | false =>
      match mode with
      | .nearest => Internal.Nearest.div x y
      | mode => Internal.Directed.div mode x y

/--
IEEE square root, rounded in `mode` (nearest-even by default). With `status := true` the result
is the `IEEEOutcome` carrying the exception flags and the ternary value.
-/
@[macro_inline] def sqrt {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => Internal.Status.sqrt x mode
  | false =>
      match mode with
      | .nearest | .nearestAway => Internal.Nearest.sqrt x
      | mode => Internal.Directed.sqrt mode x

/--
IEEE fused multiply-add `x * y + z` with one rounding in `mode` (nearest-even by default). With
`status := true` the result is the `IEEEOutcome` carrying the exception flags and the ternary
value.
-/
@[macro_inline] def fma {fmt : FloatFormat} (x y z : Model fmt)
    (mode : IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => Internal.Status.fma x y z mode
  | false =>
      match mode with
      | .nearest => Internal.Nearest.fma x y z
      | mode => Internal.Directed.fma mode x y z

end Model
end FloatLib.Floats.Formats.BinaryInterchange
