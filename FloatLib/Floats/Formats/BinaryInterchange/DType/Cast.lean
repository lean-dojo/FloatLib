/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Executable.Conversion.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
public import FloatLib.Numerics.Representations.FixedInt.Core
public meta import FloatLib.Tactic.IEEENames

/-!
# Executable scalar conversions

Integer-to-float conversion rounds once in a given IEEE direction and reports the resulting IEEE
status. Float-to-integer conversion first rounds to an unbounded mathematical integer, then checks
that integer against the signed destination range. NaN, infinity, and an out-of-range integer are
failures, so no branch silently substitutes zero or wraps modulo the width.

`DType.Semantics` relates this executable policy to integer and real arithmetic.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecDType

open FloatLib.Numerics
open FloatLib.Numerics.Representations
open FixedInt Model

/--
Convert a fixed-width signed integer to `fmt` with IEEE status and ternary value, the kernel of
`ExecDType.convertFromInt fmt x (mode := mode) (status := true)`.

The integer is decoded to an exact dyadic before one destination rounding, and the ternary value
compares the delivered value with that integer.
-/
@[inline] def Internal.Status.convertFromInt {width : Nat} (fmt : FloatFormat)
    (x : FixedInt width) (mode : IEEERoundingMode) : IEEEOutcome fmt :=
  let n := toInt x
  let exact : Numerics.Dyadic :=
    { negative := decide (n < 0)
      significand := n.natAbs
      exponent := 0 }
  let rounded := Model.Internal.Directed.roundDyadic fmt mode exact
  dyadicRoundingOutcome fmt mode exact rounded

/--
Convert a fixed-width signed integer to `fmt`, rounding once in `mode` (nearest-even by default).
With `status := true` the result is the `IEEEOutcome` carrying the exception flags and the ternary
value.

The integer is decoded to an exact dyadic before the one destination rounding. This works for
every source width and every binary-interchange destination format.
-/
@[macro_inline] def convertFromInt {width : Nat} (fmt : FloatFormat)
    (x : FixedInt width) (mode : IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => Internal.Status.convertFromInt fmt x mode
  | false => (Internal.Status.convertFromInt fmt x mode).value

/--
Convert a binary-interchange value to a checked signed integer, rounding in direction `mode`.

A finite source is first rounded to an unbounded `Int`. The conversion succeeds only when that
integer fits in `width` signed bits. The status reports whether rounding discarded a fractional
part. Infinity and NaN fail with their source classification. NaN failures preserve the sign,
signaling class, and diagnostic payload without the quiet bit.
-/
@[inline] def convertToIntegerExact {width : Nat} {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) :
    FloatLib.Floats.ExecFloat.ConversionOutcome (FixedInt width) :=
  match exactValue x with
  | .finite exact =>
      let coefficient := Model.roundDyadicToInt mode exact
      if FixedInt.InRange width coefficient then
        .success (ofInt coefficient) { inexact := !Model.dyadicIsIntegral exact }
      else
        .failure .outOfRange
  | .infinity negative =>
      .failure (.infinity .source negative)
  | .nan negative signaling payload =>
      .failure (.exceptional .source
        (.nan (some (Model.payloadOfNaNField signaling payload fmt.encoding)) negative signaling))

/--
Convert a binary-interchange value to a checked signed integer, rounding in direction `mode`,
without the inexact signal: the operations `convertToInteger...` of IEEE 754-2019 §5.4.1. The
integer and the failures are those of `convertToIntegerExact`.
-/
@[inline] def convertToInteger {width : Nat} {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) :
    FloatLib.Floats.ExecFloat.ConversionOutcome (FixedInt width) :=
  match convertToIntegerExact x mode with
  | .success value status => .success value { status with inexact := false }
  | .failure reason => .failure reason

ieee_by_direction "IEEE 754-2019 §5.4.1" convertToInteger {width : Nat} {fmt : FloatFormat}
    (x : Model fmt) : FloatLib.Floats.ExecFloat.ConversionOutcome (FixedInt width) :=
  fun mode => convertToInteger x mode

ieee_by_direction "IEEE 754-2019 §5.4.1" convertToIntegerExact {width : Nat} {fmt : FloatFormat}
    (x : Model fmt) : FloatLib.Floats.ExecFloat.ConversionOutcome (FixedInt width) :=
  fun mode => convertToIntegerExact x mode

/-- Encode `true` as positive one and `false` as positive zero. -/
@[inline] def boolToFloat (fmt : FloatFormat) (b : Bool) : Model fmt :=
  if b then posOne fmt else posZero fmt

/-- Return `x` when `m` is true and positive zero otherwise. -/
@[inline] def maskFloat (fmt : FloatFormat) (m : Bool) (x : Model fmt) : Model fmt :=
  if m then x else posZero fmt

end ExecDType
end FloatLib.Floats.Formats.BinaryInterchange
