/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Conversion.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
public import FloatLib.Numerics.Representations.FixedInt.Core

/-!
# Executable scalar conversions

Integer-to-float conversion rounds once in an explicit IEEE direction and reports the resulting
IEEE status. Float-to-integer conversion first rounds to an unbounded mathematical integer, then
checks that integer against the signed destination range. NaN, infinity, and an out-of-range
integer are explicit failures; no branch silently substitutes zero or wraps modulo the width.

These definitions describe a precise executable policy. Import `DType.Semantics` for theorems
relating that policy to integer and real arithmetic.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecDType

open FloatLib.Numerics
open FloatLib.Numerics.Representations
open FixedInt Model

/--
Convert a fixed-width signed integer to `fmt` with explicit rounding and IEEE status.

The integer is decoded exactly to a dyadic before one destination rounding. This works for every
source width and every binary-interchange destination format.
-/
@[inline] def intToFloatWithStatus {width : Nat} (fmt : FloatFormat)
    (x : FixedInt width) (rounding : IEEERoundingMode) : IEEEOutcome fmt :=
  let n := toInt x
  let exact : Numerics.Dyadic :=
    { negative := decide (n < 0)
      significand := n.natAbs
      exponent := 0 }
  let rounded := roundDyadicWithRounding fmt rounding exact
  { value := rounded
    status := dyadicRoundingStatus fmt rounding exact rounded }

/-- Value projection of `intToFloatWithStatus`. -/
@[inline] def intToFloat {width : Nat} (fmt : FloatFormat)
    (x : FixedInt width) (rounding : IEEERoundingMode) : Model fmt :=
  (intToFloatWithStatus fmt x rounding).value

/--
Convert a binary-interchange value to a checked signed integer with explicit rounding.

A finite source is first rounded to an unbounded `Int`. The conversion succeeds only when that
integer fits in `width` signed bits. The status reports whether rounding discarded a fractional
part. Infinity and NaN retain their source classification as explicit conversion failures.
NaN failures preserve the sign, signaling class, and payload.
-/
@[inline] def floatToInt {width : Nat} {fmt : FloatFormat} (x : Model fmt)
    (rounding : IEEERoundingMode) :
    FloatLib.Floats.ExecFloat.ConversionOutcome (FixedInt width) :=
  match exactValue x with
  | .finite exact =>
      let coefficient := Model.roundDyadicToInt rounding exact
      if FixedInt.InRange width coefficient then
        .success (ofInt coefficient) { inexact := !Model.dyadicIsIntegral exact }
      else
        .failure .outOfRange
  | .infinity negative =>
      .failure (.infinity .source negative)
  | .nan negative signaling payload =>
      .failure (.exceptional .source (.nan (some payload) negative signaling))

/-- Encode `true` as positive one and `false` as positive zero. -/
@[inline] def boolToFloat (fmt : FloatFormat) (b : Bool) : Model fmt :=
  if b then posOne fmt else posZero fmt

/-- Return `x` when `m` is true and positive zero otherwise. -/
@[inline] def maskFloat (fmt : FloatFormat) (m : Bool) (x : Model fmt) : Model fmt :=
  if m then x else posZero fmt

end ExecDType
end FloatLib.Floats.Formats.BinaryInterchange
