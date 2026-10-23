/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Core
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Semantics.Core

/-!
# Executable bounded fixed-point operations

Bounded fixed point stores an exact signed coefficient in a fixed-width two's-complement carrier.
Conversion and arithmetic take an `(overflow := ...)` option: `.reject`, the default, returns
`none` when the exact coefficient does not fit, `.wrap` reduces it modulo `2 ^ width`, and
`.saturate` clamps it to the signed range.

Multiplication also exposes the composed input scale and chosen destination width in its result
type. The implementation reuses the generic fixed-integer kernels and their refinement theorems.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.BoundedFixedPoint

open FloatLib.Numerics

/-- What a bounded fixed-point conversion or operation does with a coefficient that does not fit. -/
inductive OverflowPolicy where
  /-- Return `none`, or reject a conversion as `outOfRange`. -/
  | reject
  /-- Reduce the coefficient modulo `2 ^ width`. -/
  | wrap
  /-- Clamp the coefficient to the signed destination range. -/
  | saturate
  deriving DecidableEq, Repr

variable {radix : Radix} {fractionalDigits p q : Nat}
variable {width leftWidth rightWidth outWidth : Nat}

/-- Wrap a complete bounded fixed-point code without conversion. -/
@[inline] def ofCode
    (code : Formats.FixedPoint.Bounded.Code radix fractionalDigits width) :
    ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
  ExecFloat.ofRaw code

/-- Recover the complete bounded fixed-point code without conversion. -/
@[inline] def toCode
    (value : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    Formats.FixedPoint.Bounded.Code radix fractionalDigits width :=
  value.raw

/-- Construct a bounded fixed-point value from its complete unsigned word. -/
@[inline] def ofNatBits (bits : Nat) :
    ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
  ofCode (FloatLib.Numerics.Representations.FixedInt.ofNatBits bits)

/-- Read the complete bounded fixed-point word as an unsigned natural number. -/
@[inline] def toNatBits
    (value : ExecFloat.BoundedFixedPoint radix fractionalDigits width) : Nat :=
  FloatLib.Numerics.Representations.FixedInt.toNatBits value.toCode

/-- Encode an integer coefficient modulo `2 ^ width`. -/
@[inline] def ofCoefficient (coefficient : Int) :
    ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
  ofCode (Formats.FixedPoint.Bounded.ofInt width coefficient)

/--
Round an exact rational to the nearest coefficient, ties to even, then apply the `overflow`
policy when that coefficient does not fit.
-/
@[macro_inline] def ofRat (value : Rat) (overflow : OverflowPolicy := .reject) :
    match overflow with
    | .reject => Option (ExecFloat.BoundedFixedPoint radix fractionalDigits width)
    | .wrap | .saturate => ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
  match overflow with
  | .reject =>
      let stored := Formats.FixedPoint.Bounded.coefficientOf radix fractionalDigits value
      if FloatLib.Numerics.Representations.FixedInt.InRange width stored then
        some (ofCoefficient stored)
      else
        none
  | .wrap => ofCoefficient (Formats.FixedPoint.Bounded.coefficientOf radix fractionalDigits value)
  | .saturate =>
      ofCode (FloatLib.Numerics.Representations.FixedInt.ofIntSaturating
        (Formats.FixedPoint.Bounded.coefficientOf radix fractionalDigits value))

/-- Recover the stored signed integer coefficient. -/
@[inline] def coefficient
    (value : ExecFloat.BoundedFixedPoint radix fractionalDigits width) : Int :=
  Formats.FixedPoint.Bounded.coefficient value.toCode

/-- Decode a bounded fixed-point value to its exact rational meaning. -/
@[inline] def toRat
    (value : ExecFloat.BoundedFixedPoint radix fractionalDigits width) : ℚ :=
  Formats.FixedPoint.Bounded.toRat radix fractionalDigits value.toCode

/--
Same-scale addition, applying the `overflow` policy when the exact coefficient sum does not
fit.
-/
@[macro_inline] def add (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width)
    (overflow : OverflowPolicy := .reject) :
    match overflow with
    | .reject => Option (ExecFloat.BoundedFixedPoint radix fractionalDigits width)
    | .wrap | .saturate => ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
  match overflow with
  | .reject => (Formats.FixedPoint.Bounded.checkedAdd left.toCode right.toCode).map ofCode
  | .wrap => ofCode (Formats.FixedPoint.Bounded.wrapAdd left.toCode right.toCode)
  | .saturate => ofCode (Formats.FixedPoint.Bounded.saturatingAdd left.toCode right.toCode)

/-- Same-scale subtraction, with the `overflow` options of `add`. -/
@[macro_inline] def sub (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width)
    (overflow : OverflowPolicy := .reject) :
    match overflow with
    | .reject => Option (ExecFloat.BoundedFixedPoint radix fractionalDigits width)
    | .wrap | .saturate => ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
  match overflow with
  | .reject => (Formats.FixedPoint.Bounded.checkedSub left.toCode right.toCode).map ofCode
  | .wrap => ofCode (Formats.FixedPoint.Bounded.wrapSub left.toCode right.toCode)
  | .saturate => ofCode (Formats.FixedPoint.Bounded.saturatingSub left.toCode right.toCode)

/--
Multiplication into an `outWidth`-bit coefficient with exact scale composition, `p + q`
fractional digits, and the `overflow` options of `add` at the destination width.
-/
@[macro_inline] def mul (outWidth : Nat)
    (left : ExecFloat.BoundedFixedPoint radix p leftWidth)
    (right : ExecFloat.BoundedFixedPoint radix q rightWidth)
    (overflow : OverflowPolicy := .reject) :
    match overflow with
    | .reject => Option (ExecFloat.BoundedFixedPoint radix (p + q) outWidth)
    | .wrap | .saturate => ExecFloat.BoundedFixedPoint radix (p + q) outWidth :=
  match overflow with
  | .reject =>
      (Formats.FixedPoint.Bounded.checkedMul outWidth left.toCode right.toCode).map ofCode
  | .wrap => ofCode (Formats.FixedPoint.Bounded.wrapMul outWidth left.toCode right.toCode)
  | .saturate =>
      ofCode (Formats.FixedPoint.Bounded.saturatingMul outWidth left.toCode right.toCode)

end FloatLib.Floats.ExecFloat.BoundedFixedPoint
