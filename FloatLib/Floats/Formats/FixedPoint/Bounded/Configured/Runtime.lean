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
Wrapping, checked, and saturating conversions and operations have distinct names.

Multiplication also exposes the composed input scale and chosen destination width in its result
type. This makes the numerical policy visible at the call site while the implementation reuses the
generic fixed-integer kernels and their refinement theorems.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.BoundedFixedPoint

open FloatLib.Numerics

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
Round an exact rational to the nearest coefficient, ties to even, then wrap it modulo
`2 ^ width`.
-/
@[inline] def ofRatWrapping (value : Rat) :
    ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
  ofCoefficient
    (Formats.FixedPoint.Bounded.coefficientOf radix fractionalDigits value)

/--
Round an exact rational to the nearest coefficient, ties to even, and return it only when that
coefficient fits the destination width.
-/
@[inline] def ofRat? (value : Rat) :
    Option (ExecFloat.BoundedFixedPoint radix fractionalDigits width) :=
  let stored :=
    Formats.FixedPoint.Bounded.coefficientOf radix fractionalDigits value
  if FloatLib.Numerics.Representations.FixedInt.InRange width stored then
    some (ofCoefficient stored)
  else
    none

/--
Round an exact rational to the nearest coefficient, ties to even, then clamp it to the signed
destination range.
-/
@[inline] def ofRatSaturating (value : Rat) :
    ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
  let stored :=
    Formats.FixedPoint.Bounded.coefficientOf radix fractionalDigits value
  ofCode
    (FloatLib.Numerics.Representations.FixedInt.ofIntSaturating stored)

/-- Recover the stored signed integer coefficient. -/
@[inline] def coefficient
    (value : ExecFloat.BoundedFixedPoint radix fractionalDigits width) : Int :=
  Formats.FixedPoint.Bounded.coefficient value.toCode

/-- Decode a bounded fixed-point value to its exact rational meaning. -/
@[inline] def toRat
    (value : ExecFloat.BoundedFixedPoint radix fractionalDigits width) : ℚ :=
  Formats.FixedPoint.Bounded.toRat radix fractionalDigits value.toCode

/-- Same-scale addition modulo `2 ^ width`. -/
@[inline] def wrapAdd
    (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
  ofCode (Formats.FixedPoint.Bounded.wrapAdd left.toCode right.toCode)

/-- Same-scale subtraction modulo `2 ^ width`. -/
@[inline] def wrapSub
    (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
  ofCode (Formats.FixedPoint.Bounded.wrapSub left.toCode right.toCode)

/-- Multiplication modulo `2^outWidth`, with exact scale composition. -/
@[inline] def wrapMul (outWidth : Nat)
    (left : ExecFloat.BoundedFixedPoint radix p leftWidth)
    (right : ExecFloat.BoundedFixedPoint radix q rightWidth) :
    ExecFloat.BoundedFixedPoint radix (p + q) outWidth :=
  ofCode (Formats.FixedPoint.Bounded.wrapMul outWidth left.toCode right.toCode)

/-- Return the exact same-scale sum when its coefficient fits. -/
@[inline] def checkedAdd
    (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    Option (ExecFloat.BoundedFixedPoint radix fractionalDigits width) :=
  (Formats.FixedPoint.Bounded.checkedAdd left.toCode right.toCode).map ofCode

/-- Return the exact same-scale difference when its coefficient fits. -/
@[inline] def checkedSub
    (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    Option (ExecFloat.BoundedFixedPoint radix fractionalDigits width) :=
  (Formats.FixedPoint.Bounded.checkedSub left.toCode right.toCode).map ofCode

/-- Return the exact product when its coefficient fits the destination width. -/
@[inline] def checkedMul (outWidth : Nat)
    (left : ExecFloat.BoundedFixedPoint radix p leftWidth)
    (right : ExecFloat.BoundedFixedPoint radix q rightWidth) :
    Option (ExecFloat.BoundedFixedPoint radix (p + q) outWidth) :=
  (Formats.FixedPoint.Bounded.checkedMul outWidth left.toCode right.toCode).map ofCode

/-- Same-scale addition clamped to the signed coefficient bounds. -/
@[inline] def saturatingAdd
    (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
  ofCode (Formats.FixedPoint.Bounded.saturatingAdd left.toCode right.toCode)

/-- Same-scale subtraction clamped to the signed coefficient bounds. -/
@[inline] def saturatingSub
    (left right : ExecFloat.BoundedFixedPoint radix fractionalDigits width) :
    ExecFloat.BoundedFixedPoint radix fractionalDigits width :=
  ofCode (Formats.FixedPoint.Bounded.saturatingSub left.toCode right.toCode)

/-- Product clamped to the signed destination range, with exact scale composition. -/
@[inline] def saturatingMul (outWidth : Nat)
    (left : ExecFloat.BoundedFixedPoint radix p leftWidth)
    (right : ExecFloat.BoundedFixedPoint radix q rightWidth) :
    ExecFloat.BoundedFixedPoint radix (p + q) outWidth :=
  ofCode (Formats.FixedPoint.Bounded.saturatingMul outWidth left.toCode right.toCode)

end FloatLib.Floats.ExecFloat.BoundedFixedPoint
