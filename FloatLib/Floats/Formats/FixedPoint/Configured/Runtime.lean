/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Configured.Core
public import FloatLib.Numerics.Quantization.Deterministic

/-!
# Executable exact fixed-point operations

Same-scale addition, negation, and subtraction are exact. Multiplication composes the two scales
in its result type rather than silently selecting a rounding policy.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.FixedPoint

open FloatLib.Numerics

variable {radix : Radix} {fractionalDigits p q : Nat}

/-- Integer denominator of the configured fixed-point grid. -/
abbrev scale := Formats.FixedPoint.scale

/-- Wrap a complete fixed-point code without conversion. -/
@[inline] def ofCode (code : Formats.FixedPoint.Code radix fractionalDigits) :
    ExecFloat.FixedPoint radix fractionalDigits :=
  ExecFloat.ofRaw code

/-- Recover the complete fixed-point code without conversion. -/
@[inline] def toCode (value : ExecFloat.FixedPoint radix fractionalDigits) :
    Formats.FixedPoint.Code radix fractionalDigits :=
  value.raw

/-- Construct a value from its exact stored integer coefficient. -/
@[inline] def ofCoefficient (coefficient : Int) :
    ExecFloat.FixedPoint radix fractionalDigits :=
  ofCode ⟨coefficient⟩

/--
Round an exact rational once to the nearest fixed-point grid value, breaking ties to even.

This is the construction policy used by decimal and scientific literals. It never converts
through a host floating-point value.
-/
@[inline] def roundRat (value : Rat) :
    ExecFloat.FixedPoint radix fractionalDigits :=
  ofCoefficient (roundRatEven (value * scale radix fractionalDigits))

/-- Recover the exact stored integer coefficient. -/
@[inline] def coefficient (value : ExecFloat.FixedPoint radix fractionalDigits) : Int :=
  value.toCode.coefficient

/-- Decode a configured fixed-point value to its exact rational meaning. -/
@[inline] def toRat (value : ExecFloat.FixedPoint radix fractionalDigits) : ℚ :=
  value.toCode.toRat

/-- Exact same-scale addition. -/
@[inline] def add
    (left right : ExecFloat.FixedPoint radix fractionalDigits) :
    ExecFloat.FixedPoint radix fractionalDigits :=
  ofCode (Formats.FixedPoint.Code.add left.toCode right.toCode)

/-- Exact additive inverse at the same scale. -/
@[inline] def neg (value : ExecFloat.FixedPoint radix fractionalDigits) :
    ExecFloat.FixedPoint radix fractionalDigits :=
  ofCode (Formats.FixedPoint.Code.neg value.toCode)

/-- Exact same-scale subtraction. -/
@[inline] def sub
    (left right : ExecFloat.FixedPoint radix fractionalDigits) :
    ExecFloat.FixedPoint radix fractionalDigits :=
  ofCode (Formats.FixedPoint.Code.sub left.toCode right.toCode)

/-- Exact multiplication with the composed output scale visible in the result type. -/
@[inline] def mul
    (left : ExecFloat.FixedPoint radix p)
    (right : ExecFloat.FixedPoint radix q) :
    ExecFloat.FixedPoint radix (p + q) :=
  ofCode (Formats.FixedPoint.Code.mul left.toCode right.toCode)

end FloatLib.Floats.ExecFloat.FixedPoint
