/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Conversion

/-!
# N1169 fixed-point operations on exact values

N1169, ISO/IEC TR 18037:2006(E), §§4.1.6–4.1.7 and C 7.18a.6.
Arithmetic operators use the common round-then-overflow conversion. Multiplication and
division select full-precision arithmetic, which is permitted with either state of
`FX_FULL_PRECISION`; this module does not exercise the optional extra-unit adjustment.
The explicit destination/source parameters describe values after C's type selection.

`absfx` and `roundfx` saturate independently of the ordinary overflow policy.
Integer-result support functions truncate toward zero and check the supplied integer
destination. C object mutation and integer ABI layout are outside these value functions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.1: the four exact binary arithmetic operations. -/
inductive Arithmetic where
  /-- The sum `x + y`. -/
  | add
  /-- The difference `x - y`. -/
  | sub
  /-- The product `x * y`. -/
  | mul
  /-- The quotient `x / y`. -/
  | div
  deriving DecidableEq, Repr

/-- Reconstruct a `Arithmetic` constructor from its constructor index. -/
add_decl_doc Arithmetic.ofNat_ctorIdx

/-- Exact rational interpretation; division by zero has no defined result. -/
def Arithmetic.exact : Arithmetic → ℚ → ℚ → Option ℚ
  | .add, x, y => some (x + y)
  | .sub, x, y => some (x - y)
  | .mul, x, y => some (x * y)
  | .div, x, y => if y = 0 then none else some (x / y)

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.1: exact operation followed by destination
    rounding and overflow. -/
@[inline] def Arithmetic.apply (operation : Arithmetic) (destination : Format)
    (rounding : Rounding) (overflow : Overflow) (x y : ℚ) : Option destination.Code :=
  (operation.exact x y).bind (convert destination rounding overflow)

/-- All binary operations refine one exact-value conversion schema. -/
theorem Arithmetic.apply_eq_some_iff (operation : Arithmetic) (destination : Format)
    (rounding : Rounding) (overflow : Overflow) (x y : ℚ) (value : destination.Code) :
    operation.apply destination rounding overflow x y = some value ↔
      ∃ exact, operation.exact x y = some exact ∧
        convert destination rounding overflow exact = some value := by
  simp [Arithmetic.apply, Option.bind_eq_some_iff]

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.1.2: unary `+` preserves its operand and type. -/
@[inline] def Unary.«+» {format : Format} (value : format.Code) : format.Code :=
  value

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.1.2: unary `-` subtracts from exact integer zero
    before conversion. -/
@[inline] def Unary.«-» {format : Format} (rounding : Rounding) (overflow : Overflow)
    (value : format.Code) : Option format.Code :=
  convert format rounding overflow (-Format.decode value)

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.1.2: logical `!` returns integer one exactly at
    zero, otherwise zero. -/
@[inline] def Unary.«!» {format : Format} (value : format.Code) : Int :=
  if bitsfx value = 0 then 1 else 0

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.1.1: the updated value for prefix or postfix
    increment/decrement.
The Boolean selects `++` when true and `--` when false; lvalue storage is external. -/
@[inline] def Unary.update {format : Format} (increment : Bool)
    (rounding : Rounding) (overflow : Overflow) (value : format.Code) :
    Option format.Code :=
  convert format rounding overflow
    (Format.decode value + if increment then 1 else -1)

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.2 and C 6.5.7: a left or right shift, with the C
    count constraint.
The Boolean selects `<<` when true and `>>` when false. -/
@[inline] def shift {format : Format} (left : Bool) (rounding : Rounding)
    (overflow : Overflow) (value : format.Code) (count : Int) : Option format.Code :=
  if 0 ≤ count ∧ count < (format.width : Int) then
    let power := (2 : ℚ) ^ count.toNat
    convert format rounding overflow
      (if left then Format.decode value * power else Format.decode value / power)
  else none

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.2 and generic macro C 7.18a.6.7:
    saturated absolute value.
Unsigned extensions use the same definition and preserve the operand. -/
@[inline] def absfx {format : Format} (value : format.Code) : format.Code :=
  format.clamp |bitsfx value|

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.3: coarse-grid coefficient before the
    required saturation. -/
@[inline] def roundCoefficient (rounding : NearestRounding) (fractionalBits : Nat)
    (coefficient count : Int) : Int :=
  let step : Int := 2 ^ (fractionalBits - count.toNat)
  rounding.run ((coefficient : ℚ) / (step : ℚ)) * step

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.3 and generic macro C 7.18a.6.7: nearest
    coarse-grid rounding.
`none` reports a count outside `0 ≤ n < F`; the document leaves invalid counts
unspecified. Saturation may leave nonzero bits below the rounding point. -/
@[inline] def roundfx {format : Format} (rounding : NearestRounding)
    (value : format.Code) (count : Int) : Option format.Code :=
  if 0 ≤ count ∧ count < (format.fractionalBits : Int) then
    some (format.clamp (roundCoefficient rounding format.fractionalBits (bitsfx value) count))
  else none

/-- Before saturation, the rounded coefficient is a multiple of the coarse-grid step. -/
theorem roundCoefficient_dvd (rounding : NearestRounding) (fractionalBits : Nat)
    (coefficient count : Int) :
    (2 : Int) ^ (fractionalBits - count.toNat) ∣
      roundCoefficient rounding fractionalBits coefficient count :=
  dvd_mul_left _ _

/-- N1169's low-bit condition holds whenever the coarse result fits without saturation.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.7.2 (C clause 7.18a.6.3).
-/
theorem roundfx_low_bits {format : Format} (rounding : NearestRounding)
    (value result : format.Code) (count : Int)
    (hvalid : 0 ≤ count ∧ count < (format.fractionalBits : Int))
    (hrange : format.integerFormat.InRange
      (roundCoefficient rounding format.fractionalBits (bitsfx value) count))
    (hresult : roundfx rounding value count = some result) :
    (2 : Int) ^ (format.fractionalBits - count.toNat) ∣ bitsfx result := by
  rw [roundfx, ite_eq_left hvalid, Option.some.injEq] at hresult
  rw [← hresult]
  change _ ∣ format.quantizer.clampCode _
  rw [format.quantizer.clampCode_eq_self hrange.1 hrange.2]
  exact roundCoefficient_dvd _ _ _ _

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.3.1.3a and 7.18a.6.1: truncation toward zero
    into a chosen integer type. -/
@[inline] def toInteger (destination : IntegerFormat) (x : ℚ) : Option Int :=
  destination.range.round? (fun q ↦ q.num.tdiv q.den) x

/-- Generic integer-result multiplication support function of C 7.18a.6.1. -/
@[inline] def muli {format : Format} (destination : IntegerFormat)
    (integer : Int) (value : format.Code) : Option Int :=
  toInteger destination ((integer : ℚ) * Format.decode value)

/-- Generic integer/fixed division support function of C 7.18a.6.1. -/
@[inline] def divi {format : Format} (destination : IntegerFormat)
    (integer : Int) (value : format.Code) : Option Int :=
  if bitsfx value = 0 then none
  else toInteger destination ((integer : ℚ) / Format.decode value)

/-- Generic fixed/fixed division returning an integer, C 7.18a.6.1. -/
@[inline] def idiv {left right : Format} (destination : IntegerFormat)
    (x : left.Code) (y : right.Code) : Option Int :=
  if bitsfx y = 0 then none
  else toInteger destination (Format.decode x / Format.decode y)

/-- Generic integer/integer division returning fixed point, C 7.18a.6.1.
Its result saturates even for a primary destination with a DEFAULT pragma. -/
@[inline] def fxdivi (destination : Format) (rounding : Rounding)
    (numerator denominator : Int) : Option destination.Code :=
  if denominator = 0 then none
  else convert destination rounding .SAT ((numerator : ℚ) / (denominator : ℚ))

/-- Integer support-function results are exactly truncated and in the supplied integer range. -/
theorem toInteger_eq_some_iff (destination : IntegerFormat) (x : ℚ) (result : Int) :
    toInteger destination x = some result ↔
      x.num.tdiv x.den = result ∧ destination.InRange result := by
  exact IntegerRange.round?_eq_some_iff _ _ _ _

end FloatLib.Floats.Formats.FixedPoint.Embedded
