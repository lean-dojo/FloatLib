/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Core

/-!
# Fixed-point primitives for executable transcendental functions

At scale `n`, the integer `k` represents `k * 2^(-n)`. Multiplication and division round back
to that scale with ties to even. The scale is explicit so each format can choose its own working
precision. Approximation policy and constants live in `Config.lean`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.Transcendentals

/--
Number of fractional binary digits in a signed fixed-point representation.

An integer `k` at scale `n` represents `k * 2^(-n)`.
-/
abbrev FixedPoint := Nat

namespace FixedPoint

/-- The fixed-point scale as an integer exponent. -/
@[inline] def scaleInt (fixed : FixedPoint) : Int :=
  Int.ofNat fixed

/-- Integer power of two. -/
@[inline] def pow2Int (exponent : Nat) : Int :=
  Int.ofNat (Model.pow2 exponent)

/-- The fixed-point encoding of one. -/
@[inline] def one (fixed : FixedPoint) : Int :=
  pow2Int fixed

/--
Round an integer quotient to nearest, ties to even.

Callers provide a strictly positive denominator.
-/
@[inline] def roundQuotientEven (numerator denominator : Int) : Int :=
  let quotient := Int.ediv numerator denominator
  let remainder := Int.emod numerator denominator
  let twiceRemainder := 2 * remainder
  if twiceRemainder < denominator then
    quotient
  else if twiceRemainder > denominator then
    quotient + 1
  else if quotient % 2 == 0 then
    quotient
  else
    quotient + 1

/-- Divide by a power of two, rounding to nearest with ties to even. -/
@[inline] def roundDivPow2Even (value : Int) (shift : Nat) : Int :=
  if shift == 0 then value else roundQuotientEven value (pow2Int shift)

/--
Scale an integer by a signed power of two.

Negative shifts use nearest-even division.
-/
@[inline] def shiftPow2Even (value : Int) (shift : Int) : Int :=
  match shift with
  | .ofNat amount => value * pow2Int amount
  | .negSucc amount => roundDivPow2Even value (amount + 1)

/-- Fixed-point multiplication, rounded back to the context's scale. -/
@[inline] def mul (fixed : FixedPoint) (left right : Int) : Int :=
  roundDivPow2Even (left * right) fixed

/-- Fixed-point division by a positive denominator, rounded back to the context's scale. -/
@[inline] def div (fixed : FixedPoint) (numerator denominator : Int) : Int :=
  roundQuotientEven (numerator * fixed.one) denominator

/-- Divide a fixed-point value by a positive natural number. -/
@[inline] def divByNat (_fixed : FixedPoint) (value : Int) (denominator : Nat) : Int :=
  roundQuotientEven value (Int.ofNat denominator)

/-- Round an exact dyadic to the context's scale, with ties to even. -/
@[inline] def ofDyadic (fixed : FixedPoint) (value : Numerics.Dyadic) : Int :=
  let signedMantissa :=
    if value.negative then -(Int.ofNat value.significand) else Int.ofNat value.significand
  shiftPow2Even signedMantissa (value.exponent + fixed.scaleInt)

/-- Convert a signed fixed-point integer to an exact dyadic. -/
@[inline] def toDyadic (fixed : FixedPoint) (value : Int) : Numerics.Dyadic :=
  { negative := value < 0
    significand := value.natAbs
    exponent := -fixed.scaleInt }

/--
Evaluate descending fixed-point polynomial coefficients by Horner's method.

Each multiplication rounds back to the fixed-point scale. An empty coefficient list evaluates
to zero.
-/
def evalPolyDesc (fixed : FixedPoint) (coefficients : List Int) (value : Int) : Int :=
  match coefficients with
  | [] => 0
  | leading :: rest =>
      rest.foldl (fun accumulator coefficient =>
        coefficient + fixed.mul value accumulator) leading

end FixedPoint

end Model.Transcendentals
end FloatLib.Floats.Formats.BinaryInterchange
