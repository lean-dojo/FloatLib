/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.ScaledProduct.Runtime

/-!
# Arithmetic with operands and result in different formats

IEEE 754-2019 §5.4.1 specifies its arithmetic operations as formatOf operations: the operands
may have any formats of the radix, and the result is computed as if with unbounded range and
precision and rounded once into the destination format, which need not be a format of an
operand. ISO/IEC 9899:2024 (C23, N3220) F.3 paragraph 2 states the requirement for C, where
`(long double) f * d` multiplies a `float` and a `double` into a `long double`.

`formatOfAddition`, `formatOfSubtraction`, `formatOfMultiplication`, `formatOfDivision` and
`formatOfFusedMultiplyAdd` are these operations for every destination `FloatFormat` and every
operand format, in every rounding direction, with the flags and the ternary value of the one
rounding. `Model.add`, `sub`, `mul`, `div` and `fma` are the case of one format. A sum of two
`binary64` values rounded into `binary32` this way has no double rounding, unlike `cast` after
`add`.

Each operand is read as an exact value (`Reduction.Internal.Factor.ofValue`): a dyadic, an
infinity, or a NaN carried into the destination format with its sign and, where it fits, its
payload. The special cases are those of the operations of one format:

* a NaN operand gives a quiet NaN, a signaling one before a quiet one and the left operand
  before the right, with `invalid` for a signaling NaN;
* infinities of opposite signs added, zero times infinity, zero divided by zero and infinity
  divided by infinity raise `invalid` and give the default NaN of the destination;
* a nonzero finite value divided by zero gives an infinity and raises `divideByZero`;
* an exact zero sum has the sign that the rounding direction prescribes: negative when both
  terms are negative, and when they differ and the direction is toward negative infinity.

`formatOfSquareRoot` is in `Operations.FormatOf.SquareRoot`. `ExecDType.convertFromInt` is the
formatOf conversion from an integer.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

namespace Reduction.Internal

/--
The exact product of two factors: a signaling NaN before a quiet one and the left before the
right, zero times infinity invalid, and a zero product with the product of the signs.
-/
def Factor.mul {destination : FloatFormat} : Factor destination → Factor destination →
    Factor destination
  | .invalid, _ | _, .invalid => .invalid
  | .nan left true, _ => .nan left true
  | .nan left false, .nan right signaling => if signaling then .nan right true else .nan left false
  | .nan left false, _ => .nan left false
  | _, .nan right signaling => .nan right signaling
  | .infinity left, .infinity right => .infinity (Bool.xor left right)
  | .infinity negative, .finite value | .finite value, .infinity negative =>
      if value.significand == 0 then .invalid else .infinity (Bool.xor negative value.negative)
  | .finite left, .finite right =>
      .finite
        { negative := Bool.xor left.negative right.negative
          significand := left.significand * right.significand
          exponent := left.exponent + right.exponent }

/--
The outcome of an exact result in the destination format: a finite nonzero value rounded once
in `mode`, an exact zero with the sign `zeroNegative`, an infinity as the destination encodes
it, a NaN with `invalid` when it was signaling, and the default NaN with `invalid`.
-/
def Factor.deliver {destination : FloatFormat} (factor : Factor destination)
    (mode : IEEERoundingMode) (zeroNegative : Bool) : IEEEOutcome destination :=
  match factor with
  | .invalid => outcomeWithInvalid (invalidResult destination) true
  | .nan value signaling => outcomeWithInvalid value signaling
  | .infinity negative =>
      { value := nativeOverflow destination negative, status := .clear
        ternary := exactInfinityTernary negative (nativeOverflow destination negative) }
  | .finite exact =>
      if exact.significand == 0 then
        { value := zero destination zeroNegative, status := .clear, ternary := .eq }
      else
        Model.dyadicRoundingOutcome destination mode exact
          (Internal.Directed.roundDyadic destination mode exact)

end Reduction.Internal

open Reduction.Internal (Factor)

/--
IEEE 754-2019 §5.4.1 formatOf-addition: the exact sum of two operands of any formats, rounded
once into `destination` in `mode` (nearest-even by default), with the flags and the ternary value
of that rounding. See the module documentation for the special cases.
-/
def formatOfAddition (destination : FloatFormat) {left right : FloatFormat} (x : Model left)
    (y : Model right) (mode : IEEERoundingMode := .nearest) : IEEEOutcome destination :=
  (Factor.add (Factor.ofValue x) (Factor.ofValue y)).deliver mode
    (mode.zeroSumSign (signBit x) (signBit y))

/--
IEEE 754-2019 §5.4.1 formatOf-subtraction: `formatOfAddition` of `x` and the negated `y`.
-/
def formatOfSubtraction (destination : FloatFormat) {left right : FloatFormat} (x : Model left)
    (y : Model right) (mode : IEEERoundingMode := .nearest) : IEEEOutcome destination :=
  formatOfAddition destination x (neg y) mode

/--
IEEE 754-2019 §5.4.1 formatOf-multiplication: the exact product of two operands of any formats,
rounded once into `destination` in `mode` (nearest-even by default), with the flags and the
ternary value of that rounding. See the module documentation for the special cases.
-/
def formatOfMultiplication (destination : FloatFormat) {left right : FloatFormat}
    (x : Model left) (y : Model right) (mode : IEEERoundingMode := .nearest) :
    IEEEOutcome destination :=
  (Factor.mul (Factor.ofValue x) (Factor.ofValue y)).deliver mode
    (Bool.xor (signBit x) (signBit y))

/--
IEEE 754-2019 §5.4.1 formatOf-fusedMultiplyAdd: the exact value of `x * y + z` for operands of
any formats, rounded once into `destination` in `mode` (nearest-even by default). Zero times
infinity raises `invalid` whatever the addend is, and delivers the addend when it is a NaN, as
`Model.fma` does (IEEE 754-2019 §7.2 leaves the flag to the implementation when the addend is a
quiet NaN).
-/
def formatOfFusedMultiplyAdd (destination : FloatFormat) {left right addend : FloatFormat}
    (x : Model left) (y : Model right) (z : Model addend)
    (mode : IEEERoundingMode := .nearest) : IEEEOutcome destination :=
  match Factor.mul (Factor.ofValue x) (Factor.ofValue y), (Factor.ofValue z : Factor
    destination) with
  | .invalid, .nan value _ => outcomeWithInvalid value true
  | product, term =>
      (Factor.add product term).deliver mode
        (mode.zeroSumSign (Bool.xor (signBit x) (signBit y)) (signBit z))

/--
IEEE 754-2019 §5.4.1 formatOf-division: the exact quotient of two operands of any formats,
rounded once into `destination` in `mode` (nearest-even by default), with the flags and the
ternary value of that rounding. A nonzero finite dividend over zero gives an infinity and raises
`divideByZero`. See the module documentation for the other special cases.
-/
def formatOfDivision (destination : FloatFormat) {left right : FloatFormat} (x : Model left)
    (y : Model right) (mode : IEEERoundingMode := .nearest) : IEEEOutcome destination :=
  let sign := Bool.xor (signBit x) (signBit y)
  match (Factor.ofValue x : Factor destination), (Factor.ofValue y : Factor destination) with
  | .finite dx, .finite dy =>
      if dy.significand == 0 then
        if dx.significand == 0 then
          outcomeWithInvalid (invalidResult destination) true
        else
          { value := nativeOverflow destination sign, status := { divideByZero := true }
            ternary := exactInfinityTernary sign (nativeOverflow destination sign) }
      else if dx.significand == 0 then
        { value := zero destination sign, status := .clear, ternary := .eq }
      else
        Model.rationalRoundingOutcomeScaled destination mode sign dx.significand dy.significand
          (dx.exponent - dy.exponent)
          (Internal.Directed.roundRatScaled destination mode sign dx.significand dy.significand
            (dx.exponent - dy.exponent))
  | .infinity _, .infinity _ => Factor.invalid.deliver mode sign
  | .infinity _, .finite _ => (Factor.infinity sign).deliver mode sign
  | .finite _, .infinity _ =>
      { value := zero destination sign, status := .clear, ternary := .eq }
  | dividend, divisor => (Factor.add dividend divisor).deliver mode sign

end Model
end FloatLib.Floats.Formats.BinaryInterchange
