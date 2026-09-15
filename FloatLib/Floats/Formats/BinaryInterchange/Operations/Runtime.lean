/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime

/-!
# Standard operations beyond basic arithmetic

Remainder, integral rounding, and exponent operations use exact dyadics and the same rounding
modes, format policies, and exception status as the arithmetic primitives. Status wrappers also
report signaling NaNs for adjacent-value and number-preferring minimum/maximum operations.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/--
Round an exact dyadic to an integer in the selected IEEE direction.

The result is an unbounded `Int`; conversion back to a floating-point format is a separate,
explicit boundary. Large negative exponents are handled by right shifts, so this operation does
not construct a power of two merely to discard fractional bits.
-/
def roundDyadicToInt (mode : IEEERoundingMode) (value : Numerics.Dyadic) : Int :=
  if value.significand == 0 then
    0
  else
    let magnitude :=
      match value.exponent with
      | .ofNat shift => Nat.shiftLeft value.significand shift
      | .negSucc shift =>
          let discardedBits := shift + 1
          let quotient := Nat.shiftRight value.significand discardedBits
          let remainder := Numerics.shiftRightRemainder value.significand discardedBits
          match mode with
          | .nearestEven =>
              Numerics.roundShiftRightEven value.significand discardedBits
          | .towardZero => quotient
          | .towardPositiveInfinity =>
              if value.negative || remainder == 0 then quotient else quotient + 1
          | .towardNegativeInfinity =>
              if !value.negative || remainder == 0 then quotient else quotient + 1
    if value.negative then -Int.ofNat magnitude else Int.ofNat magnitude

/-- Whether an exact dyadic already denotes an integer. -/
def dyadicIsIntegral (value : Numerics.Dyadic) : Bool :=
  if value.significand == 0 then
    true
  else
    match value.exponent with
    | .ofNat _ => true
    | .negSucc shift =>
        Numerics.shiftRightRemainder value.significand (shift + 1) == 0

namespace Operations.Internal

/--
Construct an exact dyadic remainder from the division facts needed by nearest-even rounding.

The caller supplies the truncated quotient's parity and the ordinary nonnegative remainder.
Keeping this decision in one helper makes direct division and logarithmic modular reduction share
the same sign, tie, and signed-zero behavior.
-/
@[inline] def remainderFromDivision
    (dividendNegative quotientOdd : Bool)
    (remainder denominator : Nat) (exponent : Int) : Numerics.Dyadic :=
  let roundsUp :=
    Numerics.nearestEvenRoundsUp quotientOdd remainder denominator
  let magnitude :=
    if roundsUp then denominator - remainder else remainder
  { negative :=
      if magnitude == 0 then dividendNegative
      else if roundsUp then !dividendNegative else dividendNegative
    significand := magnitude
    exponent }

end Operations.Internal

/--
Exact IEEE remainder of two finite dyadics with a nonzero divisor.

The selected integer quotient is nearest to `dividend / divisor`, with ties to even. When the
dividend has the larger binary exponent, its shifted significand is reduced modulo twice the
divisor by logarithmic modular exponentiation. This avoids constructing a natural number whose
size is proportional to an arbitrary exponent gap.
-/
def remainderDyadic
    (dividend divisor : Numerics.Dyadic) (_hdivisor : divisor.significand ≠ 0) :
    Numerics.Dyadic :=
  if dividend.significand == 0 then
    dividend
  else
    if divisor.exponent ≤ dividend.exponent then
      let shift := Int.toNat (dividend.exponent - divisor.exponent)
      let modulus := 2 * divisor.significand
      let scaledResidue :=
        (dividend.significand % modulus *
          Numerics.modularPow 2 shift modulus) % modulus
      let remainder := scaledResidue % divisor.significand
      let quotientOdd := divisor.significand ≤ scaledResidue
      Operations.Internal.remainderFromDivision
        dividend.negative quotientOdd remainder divisor.significand divisor.exponent
    else
      let shift := Int.toNat (divisor.exponent - dividend.exponent)
      if (2 * dividend.significand).log2 < shift then
        dividend
      else
        let scaledDivisor := Nat.shiftLeft divisor.significand shift
        let quotient := dividend.significand / scaledDivisor
        let remainder := dividend.significand % scaledDivisor
        Operations.Internal.remainderFromDivision
          dividend.negative (quotient % 2 == 1)
          remainder scaledDivisor dividend.exponent

/--
IEEE remainder with explicit exception status.

For finite IEEE operands with a nonzero divisor, the remainder is exactly representable
(`remainderWithStatus_exact`), and this branch returns clear status. NaNs propagate with signaling
operands first, then the left operand. Otherwise, a zero divisor or infinite dividend raises
`invalid`, while a finite dividend modulo infinity is unchanged.
-/
def remainderWithStatus {fmt : FloatFormat}
    (dividend divisor : Model fmt) : IEEEOutcome fmt :=
  match exactValue dividend, exactValue divisor with
  | .nan _ true _, _ =>
      outcomeWithInvalid (quietNaN dividend) true
  | _, .nan _ true _ =>
      outcomeWithInvalid (quietNaN divisor) true
  | .nan _ false _, _ =>
      outcomeWithInvalid (quietNaN dividend) false
  | _, .nan _ false _ =>
      outcomeWithInvalid (quietNaN divisor) false
  | .infinity _, _ =>
      outcomeWithInvalid (invalidResult fmt) true
  | .finite _, .infinity _ =>
      outcomeWithInvalid dividend false
  | .finite exactDividend, .finite exactDivisor =>
      if hdivisor : exactDivisor.significand = 0 then
        outcomeWithInvalid (invalidResult fmt) true
      else
        let exact := remainderDyadic exactDividend exactDivisor hdivisor
        let value :=
          if exact.significand == 0 then
            zero fmt exactDividend.negative
          else
            roundDyadic fmt exact
        outcomeWithInvalid value false

/-- Value projection of `remainderWithStatus`. -/
@[inline] def remainder {fmt : FloatFormat}
    (dividend divisor : Model fmt) : Model fmt :=
  (remainderWithStatus dividend divisor).value

/--
IEEE 754-2019 §5.9 `roundToIntegralExact` under an explicit rounding direction.

The exact dyadic is rounded to an integer, then encoded in the same direction. Zero preserves the
input sign when the format supports signed zero. A signaling NaN raises `invalid`; a fractional
finite input raises `inexact`.

`overflow` is raised only for descriptors whose finite range ends below the rounded integer; every
IEEE interchange format satisfies `fmt.fracWidth ≤ fmt.maxNormalExponent`, and
`roundToIntegralExactWithStatus_overflow_eq_false` shows that no overflow is possible there. A
custom descriptor uses its declared overflow behavior, so an overflow result need not be integral.
-/
def roundToIntegralExactWithStatus {fmt : FloatFormat} (value : Model fmt)
    (mode : IEEERoundingMode := .nearestEven) : IEEEOutcome fmt :=
  match exactValue value with
  | .finite exact =>
      let coefficient := roundDyadicToInt mode exact
      let rounded :=
        if coefficient == 0 then
          zero fmt exact.negative
        else
          roundDyadicWithRounding fmt mode (Numerics.Dyadic.ofScaledInt coefficient 0)
      let encodingStatus := dyadicRoundingStatus fmt mode
        (Numerics.Dyadic.ofScaledInt coefficient 0) rounded
      { value := rounded
        status := { overflow := encodingStatus.overflow, inexact := !dyadicIsIntegral exact } }
  | .infinity _ => outcomeWithInvalid value false
  | .nan _ signaling _ => outcomeWithInvalid (quietNaN value) signaling

/--
Integral rounding selected by `mode`, returning only the value.

This projects the value of `roundToIntegralExactWithStatus` and discards all status flags.
Use that operation when the caller needs signaling-NaN or fractional-input status.
-/
@[inline] def roundToIntegral {fmt : FloatFormat} (value : Model fmt)
    (mode : IEEERoundingMode := .nearestEven) : Model fmt :=
  (roundToIntegralExactWithStatus value mode).value

/--
Multiply a value by `2^scale` and round once in the selected direction.

Scaling changes the exact dyadic exponent without constructing `2^scale`; the shared rounder
then applies the destination format and rounding direction.
-/
def scaleBWithStatus {fmt : FloatFormat} (value : Model fmt) (scale : Int)
    (mode : IEEERoundingMode := .nearestEven) : IEEEOutcome fmt :=
  match exactValue value with
  | .finite exact =>
      let scaled : Numerics.Dyadic := { exact with exponent := exact.exponent + scale }
      let rounded := roundDyadicWithRounding fmt mode scaled
      { value := rounded
        status := dyadicRoundingStatus fmt mode scaled rounded }
  | .infinity _ => outcomeWithInvalid value false
  | .nan _ signaling _ => outcomeWithInvalid (quietNaN value) signaling

/-- Value projection of `scaleBWithStatus`. -/
@[inline] def scaleB {fmt : FloatFormat} (value : Model fmt) (scale : Int)
    (mode : IEEERoundingMode := .nearestEven) : Model fmt :=
  (scaleBWithStatus value scale mode).value

/--
Round the exponent of the value's leading binary digit into the same format, using nearest-even.

For a nonzero finite dyadic `±m * 2^e` with `m > 0`, the exact result is `floor(log₂ m) + e`.
Either infinity returns `nativeOverflow fmt false`, the format's positive overflow value. NaNs are
quiet-propagated, with `invalid` raised only for a signaling NaN.

Zero returns `nativeOverflow fmt true` and raises `divideByZero`, following IEEE 754-2019 §5.3.3.
What that value is depends on the encoding:

* IEEE encodings deliver negative infinity, as the standard specifies.
* `finiteMaxNaN` and `finiteUnsignedZero` (FNUZ) return their NaN word with the same `divideByZero`
  flag for the zero input.
* `finite` (signed zero, no NaN) saturates to the most negative finite value.
-/
def logBWithStatus {fmt : FloatFormat} (value : Model fmt) : IEEEOutcome fmt :=
  match exactValue value with
  | .finite exact =>
      if exact.significand == 0 then
        { value := nativeOverflow fmt true
          status := { divideByZero := true } }
      else
        let exponent := Int.ofNat exact.significand.log2 + exact.exponent
        let exactResult := Numerics.Dyadic.ofScaledInt exponent 0
        let rounded := roundDyadic fmt exactResult
        { value := rounded
          status := dyadicRoundingStatus fmt .nearestEven exactResult rounded }
  | .infinity _ =>
      { value := nativeOverflow fmt false
        status := .clear }
  | .nan _ signaling _ =>
      { value := quietNaN value
        status := { invalid := signaling } }

/-- Value projection of `logBWithStatus`. -/
@[inline] def logB {fmt : FloatFormat} (value : Model fmt) : Model fmt :=
  (logBWithStatus value).value

/-!
## Status-bearing forms of the quiet operations

`nextUp`, `nextDown`, `minimumNumber`, and `maximumNumber` are value-only in `Model`. IEEE
754-2019 §5.3.1 and §9.6 still require a signaling NaN operand to raise `invalid`; the wrappers
below add exactly that indicator and change nothing else.
-/

/-- `nextUp` with `invalid` set exactly for a signaling NaN input. -/
@[inline] def nextUpWithStatus {fmt : FloatFormat} (x : Model fmt) : IEEEOutcome fmt :=
  outcomeWithInvalid (nextUp x) (isSNaN x)

/-- `nextDown` with `invalid` set exactly for a signaling NaN input. -/
@[inline] def nextDownWithStatus {fmt : FloatFormat} (x : Model fmt) : IEEEOutcome fmt :=
  outcomeWithInvalid (nextDown x) (isSNaN x)

/--
IEEE 754-2019 §9.6 `minimumNumber` with status. A signaling NaN raises `invalid`, including when
the other operand is a number and supplies the result.
-/
@[inline] def minimumNumberWithStatus {fmt : FloatFormat} (x y : Model fmt) : IEEEOutcome fmt :=
  outcomeWithInvalid (minimumNumber x y) (isSNaN x || isSNaN y)

/--
IEEE 754-2019 §9.6 `maximumNumber` with status. A signaling NaN raises `invalid`, including when
the other operand is a number and supplies the result.
-/
@[inline] def maximumNumberWithStatus {fmt : FloatFormat} (x y : Model fmt) : IEEEOutcome fmt :=
  outcomeWithInvalid (maximumNumber x y) (isSNaN x || isSNaN y)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
