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
modes, format policies, and exception status as the arithmetic primitives. Like the arithmetic
operations, each has one name with options: `roundToIntegral x (mode := .up)`,
`scale x n (mode := .down) (status := true)`, `remainder x y (status := true)`. Integral rounding
and scaling take a rounding direction. The rounded binary exponent always rounds to nearest-even,
and remainder, `nextUp`, `nextDown`, `minimumNumber`, and `maximumNumber` are exact, so they take
only `status`. With `status := true`, `nextUp` and its three siblings report the `invalid` signal
that a signaling NaN operand owes.

Each public operation is a small `@[macro_inline]` selector that tests `status` before computing
anything. The kernels it selects live in `Model.Internal.Status` and `Model.Internal.Value`.
Integral rounding, scaling, and the rounded binary exponent carry `@[specialize fmt]`: a module
that calls them with a closed format compiles a copy specialized to that descriptor term (calls
that spell the same descriptor alike share it), and other callers run the compiled generic body.
Their value kernels inline the status body and compute no flags or ternary value.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/--
Round an exact dyadic to an integer in the selected direction.

The result is an unbounded `Int`, and converting it back to a floating-point format is a separate
step. Large negative exponents are handled by right shifts, so this operation does
not construct a power of two merely to discard fractional bits. Nearest-away rounding and rounding
away from zero apply `Numerics.roundShiftRight` to the magnitude. They select the integers of IEEE
754-2019 roundToIntegralTiesToAway and of MPFR's `mpfr_rint` under `MPFR_RNDA`.
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
          | .nearest =>
              Numerics.roundShiftRightEven value.significand discardedBits
          | .nearestAway =>
              Numerics.roundShiftRight .nearestAway value.significand discardedBits
          | .towardZero => quotient
          | .up =>
              if value.negative || remainder == 0 then quotient else quotient + 1
          | .down =>
              if !value.negative || remainder == 0 then quotient else quotient + 1
          | .away => Numerics.roundShiftRight .up value.significand discardedBits
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
Direct division and logarithmic modular reduction both call it, so they share the same sign, tie,
and signed-zero behavior.
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

namespace Internal.Status

/--
IEEE remainder with exception status, the kernel of
`Model.remainder dividend divisor (status := true)`.

For finite IEEE operands with a nonzero divisor, the remainder is exactly representable
(`remainder_exact`), and this branch returns clear status and the ternary value `.eq`.
NaNs propagate with signaling operands first, then the left operand. Otherwise, a zero divisor or
infinite dividend raises `invalid`, while a finite dividend modulo infinity is unchanged. Every
branch has the ternary value `.eq`.
-/
def remainder {fmt : FloatFormat}
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
            Model.roundDyadic fmt exact
        outcomeWithInvalid value false

end Internal.Status

/--
IEEE 754-2019 §5.3.1 `remainder`: `dividend - n * divisor` for the integer `n` nearest to the
exact quotient, ties to even. The result is exact, so there is no rounding option. With
`status := true` the result is the `IEEEOutcome` carrying the `invalid` flag of a zero divisor, an
infinite dividend, or a signaling NaN.
-/
@[macro_inline] def remainder {fmt : FloatFormat} (dividend divisor : Model fmt)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => Internal.Status.remainder dividend divisor
  | false => (Internal.Status.remainder dividend divisor).value

namespace Internal.Status

/--
IEEE 754-2019 §5.9 `roundToIntegralExact` in rounding direction `mode`, the kernel of
`Model.roundToIntegral value (mode := mode) (status := true)`.

The exact dyadic is rounded to an integer, then encoded in the same direction. Zero preserves the
input sign when the format supports signed zero. A signaling NaN raises `invalid`, and a
fractional finite input raises `inexact`.

`overflow` is raised only for descriptors whose finite range ends below the rounded integer. Every
IEEE interchange format satisfies `fmt.fracWidth ≤ fmt.maxNormalExponent`, and
`roundToIntegral_overflow_eq_false` shows that no overflow is possible there, so on an IEEE
descriptor with that range the overflow test is skipped. The range test is stated over natural
numbers, `fmt.fracWidth + fmt.exponentBias ≤ fmt.maxFiniteExpField`, so a closed format folds it
at compile time. `roundToIntegral_status_of_finite` states the finite outcome with the encoder's
overflow classification. A custom descriptor uses its declared overflow behavior, so an overflow
result need not be integral.

The ternary value compares the delivered value with the input, as MPFR's `mpfr_rint` does. It is
therefore not determined by `inexact`: a saturating descriptor can deliver its own fractional
input, with `inexact` raised and the ternary value `.eq`.
-/
@[specialize fmt] def roundToIntegral {fmt : FloatFormat} (value : Model fmt)
    (mode : IEEERoundingMode) : IEEEOutcome fmt :=
  match exactValue value with
  | .finite exact =>
      let coefficient := roundDyadicToInt mode exact
      let rounded :=
        if coefficient == 0 then
          zero fmt exact.negative
        else
          Directed.roundDyadic fmt mode (Numerics.Dyadic.ofScaledInt coefficient 0)
      let overflow :=
        if fmt.isIEEE && decide (fmt.fracWidth + fmt.exponentBias ≤ fmt.maxFiniteExpField) then
          false
        else
          -- The overflow indicator of `dyadicRoundingStatus` (`dyadicRoundingStatus_overflow`),
          -- read without decoding the delivery or testing inexactness and tininess.
          dyadicRoundingOverflows fmt mode (Numerics.Dyadic.ofScaledInt coefficient 0) ||
            (!isFinite rounded && isInf rounded)
      { value := rounded
        status := { overflow, inexact := !dyadicIsIntegral exact }
        ternary := dyadicTernary exact rounded }
  | .infinity _ => outcomeWithInvalid value false
  | .nan _ signaling _ => outcomeWithInvalid (quietNaN value) signaling

/--
Multiply a value by `2^n`, round once, and report exception flags (IEEE 754 `scaleB`), the kernel
of `Model.scale value n (mode := mode) (status := true)`.

Scaling changes the exact dyadic exponent without constructing `2^n`, and the shared rounder
then applies the destination format and rounding direction. The ternary value compares the
delivered value with the exact scaled dyadic.
-/
@[specialize fmt] def scale {fmt : FloatFormat} (value : Model fmt) (n : Int)
    (mode : IEEERoundingMode) : IEEEOutcome fmt :=
  match exactValue value with
  | .finite exact =>
      let scaled : Numerics.Dyadic := { exact with exponent := exact.exponent + n }
      let rounded := Directed.roundDyadic fmt mode scaled
      Model.dyadicRoundingOutcome fmt mode scaled rounded
  | .infinity _ => outcomeWithInvalid value false
  | .nan _ signaling _ => outcomeWithInvalid (quietNaN value) signaling

end Internal.Status

namespace Internal.Value

/--
The value of `Status.roundToIntegral`, the kernel of `Model.roundToIntegral value (mode := mode)`.
The status body is inlined here, so the compiled kernel computes neither flags nor the ternary
value.
-/
@[specialize fmt] def roundToIntegral {fmt : FloatFormat} (value : Model fmt)
    (mode : IEEERoundingMode) : Model fmt :=
  (inline (Status.roundToIntegral value mode)).value

/--
The value of `Status.scale`, the kernel of `Model.scale value n (mode := mode)`, with the status
body inlined as in `Internal.Value.roundToIntegral`.
-/
@[specialize fmt] def scale {fmt : FloatFormat} (value : Model fmt) (n : Int)
    (mode : IEEERoundingMode) : Model fmt :=
  (inline (Status.scale value n mode)).value

end Internal.Value

/--
IEEE 754-2019 §5.9 integral rounding in `mode` (nearest-even by default).

The value is `roundToIntegral`: the input rounded to an integer and encoded in the same
direction. With `status := true` the result is the `IEEEOutcome` of `roundToIntegralExact`: a
signaling NaN raises `invalid` and a fractional finite input raises `inexact`, and the ternary
value compares the delivered value with the input.
-/
@[macro_inline] def roundToIntegral {fmt : FloatFormat} (value : Model fmt)
    (mode : IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => Internal.Status.roundToIntegral value mode
  | false => Internal.Value.roundToIntegral value mode

/--
Multiply by `2^n` and round once in `mode` (nearest-even by default), IEEE 754 `scaleB`. With
`status := true` the result is the `IEEEOutcome` carrying the exception flags and the ternary
value.
-/
@[macro_inline] def scale {fmt : FloatFormat} (value : Model fmt) (n : Int)
    (mode : IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => Internal.Status.scale value n mode
  | false => Internal.Value.scale value n mode

/-- Integer result and default exception indicators for IEEE `logB`. -/
structure IntegerExponentOutcome where
  /-- Exact leading exponent, or a format-dependent exceptional sentinel. -/
  value : Int
  /-- Exceptional integer results signal invalid, and finite nonzero inputs raise no flags. -/
  status : Numerics.IEEEStatus := {}
  deriving DecidableEq, Repr

/-- The IEEE integer `logB` exceptional-result bound `emax + p - 1`. -/
def logBBound (fmt : FloatFormat) : Int :=
  fmt.maxNormalExponent + fmt.fracWidth

/-- Exceptional integer outside the finite exponent range and the IEEE `logB` bound. -/
def binaryExponentSentinel (fmt : FloatFormat) : Int :=
  2 * max (max |fmt.minSubnormalExponent| |fmt.maxNormalExponent|) |logBBound fmt| + 1

/--
Exact IEEE 754-2019 §5.3.3 `logB` with an unbounded integer result format.

For nonzero finite `±m * 2^e`, return `floor(log₂ m) + e` with clear status. Zero returns
the negative exceptional sentinel, and infinity and either kind of NaN return the positive one.
All exceptional integer results signal `invalid`, as required for an integer `logBFormat`.
No rounding of the exponent occurs, including for low-precision source descriptors.
-/
def binaryExponentInt {fmt : FloatFormat} (value : Model fmt) : IntegerExponentOutcome :=
  match exactValue value with
  | .finite exact =>
      if exact.significand == 0 then
        { value := -binaryExponentSentinel fmt, status := { invalid := true } }
      else
        { value := Int.ofNat exact.significand.log2 + exact.exponent }
  | .infinity _ | .nan _ _ _ =>
      { value := binaryExponentSentinel fmt, status := { invalid := true } }

namespace Internal.Status

/--
Return the leading binary exponent rounded into the same format, with exception flags, the kernel
of `Model.binaryExponent value (status := true)`.

This convenience operation uses nearest-even. It agrees with floating-result IEEE `logB`
only when the source format can represent the exponent exactly, and `binaryExponentInt` provides
the exact integer-result operation for every descriptor.

For a nonzero finite dyadic `±m * 2^e` with `m > 0`, the exact result is `floor(log₂ m) + e`.
Either infinity returns `nativeOverflow fmt false`, the format's positive overflow value. NaNs are
quiet-propagated, with `invalid` raised only for a signaling NaN.

Zero returns `nativeOverflow fmt true` and raises `divideByZero`, following IEEE 754-2019 §5.3.3.
What that value is depends on the encoding:

* IEEE encodings deliver negative infinity, as the standard specifies.
* `finiteMaxNaN` and `finiteUnsignedZero` (FNUZ) return their NaN word with the same `divideByZero`
  flag for the zero input.
* `finite` (signed zero, no NaN) saturates to the most negative finite value.

The ternary value compares the delivered value with the exact exponent, so a low-precision
format that rounds the exponent reports the direction: in `ieee 5 1` the exponent `13` of `2^13`
is delivered as `12` with `.lt`. The exact infinities of zero and infinite inputs use
`exactInfinityTernary`, which is `.eq` for IEEE encodings and records the saturated or NaN
replacement elsewhere.
-/
@[specialize fmt] def binaryExponent {fmt : FloatFormat} (value : Model fmt) :
    IEEEOutcome fmt :=
  match exactValue value with
  | .finite exact =>
      if exact.significand == 0 then
        let result := nativeOverflow fmt true
        { value := result
          status := { divideByZero := true }
          ternary := exactInfinityTernary true result }
      else
        let exponent := Int.ofNat exact.significand.log2 + exact.exponent
        let exactResult := Numerics.Dyadic.ofScaledInt exponent 0
        let rounded := Model.roundDyadic fmt exactResult
        Model.dyadicRoundingOutcome fmt .nearest exactResult rounded
  | .infinity _ =>
      let result := nativeOverflow fmt false
      { value := result
        status := .clear
        ternary := exactInfinityTernary false result }
  | .nan _ signaling _ =>
      { value := quietNaN value
        status := { invalid := signaling }
        ternary := .eq }

end Internal.Status

/--
The value of `Status.binaryExponent`, the kernel of `Model.binaryExponent value`, with the status
body inlined as in `Internal.Value.roundToIntegral`.
-/
@[specialize fmt] def Internal.Value.binaryExponent {fmt : FloatFormat} (value : Model fmt) :
    Model fmt :=
  (inline (Internal.Status.binaryExponent value)).value

/--
Leading binary exponent rounded into the source format, always to nearest-even.
`binaryExponentInt` is the exact integer version. With `status := true` the result is the
`IEEEOutcome` carrying the exception flags and the ternary value.
-/
@[macro_inline] def binaryExponent {fmt : FloatFormat} (value : Model fmt)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => Internal.Status.binaryExponent value
  | false => Internal.Value.binaryExponent value

/-!
## Status of the quiet operations

`nextUp`, `nextDown`, `minimumNumber`, and `maximumNumber` compute exact results without a
status. IEEE 754-2019 §5.3.1 and §9.6 still require a signaling NaN operand to raise `invalid`,
so with `status := true` each operation adds that indicator and changes nothing else. Their
results are exact, so the ternary value is `.eq`.
-/

/--
The next representable value strictly greater than `x`, IEEE 754-2019 §5.3.1 `nextUp`. With
`status := true` the result is the `IEEEOutcome` with `invalid` set exactly for a signaling NaN.
-/
@[macro_inline] def nextUp {fmt : FloatFormat} (x : Model fmt) (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => outcomeWithInvalid (Internal.Value.nextUp x) (isSNaN x)
  | false => Internal.Value.nextUp x

/--
The next representable value strictly less than `x`, IEEE 754-2019 §5.3.1 `nextDown`. With
`status := true` the result is the `IEEEOutcome` with `invalid` set exactly for a signaling NaN.
-/
@[macro_inline] def nextDown {fmt : FloatFormat} (x : Model fmt) (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => outcomeWithInvalid (Internal.Value.nextDown x) (isSNaN x)
  | false => Internal.Value.nextDown x

/--
IEEE 754-2019 §9.6 `minimumNumber`. With `status := true` the result is the `IEEEOutcome`: a
signaling NaN raises `invalid`, including when the other operand is a number and supplies the
result.
-/
@[macro_inline] def minimumNumber {fmt : FloatFormat} (x y : Model fmt)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => outcomeWithInvalid (Internal.Value.minimumNumber x y) (isSNaN x || isSNaN y)
  | false => Internal.Value.minimumNumber x y

/--
IEEE 754-2019 §9.6 `maximumNumber`. With `status := true` the result is the `IEEEOutcome`: a
signaling NaN raises `invalid`, including when the other operand is a number and supplies the
result.
-/
@[macro_inline] def maximumNumber {fmt : FloatFormat} (x y : Model fmt)
    (status : Bool := false) :
    match status with
    | true => IEEEOutcome fmt
    | false => Model fmt :=
  match status with
  | true => outcomeWithInvalid (Internal.Value.maximumNumber x y) (isSNaN x || isSNaN y)
  | false => Internal.Value.maximumNumber x y

end Model
end FloatLib.Floats.Formats.BinaryInterchange
