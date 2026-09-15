/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Format.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime

/-!
# Numeric conversion between binary and decimal interchange

Both directions evaluate the finite input exactly as a rational before rounding
once to the destination. Binary-to-decimal conversion prefers quantum zero on
an exact result; decimal projection supplies the least quantum for an inexact
result. For an exact result, the selected quantum is closest to zero among its
representable cohort members. Decimal-to-binary conversion uses the existing
binary rational kernels.
Nearest-away first rounds the exact rational to the destination binary grid,
then encodes that representable dyadic with the existing binary encoder.

Zeros and infinities retain their signs. NaNs are quieted and raise invalid
exactly when signaling. The diagnostic payload is interpreted as a natural
number: it is preserved when it fits the destination, otherwise replaced by
zero. This is an explicit payload-selection policy, not a claim that IEEE 754
uniquely specifies a payload when narrowing.

Decimal destinations use tininess before rounding. Binary destinations use the
existing library convention: tininess after rounding to the destination
precision with an unbounded exponent range. The constants for the binary midpoint
and predecessor are shared with the scalar status implementation.

## References

* IEEE 754-2019, §§4.3, 5.2, 5.4.2, 6.2, 7.4 and 7.5.
* ISO/IEC JTC1/SC22/WG14, N2596, §5.2.4.2.3, preferred quantum exponents:
  <https://www.open-std.org/jtc1/sc22/wg14/www/docs/n2596.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion

open FloatLib.Floats.Formats

/-- Extract the diagnostic payload of an IEEE binary NaN, excluding its quiet bit. -/
def binaryPayload {fmt : BinaryInterchange.FloatFormat} (x : BinaryInterchange.Model fmt) : Nat :=
  BinaryInterchange.Model.fracField x % (2 ^ (fmt.fracWidth - 1))

/-- Convert a binary model to a decimal datum. Exact finite results prefer quantum zero;
the source zero sign is retained. The numerical path also accepts custom binary models
according to their descriptors; IEEE class guarantees apply to IEEE source formats. -/
def fromBinary {fmt : BinaryInterchange.FloatFormat} (target : Format) (mode : RoundingMode)
    (x : BinaryInterchange.Model fmt) : Outcome :=
  match BinaryInterchange.Model.toRat? x with
  | some value => project target mode value 0 (BinaryInterchange.Model.signBit x)
  | none =>
      if BinaryInterchange.Model.isNaN x then
        Arithmetic.nanResult target (BinaryInterchange.Model.signBit x) (binaryPayload x)
          (BinaryInterchange.Model.isSNaN x)
      else
        { value := .infinity (BinaryInterchange.Model.signBit x) }

/-- Encode a quiet binary NaN with its sign and a fitting natural-number payload.
`toBinary` uses this only for an IEEE destination. -/
def binaryNaN (fmt : BinaryInterchange.FloatFormat) (negative : Bool) (payload : Nat) :
    BinaryInterchange.Model fmt :=
  let quiet := 2 ^ (fmt.fracWidth - 1)
  BinaryInterchange.Model.ofFields fmt negative fmt.expAllOnesNat
    (quiet + if payload < quiet then payload else 0)

/-- Binary grid exponent for a rational magnitude, bounded below by the subnormal quantum. -/
def binaryQuantum (fmt : BinaryInterchange.FloatFormat) (magnitude : ℚ) : Int :=
  max fmt.minSubnormalExponent
    (Numerics.RationalBinary.floorLog2 magnitude.num.natAbs magnitude.den - fmt.fracWidth)

/-- Round to nearest, ties away, on the destination's binary grid. The significand can
equal `2^precision` at a carry; this is still exactly representable before overflow. -/
def binaryNearestAwayDyadic (fmt : BinaryInterchange.FloatFormat) (negative : Bool)
    (magnitude : ℚ) : Numerics.Dyadic :=
  let exponent := binaryQuantum fmt magnitude
  { negative
    significand := RoundingMode.nearestAway.roundMagnitude negative
      (magnitude / (2 : ℚ) ^ exponent)
    exponent }

/-- Round a signed rational magnitude directly into the binary destination.
The magnitude is supplied as a nonnegative rational by `toBinary`. -/
def roundBinaryMagnitude (fmt : BinaryInterchange.FloatFormat) (mode : RoundingMode)
    (negative : Bool) (magnitude : ℚ) : BinaryInterchange.Model fmt :=
  let num := magnitude.num.natAbs
  let den := magnitude.den
  match mode with
  | .nearestEven =>
      BinaryInterchange.Model.roundRatWithRounding fmt .nearestEven negative num den
  | .nearestAway =>
      BinaryInterchange.Model.roundDyadic fmt (binaryNearestAwayDyadic fmt negative magnitude)
  | .towardZero =>
      BinaryInterchange.Model.roundRatWithRounding fmt .towardZero negative num den
  | .towardPositive =>
      BinaryInterchange.Model.roundRatWithRounding fmt .towardPositiveInfinity negative num den
  | .towardNegative =>
      BinaryInterchange.Model.roundRatWithRounding fmt .towardNegativeInfinity negative num den

/-- Whether a directed conversion increases a nonzero magnitude. Nearest modes
use midpoint rules instead of this directed-mode predicate. -/
def binaryRoundsAway (mode : RoundingMode) (negative : Bool) : Bool :=
  match mode with
  | .towardPositive => !negative
  | .towardNegative => negative
  | .nearestEven | .nearestAway | .towardZero => false

/-- IEEE overflow compares the precision-rounded unbounded result with the exponent limit.
For IEEE binary layouts the largest finite significand is odd, so both nearest modes
include the upper midpoint. -/
def binaryOverflow (fmt : BinaryInterchange.FloatFormat) (mode : RoundingMode)
    (negative : Bool) (magnitude : ℚ) : Bool :=
  match mode with
  | .nearestEven | .nearestAway =>
      decide ((BinaryInterchange.Model.overflowMidpoint fmt).toRat ≤ magnitude)
  | .towardZero | .towardPositive | .towardNegative =>
      if binaryRoundsAway mode negative then
        decide ((BinaryInterchange.Model.maxFiniteDyadic fmt).toRat < magnitude)
      else
        decide ((BinaryInterchange.Model.overflowLimit fmt).toRat ≤ magnitude)

/-- Tininess after precision rounding, including exact values which deliver the smallest
normal but whose unbounded-precision-grid rounding is still tiny. -/
def binaryTiny (fmt : BinaryInterchange.FloatFormat) (mode : RoundingMode)
    (negative : Bool) (magnitude : ℚ) (rounded : BinaryInterchange.Model fmt) : Bool :=
  BinaryInterchange.Model.isTinyAfterRounding rounded ||
    match mode with
    | .nearestEven | .nearestAway =>
        decide (magnitude < (BinaryInterchange.Model.underflowMidpoint fmt).toRat)
    | .towardZero | .towardPositive | .towardNegative =>
        if binaryRoundsAway mode negative then
          decide (magnitude ≤ (BinaryInterchange.Model.underflowPredecessor fmt).toRat)
        else
          decide (magnitude < (BinaryInterchange.Model.minNormalDyadic fmt).toRat)

/-- Default binary conversion flags, using exact rational comparisons. Invalid and
divide-by-zero are absent on the finite path; overflow always raises inexact. -/
def binaryStatus (fmt : BinaryInterchange.FloatFormat) (mode : RoundingMode)
    (negative : Bool) (magnitude : ℚ) (rounded : BinaryInterchange.Model fmt) :
    BinaryInterchange.Model.IEEEStatus :=
  let overflow := binaryOverflow fmt mode negative magnitude
  let exact := if negative then -magnitude else magnitude
  let inexact := overflow || decide (BinaryInterchange.Model.toRat? rounded ≠ some exact)
  { overflow
    inexact
    underflow := !overflow && binaryTiny fmt mode negative magnitude rounded && inexact }

/-- Convert a decimal datum to an IEEE binary destination in any of the five rounding
directions. The IEEE descriptor proof excludes finite-only exceptional-value policies.
Finite input coefficients and quantum exponents are evaluated exactly, so the source
decimal cohort does not affect the binary result. -/
def toBinary (target : BinaryInterchange.FloatFormat) (_hIEEE : target.isIEEE = true)
    (mode : RoundingMode) (x : Datum) : BinaryInterchange.Model.IEEEOutcome target :=
  match x with
  | .finite negative coefficient quantum =>
      let magnitude := (coefficient : ℚ) * (10 : ℚ) ^ quantum
      let rounded := roundBinaryMagnitude target mode negative magnitude
      { value := rounded
        status := binaryStatus target mode negative magnitude rounded }
  | .infinity negative =>
      { value := BinaryInterchange.Model.infinityOrMaxFinite target negative, status := {} }
  | .nan negative signaling payload =>
      { value := binaryNaN target negative payload, status := { invalid := signaling } }

end FloatLib.Floats.Formats.DecimalInterchange.Conversion
