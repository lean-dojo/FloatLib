/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Runtime
public import FloatLib.Numerics.Exact.RationalBinary

/-!
# Exact-rational P3109 projection

Configured binary floats, posits, integer inputs, and exact finite arithmetic can all supply
exact rational values. This module projects them directly into any valid P3109 descriptor,
rounding from the numerator and denominator without an intermediate approximation.

The runtime follows the same P3109 projection order as dyadic projection:

1. select the descriptor quantum;
2. round the exact quotient according to the requested P3109 mode;
3. apply the shared saturation rule;
4. encode the resulting datum directly.

The dyadic entry point remains useful when the caller already owns an exact binary value. Both
paths share saturation, encoding, and descriptor logic.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109
namespace Format

namespace Internal

/-- Floor of `(remainder / denominator) * 2^outputBits`. -/
@[inline] def scaleRationalFractionFloor
    (remainder denominator outputBits : Nat) : Nat :=
  Nat.shiftLeft remainder outputBits / denominator

/-- Nearest-even integer to `(remainder / denominator) * 2^outputBits`. -/
@[inline] def scaleRationalFractionNearestEven
    (remainder denominator outputBits : Nat) : Nat :=
  roundQuotientEven (Nat.shiftLeft remainder outputBits) denominator

/--
Decide whether exact rational rounding selects the integer above the quotient floor.

`denominator` is positive for every `Rat`. Keeping it explicit makes the stochastic formulas
match P3109 Section 4.7.4 directly.
-/
@[inline] def roundRationalAwayWithParity
    (mode : RoundingMode) (negative lowerEven : Bool)
    (remainder denominator : Nat) : Bool :=
  if remainder == 0 then
    false
  else
    let twiceRemainder := 2 * remainder
    match mode with
    | .towardZero => false
    | .towardPositive => !negative
    | .towardNegative => negative
    | .nearestTiesToAway => decide (denominator ≤ twiceRemainder)
    | .nearestTiesToEven =>
        decide (denominator < twiceRemainder) ||
          (denominator == twiceRemainder && !lowerEven)
    | .toOdd => lowerEven
    | .stochasticA random =>
        let scaled :=
          scaleRationalFractionFloor remainder denominator random.width
        decide (2 ^ random.width ≤ scaled + random.toNat)
    | .stochasticB random =>
        let scaled :=
          scaleRationalFractionFloor
            remainder denominator (random.width + 1)
        decide
          (2 ^ (random.width + 1) ≤
            scaled + (2 * random.toNat + 1))
    | .stochasticC random =>
        let scaled :=
          scaleRationalFractionNearestEven
            remainder denominator random.width
        decide (2 ^ random.width ≤ scaled + random.toNat)

/-- P3109 rational rounding uses the descriptor's code parity, including precision one. -/
@[inline] def roundRationalAway
    (format : Format) (mode : RoundingMode) (negative : Bool)
    (quantumExponent : Int) (lower remainder denominator : Nat) : Bool :=
  roundRationalAwayWithParity mode negative
    (format.lowerCodeIsEven quantumExponent lower) remainder denominator

end Internal

/--
Round one exact finite rational to the descriptor's P3109 precision.

The selected quantum is
`max(floor(log2 |x|), 1 - B) - P + 1`. Scaling by the opposite quantum turns the rounding decision
into one natural-number quotient and remainder. The result is an exact dyadic datum on the P3109
precision grid.
-/
@[inline] def roundFiniteRatToPrecision
    (format : Format) (mode : RoundingMode) (exact : Rat) :
    Numerics.Dyadic :=
  let numerator := exact.num.natAbs
  if numerator == 0 then
    .zero
  else
    let negative := exact.num < 0
    let leadingExponent :=
      Numerics.RationalBinary.floorLog2 numerator exact.den
    let quantumExponent :=
      max leadingExponent format.minimumNormalExponent -
        Int.ofNat format.precision + 1
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        numerator exact.den (-quantumExponent)
    let lower := scaled.1 / scaled.2
    let remainder := scaled.1 % scaled.2
    let rounded :=
      if Internal.roundRationalAway format mode negative
          quantumExponent lower remainder scaled.2 then
        lower + 1
      else
        lower
    if rounded == 0 then
      .zero
    else
      {
        negative
        significand := rounded
        exponent := quantumExponent
      }

/-- Apply P3109 precision rounding to an exact-rational closed value. -/
@[inline] def roundRatToPrecision
    (format : Format) (mode : RoundingMode)
    (value : NumericalValue Rat) :
    NumericalValue Numerics.Dyadic :=
  match value with
  | .finite exact => .finite (format.roundFiniteRatToPrecision mode exact)
  | .infinity negative => .infinity negative
  | .exceptional _ => .exceptional (.nan)

/-- Exact-rational P3109 result before representation encoding. -/
@[inline] def projectRatValue
    (format : Format) (policy : ProjectionPolicy)
    (value : NumericalValue Rat) :
    NumericalValue Numerics.Dyadic :=
  format.saturate policy.saturation policy.rounding
    (format.roundRatToPrecision policy.rounding value)

/-- Project one exact-rational closed value and return its descriptor-width code. -/
@[inline] def projectRatCode
    (format : Format) (policy : ProjectionPolicy)
    (value : NumericalValue Rat) : BitVec format.bitWidth :=
  BitVec.ofNat format.bitWidth
    (Internal.encodeDatumNat format
      (format.projectRatValue policy value))

end Format
end FloatLib.Floats.Formats.P3109

namespace FloatLib.Floats.ExecFloat.P3109

variable {format : Formats.P3109.Format}

/--
Project an exact rational, infinity, or exceptional observation into a P3109 descriptor.

Finite values are rounded once from their exact numerator and denominator. No intermediate binary
or host floating-point format is involved.
-/
@[inline] def projectRat
    (policy : Formats.P3109.ProjectionPolicy)
    (value : NumericalValue Rat) :
    ExecFloat.P3109 format :=
  ExecFloat.Codebook.ofCode (format.projectRatCode policy value)

/-- Project one finite exact rational into a P3109 descriptor. -/
@[inline] def ofRat
    (policy : Formats.P3109.ProjectionPolicy) (value : Rat) :
    ExecFloat.P3109 format :=
  projectRat policy (.finite value)

end FloatLib.Floats.ExecFloat.P3109
