/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Mode

/-!
# Division with one integer quotient

The nearest-even kernel divides a doubled numerator. The low quotient bit distinguishes values
below a rounding midpoint; the next bit resolves ties whose retained significand is odd. Only the
remaining case needs an exactness check. A machine-word product often disproves exactness before
the full product is needed. Equality of machine words never certifies equality of natural numbers.

Scaling and the extra quotient bit share one numerator shift. Neither the fraction width nor the
integer division has a fixed limb bound. `GeneralProof` proves agreement with the exact rational
rounders, including subnormal results and all four IEEE rounding directions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteQuotientRound

open FloatLib.Numerics

/--
Round `doubled / (2 * den)` to nearest, with ties to even.

Callers supply an even `doubled` and a nonzero denominator. Computing the extra quotient bit
avoids a second arbitrary-precision division for a remainder. A failed low-word comparison
certifies inexactness; a successful comparison still requires equality of the full product.
-/
@[inline] def roundEvenDoubled (doubled den : Nat) : Nat :=
  let quotient := doubled / den
  let lower := quotient >>> 1
  let low := UInt64.ofNat quotient
  if (low &&& 1) == 0 then lower
  else if (low &&& 2) != 0 then lower + 1
  else if low * UInt64.ofNat den != UInt64.ofNat doubled then lower + 1
  else if quotient * den != doubled then lower + 1
  else lower

/-- Nearest-even quotient rounding with a fused binary scale and extra quotient bit. -/
@[inline] def roundEvenScaled (num den : Nat) : Int → Nat
  | .ofNat shift => roundEvenDoubled (num <<< (shift + 1)) den
  | .negSucc shift => roundEvenDoubled (num <<< 1) (den <<< (shift + 1))

/-- Ceiling division using one quotient, with the reference convention for a zero denominator. -/
@[inline] def ceilQuotient (num den : Nat) : Nat :=
  if num == 0 || den == 0 then 0 else (num - 1) / den + 1

/-- Directed quotient rounding after an exact binary scale. -/
@[inline] def roundDirectedScaled (up : Bool) (num den : Nat) (shift : Int) : Nat :=
  let (scaledNum, scaledDen) := RationalBinary.scaleByPowerOfTwo num den shift
  if up then ceilQuotient scaledNum scaledDen else scaledNum / scaledDen

/--
IEEE nearest-even rational rounding with a supplied rational exponent.

`rationalExponent` must equal `RationalBinary.floorLog2 num den`. Supplying it lets a finite
division use a single significand comparison when both operands are normal.
-/
@[inline] def ieeeRoundAtExponent (fmt : FloatFormat) (sign : Bool) (num den : Nat)
    (exponent rationalExponent : Int) : Model fmt :=
  let p := fmt.fracWidth
  let maxUnb : Int := Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)
  let minUnb : Int := FloatFormat.ieeeMinNormalExponent fmt
  let underK : Int := -Int.ofNat (FloatFormat.normalMantissaExpOffset fmt)
  let subAlign : Nat := FloatFormat.subnormalAlignExp fmt
  let bias : Nat := fmt.bias
  if den == 0 then
    canonicalNaN fmt
  else if num == 0 then
    if sign then negZero fmt else posZero fmt
  else
    let totalExponent := rationalExponent + exponent
    if totalExponent > maxUnb then
      if sign then negInf fmt else posInf fmt
    else if totalExponent < underK then
      if sign then negZero fmt else posZero fmt
    else if totalExponent < minUnb then
      let fraction := roundEvenScaled num den (exponent + Int.ofNat subAlign)
      if fraction == 0 then
        if sign then negZero fmt else posZero fmt
      else
        match Nat.decLe (pow2 p) fraction with
        | isTrue _ => ofFields fmt sign 1 0
        | isFalse _ => ofFields fmt sign 0 fraction
    else
      let mantissa := roundEvenScaled num den (Int.ofNat p - rationalExponent)
      let carried := mantissa == pow2 (p + 1)
      let resultExponent := if carried then totalExponent + 1 else totalExponent
      let resultMantissa := if carried then pow2 p else mantissa
      if resultExponent > maxUnb then
        if sign then negInf fmt else posInf fmt
      else
        ofFields fmt sign (resultExponent + Int.ofNat bias).toNat (resultMantissa - pow2 p)

/-- Descriptor-generic nearest-even rational rounding with a supplied rational exponent. -/
@[inline] def generalRoundAtExponent (fmt : FloatFormat) (sign : Bool) (num den : Nat)
    (exponent rationalExponent : Int) : Model fmt :=
  let precision := fmt.fracWidth
  if den == 0 then
    invalidResult fmt
  else if num == 0 then
    zero fmt sign
  else
    let totalExponent := rationalExponent + exponent
    if totalExponent > fmt.maxNormalExponent then
      nativeOverflow fmt sign
    else if totalExponent + 1 < fmt.minSubnormalExponent then
      zero fmt sign
    else if totalExponent < fmt.minNormalExponent then
      let fraction :=
        roundEvenScaled num den (exponent + Int.ofNat (fmt.exponentBias + precision - 1))
      packRoundedSubnormal fmt sign (zero fmt sign) fraction
    else
      let rounded := roundEvenScaled num den (Int.ofNat precision - rationalExponent)
      packRoundedNormal fmt sign (nativeOverflow fmt sign) totalExponent rounded

/-- Directed rational rounding with a supplied rational exponent. -/
@[inline] def directedRoundAtExponent (fmt : FloatFormat) (up sign : Bool) (num den : Nat)
    (exponent rationalExponent : Int) : Model fmt :=
  let precision := fmt.fracWidth
  if den == 0 then
    invalidResult fmt
  else if num == 0 then
    zero fmt sign
  else
    let totalExponent := rationalExponent + exponent
    if totalExponent > fmt.maxNormalExponent then
      directedOverflow fmt sign up
    else if totalExponent < fmt.minSubnormalExponent then
      if up then
        if sign then negMinSubnormal fmt else posMinSubnormal fmt
      else
        zero fmt sign
    else if totalExponent < fmt.minNormalExponent then
      let fraction :=
        roundDirectedScaled up num den (exponent + Int.ofNat (fmt.exponentBias + precision - 1))
      packRoundedSubnormal fmt sign (zero fmt sign) fraction
    else
      let rounded := roundDirectedScaled up num den (Int.ofNat precision - rationalExponent)
      packRoundedNormal fmt sign (directedOverflow fmt sign up) totalExponent rounded

/-- Rational rounding in any IEEE direction, reusing a supplied rational exponent. -/
@[inline] def roundAtExponent (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (num den : Nat) (exponent rationalExponent : Int) : Model fmt :=
  match mode with
  | .nearestEven =>
      if fmt.isIEEE then ieeeRoundAtExponent fmt sign num den exponent rationalExponent
      else generalRoundAtExponent fmt sign num den exponent rationalExponent
  | .towardZero => directedRoundAtExponent fmt false sign num den exponent rationalExponent
  | .towardPositiveInfinity =>
      directedRoundAtExponent fmt (!sign) sign num den exponent rationalExponent
  | .towardNegativeInfinity =>
      directedRoundAtExponent fmt sign sign num den exponent rationalExponent

/-- Round with one integer quotient, inlining the thresholds for fixed descriptors. -/
@[inline] def roundScaled (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (num den : Nat) (exponent : Int) : Model fmt :=
  roundAtExponent fmt mode sign num den exponent (RationalBinary.floorLog2 num den)

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteQuotientRound
