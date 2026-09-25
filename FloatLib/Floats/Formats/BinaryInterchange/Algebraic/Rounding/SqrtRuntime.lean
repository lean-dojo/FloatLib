/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.Runtime
public import FloatLib.Kernels.IntegerRoot.Runtime
public import FloatLib.Numerics.Exact.RationalBinary

/-!
# Integer-root certificates for rational radicands

The binary logarithm of the exact radicand locates the root's binade without searching the
descriptor's exponent range. After target scaling, the proved integer-root kernel supplies the
significand. Scaling is shared with the exact fractional classification, and the binade is reused
when constructing the final certificate. Degree zero retains the total comparison specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding

open Float.Model.UnpackedFloat

/-- Exact ratio after scaling a degree-`degree` root by `2 ^ (-exponent)`. -/
@[inline] def rootScale (radicand : Rat) (degree : Nat) (exponent : Int) : Nat × Nat :=
  Numerics.RationalBinary.scaleByPowerOfTwo radicand.num.natAbs radicand.den
    (-(exponent * (degree : Int)))

/-- Integer part of the square root after exact target scaling. -/
def sqrtMantissa (radicand : Rat) (exponent : Int) : Nat :=
  let scaled := rootScale radicand 2 exponent
  Numerics.FixedWord.IntegerSquareRoot.sqrtNat (scaled.1 / scaled.2)

/-- Floor binary logarithm of a positive root, using Euclidean division for negative exponents. -/
@[inline] def rootBinade (radicand : Rat) (degree : Nat) : Int :=
  Numerics.RationalBinary.floorLog2 radicand.num.natAbs radicand.den / (degree : Int)

/-- Exact integer part of a scaled root; degree zero retains the comparison specification. -/
@[specialize fmt] def rootMantissa
    (fmt : FloatFormat) (radicand : Rat) (degree : Nat) (exponent : Int) :
    Nat :=
  if degree = 0 then
    truncatedMantissa fmt (Posit.Model.RootRounding.compareRoot radicand degree) exponent
  else
    let scaled := rootScale radicand degree exponent
    Numerics.IntegerRoot.root degree (scaled.1 / scaled.2)

/-- Classify the root's fractional part using its already scaled numerator and denominator. -/
@[inline] def scaledRootAccuracy (numerator denominator degree mantissa : Nat) : Accuracy :=
  if numerator = mantissa ^ degree * denominator then .exact
  else .inexact (cmp (numerator <<< degree) ((2 * mantissa + 1) ^ degree * denominator))

/-- Integer cross-products classify the exact root against an integer and its midpoint. -/
def rootAccuracy (radicand : Rat) (degree : Nat) (exponent : Int) (mantissa : Nat) : Accuracy :=
  let scaled := rootScale radicand degree exponent
  scaledRootAccuracy scaled.1 scaled.2 degree mantissa

/-- Build an integer-root certificate at a known exponent, sharing the exact scaled ratio. -/
@[specialize fmt] def rootCertificateAt
    (fmt : FloatFormat) (radicand : Rat) (degree : Nat) (exponent : Int) : Certificate :=
  let scaled := rootScale radicand degree exponent
  let mantissa :=
    if degree = 0 then
      truncatedMantissa fmt (Posit.Model.RootRounding.compareRoot radicand degree) exponent
    else Numerics.IntegerRoot.root degree (scaled.1 / scaled.2)
  ⟨mantissa, exponent, scaledRootAccuracy scaled.1 scaled.2 degree mantissa⟩

/-- Build the same accuracy certificate using integer roots and the radicand's binary logarithm. -/
@[specialize fmt] def rootCertificate
    (fmt : FloatFormat) (radicand : Rat) (degree : Nat) : Certificate :=
  let exponent := certificateExponent fmt (rootBinade radicand degree)
  rootCertificateAt fmt radicand degree exponent

/-- The degree-two specialization of the integer-root certificate. -/
@[inline] def sqrtCertificate (fmt : FloatFormat) (radicand : Rat) : Certificate :=
  rootCertificate fmt radicand 2

/--
Single-round rational root using integer binade classification and exact integer roots.

Only the exact underflow midpoint needs a power comparison at a descriptor boundary. Degree
zero and nonpositive radicands retain the reference oracle's total behavior.
-/
@[specialize fmt] def rootRat
    (fmt : FloatFormat) (sign : Bool) (radicand : Rat) (degree : Nat) : Model fmt :=
  if degree = 0 ∨ radicand ≤ 0 then root fmt sign radicand degree
  else
    let binade := rootBinade radicand degree
    if binade < lowerExponent fmt then zero fmt sign
    else if upperExponent fmt ≤ binade then nativeOverflow fmt sign
    else if binade = lowerExponent fmt ∧
        Posit.Model.RootRounding.compareRoot radicand degree (powerOfTwo binade) = .eq then
      zero fmt sign
    else
      roundCertificate fmt sign
        (rootCertificateAt fmt radicand degree (certificateExponent fmt binade))

/-- Single-round rational square root without exponent or significand comparison searches. -/
@[inline] def sqrtRat (fmt : FloatFormat) (sign : Bool) (radicand : Rat) : Model fmt :=
  rootRat fmt sign radicand 2

/-- Use integer square root at degree two and proved integer Newton iteration otherwise. -/
@[inline] def rootWithSqrt (fmt : FloatFormat) (sign : Bool) (radicand : Rat) (degree : Nat) :
    Model fmt :=
  rootRat fmt sign radicand degree

end FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding
