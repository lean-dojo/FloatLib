/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rounding
public import FloatLib.Floats.Formats.Posit.Algebraic.Root.Runtime

/-!
# Exact comparison rounding for binary algebraic operations

A comparison oracle orders a nonnegative real target against exact rational candidates. Two
bounded searches locate its binade and a truncated significand with two extra bits. An exact
comparison with the half-integer then supplies Lean's accuracy certificate. The final rounding
discards that certificate once; no floating-point approximation of the target is needed.

The search bounds come from the complete descriptor. Custom biases and finite encodings use
the descriptor-aware dyadic rounder with a representative of the same accuracy class.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding

open Float.Model.UnpackedFloat

/-- Exact rational power of two, including negative exponents. -/
@[inline] def powerOfTwo (exponent : Int) : Rat :=
  (Numerics.Dyadic.mk false 1 exponent).toRat

/-- Reuse the total bounded integer search shared by exact posit operations. -/
abbrev bisect := Posit.Model.lowerCodeByBisection

/-- The lowest binade whose values can round to a nonzero encoding. -/
@[inline] def lowerExponent (fmt : FloatFormat) : Int := fmt.minSubnormalExponent - 1

/-- An exclusive upper bound above every finite magnitude. -/
@[inline] def upperExponent (fmt : FloatFormat) : Int := fmt.maxNormalExponent + 1

/-- Number of candidate exponent intervals. -/
@[inline] def exponentSpan (fmt : FloatFormat) : Nat :=
  (upperExponent fmt - lowerExponent fmt).toNat

/-- Locate the binade by exact comparisons with powers of two. -/
def binade (fmt : FloatFormat) (compare : Rat → Ordering) : Int :=
  let span := exponentSpan fmt
  lowerExponent fmt + bisect
    (fun index => decide (compare (powerOfTwo (lowerExponent fmt + index)) ≠ .lt))
    (span.log2 + 1) 0 span

/-- Keep two bits below the final normal or subnormal rounding position. -/
@[inline] def certificateExponent (fmt : FloatFormat) (binade : Int) : Int :=
  max (fmt.minSubnormalExponent - 2) (binade - (fmt.fracWidth : Int) - 2)

/-- A truncated positive magnitude and the exact location of its discarded fraction. -/
structure Certificate where
  /-- Integer part of the magnitude after scaling by `2 ^ (-exponent)`. -/
  mantissa : Nat
  /-- Power of two represented by one unit of the mantissa. -/
  exponent : Int
  /-- Whether the discarded fraction is zero, below a half, a half, or above a half. -/
  accuracy : Accuracy

/-- Integer part of a scaled magnitude, found by exact comparisons. -/
def truncatedMantissa (fmt : FloatFormat) (compare : Rat → Ordering) (exponent : Int) :
    Nat :=
  let bits := fmt.fracWidth + 3
  bisect (fun candidate => decide
    (compare ((candidate : Rat) * powerOfTwo exponent) ≠ .lt)) bits 0 (2 ^ bits)

/-- Exact fractional classification after finding the integer part. -/
def accuracyAt (compare : Rat → Ordering) (mantissa : Nat) : Accuracy :=
  if compare mantissa = .eq then .exact
  else .inexact (compare ((mantissa : Rat) + 1 / 2))

/-- Build a certificate with a search bounded by the descriptor's precision. -/
def certificate (fmt : FloatFormat) (compare : Rat → Ordering) : Certificate :=
  let exponent := certificateExponent fmt (binade fmt compare)
  let scaledCompare := fun candidate => compare (candidate * powerOfTwo exponent)
  let mantissa := truncatedMantissa fmt compare exponent
  ⟨mantissa, exponent, accuracyAt scaledCompare mantissa⟩

/-- A quarter-integer in the same accuracy class as a certificate's real mantissa. -/
@[inline] def accuracyQuarter : Accuracy → Nat
  | .exact => 0
  | .inexact .lt => 1
  | .inexact .eq => 2
  | .inexact .gt => 3

/--
Round a certificate once. Its exponent must be no greater than the target exponent; the
constructor above reserves two guard bits to ensure this throughout the finite search interval.
-/
@[inline] def roundCertificate (fmt : FloatFormat) (sign : Bool) (c : Certificate) :
    Model fmt :=
  if fmt.isIEEE then
    ofModel fmt (roundWithAccuracy (FloatFormat.toModel fmt) (modelSign sign)
      c.mantissa c.exponent c.accuracy)
  else
    roundDyadic fmt ⟨sign, 4 * c.mantissa + accuracyQuarter c.accuracy, c.exponent - 2⟩

/--
Total nearest-even rounding of a signed magnitude given an exact comparison oracle.

The oracle's contract is comparison with a nonnegative real. At half the least subnormal,
ties select signed zero. The upper cutoff uses the descriptor's overflow policy; values just
below it still pass through the significand rounder, which handles overflow caused by carry.
-/
def round (fmt : FloatFormat) (sign : Bool) (compare : Rat → Ordering) : Model fmt :=
  if compare (powerOfTwo (lowerExponent fmt)) ≠ .gt then
    zero fmt sign
  else if compare (powerOfTwo (upperExponent fmt)) ≠ .lt then
    nativeOverflow fmt sign
  else
    roundCertificate fmt sign (certificate fmt compare)

/-- Single-round evaluation of a nonnegative rational root. -/
@[inline] def root (fmt : FloatFormat) (sign : Bool) (radicand : Rat) (degree : Nat) :
    Model fmt :=
  round fmt sign (Posit.Model.RootRounding.compareRoot radicand degree)

end FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding
