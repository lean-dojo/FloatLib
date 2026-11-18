/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rounding
public import FloatLib.Floats.Formats.Posit.Algebraic.Root.Runtime
public import FloatLib.Numerics.Order.Bisection.Runtime

/-!
# Exact comparison rounding for binary algebraic operations

A comparison oracle orders a nonnegative real target against exact rational candidates. Two
bounded searches locate its binade and a truncated significand with two extra bits. An exact
comparison with the half-integer then supplies Lean's accuracy certificate. The final rounding
discards that certificate once, and no floating-point approximation of the target is needed.

The search bounds come from the complete descriptor. Custom biases and finite encodings use
the descriptor-aware dyadic rounder with a representative of the same accuracy class.

The comparisons with powers of two go through `PowerBounds`: the target is first compared with
`1` and then with `2 ^ ±1`, `2 ^ ±2`, `2 ^ ±4`, … until two of these powers enclose it, and a
comparison with a power outside that enclosure is read off it. So the rational numbers
`2 ^ emin` and `2 ^ emax` are built only for a target that is itself near the end of the
exponent range, and the search works for layouts whose exponent field has 27 or 35 bits.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding

open Float.Model.UnpackedFloat

/-- Exact rational power of two, including negative exponents. -/
@[inline] def powerOfTwo (exponent : Int) : Rat :=
  (Numerics.Dyadic.mk false 1 exponent).toRat

/-- The lowest binade whose values can round to a nonzero encoding. -/
@[inline] def lowerExponent (fmt : FloatFormat) : Int := fmt.minSubnormalExponent - 1

/-- An exclusive upper bound above every finite magnitude. -/
@[inline] def upperExponent (fmt : FloatFormat) : Int := fmt.maxNormalExponent + 1

/-- Number of candidate exponent intervals. -/
@[inline] def exponentSpan (fmt : FloatFormat) : Nat :=
  (upperExponent fmt - lowerExponent fmt).toNat

/--
The first of `step`, `2 * step`, `4 * step`, … below `limit` that `hit` accepts, trying at most
`fuel` of them.
-/
def firstRung (hit : Nat → Bool) (limit : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, step =>
      if limit ≤ step then none
      else if hit step then some step
      else firstRung hit limit fuel (2 * step)

/-- Exponents whose powers of two a comparator has placed around its target. -/
structure PowerBounds where
  /-- An exponent `k` at which the comparator answered `.lt`: the target is below `2 ^ k`. -/
  above : Option Int
  /-- An exponent `k` at which the comparator answered `.gt`: the target is above `2 ^ k`. -/
  below : Option Int

/--
Powers of two around the target of `compare`, from a comparison with `1` and then with
`2 ^ 1`, `2 ^ 2`, `2 ^ 4`, … below `2 ^ upperExponent` and with `2 ^ (-1)`, `2 ^ (-2)`,
`2 ^ (-4)`, … above `2 ^ lowerExponent`, each until the comparator places the target on the near
side. A side on which no such power is found has no bound.
-/
def powerBounds (fmt : FloatFormat) (compare : Rat → Ordering) : PowerBounds :=
  let unit := compare (powerOfTwo 0)
  let up := (upperExponent fmt).toNat
  let down := (-lowerExponent fmt).toNat
  { above :=
      if unit = .lt then some 0
      else (firstRung (fun rung => decide (compare (powerOfTwo rung) = .lt)) up (up.log2 + 1) 1).map
        Int.ofNat
    below :=
      if unit = .gt then some 0
      else (firstRung (fun rung => decide (compare (powerOfTwo (-(rung : Int))) = .gt)) down
        (down.log2 + 1) 1).map fun (rung : Nat) => -(rung : Int) }

/--
The ordering of the target and `2 ^ exponent`: `.lt` at or beyond the upper bound, `.gt` at or
beyond the lower bound, and the comparator's answer between them. For an exact comparator this is
`compare (2 ^ exponent)` (`powerBounds_compare`), and the power is built only between the bounds.
-/
def PowerBounds.compare (bounds : PowerBounds) (compare : Rat → Ordering) (exponent : Int) :
    Ordering :=
  if bounds.above.any (fun rung => decide (rung ≤ exponent)) then .lt
  else if bounds.below.any (fun rung => decide (exponent ≤ rung)) then .gt
  else compare (powerOfTwo exponent)

/-- Locate the binade by exact comparisons with powers of two. -/
def binade (fmt : FloatFormat) (compare : Rat → Ordering) : Int :=
  let span := exponentSpan fmt
  let bounds := powerBounds fmt compare
  lowerExponent fmt + Numerics.bisect
    (fun index => decide (bounds.compare compare (lowerExponent fmt + index) ≠ .lt))
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
  Numerics.bisect (fun candidate => decide
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
Round a certificate once. Its exponent must be no greater than the target exponent. The
constructor above reserves two guard bits so that this holds throughout the finite search interval.
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
ties select signed zero. The upper cutoff uses the descriptor's overflow policy. Values just
below it still pass through the significand rounder, which handles overflow caused by carry.
The two cutoffs are compared through `powerBounds`; for an exact comparator they are the
comparisons with `2 ^ lowerExponent` and `2 ^ upperExponent` (`round_eq`).
-/
def round (fmt : FloatFormat) (sign : Bool) (compare : Rat → Ordering) : Model fmt :=
  let bounds := powerBounds fmt compare
  if bounds.compare compare (lowerExponent fmt) ≠ .gt then
    zero fmt sign
  else if bounds.compare compare (upperExponent fmt) ≠ .lt then
    nativeOverflow fmt sign
  else
    roundCertificate fmt sign (certificate fmt compare)

/-- Single-round evaluation of a nonnegative rational root. -/
@[inline] def root (fmt : FloatFormat) (sign : Bool) (radicand : Rat) (degree : Nat) :
    Model fmt :=
  round fmt sign (Posit.Model.RootRounding.compareRoot radicand degree)

end FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding
