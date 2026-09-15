/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime

/-!
# Executable rational-free exact posit quotient rounding

Finite posit operands are dyadic, but their quotient need not be. Correct rounding still requires
no rational normalization and no materialized quotient. For a positive denominator `d`,

`candidate ≤ numerator / d` exactly when `candidate * d ≤ numerator`.

This module drives the standard logarithmic code search and every underflow, threshold,
saturation, and tie decision with exact dyadic products. Refinement to rational division is proved
in `Quotient.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DyadicQuotient

open FloatLib.Numerics

/--
Greatest nonnegative posit code whose decoded value does not exceed an exact positive quotient.

The quotient itself is never constructed. Multiplying each candidate by the positive denominator
turns the comparison into a closed exact-dyadic operation.
-/
@[inline] def lowerCode
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) : Nat :=
  Model.lowerCodeByBisection
    (fun code =>
      let value := DyadicRounding.nonnegativeDyadicAt format code
      (value.mul denominator).isLessOrEqual numerator)
    format.bits 0 format.signMaskNat

/-- Round from a known greatest lower quotient code. -/
@[inline] def roundFromLowerCode
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic)
    (lower : Nat) : Nat :=
  let upper := lower + 1
  if upper < format.signMaskNat then
    let thresholdTimesDenominator :=
      (DyadicRounding.roundingThreshold format lower).mul denominator
    if numerator.isLess thresholdTimesDenominator then
      lower
    else if thresholdTimesDenominator.isLess numerator then
      upper
    else if lower % 2 = 0 then
      lower
    else
      upper
  else
    lower

/--
Round a positive exact-dyadic quotient to a nonnegative posit code.

The total guard returns zero unless both carriers have the positive-magnitude shape established
by the arithmetic caller. No division is executed: each comparison cross-multiplies by the
denominator.
-/
@[inline] def roundPositiveCode
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) : Nat :=
  if numerator.significand == 0 || numerator.negative ||
      denominator.significand == 0 || denominator.negative then
    0
  else
    let minPosTimesDenominator :=
      (DyadicRounding.minPositive format).mul denominator
    if numerator.isLess minPosTimesDenominator then
      1
    else
      let lower := lowerCode format numerator denominator
      roundFromLowerCode format numerator denominator lower

/-- Pack the code chosen by exact cross-multiplied quotient rounding. -/
@[inline] def roundPositive
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) :
    Model format :=
  Model.ofNatBits (roundPositiveCode format numerator denominator)

/--
Apply the exceptional-value and sign policy shared by exact quotient kernels.

The caller supplies only the positive-magnitude rounder. Inlining this shell keeps the
cross-multiplied and direct-prefix kernels specialized while giving both implementations one
definition of division by zero, zero numerators, magnitude extraction, and sign restoration.
-/
@[always_inline, inline] def roundSignedWith
    (format : Format)
    (roundMagnitude :
      FloatLib.Numerics.Dyadic → FloatLib.Numerics.Dyadic → Model format)
    (numerator denominator : FloatLib.Numerics.Dyadic) :
    Model format :=
  if denominator.significand == 0 then
    Model.nar format
  else if numerator.significand == 0 then
    Model.zero format
  else
    let numeratorMagnitude := DyadicRounding.magnitude numerator
    let denominatorMagnitude := DyadicRounding.magnitude denominator
    let result := roundMagnitude numeratorMagnitude denominatorMagnitude
    if Bool.xor numerator.negative denominator.negative then
      Model.neg result
    else
      result

/--
Round the quotient of two arbitrary signed dyadics without constructing the quotient.

A zero denominator produces NaR. With a nonzero denominator, a zero numerator produces the unique
posit zero. Otherwise the positive magnitudes use cross-multiplied rounding and the result sign
is restored by whole-word posit negation.
-/
@[inline] def round
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) :
    Model format :=
  roundSignedWith format (roundPositive format) numerator denominator

end FloatLib.Floats.Formats.Posit.Model.DyadicQuotient
