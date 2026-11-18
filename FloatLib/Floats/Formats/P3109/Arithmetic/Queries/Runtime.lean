/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Runtime

/-!
# P3109 queries and adjacent values

Format queries give you the descriptor and its distinguished encoded values. Classification and
adjacent-value operations look at the code itself, so their cost doesn't depend on the decoded
exponent. Two cases are worth knowing. `maxSubnormalOf` returns NaN at precision one, where there
are no subnormals. And `nextGreaterThan` maps positive infinity to NaN, as `nextLessThan` does
negative infinity, which differs on purpose from IEEE `nextUp` and `nextDown`.

Reference: P3109 unapproved interim report v4.1 (14 September 2026),
revision `2d45cf2`, §§4.13–4.16.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.Format

/-- Total encoded width, as queried by §4.14.

P3109 interim report v4.1 (14 September 2026), §4.14; unapproved draft.
-/
@[inline] def BitwidthOf (format : Format) : Nat := format.bitWidth

/-- Precision including the implicit leading bit.

P3109 interim report v4.1 (14 September 2026), §4.14; unapproved draft.
-/
@[inline] def PrecisionOf (format : Format) : Nat := format.precision

/-- Whether negative finite values are represented.

P3109 interim report v4.1 (14 September 2026), §4.14; unapproved draft.
-/
@[inline] def SignednessOf (format : Format) : Signedness := format.signedness

/-- Whether infinities are represented.

P3109 interim report v4.1 (14 September 2026), §4.14; unapproved draft.
-/
@[inline] def DomainOf (format : Format) : Domain := format.domain

/-- Width of the biased exponent.

P3109 interim report v4.1 (14 September 2026), §4.14; unapproved draft.
-/
@[inline] def ExponentBitwidthOf (format : Format) : Nat := format.exponentBits

/-- Width of the trailing significand field.

P3109 interim report v4.1 (14 September 2026), §4.14; unapproved draft.
-/
@[inline] def TrailingSignificandBitwidthOf (format : Format) : Nat := format.trailingBits

/-- Bias subtracted from nonzero encoded exponents.

P3109 interim report v4.1 (14 September 2026), §4.14; unapproved draft.
-/
@[inline] def ExponentBiasOf (format : Format) : Nat := format.exponentBias

/-- Largest finite value as a value of the queried format.

P3109 interim report v4.1 (14 September 2026), §4.14; unapproved draft.
-/
@[inline] def MaxFiniteOf (format : Format) : ExecFloat.P3109 format :=
  ExecFloat.P3109.ofNatBits format.maxFiniteBits

/-- Smallest finite value, which is zero for unsigned formats.

P3109 interim report v4.1 (14 September 2026), §4.14; unapproved draft.
-/
@[inline] def MinFiniteOf (format : Format) : ExecFloat.P3109 format :=
  ExecFloat.P3109.ofNatBits
    (if format.signedness == .signed then format.signBoundary + format.maxFiniteBits else 0)

/-- Least strictly positive value.

P3109 interim report v4.1 (14 September 2026), §4.14; unapproved draft.
-/
@[inline] def MinPositiveOf (format : Format) : ExecFloat.P3109 format :=
  ExecFloat.P3109.ofNatBits 1

/-- Largest positive subnormal, or NaN when precision one leaves no subnormal values.

P3109 interim report v4.1 (14 September 2026), §4.14; unapproved draft.
-/
@[inline] def MaxSubnormalOf (format : Format) : ExecFloat.P3109 format :=
  if format.precision == 1 then ExecFloat.P3109.nan
  else ExecFloat.P3109.ofNatBits (2 ^ format.trailingBits - 1)

/-- Least positive normal value.

P3109 interim report v4.1 (14 September 2026), §4.14; unapproved draft.
-/
@[inline] def MinNormalOf (format : Format) : ExecFloat.P3109 format :=
  ExecFloat.P3109.ofNatBits (2 ^ format.trailingBits)

end FloatLib.Floats.Formats.P3109.Format

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format : Format}

/-- The format's unique zero has code zero.

P3109 interim report v4.1 (14 September 2026), §4.13; unapproved draft.
-/
@[inline] def IsZero (value : ExecFloat.P3109 format) : Bool :=
  value.toNatBits == 0

/-- Test the unique NaN code.

P3109 interim report v4.1 (14 September 2026), §4.13; unapproved draft.
-/
@[inline] def IsNaN (value : ExecFloat.P3109 format) : Bool :=
  value.toNatBits == format.nanBits

/-- Test either infinity, respecting signedness and the finite/extended domain.

P3109 interim report v4.1 (14 September 2026), §4.13; unapproved draft.
-/
@[inline] def IsInfinite (value : ExecFloat.P3109 format) : Bool :=
  format.domain == .extended &&
    (value.toNatBits == format.positiveInfinityBits ||
      (format.signedness == .signed && value.toNatBits == format.negativeInfinityBits))

/-- Finite excludes NaN and either infinity.

P3109 interim report v4.1 (14 September 2026), §4.13; unapproved draft.
-/
@[inline] def IsFinite (value : ExecFloat.P3109 format) : Bool :=
  !(value.IsNaN || value.IsInfinite)

/-- Negative finite values and negative infinity have negative sign, and NaN and zero do not.

P3109 interim report v4.1 (14 September 2026), §4.13; unapproved draft.
-/
@[inline] def IsSignMinus (value : ExecFloat.P3109 format) : Bool :=
  format.signedness == .signed && decide (format.signBoundary < value.toNatBits)

/-- Unsigned magnitude code, removing the sign partition in signed formats. -/
@[inline] def magnitudeBits (value : ExecFloat.P3109 format) : Nat :=
  if format.signedness == .signed && decide (format.signBoundary ≤ value.toNatBits) then
    value.toNatBits - format.signBoundary
  else value.toNatBits

/-- Test exact numerical equality to one without constructing a large rational.

P3109 interim report v4.1 (14 September 2026), §4.13; unapproved draft.
-/
@[inline] def IsOne (value : ExecFloat.P3109 format) : Bool :=
  match value.decode with
  | .finite exact =>
      FloatLib.Numerics.Dyadic.Internal.compareScalable exact
        { negative := false, significand := 1, exponent := 0 } == .eq
  | _ => false

/-- Normal values are finite and have a nonzero biased exponent in their magnitude code.

P3109 interim report v4.1 (14 September 2026), §4.13; unapproved draft.
-/
@[inline] def IsNormal (value : ExecFloat.P3109 format) : Bool :=
  value.IsFinite && decide (2 ^ format.trailingBits ≤ value.magnitudeBits)

/-- Nonzero finite values below the normal range.

P3109 interim report v4.1 (14 September 2026), §4.13; unapproved draft.
-/
@[inline] def IsSubnormal (value : ExecFloat.P3109 format) : Bool :=
  value.IsFinite && decide (0 < value.magnitudeBits) &&
    decide (value.magnitudeBits < 2 ^ format.trailingBits)

/-- Least greater value, or NaN when there is no greater datum.

P3109 interim report v4.1 (14 September 2026), §4.16; unapproved draft.
-/
@[inline] def NextGreaterThan (value : ExecFloat.P3109 format) : ExecFloat.P3109 format :=
  if value.IsNaN then nan
  else if value.IsSignMinus then
    if value.toNatBits == format.signBoundary + 1 then zero
    else ofNatBits (value.toNatBits - 1)
  else if value.toNatBits == format.positiveInfinityBits then nan
  else ofNatBits (value.toNatBits + 1)

/-- Greatest lesser value, or NaN when there is no lesser datum.

P3109 interim report v4.1 (14 September 2026), §4.16; unapproved draft.
-/
@[inline] def NextLessThan (value : ExecFloat.P3109 format) : ExecFloat.P3109 format :=
  if value.IsNaN then nan
  else if value.IsZero then
    if format.signedness == .signed then ofNatBits (format.signBoundary + 1) else nan
  else if value.IsSignMinus then
    if value.toNatBits == format.negativeInfinityBits then nan
    else ofNatBits (value.toNatBits + 1)
  else ofNatBits (value.toNatBits - 1)

end FloatLib.Floats.ExecFloat.P3109
