/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Runtime

/-!
# P3109 queries and adjacent values

Format queries expose the descriptor and its distinguished encoded values. Classification and
adjacent-value operations inspect codes directly, so their cost does not depend on the decoded
exponent. `maxSubnormalOf` returns NaN at precision one. `nextGreaterThan` maps positive infinity
to NaN, and `nextLessThan` maps negative infinity to NaN: these are deliberately different from
IEEE `nextUp` and `nextDown`.

Reference: P3109 unapproved interim report 4.0.3, revision `34f5964`, §§4.13–4.16.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.Format

/-- Total encoded width, as queried by §4.14. -/
@[inline] def bitwidthOf (format : Format) : Nat := format.bitWidth

/-- Precision including the implicit leading bit. -/
@[inline] def precisionOf (format : Format) : Nat := format.precision

/-- Whether negative finite values are represented. -/
@[inline] def signednessOf (format : Format) : Signedness := format.signedness

/-- Whether infinities are represented. -/
@[inline] def domainOf (format : Format) : Domain := format.domain

/-- Width of the biased exponent. -/
@[inline] def exponentBitwidthOf (format : Format) : Nat := format.exponentBits

/-- Width of the trailing significand field. -/
@[inline] def trailingSignificandBitwidthOf (format : Format) : Nat := format.trailingBits

/-- Bias subtracted from nonzero encoded exponents. -/
@[inline] def exponentBiasOf (format : Format) : Nat := format.exponentBias

/-- Largest finite value as a value of the queried format. -/
@[inline] def maxFiniteOf (format : Format) : ExecFloat.P3109 format :=
  ExecFloat.P3109.ofNatBits format.maxFiniteBits

/-- Smallest finite value; unsigned formats return zero. -/
@[inline] def minFiniteOf (format : Format) : ExecFloat.P3109 format :=
  ExecFloat.P3109.ofNatBits
    (if format.signedness == .signed then format.signBoundary + format.maxFiniteBits else 0)

/-- Least strictly positive value. -/
@[inline] def minPositiveOf (format : Format) : ExecFloat.P3109 format :=
  ExecFloat.P3109.ofNatBits 1

/-- Largest positive subnormal, or NaN when precision one leaves no subnormal values. -/
@[inline] def maxSubnormalOf (format : Format) : ExecFloat.P3109 format :=
  if format.precision == 1 then ExecFloat.P3109.nan
  else ExecFloat.P3109.ofNatBits (2 ^ format.trailingBits - 1)

/-- Least positive normal value. -/
@[inline] def minNormalOf (format : Format) : ExecFloat.P3109 format :=
  ExecFloat.P3109.ofNatBits (2 ^ format.trailingBits)

end FloatLib.Floats.Formats.P3109.Format

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format : Format}

/-- The format's unique zero has code zero. -/
@[inline] def isZero (value : ExecFloat.P3109 format) : Bool :=
  value.toNatBits == 0

/-- Test the unique NaN code. -/
@[inline] def isNaN (value : ExecFloat.P3109 format) : Bool :=
  value.toNatBits == format.nanBits

/-- Test either infinity, respecting signedness and the finite/extended domain. -/
@[inline] def isInfinite (value : ExecFloat.P3109 format) : Bool :=
  format.domain == .extended &&
    (value.toNatBits == format.positiveInfinityBits ||
      (format.signedness == .signed && value.toNatBits == format.negativeInfinityBits))

/-- Finite excludes NaN and either infinity. -/
@[inline] def isFinite (value : ExecFloat.P3109 format) : Bool :=
  !(value.isNaN || value.isInfinite)

/-- Negative finite values and negative infinity have negative sign; NaN and zero do not. -/
@[inline] def isSignMinus (value : ExecFloat.P3109 format) : Bool :=
  format.signedness == .signed && decide (format.signBoundary < value.toNatBits)

/-- Unsigned magnitude code, removing the sign partition in signed formats. -/
@[inline] def magnitudeBits (value : ExecFloat.P3109 format) : Nat :=
  if format.signedness == .signed && decide (format.signBoundary ≤ value.toNatBits) then
    value.toNatBits - format.signBoundary
  else value.toNatBits

/-- Test exact numerical equality to one without constructing a large rational. -/
@[inline] def isOne (value : ExecFloat.P3109 format) : Bool :=
  match value.decode with
  | .finite exact =>
      FloatLib.Numerics.Dyadic.Internal.compareScalable exact
        { negative := false, significand := 1, exponent := 0 } == .eq
  | _ => false

/-- Normal values are finite and have a nonzero biased exponent in their magnitude code. -/
@[inline] def isNormal (value : ExecFloat.P3109 format) : Bool :=
  value.isFinite && decide (2 ^ format.trailingBits ≤ value.magnitudeBits)

/-- Nonzero finite values below the normal range. -/
@[inline] def isSubnormal (value : ExecFloat.P3109 format) : Bool :=
  value.isFinite && decide (0 < value.magnitudeBits) &&
    decide (value.magnitudeBits < 2 ^ format.trailingBits)

/-- Least greater value, or NaN when there is no greater datum. -/
@[inline] def nextGreaterThan (value : ExecFloat.P3109 format) : ExecFloat.P3109 format :=
  if value.isNaN then nan
  else if value.isSignMinus then
    if value.toNatBits == format.signBoundary + 1 then zero
    else ofNatBits (value.toNatBits - 1)
  else if value.toNatBits == format.positiveInfinityBits then nan
  else ofNatBits (value.toNatBits + 1)

/-- Greatest lesser value, or NaN when there is no lesser datum. -/
@[inline] def nextLessThan (value : ExecFloat.P3109 format) : ExecFloat.P3109 format :=
  if value.isNaN then nan
  else if value.isZero then
    if format.signedness == .signed then ofNatBits (format.signBoundary + 1) else nan
  else if value.isSignMinus then
    if value.toNatBits == format.negativeInfinityBits then nan
    else ofNatBits (value.toNatBits + 1)
  else ofNatBits (value.toNatBits - 1)

end FloatLib.Floats.ExecFloat.P3109
