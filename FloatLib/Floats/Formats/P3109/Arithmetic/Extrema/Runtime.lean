/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Mixed.Runtime

/-!
# P3109 comparisons and extrema

Comparisons are unordered at NaN. The ten extrema differ in NaN handling, magnitude ordering,
and preference for finite operands. Equal magnitudes use numerical order to resolve the sign:
minimum selects the negative operand, maximum the positive operand.

Reference: P3109 unapproved interim report 4.0.3, revision `34f5964`, §§4.11–4.12.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

/-- Strict extended-real comparison; NaN is unordered, including with itself. -/
def less : NumericalValue Rat → NumericalValue Rat → Bool
  | .exceptional _, _ | _, .exceptional _ => false
  | .infinity true, .infinity true | .infinity false, _ => false
  | .infinity true, _ | _, .infinity false => true
  | _, .infinity true => false
  | .finite left, .finite right => decide (left < right)

/-- Numerical equality, ignoring NaN payloads by making every NaN comparison false. -/
def equal : NumericalValue Rat → NumericalValue Rat → Bool
  | .finite left, .finite right => left == right
  | .infinity left, .infinity right => left == right
  | _, _ => false

/-- Non-strict extended-real comparison; NaN remains unordered. -/
def lessEqual (left right : NumericalValue Rat) : Bool :=
  less left right || equal left right

/-- Reverse strict comparison. -/
def greater (left right : NumericalValue Rat) : Bool := less right left

/-- Reverse non-strict comparison. -/
def greaterEqual (left right : NumericalValue Rat) : Bool := lessEqual right left

/-- Minimum, propagating either NaN operand. -/
def minimum : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | left, right => if less left right then left else right

/-- Maximum, propagating either NaN operand. -/
def maximum : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | left, right => if less left right then right else left

/-- Ignore a single NaN before applying an extremum; two NaNs yield the canonical NaN. -/
def numberVariant
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat) :
    NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, .exceptional _ => nan
  | .exceptional _, right => right
  | left, .exceptional _ => left
  | left, right => operation left right

/-- Minimum with a numerical operand preferred to NaN. -/
def minimumNumber : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat :=
  numberVariant minimum

/-- Maximum with a numerical operand preferred to NaN. -/
def maximumNumber : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat :=
  numberVariant maximum

/-- Minimum absolute value, resolving equal magnitudes toward the numerically smaller datum. -/
def minimumMagnitude : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | left, right =>
      if less (abs left) (abs right) then left
      else if less (abs right) (abs left) then right
      else minimum left right

/-- Maximum absolute value, resolving equal magnitudes toward the numerically larger datum. -/
def maximumMagnitude : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | left, right =>
      if less (abs left) (abs right) then right
      else if less (abs right) (abs left) then left
      else maximum left right

/-- Minimum magnitude with a numerical operand preferred to NaN. -/
def minimumMagnitudeNumber : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat :=
  numberVariant minimumMagnitude

/-- Maximum magnitude with a numerical operand preferred to NaN. -/
def maximumMagnitudeNumber : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat :=
  numberVariant maximumMagnitude

/-- Prefer the finite operand to an infinity, then use the supplied number extremum. -/
def finiteVariant
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat) :
    NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .finite left, .infinity _ => .finite left
  | .infinity _, .finite right => .finite right
  | left, right => operation left right

/-- Minimum finite variant: finite values outrank infinities, which outrank NaN. -/
def minimumFinite : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat :=
  finiteVariant minimumNumber

/-- Maximum finite variant: finite values outrank infinities, which outrank NaN. -/
def maximumFinite : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat :=
  finiteVariant maximumNumber

end FloatLib.Floats.Formats.P3109.Arithmetic

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format : Format}

/-- Strict comparison of decoded operands, with NaN unordered. -/
@[inline] def less (left right : ExecFloat.P3109 format) : Bool :=
  Arithmetic.less left.toClosedRat right.toClosedRat

/-- Non-strict comparison of decoded operands, with NaN unordered. -/
@[inline] def lessEqual (left right : ExecFloat.P3109 format) : Bool :=
  Arithmetic.lessEqual left.toClosedRat right.toClosedRat

/-- Numerical equality; NaN compares unequal to every operand. -/
@[inline] def equal (left right : ExecFloat.P3109 format) : Bool :=
  Arithmetic.equal left.toClosedRat right.toClosedRat

/-- Strict reverse comparison of decoded operands. -/
@[inline] def greater (left right : ExecFloat.P3109 format) : Bool :=
  Arithmetic.greater left.toClosedRat right.toClosedRat

/-- Non-strict reverse comparison of decoded operands. -/
@[inline] def greaterEqual (left right : ExecFloat.P3109 format) : Bool :=
  Arithmetic.greaterEqual left.toClosedRat right.toClosedRat

/-- Minimum with NaN propagation and the supplied final projection. -/
@[inline] def minimum (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  binaryTo format policy Arithmetic.minimum left right

/-- Maximum with NaN propagation and the supplied final projection. -/
@[inline] def maximum (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  binaryTo format policy Arithmetic.maximum left right

/-- Minimum with a numerical operand preferred to NaN. -/
@[inline] def minimumNumber (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  binaryTo format policy Arithmetic.minimumNumber left right

/-- Maximum with a numerical operand preferred to NaN. -/
@[inline] def maximumNumber (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  binaryTo format policy Arithmetic.maximumNumber left right

/-- Minimum magnitude, with negative sign preferred at a tie. -/
@[inline] def minimumMagnitude (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  binaryTo format policy Arithmetic.minimumMagnitude left right

/-- Maximum magnitude, with positive sign preferred at a tie. -/
@[inline] def maximumMagnitude (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  binaryTo format policy Arithmetic.maximumMagnitude left right

/-- Minimum magnitude with a numerical operand preferred to NaN. -/
@[inline] def minimumMagnitudeNumber (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  binaryTo format policy Arithmetic.minimumMagnitudeNumber left right

/-- Maximum magnitude with a numerical operand preferred to NaN. -/
@[inline] def maximumMagnitudeNumber (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  binaryTo format policy Arithmetic.maximumMagnitudeNumber left right

/-- Minimum preferring finite values to infinity and infinity to NaN. -/
@[inline] def minimumFinite (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  binaryTo format policy Arithmetic.minimumFinite left right

/-- Maximum preferring finite values to infinity and infinity to NaN. -/
@[inline] def maximumFinite (left right : ExecFloat.P3109 format)
    (policy : ProjectionPolicy := .nearestEven) : ExecFloat.P3109 format :=
  binaryTo format policy Arithmetic.maximumFinite left right

end FloatLib.Floats.ExecFloat.P3109
