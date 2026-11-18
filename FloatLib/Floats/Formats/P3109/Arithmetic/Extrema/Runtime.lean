/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Mixed.Runtime

/-!
# P3109 comparisons and extrema

Comparisons are unordered at NaN, and since `compare` is the order behind `==` on P3109 values,
NaN compares unequal to itself. There are ten extrema. They differ in how they treat NaN, whether
they order by magnitude, and whether they prefer finite operands. When two magnitudes are equal,
numerical order settles the sign, so of `-2` and `2` the minimum by magnitude is `-2` and the
maximum is `2`.

Reference: P3109 unapproved interim report v4.1 (14 September 2026),
revision `2d45cf2`, §§4.11–4.12.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

/-- Strict extended-real comparison, with NaN unordered even against itself.

P3109 interim report v4.1 (14 September 2026), §4.12; unapproved draft.
-/
def CompareLess : NumericalValue Rat → NumericalValue Rat → Bool
  | .exceptional _, _ | _, .exceptional _ => false
  | .infinity true, .infinity true | .infinity false, _ => false
  | .infinity true, _ | _, .infinity false => true
  | _, .infinity true => false
  | .finite left, .finite right => decide (left < right)

/-- Numerical equality, ignoring NaN payloads by making every NaN comparison false.

P3109 interim report v4.1 (14 September 2026), §4.12; unapproved draft.
-/
def CompareEqual : NumericalValue Rat → NumericalValue Rat → Bool
  | .finite left, .finite right => left == right
  | .infinity left, .infinity right => left == right
  | _, _ => false

/-- Non-strict extended-real comparison, with NaN unordered.

P3109 interim report v4.1 (14 September 2026), §4.12; unapproved draft.
-/
def CompareLessEqual (left right : NumericalValue Rat) : Bool :=
  CompareLess left right || CompareEqual left right

/-- Reverse strict comparison.

P3109 interim report v4.1 (14 September 2026), §4.12; unapproved draft.
-/
def CompareGreater (left right : NumericalValue Rat) : Bool := CompareLess right left

/-- Reverse non-strict comparison.

P3109 interim report v4.1 (14 September 2026), §4.12; unapproved draft.
-/
def CompareGreaterEqual (left right : NumericalValue Rat) : Bool := CompareLessEqual right left

/-- Minimum, propagating either NaN operand.

P3109 interim report v4.1 (14 September 2026), §4.11.1; unapproved draft.
-/
def Minimum : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | left, right => if CompareLess left right then left else right

/-- Maximum, propagating either NaN operand.

P3109 interim report v4.1 (14 September 2026), §4.11.1; unapproved draft.
-/
def Maximum : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | left, right => if CompareLess left right then right else left

/-- Ignore a single NaN before applying an extremum. Two NaNs give the canonical NaN. -/
def numberVariant
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat) :
    NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, .exceptional _ => nan
  | .exceptional _, right => right
  | left, .exceptional _ => left
  | left, right => operation left right

/-- Minimum with a numerical operand preferred to NaN.

P3109 interim report v4.1 (14 September 2026), §4.11.1; unapproved draft.
-/
def MinimumNumber : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat :=
  numberVariant Minimum

/-- Maximum with a numerical operand preferred to NaN.

P3109 interim report v4.1 (14 September 2026), §4.11.1; unapproved draft.
-/
def MaximumNumber : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat :=
  numberVariant Maximum

/-- Minimum absolute value, resolving equal magnitudes toward the numerically smaller datum.

P3109 interim report v4.1 (14 September 2026), §4.11.2; unapproved draft.
-/
def MinimumMagnitude : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | left, right =>
      if CompareLess (Abs left) (Abs right) then left
      else if CompareLess (Abs right) (Abs left) then right
      else Minimum left right

/-- Maximum absolute value, resolving equal magnitudes toward the numerically larger datum.

P3109 interim report v4.1 (14 September 2026), §4.11.2; unapproved draft.
-/
def MaximumMagnitude : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .exceptional _, _ | _, .exceptional _ => nan
  | left, right =>
      if CompareLess (Abs left) (Abs right) then right
      else if CompareLess (Abs right) (Abs left) then left
      else Maximum left right

/-- Minimum magnitude with a numerical operand preferred to NaN.

P3109 interim report v4.1 (14 September 2026), §4.11.2; unapproved draft.
-/
def MinimumMagnitudeNumber : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat :=
  numberVariant MinimumMagnitude

/-- Maximum magnitude with a numerical operand preferred to NaN.

P3109 interim report v4.1 (14 September 2026), §4.11.2; unapproved draft.
-/
def MaximumMagnitudeNumber : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat :=
  numberVariant MaximumMagnitude

/-- Prefer the finite operand to an infinity, then use the supplied number extremum. -/
def finiteVariant
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat) :
    NumericalValue Rat → NumericalValue Rat → NumericalValue Rat
  | .finite left, .infinity _ => .finite left
  | .infinity _, .finite right => .finite right
  | left, right => operation left right

/-- Minimum finite variant: finite values outrank infinities, which outrank NaN.

P3109 interim report v4.1 (14 September 2026), §4.11.3; unapproved draft.
-/
def MinimumFinite : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat :=
  finiteVariant MinimumNumber

/-- Maximum finite variant: finite values outrank infinities, which outrank NaN.

P3109 interim report v4.1 (14 September 2026), §4.11.3; unapproved draft.
-/
def MaximumFinite : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat :=
  finiteVariant MaximumNumber

/-- Report §4.11.4 clamp, propagating NaN and rejecting reversed bounds.

P3109 interim report v4.1 (14 September 2026), §4.11.4; unapproved draft.
-/
def Clamp (value lower upper : NumericalValue Rat) : NumericalValue Rat :=
  if CompareGreater lower upper then nan else Minimum (Maximum value lower) upper

end FloatLib.Floats.Formats.P3109.Arithmetic

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format rightFormat thirdFormat : Format}

/--
Clamp `value` to `[lower, upper]` with exact bound checks, then project once into `target`, by
default the format of `value`. Reversed bounds and NaN yield NaN.

P3109 interim report v4.1 (14 September 2026), §4.11.4; unapproved draft.
-/
@[inline] def Clamp (value : ExecFloat.P3109 format) (lower : ExecFloat.P3109 rightFormat)
    (upper : ExecFloat.P3109 thirdFormat) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  ternary Arithmetic.Clamp value lower upper target mode saturation

/-- Strict comparison of decoded operands, with NaN unordered.

P3109 interim report v4.1 (14 September 2026), §4.12; unapproved draft.
-/
@[inline] def CompareLess (left : ExecFloat.P3109 format) (right : ExecFloat.P3109 rightFormat)
    : Bool :=
  Arithmetic.CompareLess left.toClosedRat right.toClosedRat

/-- Non-strict comparison of decoded operands, with NaN unordered.

P3109 interim report v4.1 (14 September 2026), §4.12; unapproved draft.
-/
@[inline] def CompareLessEqual (left : ExecFloat.P3109 format) (right : ExecFloat.P3109
    rightFormat) : Bool :=
  Arithmetic.CompareLessEqual left.toClosedRat right.toClosedRat

/-- Numerical equality, under which NaN is unequal to every operand.

P3109 interim report v4.1 (14 September 2026), §4.12; unapproved draft.
-/
@[inline] def CompareEqual (left : ExecFloat.P3109 format) (right : ExecFloat.P3109 rightFormat)
    : Bool :=
  Arithmetic.CompareEqual left.toClosedRat right.toClosedRat

/-- Strict reverse comparison of decoded operands.

P3109 interim report v4.1 (14 September 2026), §4.12; unapproved draft.
-/
@[inline] def CompareGreater (left : ExecFloat.P3109 format) (right : ExecFloat.P3109
    rightFormat) : Bool :=
  Arithmetic.CompareGreater left.toClosedRat right.toClosedRat

/-- Non-strict reverse comparison of decoded operands.

P3109 interim report v4.1 (14 September 2026), §4.12; unapproved draft.
-/
@[inline] def CompareGreaterEqual (left : ExecFloat.P3109 format) (right : ExecFloat.P3109
    rightFormat) : Bool :=
  Arithmetic.CompareGreaterEqual left.toClosedRat right.toClosedRat

/--
Order of two decoded operands, or `none` when either is NaN.

Infinities are ordered at the ends of the extended reals and equal when their signs agree.
-/
@[inline] def compare (left : ExecFloat.P3109 format) (right : ExecFloat.P3109 rightFormat) :
    Option Ordering :=
  let x := left.toClosedRat
  let y := right.toClosedRat
  if Arithmetic.CompareLess x y then some .lt
  else if Arithmetic.CompareLess y x then some .gt
  else if Arithmetic.CompareEqual x y then some .eq
  else none

/-- Minimum with NaN propagation and the supplied final projection.

P3109 interim report v4.1 (14 September 2026), §4.11.1; unapproved draft.
-/
@[inline] def Minimum (left : ExecFloat.P3109 format) (right : ExecFloat.P3109 rightFormat)
    (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.Minimum left right target mode saturation

/-- Maximum with NaN propagation and the supplied final projection.

P3109 interim report v4.1 (14 September 2026), §4.11.1; unapproved draft.
-/
@[inline] def Maximum (left : ExecFloat.P3109 format) (right : ExecFloat.P3109 rightFormat)
    (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.Maximum left right target mode saturation

/-- Minimum with a numerical operand preferred to NaN.

P3109 interim report v4.1 (14 September 2026), §4.11.1; unapproved draft.
-/
@[inline] def MinimumNumber (left : ExecFloat.P3109 format) (right : ExecFloat.P3109
    rightFormat) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.MinimumNumber left right target mode saturation

/-- Maximum with a numerical operand preferred to NaN.

P3109 interim report v4.1 (14 September 2026), §4.11.1; unapproved draft.
-/
@[inline] def MaximumNumber (left : ExecFloat.P3109 format) (right : ExecFloat.P3109
    rightFormat) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.MaximumNumber left right target mode saturation

/-- Minimum magnitude, with negative sign preferred at a tie.

P3109 interim report v4.1 (14 September 2026), §4.11.2; unapproved draft.
-/
@[inline] def MinimumMagnitude (left : ExecFloat.P3109 format) (right : ExecFloat.P3109
    rightFormat) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.MinimumMagnitude left right target mode saturation

/-- Maximum magnitude, with positive sign preferred at a tie.

P3109 interim report v4.1 (14 September 2026), §4.11.2; unapproved draft.
-/
@[inline] def MaximumMagnitude (left : ExecFloat.P3109 format) (right : ExecFloat.P3109
    rightFormat) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.MaximumMagnitude left right target mode saturation

/-- Minimum magnitude with a numerical operand preferred to NaN.

P3109 interim report v4.1 (14 September 2026), §4.11.2; unapproved draft.
-/
@[inline] def MinimumMagnitudeNumber (left : ExecFloat.P3109 format) (right : ExecFloat.P3109
    rightFormat)
    (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.MinimumMagnitudeNumber left right target mode saturation

/-- Maximum magnitude with a numerical operand preferred to NaN.

P3109 interim report v4.1 (14 September 2026), §4.11.2; unapproved draft.
-/
@[inline] def MaximumMagnitudeNumber (left : ExecFloat.P3109 format) (right : ExecFloat.P3109
    rightFormat)
    (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.MaximumMagnitudeNumber left right target mode saturation

/-- Minimum preferring finite values to infinity and infinity to NaN.

P3109 interim report v4.1 (14 September 2026), §4.11.3; unapproved draft.
-/
@[inline] def MinimumFinite (left : ExecFloat.P3109 format) (right : ExecFloat.P3109
    rightFormat) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.MinimumFinite left right target mode saturation

/-- Maximum preferring finite values to infinity and infinity to NaN.

P3109 interim report v4.1 (14 September 2026), §4.11.3; unapproved draft.
-/
@[inline] def MaximumFinite (left : ExecFloat.P3109 format) (right : ExecFloat.P3109
    rightFormat) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  binary Arithmetic.MaximumFinite left right target mode saturation

end FloatLib.Floats.ExecFloat.P3109
