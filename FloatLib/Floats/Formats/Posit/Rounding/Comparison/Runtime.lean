/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Runtime
public import Mathlib.Order.Compare

/-!
# Posit rounding from exact rational comparisons

An exact result need not itself be rational. To round it, the posit search only needs to compare
it with rational code values and appended-bit boundaries. This module shares that bounded search
among algebraic and analytic operations whose comparisons can be decided exactly.

`compareTarget q` reports the ordering of the mathematical target relative to the rational `q`.
The proof layer states this requirement explicitly; an approximate comparator cannot discharge it.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.ComparisonRounding

/-- Locate the lower posit code using exact target-to-candidate comparisons. -/
def lowerCode (format : Format) (compareTarget : Rat → Ordering) : Nat :=
  lowerCodeByBisection
    (fun code => decide (compareTarget (nonnegativeRatAt format code) ≠ .lt))
    format.bits 0 format.signMaskNat

/--
Round through the standard appended-bit boundaries, including even ties and saturation.

As with `roundPositiveCode`, targets at or below zero give zero. Signed operations round the
magnitude and restore its sign outside this helper.
-/
def roundCode (format : Format) (compareTarget : Rat → Ordering) : Nat :=
  if compareTarget 0 ≠ .gt then 0
  else if compareTarget (minPositiveRat format) = .lt then 1
  else
    let lower := lowerCode format compareTarget
    let upper := lower + 1
    if upper < format.signMaskNat then
      let comparison := compareTarget (roundingThreshold format lower)
      if comparison = .lt then lower
      else if comparison = .gt then upper
      else if lower % 2 = 0 then lower else upper
    else lower

/-- Model-valued rounding from an exact comparison procedure. -/
def round (format : Format) (compareTarget : Rat → Ordering) : Model format :=
  ofNatBits (roundCode format compareTarget)

/-- Signed rounding, using the comparator itself to determine the sign of the exact result. -/
def roundSigned (format : Format) (compareTarget : Rat → Ordering) : Model format :=
  if compareTarget 0 = .lt then
    neg (round format (fun q => (compareTarget (-q)).swap))
  else round format compareTarget

end FloatLib.Floats.Formats.Posit.Model.ComparisonRounding
