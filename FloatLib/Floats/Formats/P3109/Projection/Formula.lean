/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Runtime
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Fractional-part formulas for P3109 rounding

P3109 interim report v4.1 (14 September 2026), §4.7.4, unapproved draft.
One definition over ordered fields with floor serves both exact rationals and
real semantics. The supplied random word is data; these definitions impose no
probability distribution.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.RoundingFormula

variable {α : Type*} [Field α] [LinearOrder α] [FloorRing α]

/-- Nearest integer to a nonnegative value, with ties sent to the even integer. -/
def nearestEven (value : α) : Nat :=
  let lower : Nat := ⌊value⌋₊
  if value < lower + 1 / 2 ∨ (value = lower + 1 / 2 ∧ lower % 2 = 0) then lower
  else lower + 1

/-- The report's nine rounding decisions in terms of the exact fractional part. -/
def roundAway (mode : RoundingMode) (negative lowerEven : Bool) (fraction : α) : Bool :=
  match mode with
  | .towardZero => false
  | .up => decide (0 < fraction) && !negative
  | .down => decide (0 < fraction) && negative
  | .nearestAway => decide (1 / 2 ≤ fraction)
  | .nearest =>
      decide (1 / 2 < fraction) || (decide (fraction = 1 / 2) && !lowerEven)
  | .toOdd => decide (0 < fraction) && lowerEven
  | .stochasticA random =>
      decide (2 ^ random.width ≤ ⌊fraction * 2 ^ random.width⌋₊ + random.toNat)
  | .stochasticB random =>
      decide (2 ^ (random.width + 1) ≤
        ⌊fraction * 2 ^ (random.width + 1)⌋₊ + (2 * random.toNat + 1))
  | .stochasticC random =>
      decide (2 ^ random.width ≤ nearestEven (fraction * 2 ^ random.width) + random.toNat)

end FloatLib.Floats.Formats.P3109.RoundingFormula
