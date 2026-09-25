/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import Mathlib.Data.Rat.Floor

/-!
# Exact rounding on a decimal coefficient grid

IEEE 754-2019 §4.3 requires five rounding directions for decimal arithmetic.
The integer decision below works on an exact rational magnitude. In particular,
midpoints are compared exactly; no binary floating approximation is used.
Format precision, exponent range, and cohort selection are handled separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- The five IEEE 754-2019 §4.3 decimal rounding-direction attributes. -/
inductive RoundingMode where
  | nearestEven
  | nearestAway
  | towardZero
  | towardPositive
  | towardNegative
  deriving DecidableEq, Repr, Inhabited

namespace RoundingMode

/-- Whether an inexact result should increase in magnitude at a given integer grid point.
`remainder` is the exact fractional part, between zero and one. -/
def increment (mode : RoundingMode) (negative : Bool) (lower : Nat)
    (remainder : ℚ) : Bool :=
  match mode with
  | .nearestEven =>
      decide (1 < 2 * remainder ∨ (2 * remainder = 1 ∧ lower % 2 = 1))
  | .nearestAway => decide (1 ≤ 2 * remainder)
  | .towardZero => false
  | .towardPositive => !negative && decide (0 < remainder)
  | .towardNegative => negative && decide (0 < remainder)

/-- Round a nonnegative exact rational magnitude to an integer coefficient.
The sign affects the directed modes, including rounding a negative value to zero.
The integer remainder avoids constructing and normalizing a fractional rational. -/
def roundMagnitude (mode : RoundingMode) (negative : Bool) (x : ℚ) : Nat :=
  let numerator := x.num.toNat
  let lower := numerator / x.den
  let remainder := numerator % x.den
  let up := match mode with
    | .nearestEven =>
        decide (x.den < 2 * remainder ∨ (2 * remainder = x.den ∧ lower % 2 = 1))
    | .nearestAway => decide (x.den ≤ 2 * remainder)
    | .towardZero => false
    | .towardPositive => !negative && decide (0 < remainder)
    | .towardNegative => negative && decide (0 < remainder)
  if up then lower + 1 else lower

/-- Apply the sign after rounding; callers retain the separate sign for signed zero. -/
def roundSigned (mode : RoundingMode) (negative : Bool) (x : ℚ) : ℚ :=
  if negative then -(mode.roundMagnitude negative x : ℚ)
  else mode.roundMagnitude negative x

/-- Rounding on a decimal grid whose quantum is `10 ^ q`. -/
def roundAt (mode : RoundingMode) (negative : Bool) (x : ℚ) (q : Int) : Nat :=
  mode.roundMagnitude negative (x / (10 : ℚ) ^ q)

end RoundingMode

end FloatLib.Floats.Formats.DecimalInterchange
