/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Rat.Cast.Order

/-!
# Executable rational intervals

The endpoints stay rational throughout a calculation, with no rounding in these operations.
Callers use the bounds to compare an exact value with rounding boundaries or to establish a
unique rounded result. Soundness over the reals is proved in `Rational.Proof`.

An interval may be empty: the carrier records endpoints without enforcing their order.
Membership hypotheses supply the required ordering in proofs.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- Closed rational endpoints used to enclose a real value. -/
structure RationalInterval where
  /-- Lower endpoint. -/
  lo : ℚ
  /-- Upper endpoint. -/
  hi : ℚ
  deriving DecidableEq, Repr

namespace RationalInterval

/-- The degenerate interval containing one rational value. -/
def point (x : ℚ) : RationalInterval :=
  ⟨x, x⟩

/-- An interval described by its midpoint and absolute-error radius. -/
def around (midpoint radius : ℚ) : RationalInterval :=
  ⟨midpoint - radius, midpoint + radius⟩

/-- Negation reverses the endpoints. -/
def neg (interval : RationalInterval) : RationalInterval :=
  ⟨-interval.hi, -interval.lo⟩

/-- Exact endpoint addition. -/
def add (left right : RationalInterval) : RationalInterval :=
  ⟨left.lo + right.lo, left.hi + right.hi⟩

/-- Exact endpoint subtraction. -/
def sub (left right : RationalInterval) : RationalInterval :=
  add left (neg right)

/-- Multiply both endpoints by a nonnegative rational scale. -/
def scaleNonnegative (interval : RationalInterval) (factor : ℚ) : RationalInterval :=
  ⟨factor * interval.lo, factor * interval.hi⟩

/-- Exact rational scaling, reversing the endpoints when the factor is negative. -/
def scale (interval : RationalInterval) (factor : ℚ) : RationalInterval :=
  if 0 ≤ factor then interval.scaleNonnegative factor
  else (interval.scaleNonnegative (-factor)).neg

/--
Square an interval known to contain a nonnegative value.

Clamping the lower endpoint at zero avoids squaring a negative error bound. This operation is
used in exponential range reduction, where positivity follows from the function being enclosed.
-/
def squareNonnegative (interval : RationalInterval) : RationalInterval :=
  ⟨(max 0 interval.lo) ^ 2, interval.hi ^ 2⟩

/-- Repeated squaring of a nonnegative enclosure. -/
def squareRepeat (interval : RationalInterval) : Nat → RationalInterval
  | 0 => interval
  | n + 1 => squareNonnegative (squareRepeat interval n)

end RationalInterval
end FloatLib.Numerics
