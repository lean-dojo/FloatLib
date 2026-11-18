/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.QProof

/-!
# Executable rational intervals

Nothing here rounds. The endpoints stay rational throughout a calculation, and callers use the
bounds to compare an exact value with rounding boundaries or to establish a unique rounded result.
Soundness over the reals is proved in `Rational.Proof`.

An interval may be empty, since the carrier records endpoints without enforcing their order. In
proofs, membership hypotheses supply the ordering.

`around`, `add`, `scaleNonnegative` and `squareNonnegative` are written with the kernel functions
of `FloatLib.Numerics.Kernel.Q`, because Lean's kernel evaluates them in every elementary
enclosure, and core's sum of two rationals whose denominators share a factor costs it 0.4 ms. The
theorems `around_def`, `add_def`, `scaleNonnegative_def` and `squareNonnegative_def` state them in
ordinary notation.
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

/--
The interval with endpoints `midpoint - radius` and `midpoint + radius`, for any `radius`. With a
nonnegative radius it is the ball of absolute error `radius` around `midpoint` (`contains_around`).
A negative radius gives reversed endpoints, which is an empty interval.
-/
def around (midpoint radius : ℚ) : RationalInterval :=
  ⟨Kernel.Q.sub midpoint radius, Kernel.Q.add midpoint radius⟩

/-- The endpoints of `around`, in ordinary notation. -/
theorem around_def (midpoint radius : ℚ) :
    around midpoint radius = ⟨midpoint - radius, midpoint + radius⟩ := by
  rw [around, Kernel.Q.sub_eq, Kernel.Q.add_eq]

/-- Negation reverses the endpoints. -/
def neg (interval : RationalInterval) : RationalInterval :=
  ⟨-interval.hi, -interval.lo⟩

/-- Exact endpoint addition. -/
def add (left right : RationalInterval) : RationalInterval :=
  ⟨Kernel.Q.add left.lo right.lo, Kernel.Q.add left.hi right.hi⟩

/-- The endpoints of a sum, in ordinary notation. -/
theorem add_def (left right : RationalInterval) :
    add left right = ⟨left.lo + right.lo, left.hi + right.hi⟩ := by
  rw [add, Kernel.Q.add_eq, Kernel.Q.add_eq]

/-- Exact endpoint subtraction. -/
def sub (left right : RationalInterval) : RationalInterval :=
  add left (neg right)

/--
Multiply both endpoints of `interval` by `factor` without exchanging them, for any rational
`factor`. The intended use is a nonnegative factor, where the result encloses `factor * x` for every
enclosed `x` (`contains_scaleNonnegative`). With a negative factor and ordered endpoints the new
lower endpoint is the larger one, and `scale` is the version that exchanges them.
-/
def scaleNonnegative (interval : RationalInterval) (factor : ℚ) : RationalInterval :=
  ⟨Kernel.Q.mul factor interval.lo, Kernel.Q.mul factor interval.hi⟩

/-- The endpoints of a scaled interval, in ordinary notation. -/
theorem scaleNonnegative_def (interval : RationalInterval) (factor : ℚ) :
    interval.scaleNonnegative factor = ⟨factor * interval.lo, factor * interval.hi⟩ := by
  rw [scaleNonnegative, Kernel.Q.mul_eq, Kernel.Q.mul_eq]

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
  ⟨Kernel.Q.pow (Kernel.Q.max 0 interval.lo) 2, Kernel.Q.pow interval.hi 2⟩

/-- The endpoints of `squareNonnegative`, in ordinary notation. -/
theorem squareNonnegative_def (interval : RationalInterval) :
    interval.squareNonnegative = ⟨(max 0 interval.lo) ^ 2, interval.hi ^ 2⟩ := by
  unfold squareNonnegative
  rw [Kernel.Q.pow_eq, Kernel.Q.pow_eq, Kernel.Q.max_eq]

/-- Repeated squaring of a nonnegative enclosure. -/
def squareRepeat (interval : RationalInterval) : Nat → RationalInterval
  | 0 => interval
  | n + 1 => squareNonnegative (squareRepeat interval n)

end RationalInterval
end FloatLib.Numerics
