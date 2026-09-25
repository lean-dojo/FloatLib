/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Elementary

/-!
# Rational interval arcsine and arccosine

Arcsine reduces an interior endpoint to `atan (x / sqrt (1 - x²))`. Integer square-root
bounds enclose the denominator, and the rational arctangent kernel encloses the quotient.
The endpoints `-1` and `1` use the proved enclosure of π/4 instead of dividing by zero.
Arccosine follows from `π/2 - asin x`, with an exact zero at `x = 1`.

Both operations reject intervals extending outside `[-1, 1]`. The Taylor degree `terms`
controls the arctangent and π enclosures; `precision` is the number of fractional binary
digits in the square-root bounds. An interior point returns `none` if those bounds cannot
separate its square root from zero. `InverseTrigProof` proves containment over the reals.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- Enclose a rational arcsine value, treating the two endpoints and zero explicitly. -/
def Internal.asinPointBounds? (x : ℚ) (terms precision : Nat) : Option (Interval ℚ) :=
  if x = 0 then some (point 0)
  else if x = 1 then
    let pi := Enclosure.piQuarter terms
    some ⟨2 * pi.lo, 2 * pi.hi⟩
  else if x = -1 then
    let pi := Enclosure.piQuarter terms
    some ⟨-(2 * pi.hi), -(2 * pi.lo)⟩
  else if -1 < x ∧ x < 1 then
    let root := sqrtPointBounds (1 - x ^ 2) precision
    if 0 < root.lo then
      some (atanBounds
        ⟨min (x / root.lo) (x / root.hi), max (x / root.lo) (x / root.hi)⟩ terms)
    else none
  else none

/--
Enclose arcsine on an ordered interval contained in `[-1, 1]`, including both endpoints.

A point interval is evaluated once, and zero gives the exact interval `[0, 0]`. Invalid
input bounds or a square-root lower bound that is too coarse return `none`.
-/
def asinBounds? (I : Interval ℚ) (terms precision : Nat) : Option (Interval ℚ) :=
  if -1 ≤ I.lo ∧ I.hi ≤ 1 ∧ I.lo ≤ I.hi then do
    let lo ← Internal.asinPointBounds? I.lo terms precision
    if I.lo = I.hi then some lo
    else
      let hi ← Internal.asinPointBounds? I.hi terms precision
      some ⟨lo.lo, hi.hi⟩
  else none

/--
Enclose arccosine on an ordered interval contained in `[-1, 1]`.

The exact input `[1, 1]` gives `[0, 0]`. Other inputs use `π/2 - asin x` and the known
nonnegativity of arccosine. Domain and precision failures are the same as for `asinBounds?`.
-/
def acosBounds? (I : Interval ℚ) (terms precision : Nat) : Option (Interval ℚ) :=
  if I.lo = 1 ∧ I.hi = 1 then some (point 0)
  else do
    let J ← asinBounds? I terms precision
    let pi := Enclosure.piQuarter terms
    some ⟨max 0 (2 * pi.lo - J.hi), 2 * pi.hi - J.lo⟩

end FloatLib.Numerics.Interval
