/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Elementary
public import FloatLib.Numerics.Enclosure.Interval.Operations

/-!
# Rational intervals for tangent and hyperbolic functions

Tangent divides the sine enclosure by the cosine enclosure and requires the latter to exclude
zero. The hyperbolic functions use exponential enclosures and exact rational arithmetic.
Hyperbolic cosine first takes the absolute-value range, retaining its minimum at zero.
Hyperbolic tangent uses `(exp (2*x) - 1) / (exp (2*x) + 1)`, whose denominator stays positive.

`HyperbolicProof` proves containment for every real member of the input interval.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- Exact rational endpoints need no outward adjustment. -/
def Internal.rationalOutwardRounding : OutwardRounding ℚ ℚ where
  decode := some
  enclose? q := some (point q)
  sound := by
    intro q I h
    cases Option.some.inj h
    exact ⟨q, q, rfl, rfl, le_rfl, le_rfl⟩

/--
Enclose tangent when the cosine enclosure lies strictly on one side of zero.

Failure can mean that the input crosses a pole, or that the cosine bounds are too coarse to
exclude zero. Increasing the Taylor degree or subdividing the input can resolve the latter.
-/
def tanBounds? (I : Interval ℚ) (terms : Nat) : Option (Interval ℚ) :=
  div? Internal.rationalOutwardRounding (sinBounds I terms) (cosBounds I terms)

/-- Point enclosure from `sinh x = (exp x - exp (-x)) / 2`. -/
def Internal.sinhPointBounds (x : ℚ) (terms : Nat) : Interval ℚ :=
  let positive := Enclosure.exp x terms
  let negative := Enclosure.exp (-x) terms
  ⟨(positive.lo - negative.hi) / 2, (positive.hi - negative.lo) / 2⟩

/-- Enclose hyperbolic sine by its monotonicity and certified endpoint values. -/
def sinhBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  monotoneBounds (fun x => Internal.sinhPointBounds x terms) I

/-- Point enclosure for hyperbolic cosine, intersected with its range `[1, ∞)`. -/
def Internal.coshPointBounds (x : ℚ) (terms : Nat) : Interval ℚ :=
  let positive := Enclosure.exp x terms
  let negative := Enclosure.exp (-x) terms
  ⟨max 1 ((positive.lo + negative.lo) / 2),
    (positive.hi + negative.hi) / 2⟩

/--
Enclose hyperbolic cosine by monotonicity on the absolute-value range.

An input crossing zero has lower bound one. Both negative and positive intervals retain their
endpoint-dependent lower bound; hyperbolic cosine is not monotone on all of the real line.
-/
def coshBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  monotoneBounds (fun x => Internal.coshPointBounds x terms) (absBounds I)

/--
Enclose hyperbolic tangent with a positive denominator, even at Taylor degree zero.

The map `(u - 1) / (u + 1)` is monotone for `u ≥ 0`. Clamping the exponential bounds to this
domain keeps the result in `[-1, 1]` without dividing by an enclosure that could contain zero.
-/
def tanhBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  let E := expBounds ⟨2 * I.lo, 2 * I.hi⟩ terms
  let lo := max 0 E.lo
  let hi := max 0 E.hi
  ⟨(lo - 1) / (lo + 1), (hi - 1) / (hi + 1)⟩

end FloatLib.Numerics.Interval
