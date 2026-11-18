/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Elementary
public import FloatLib.Numerics.Enclosure.Interval.Operations

/-!
# Rational intervals for tangent and hyperbolic functions

Tangent divides the sine enclosure by the cosine enclosure, which has to exclude zero. The
hyperbolic functions use exponential enclosures and exact rational arithmetic. The definitions
call the kernel rational functions of `FloatLib.Numerics.Kernel.Q`, and each has a theorem
`…_def` that states it in ordinary notation. Hyperbolic cosine
first takes the absolute-value range, so it keeps its minimum at zero, and hyperbolic tangent uses
`(exp (2*x) - 1) / (exp (2*x) + 1)`, whose denominator stays positive. `HyperbolicProof` proves
containment for every real member of the input interval.
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
Four-corner division of rational intervals for a denominator strictly on one side of zero, and
`none` otherwise, on the kernel rational functions. It is the division `div?` with exact
rational endpoints (`Internal.divRational?_def`).
-/
def Internal.divRational? (a b : Interval ℚ) : Option (Interval ℚ) :=
  (fun quotient =>
    Bool.casesOn (motive := fun _ => Option (Interval ℚ)) (Kernel.Q.lt b.hi 0)
      (Bool.casesOn (motive := fun _ => Option (Interval ℚ)) (Kernel.Q.lt 0 b.lo) none quotient)
      quotient)
    ((fun p q r s =>
      some ⟨Kernel.Q.min (Kernel.Q.min p q) (Kernel.Q.min r s),
        Kernel.Q.max (Kernel.Q.max p q) (Kernel.Q.max r s)⟩)
      (Kernel.Q.div a.lo b.lo) (Kernel.Q.div a.lo b.hi) (Kernel.Q.div a.hi b.lo)
      (Kernel.Q.div a.hi b.hi))

/-- `Internal.divRational?` is the generic division at exact rational endpoints. -/
theorem Internal.divRational?_def (a b : Interval ℚ) :
    Internal.divRational? a b = div? Internal.rationalOutwardRounding a b := by
  unfold Internal.divRational? div?
  simp only [Kernel.Q.casesOn_lt, Kernel.Q.min_eq, Kernel.Q.max_eq, Kernel.Q.div_eq]
  by_cases h₁ : b.hi < 0
  · simp [h₁, decode?, encloseInterval?, Internal.rationalOutwardRounding, point]
  · by_cases h₂ : 0 < b.lo
    · simp [h₁, h₂, decode?, encloseInterval?, Internal.rationalOutwardRounding, point]
    · simp [h₁, h₂, decode?, Internal.rationalOutwardRounding]

/--
Enclose tangent when the cosine enclosure lies strictly on one side of zero.

Failure can mean that the input crosses a pole, or that the cosine bounds are too coarse to
exclude zero. Increasing the Taylor degree or subdividing the input can resolve the latter.
-/
def tanBounds? (I : Interval ℚ) (terms : Nat) : Option (Interval ℚ) :=
  Internal.divRational? (sinBounds I terms) (cosBounds I terms)

/-- The tangent bounds are the generic division of the sine bounds by the cosine bounds. -/
theorem tanBounds?_def (I : Interval ℚ) (terms : Nat) :
    tanBounds? I terms =
      div? Internal.rationalOutwardRounding (sinBounds I terms) (cosBounds I terms) :=
  Internal.divRational?_def _ _

/-- Point enclosure from `sinh x = (exp x - exp (-x)) / 2` (`Internal.sinhPointBounds_def`). -/
def Internal.sinhPointBounds (x : ℚ) (terms : Nat) : Interval ℚ :=
  let positive := Enclosure.exp x terms
  let negative := Enclosure.exp (Kernel.Q.neg x) terms
  ⟨Kernel.Q.divPow2 (Kernel.Q.sub positive.lo negative.hi) 1,
    Kernel.Q.divPow2 (Kernel.Q.sub positive.hi negative.lo) 1⟩

/-- The point enclosure of the hyperbolic sine, in ordinary notation. -/
theorem Internal.sinhPointBounds_def (x : ℚ) (terms : Nat) :
    Internal.sinhPointBounds x terms =
      (let positive := Enclosure.exp x terms
       let negative := Enclosure.exp (-x) terms
       ⟨(positive.lo - negative.hi) / 2, (positive.hi - negative.lo) / 2⟩) := by
  unfold Internal.sinhPointBounds
  simp only [Kernel.Q.divPow2_eq, Kernel.Q.sub_eq, Kernel.Q.neg_eq, pow_one]

/-- Enclose hyperbolic sine by its monotonicity and certified endpoint values. -/
def sinhBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  monotoneBounds (fun x => Internal.sinhPointBounds x terms) I

/--
Point enclosure for hyperbolic cosine, intersected with its range `[1, ∞)`
(`Internal.coshPointBounds_def`).
-/
def Internal.coshPointBounds (x : ℚ) (terms : Nat) : Interval ℚ :=
  let positive := Enclosure.exp x terms
  let negative := Enclosure.exp (Kernel.Q.neg x) terms
  ⟨Kernel.Q.max 1 (Kernel.Q.divPow2 (Kernel.Q.add positive.lo negative.lo) 1),
    Kernel.Q.divPow2 (Kernel.Q.add positive.hi negative.hi) 1⟩

/-- The point enclosure of the hyperbolic cosine, in ordinary notation. -/
theorem Internal.coshPointBounds_def (x : ℚ) (terms : Nat) :
    Internal.coshPointBounds x terms =
      (let positive := Enclosure.exp x terms
       let negative := Enclosure.exp (-x) terms
       ⟨max 1 ((positive.lo + negative.lo) / 2), (positive.hi + negative.hi) / 2⟩) := by
  unfold Internal.coshPointBounds
  simp only [Kernel.Q.divPow2_eq, Kernel.Q.add_eq, Kernel.Q.neg_eq, Kernel.Q.max_eq, pow_one]

/--
Enclose hyperbolic cosine by monotonicity on the absolute-value range.

An input crossing zero has lower bound one. Negative and positive intervals both keep their
endpoint-dependent lower bound, since hyperbolic cosine isn't monotone on the whole real line.
-/
def coshBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  monotoneBounds (fun x => Internal.coshPointBounds x terms) (absBounds I)

/--
Enclose hyperbolic tangent with a positive denominator, even at Taylor degree zero
(`tanhBounds_def`).

The map `(u - 1) / (u + 1)` is monotone for `u ≥ 0`. Clamping the exponential bounds to this
domain keeps the result in `[-1, 1]` without dividing by an enclosure that could contain zero.
-/
def tanhBounds (I : Interval ℚ) (terms : Nat) : Interval ℚ :=
  let E := expBounds ⟨Kernel.Q.mulPow2 I.lo 1, Kernel.Q.mulPow2 I.hi 1⟩ terms
  let lo := Kernel.Q.max 0 E.lo
  let hi := Kernel.Q.max 0 E.hi
  ⟨Kernel.Q.div (Kernel.Q.sub lo 1) (Kernel.Q.add lo 1),
    Kernel.Q.div (Kernel.Q.sub hi 1) (Kernel.Q.add hi 1)⟩

/-- The hyperbolic tangent bounds, in ordinary notation. -/
theorem tanhBounds_def (I : Interval ℚ) (terms : Nat) :
    tanhBounds I terms =
      (let E := expBounds ⟨2 * I.lo, 2 * I.hi⟩ terms
       let lo := max 0 E.lo
       let hi := max 0 E.hi
       ⟨(lo - 1) / (lo + 1), (hi - 1) / (hi + 1)⟩) := by
  unfold tanhBounds
  simp only [Kernel.Q.mulPow2_eq, Kernel.Q.max_eq, Kernel.Q.div_eq, Kernel.Q.sub_eq,
    Kernel.Q.add_eq, pow_one, mul_comm _ (2 : ℚ)]

end FloatLib.Numerics.Interval
