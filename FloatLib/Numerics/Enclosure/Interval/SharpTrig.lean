/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Elementary
public import FloatLib.Numerics.Enclosure.Interval.Exact
public import FloatLib.Numerics.Enclosure.Interval.Rounding

/-!
# Sharper sine and cosine on monotone panels

`sinBounds` and `cosBounds` enclose the value at the midpoint of an interval and widen it by the
half-width, since sine and cosine are 1-Lipschitz. That's cheap, but it overestimates the range by
about the width of the interval, even where the function is monotone. On `[1, 3/2]`, say, the
midpoint bound is about `[0.699, 1]`, while sine only runs from `sin 1 ≈ 0.841` to
`sin (3/2) ≈ 0.997`.

The enclosures here round the midpoint bounds outward to the grid of step `2 ^ (-bits)`
(`sinBase`, `cosBase`) and intersect them (`Exact.intersect`) with bounds from the point
enclosures at the two ends of the interval, when the interval lies where its end values control
the range:

* sine increases on `[-π/2, π/2]`, and on `[0, π]` it is at least the smaller of its two end
  values.
* cosine decreases on `[0, π]` and increases on `[-π, 0]`, and on an interval of `[-π, π]` around
  zero it is at least the smaller of its two end values.
* either function is monotone where the enclosure of its derivative has one sign.

On `[0, piLower]` the sine bounds are then raised to zero from below, and so are the cosine bounds
on `[-piLower/2, piLower/2]`. The branch tests compare the ends of the interval with `piLower`, the
twenty-decimal lower bound for `π`, so they're exact rational comparisons. A call evaluates at
most four enclosures: the midpoint bound, the two ends, and on the derivative branch the midpoint
bound of the other function.

## Main definitions

* `sharpSinBounds I terms bits` and `sharpCosBounds I terms bits`: the enclosures, at Taylor degree
  `terms` on the grid of step `2 ^ (-bits)`.
* `sinMonotoneBase` and `cosMonotoneBase`: the midpoint bounds intersected with the bounds from
  the ends, before the clamp at zero.
* `piLower`: the rational lower bound for `π` that the branch tests use.

## Implementation notes

The definitions are written with the kernel functions of `FloatLib.Numerics.Kernel`, as in
`Interval.Elementary`, because Lean's kernel evaluates these bounds when it checks a proof that
uses them. `sinMonotoneBase_def`, `cosMonotoneBase_def`, `sharpSinBounds_def` and
`sharpCosBounds_def` state them in ordinary notation. `SharpTrigProof` proves that the bounds
contain the sine and cosine of every real member of the interval.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- `3.14159265358979323846`, the twenty-decimal lower bound for `π` of Mathlib's
`Real.pi_gt_d20`. The branch tests of the sharp sine and cosine compare the ends of an interval
with it. -/
def piLower : ℚ := Kernel.Q.mk 314159265358979323846 100000000000000000000

/-- `sinBounds I terms`, rounded outward to the grid of step `2 ^ (-bits)`. -/
def sinBase (I : Interval ℚ) (terms bits : Nat) : Interval ℚ :=
  dyadicHull bits (sinBounds I terms)

/-- `cosBounds I terms`, rounded outward to the grid of step `2 ^ (-bits)`. -/
def cosBase (I : Interval ℚ) (terms bits : Nat) : Interval ℚ :=
  dyadicHull bits (cosBounds I terms)

/-- `sinBase` at the point `q`. -/
def sinPoint (q : ℚ) (terms bits : Nat) : Interval ℚ :=
  sinBase (point q) terms bits

/-- `cosBase` at the point `q`. -/
def cosPoint (q : ℚ) (terms bits : Nat) : Interval ℚ :=
  cosBase (point q) terms bits

/-- The point bounds of sine at the two ends, for an interval on which sine increases. -/
def sinEndpoint (I : Interval ℚ) (terms bits : Nat) : Interval ℚ :=
  monotoneBounds (fun q => sinPoint q terms bits) I

/-- The point bounds of cosine at the two ends, for an interval on which cosine decreases. -/
def cosEndpoint (I : Interval ℚ) (terms bits : Nat) : Interval ℚ :=
  antitoneBounds (fun q => cosPoint q terms bits) I

/-- `cosEndpoint` of the negated interval, for an interval of `[-π, 0]`: cosine is even. -/
def cosNegativeEndpoint (I : Interval ℚ) (terms bits : Nat) : Interval ℚ :=
  cosEndpoint (Exact.neg I) terms bits

/-- The smaller of the two lower point bounds of sine at the ends, and `1`, for an interval of
`[0, π]`, where sine rises and then falls. -/
def sinPositiveEndpoint (I : Interval ℚ) (terms bits : Nat) : Interval ℚ :=
  ⟨Kernel.Q.min (sinPoint I.lo terms bits).lo (sinPoint I.hi terms bits).lo, 1⟩

/-- The smaller of the two lower point bounds of cosine at the ends, and `1`, for an interval of
`[-π, π]` around zero, where cosine rises and then falls. -/
def cosCrossZeroEndpoint (I : Interval ℚ) (terms bits : Nat) : Interval ℚ :=
  ⟨Kernel.Q.min (cosPoint I.lo terms bits).lo (cosPoint I.hi terms bits).lo, 1⟩

/--
`sinBase` intersected with bounds from the ends of the interval: `sinEndpoint` on
`[-piLower/2, piLower/2]`, `sinPositiveEndpoint` on `[0, piLower]`, and the hull of the two point
bounds where `cosBase` has one sign. Elsewhere the result is `sinBase`.
-/
def sinMonotoneBase (I : Interval ℚ) (terms bits : Nat) : Interval ℚ :=
  let base := sinBase I terms bits
  let halfPi := Kernel.Q.divPow2 piLower 1
  Exact.intersect base
    (Bool.casesOn (motive := fun _ => Interval ℚ)
      (Kernel.Q.le (Kernel.Q.neg halfPi) I.lo && Kernel.Q.le I.hi halfPi)
      (Bool.casesOn (motive := fun _ => Interval ℚ)
        (Kernel.Q.le 0 I.lo && Kernel.Q.le I.hi piLower)
        (let D := cosBase I terms bits
         Bool.casesOn (motive := fun _ => Interval ℚ)
          (Kernel.Q.le 0 D.lo || Kernel.Q.le D.hi 0) base
          (Exact.hull (sinPoint I.lo terms bits) (sinPoint I.hi terms bits)))
        (sinPositiveEndpoint I terms bits))
      (sinEndpoint I terms bits))

/-- The sine bounds from the ends of the interval, in ordinary notation. -/
theorem sinMonotoneBase_def (I : Interval ℚ) (terms bits : Nat) :
    sinMonotoneBase I terms bits =
      Exact.intersect (sinBase I terms bits)
        (if -(piLower / 2) ≤ I.lo ∧ I.hi ≤ piLower / 2 then sinEndpoint I terms bits
         else if 0 ≤ I.lo ∧ I.hi ≤ piLower then sinPositiveEndpoint I terms bits
         else if 0 ≤ (cosBase I terms bits).lo ∨ (cosBase I terms bits).hi ≤ 0 then
           Exact.hull (sinPoint I.lo terms bits) (sinPoint I.hi terms bits)
         else sinBase I terms bits) := by
  unfold sinMonotoneBase
  simp only [Kernel.Z.casesOn_eq_ite Iff.rfl, Bool.and_eq_true, Bool.or_eq_true, Kernel.Q.le_iff,
    Kernel.Q.neg_eq, Kernel.Q.divPow2_eq, pow_one]

/--
`cosBase` intersected with bounds from the ends of the interval: `cosEndpoint` on `[0, piLower]`,
`cosNegativeEndpoint` on `[-piLower, 0]`, `cosCrossZeroEndpoint` on an interval of
`[-piLower, piLower]` containing zero, and the hull of the two point bounds where `sinBase` has
one sign. Elsewhere the result is `cosBase`.
-/
def cosMonotoneBase (I : Interval ℚ) (terms bits : Nat) : Interval ℚ :=
  let base := cosBase I terms bits
  Exact.intersect base
    (Bool.casesOn (motive := fun _ => Interval ℚ)
      (Kernel.Q.le 0 I.lo && Kernel.Q.le I.hi piLower)
      (Bool.casesOn (motive := fun _ => Interval ℚ)
        (Kernel.Q.le (Kernel.Q.neg piLower) I.lo && Kernel.Q.le I.hi 0)
        (Bool.casesOn (motive := fun _ => Interval ℚ)
          (Kernel.Q.le (Kernel.Q.neg piLower) I.lo && (Kernel.Q.le I.lo 0 &&
            (Kernel.Q.le 0 I.hi && Kernel.Q.le I.hi piLower)))
          (let S := sinBase I terms bits
           Bool.casesOn (motive := fun _ => Interval ℚ)
            (Kernel.Q.le 0 S.lo || Kernel.Q.le S.hi 0) base
            (Exact.hull (cosPoint I.lo terms bits) (cosPoint I.hi terms bits)))
          (cosCrossZeroEndpoint I terms bits))
        (cosNegativeEndpoint I terms bits))
      (cosEndpoint I terms bits))

/-- The cosine bounds from the ends of the interval, in ordinary notation. -/
theorem cosMonotoneBase_def (I : Interval ℚ) (terms bits : Nat) :
    cosMonotoneBase I terms bits =
      Exact.intersect (cosBase I terms bits)
        (if 0 ≤ I.lo ∧ I.hi ≤ piLower then cosEndpoint I terms bits
         else if -piLower ≤ I.lo ∧ I.hi ≤ 0 then cosNegativeEndpoint I terms bits
         else if -piLower ≤ I.lo ∧ I.lo ≤ 0 ∧ 0 ≤ I.hi ∧ I.hi ≤ piLower then
           cosCrossZeroEndpoint I terms bits
         else if 0 ≤ (sinBase I terms bits).lo ∨ (sinBase I terms bits).hi ≤ 0 then
           Exact.hull (cosPoint I.lo terms bits) (cosPoint I.hi terms bits)
         else cosBase I terms bits) := by
  unfold cosMonotoneBase
  simp only [Kernel.Z.casesOn_eq_ite Iff.rfl, Bool.and_eq_true, Bool.or_eq_true, Kernel.Q.le_iff,
    Kernel.Q.neg_eq]

/--
Enclose sine for every real in the interval: `sinMonotoneBase` at Taylor degree `terms` on the grid
of step `2 ^ (-bits)`, with the lower bound raised to `0` on an interval of `[0, piLower]`.
-/
def sharpSinBounds (I : Interval ℚ) (terms bits : Nat) : Interval ℚ :=
  let J := sinMonotoneBase I terms bits
  Bool.casesOn (motive := fun _ => Interval ℚ)
    (Kernel.Q.le 0 I.lo && Kernel.Q.le I.hi piLower) J ⟨Kernel.Q.max J.lo 0, J.hi⟩

/-- The sharp sine bounds, in ordinary notation. -/
theorem sharpSinBounds_def (I : Interval ℚ) (terms bits : Nat) :
    sharpSinBounds I terms bits =
      (let J := sinMonotoneBase I terms bits
       if 0 ≤ I.lo ∧ I.hi ≤ piLower then ⟨max J.lo 0, J.hi⟩ else J) := by
  unfold sharpSinBounds
  simp only [Kernel.Z.casesOn_eq_ite Iff.rfl, Bool.and_eq_true, Kernel.Q.le_iff, Kernel.Q.max_eq]

/--
Enclose cosine for every real in the interval: `cosMonotoneBase` at Taylor degree `terms` on the
grid of step `2 ^ (-bits)`, with the lower bound raised to `0` on `[-piLower/2, piLower/2]`.
-/
def sharpCosBounds (I : Interval ℚ) (terms bits : Nat) : Interval ℚ :=
  let J := cosMonotoneBase I terms bits
  let halfPi := Kernel.Q.divPow2 piLower 1
  Bool.casesOn (motive := fun _ => Interval ℚ)
    (Kernel.Q.le (Kernel.Q.neg halfPi) I.lo && Kernel.Q.le I.hi halfPi) J
    ⟨Kernel.Q.max J.lo 0, J.hi⟩

/-- The sharp cosine bounds, in ordinary notation. -/
theorem sharpCosBounds_def (I : Interval ℚ) (terms bits : Nat) :
    sharpCosBounds I terms bits =
      (let J := cosMonotoneBase I terms bits
       if -(piLower / 2) ≤ I.lo ∧ I.hi ≤ piLower / 2 then ⟨max J.lo 0, J.hi⟩ else J) := by
  unfold sharpCosBounds
  simp only [Kernel.Z.casesOn_eq_ite Iff.rfl, Bool.and_eq_true, Kernel.Q.le_iff, Kernel.Q.max_eq,
    Kernel.Q.neg_eq, Kernel.Q.divPow2_eq, pow_one]

end FloatLib.Numerics.Interval
