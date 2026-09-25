/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Runtime

/-!
# Powers and set operations for finite intervals

Absolute values and even powers account for an interval crossing zero. Natural powers use
mathlib's binary exponentiation on exact endpoints and round only the final bounds. Hull and
intersection select existing endpoint encodings, so they introduce no further rounding.

As in `Interval.Runtime`, `none` reports an unavailable finite enclosure. Reciprocal requires
a range strictly on one side of zero; intersection also fails when the ranges are disjoint.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

variable {α β : Type*} [Field β] [LinearOrder β] [IsStrictOrderedRing β]

/-- Exact range of absolute value on an ordered interval. -/
def absBounds (I : Interval β) : Interval β :=
  if 0 ≤ I.lo then I
  else if I.hi ≤ 0 then ⟨-I.hi, -I.lo⟩
  else ⟨0, max (-I.lo) I.hi⟩

/-- Exact square bounds on an ordered interval, with lower bound zero if it crosses zero. -/
def squareBounds (I : Interval β) : Interval β :=
  let a := absBounds I
  ⟨a.lo * a.lo, a.hi * a.hi⟩

/--
Exact natural-power bounds for an ordered interval, evaluated by repeated squaring.

The zeroth power is `[1, 1]`, including at zero. Even positive powers use the absolute-value
range; odd powers preserve endpoint order.
-/
def powBounds (I : Interval β) (n : ℕ) : Interval β :=
  if n = 0 then point 1
  else if n % 2 = 0 then
    let a := absBounds I
    ⟨npowBinRec n a.lo, npowBinRec n a.hi⟩
  else ⟨npowBinRec n I.lo, npowBinRec n I.hi⟩

/-- Outward-rounded absolute value, accounting for zero-crossing ranges before rounding. -/
def abs? (R : OutwardRounding α β) (I : Interval α) : Option (Interval α) :=
  liftUnary? R absBounds I

/--
Outward-rounded square using the dependent range of `x * x`, rather than two independent inputs.
-/
def square? (R : OutwardRounding α β) (I : Interval α) : Option (Interval α) :=
  liftUnary? R squareBounds I

/-- Natural power using logarithmically many endpoint multiplications, then outward rounding. -/
def pow? (R : OutwardRounding α β) (I : Interval α) (n : ℕ) : Option (Interval α) :=
  liftUnary? R (fun a => powBounds a n) I

/-- Outward-rounded pointwise minimum of two intervals. -/
def min? (R : OutwardRounding α β) (I J : Interval α) : Option (Interval α) :=
  liftBinary? R (fun a b => ⟨min a.lo b.lo, min a.hi b.hi⟩) I J

/-- Outward-rounded pointwise maximum of two intervals. -/
def max? (R : OutwardRounding α β) (I J : Interval α) : Option (Interval α) :=
  liftBinary? R (fun a b => ⟨max a.lo b.lo, max a.hi b.hi⟩) I J

/-- Outward-rounded reciprocal, failing for a range containing zero or unavailable bounds. -/
def inv? (R : OutwardRounding α β) (I : Interval α) : Option (Interval α) :=
  match I.decode? R.decode with
  | some a =>
    if a.hi < 0 ∨ 0 < a.lo then
      encloseInterval? R ⟨a.hi⁻¹, a.lo⁻¹⟩
    else none
  | none => none

/--
Smallest interval containing two finite ordered intervals.

The selected input encodings are preserved. Undecodable or reversed input bounds return `none`.
-/
def hull? (R : OutwardRounding α β) (I J : Interval α) : Option (Interval α) :=
  match I.decode? R.decode, J.decode? R.decode with
  | some a, some b =>
    if a.lo ≤ a.hi ∧ b.lo ≤ b.hi then
      some ⟨if a.lo ≤ b.lo then I.lo else J.lo, if a.hi ≤ b.hi then J.hi else I.hi⟩
    else none
  | _, _ => none

/--
Intersection of two finite intervals, retaining the selected input encodings.

Disjoint, reversed, or undecodable bounds return `none`; touching endpoints give a point interval.
-/
def intersect? (R : OutwardRounding α β) (I J : Interval α) : Option (Interval α) :=
  match I.decode? R.decode, J.decode? R.decode with
  | some a, some b =>
    if max a.lo b.lo ≤ min a.hi b.hi then
      some ⟨if a.lo ≤ b.lo then J.lo else I.lo, if a.hi ≤ b.hi then I.hi else J.hi⟩
    else none
  | _, _ => none

end FloatLib.Numerics.Interval
