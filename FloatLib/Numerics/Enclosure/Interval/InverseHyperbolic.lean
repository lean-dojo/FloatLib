/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Hyperbolic

/-!
# Rational enclosures for inverse hyperbolic functions

These enclosures compose square roots, logarithms, and exact interval arithmetic.
Inverse hyperbolic cosine accepts inputs at least one; inverse hyperbolic tangent requires
an interval strictly inside `(-1, 1)`. Inverse hyperbolic sine uses monotonicity and odd symmetry
to avoid cancellation in its logarithmic formula at negative inputs.
`InverseHyperbolicProof` proves containment for every real member of an accepted interval.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- The logarithmic formula for inverse hyperbolic sine, used at nonnegative endpoints. -/
def Internal.asinhFormulaBounds? (I : Interval ℚ) (terms precision : Nat) :
    Option (Interval ℚ) := do
  let square ← pow? Internal.rationalOutwardRounding I 2
  let radicand ← add? Internal.rationalOutwardRounding (point 1) square
  let root ← sqrtBounds? radicand precision
  let argument ← add? Internal.rationalOutwardRounding I root
  logBounds? argument terms

/-- Use odd symmetry before evaluating the logarithmic formula at a negative endpoint. -/
def Internal.asinhPointBounds? (x : ℚ) (terms precision : Nat) : Option (Interval ℚ) :=
  if x < 0 then do
    let J ← asinhFormulaBounds? (point (-x)) terms precision
    neg? rationalOutwardRounding J
  else asinhFormulaBounds? (point x) terms precision

/-- Enclose inverse hyperbolic sine by monotonicity and stable endpoint values. -/
def asinhBounds? (I : Interval ℚ) (terms precision : Nat) : Option (Interval ℚ) := do
  let lower ← Internal.asinhPointBounds? I.lo terms precision
  let upper ← Internal.asinhPointBounds? I.hi terms precision
  return ⟨lower.lo, upper.hi⟩

/-- Enclose inverse hyperbolic cosine on intervals with lower endpoint at least one. -/
def acoshBounds? (I : Interval ℚ) (terms precision : Nat) : Option (Interval ℚ) :=
  if 1 ≤ I.lo then do
    let square ← pow? Internal.rationalOutwardRounding I 2
    let radicand ← sub? Internal.rationalOutwardRounding square (point 1)
    let root ← sqrtBounds? radicand precision
    let argument ← add? Internal.rationalOutwardRounding I root
    logBounds? argument terms
  else none

/-- Enclose inverse hyperbolic tangent using `log ((1 + x) / (1 - x)) / 2`.
Both poles and intervals reaching them are rejected. -/
def atanhBounds? (I : Interval ℚ) (terms : Nat) : Option (Interval ℚ) :=
  if -1 < I.lo ∧ I.hi < 1 then do
    let numerator ← add? Internal.rationalOutwardRounding (point 1) I
    let denominator ← sub? Internal.rationalOutwardRounding (point 1) I
    let quotient ← div? Internal.rationalOutwardRounding numerator denominator
    let logarithm ← logBounds? quotient terms
    mul? Internal.rationalOutwardRounding (point (1 / 2)) logarithm
  else none

end FloatLib.Numerics.Interval
