/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Numerics.Enclosure.Expression.BackendsProof

/-!
# Backends with separate roundings

`Backend.ofRoundings` rounds algebraic results, quotients and elementary results with three
rounders of its own. The backend here keeps the algebra exact and rounds quotients and elementary
results outward to integers, so each example shows which rounder an operation used. Then come
rejected domains, the soundness theorem applied to a real inequality, and `ofRounding` as the
member of the family with one rounder.
-/

namespace FloatLibTests.Numerics.Roundings

open FloatLib.Numerics FloatLib.Numerics.Interval

/-- Outward rounding of a rational to the integers around it. -/
def integers : OutwardRounding ℚ ℚ :=
  OutwardRounding.ofCandidates some fun q => ⟨(q.floor : ℚ), (q.ceil : ℚ)⟩

/-- Exact algebra, with quotients and elementary results rounded outward to integers. -/
def mixed : Backend ℚ :=
  Backend.ofRoundings Internal.rationalOutwardRounding integers integers
    (Backend.elementaryBounds? {})

/-- The three rounders of `mixed` read endpoints alike, so it is sound. -/
theorem mixed_sound : mixed.Sound :=
  Backend.ofRoundings_sound _ _ _ _ rfl rfl (Backend.containsReal_elementaryBounds? {})

/-! ## Each operation uses its own rounder -/

-- Sums and powers stay exact.
example : mixed.binary? .add ⟨1 / 3, 1 / 3⟩ ⟨1 / 3, 1 / 3⟩ = some ⟨2 / 3, 2 / 3⟩ := by
  decide +kernel

example : mixed.unary? (.pow 2) ⟨-1 / 2, 1 / 3⟩ = some ⟨0, 1 / 4⟩ := by decide +kernel

-- Quotients and reciprocals are rounded to integers.
example : mixed.binary? .div ⟨1, 1⟩ ⟨3, 3⟩ = some ⟨0, 1⟩ := by decide +kernel

example : mixed.unary? .inv ⟨-3, -2⟩ = some ⟨-1, 0⟩ := by decide +kernel

-- So is the exponential: `e` lies between 2 and 3.
example : mixed.unary? .exp ⟨1, 1⟩ = some ⟨2, 3⟩ := by decide +kernel

/-! ## Rejected domains -/

-- The table has no logarithm for a range that reaches below zero.
example : mixed.unary? .log ⟨-1, 1⟩ = none := by decide +kernel

-- Neither a reciprocal nor a quotient has an enclosure when the denominator can be zero.
example :
    mixed.unary? .inv ⟨-1, 1⟩ = none ∧ mixed.binary? .div ⟨1, 1⟩ ⟨0, 1⟩ = none := by
  decide +kernel

-- A table that encloses nothing rejects every elementary operation and leaves the rest alone.
example :
    (Backend.ofRoundings integers integers integers fun _ _ => none).unary? .sqrt ⟨4, 4⟩ =
        none ∧
      (Backend.ofRoundings integers integers integers fun _ _ => none).unary? .abs ⟨-4, 1⟩ =
        some ⟨0, 4⟩ := by
  decide +kernel

/-! ## Soundness -/

/-- The expression `exp x / 3`. -/
def expThird : Expr :=
  .binary .div (.unary .exp (.var 0)) (.const 3)

/-- On `[0, 1]` the exponential is rounded to `[1, 3]` and the quotient by 3 to `[0, 1]`. -/
theorem expThird_eval : expThird.eval? mixed (fun _ => some ⟨0, 1⟩) = some ⟨0, 1⟩ := by
  decide +kernel

-- So `exp x / 3 ≤ 1` for every real `x` in `[0, 1]`.
example (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) : Real.exp x / 3 ≤ 1 := by
  have h := expThird.containsReal_eval? mixed_sound (values := fun _ => x)
    (fun _ I hI => by
      cases hI
      exact (containsReal_some_iff _ x).2 (by simpa using hx))
    expThird_eval
  simpa [expThird, Expr.eval, UnaryOp.eval, BinaryOp.eval] using
    ((containsReal_some_iff _ _).1 h).2

/-! ## One rounder for everything -/

-- `ofRounding` is the member of the family with one rounder and the table `elementaryBounds?`,
-- and `rational` is that member with exact endpoints. So they share one operation table.
example {α : Type*} (R : OutwardRounding α ℚ) (config : Backend.Config) :
    Backend.ofRounding R config = Backend.ofRoundings R R R (Backend.elementaryBounds? config) :=
  rfl

end FloatLibTests.Numerics.Roundings
