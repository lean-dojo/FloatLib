/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Rational.Runtime
public import Mathlib.Data.Nat.Find

/-!
# Adaptive comparison with rational enclosures

The search uses only rational arithmetic. Its termination argument is a proposition and is
erased from executable code. Callers supply a sequence of increasingly accurate intervals and
a proof that some interval excludes the boundary; real containment is used separately to prove
the returned ordering correct.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.Comparison

/-- An interval lies strictly on one side of a rational boundary. -/
def Separates (interval : RationalInterval) (boundary : ℚ) : Prop :=
  interval.hi < boundary ∨ boundary < interval.lo

instance (interval : RationalInterval) (boundary : ℚ) :
    Decidable (Separates interval boundary) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Search for the first separating interval and return whether it lies below or above the boundary. -/
def compare (intervals : Nat → RationalInterval) (boundary : ℚ)
    (terminates : ∃ n, Separates (intervals n) boundary) : Ordering :=
  let interval := intervals (Nat.find terminates)
  if interval.hi < boundary then .lt else .gt

end FloatLib.Numerics.Enclosure.Comparison
