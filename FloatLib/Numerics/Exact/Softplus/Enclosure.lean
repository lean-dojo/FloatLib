/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.ExponentialSum
public import FloatLib.Numerics.Enclosure.Elementary.Convergence
public import FloatLib.Numerics.Enclosure.Comparison.Proof
public import FloatLib.Numerics.Enclosure.Rational.AffineConvergence

/-!
# Enclosures for Softplus comparisons

When a rational boundary exceeds both zero and the argument, comparing
Softplus with it reduces to comparing a sum of two decaying exponentials
with one. Containment and convergence come from the shared interval API;
rational exponential separation proves termination.
-/

@[expose] public section

namespace FloatLib.Numerics.Softplus

/-- Enclose the two exponential terms after division by the boundary's exponential. -/
def interval (argument boundary : ℚ) (degree : Nat) : RationalInterval :=
  (Enclosure.exp (argument - boundary) degree).add (Enclosure.exp (-boundary) degree)

/-- The comparison interval contains the exact scaled exponential sum. -/
theorem contains_interval (argument boundary : ℚ) (degree : Nat) :
    (interval argument boundary degree).Contains
      (Real.exp ((argument - boundary : ℚ) : ℝ) + Real.exp ((-boundary : ℚ) : ℝ)) :=
  RationalInterval.contains_add (Enclosure.contains_exp (argument - boundary) degree)
    (Enclosure.contains_exp (-boundary) degree)

/-- Doubling the enclosure degree eventually separates the scaled exponential sum from one. -/
theorem exists_separating (argument boundary : ℚ)
    (hpositive : 0 < boundary) (habove : argument < boundary) :
    ∃ level, Enclosure.Comparison.Separates (interval argument boundary (2 ^ level)) 1 := by
  apply Enclosure.Comparison.exists_separating_two_pow
    (x := Real.exp ((argument - boundary : ℚ) : ℝ) + Real.exp ((-boundary : ℚ) : ℝ)) 1
  · have hne := Enclosure.exp_neg_add_exp_neg_ne_ratCast
      (boundary - argument) boundary 1 (sub_pos.mpr habove) hpositive
    simpa only [Rat.cast_sub, Rat.cast_neg, neg_sub] using hne
  · exact RationalInterval.tendsto_add_lo
      (Enclosure.tendsto_exp_lo (argument - boundary)) (Enclosure.tendsto_exp_lo (-boundary))
  · exact RationalInterval.tendsto_add_hi
      (Enclosure.tendsto_exp_hi (argument - boundary)) (Enclosure.tendsto_exp_hi (-boundary))

end FloatLib.Numerics.Softplus
