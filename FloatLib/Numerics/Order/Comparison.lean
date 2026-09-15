/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Compare

/-!
# Quotient comparisons in ordered fields

Comparing a quotient with a boundary is equivalent to testing a linear residual against zero.
A negative denominator reverses the ordering. These identities let interval-based comparisons
use subtraction and multiplication without constructing quotient intervals.
-/

public section

namespace FloatLib.Numerics

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- A positive denominator preserves the ordering of the quotient's linear residual. -/
theorem cmp_div_of_pos (s c b : α) (hc : 0 < c) :
    cmp (s - b * c) 0 = cmp (s / c) b := by
  simp only [cmp, cmpUsing, sub_lt_zero, sub_pos, div_lt_iff₀ hc, lt_div_iff₀ hc]

/-- A negative denominator reverses the ordering of the quotient's linear residual. -/
theorem cmp_div_of_neg (s c b : α) (hc : c < 0) :
    (cmp (s - b * c) 0).swap = cmp (s / c) b := by
  rw [cmp_swap]
  simp only [cmp, cmpUsing, sub_lt_zero, sub_pos, div_lt_iff_of_neg hc, lt_div_iff_of_neg hc]

end FloatLib.Numerics
