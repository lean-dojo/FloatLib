/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.Interval

/-!
# Constants in `interval`

This module imports `FloatLib.Tactic.Interval` alone, so only the enclosure route runs. The box of
that route gives `π` the endpoints of Mathlib's `Real.pi_gt_d20` and `Real.pi_lt_d20`, and a goal
about `π` needs no hypothesis.
-/

@[expose] public section

namespace FloatLibTests.Tactic.Interval.Constants

example : (3 : ℝ) < Real.pi := by interval

example : Real.pi < 22 / 7 := by interval

/-- The endpoints are those of the two lemmas: twenty digits on either side. -/
example : (3.14159265358979323846 : ℝ) ≤ Real.pi ∧ Real.pi ≤ 3.14159265358979323847 := by
  constructor <;> interval

/-- A hypothesis that is weaker than the constant's bounds does not replace them. -/
example (_h : Real.pi ≤ 4) : Real.pi ^ 2 < 10 := by interval

/-- The constant beside a variable with bounds from the context. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * Real.pi ≤ 22 / 7 := by interval

end FloatLibTests.Tactic.Interval.Constants
