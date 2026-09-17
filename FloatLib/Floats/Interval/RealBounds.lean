/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Bounds
public import Mathlib.Basic.Real.Basic

/-!
# Real interval corner bounds

The ordered-field proofs live in `Numerics.Enclosure.Interval.Bounds`. These real-specialized
names preserve the interval API used by floating-point model semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Interval

/-- Minimum of four values with the grouping used by interval corner calculations. -/
def minOfFour {α : Type*} [LinearOrder α] (a b c d : α) : α :=
  min (min a b) (min c d)

/-- Maximum of four values with the grouping used by interval corner calculations. -/
def maxOfFour {α : Type*} [LinearOrder α] (a b c d : α) : α :=
  max (max a b) (max c d)

/-- Four-corner enclosure of a real product. -/
theorem mul_bounds_Icc (a b c d x y : ℝ)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    x * y ∈ Set.Icc (minOfFour (a * c) (a * d) (b * c) (b * d))
      (maxOfFour (a * c) (a * d) (b * c) (b * d)) :=
  Numerics.Interval.mul_bounds_Icc a b c d x y hx hy

/-- Four-corner enclosure of a real quotient when the denominator interval excludes zero. -/
theorem div_bounds_Icc (a b c d x y : ℝ)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d)
    (hzero : d < 0 ∨ 0 < c) :
    x / y ∈ Set.Icc (minOfFour (a / c) (a / d) (b / c) (b / d))
      (maxOfFour (a / c) (a / d) (b / c) (b / d)) :=
  Numerics.Interval.div_bounds_Icc a b c d x y hx hy hzero

end FloatLib.Floats.Interval
