/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibTests.Support.IntervalExtensions

/-!
# Registered interval operation conformance

Importing a provider module makes its constant and function certificates available automatically.
The tests cover precision, nested calls, arbitrary arity, rejection, and refinement on subdivisions.
-/

public section

namespace FloatLibTests.Conformance.Numerics.IntervalExtensions

open FloatLib.Numerics.Interval FloatLibTests.Support.IntervalExtensions

/-- error: interval_extension expects ConstantBounds c or a theorem of type E.Sound f -/
#guard_msgs in
attribute [interval_extension] Nat.add_comm

example : myConstant < (1.6 : ℝ) := by interval
example : (1.3 : ℝ) < myConstant := by interval
example : Real.logb 2 myConstant < (1 : ℝ) := by interval

example : shrinkingOne < (2 : ℝ) := by
  fail_if_success interval (precision := 0)
  interval (precision := 8)

example : True := by
  fail_if_success have : myConstant < (1 : ℝ) := by interval
  trivial

example : (7 / 5 : ℝ) < rootTwo := by interval
example : rootTwo * rootTwo < (201 / 100 : ℝ) := by interval (precision := 128)
example : Real.logb 2 rootTwo < (1 : ℝ) := by interval
example : Real.exp rootTwo < (5 : ℝ) := by interval (degree := 24)

example : rootTwo < (3 / 2 : ℝ) := by
  fail_if_success interval (precision := 0)
  interval (precision := 16)

example (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : cancel x < (1 / 10 : ℝ) := by
  fail_if_success interval (depth := 0)
  interval (depth := 6)

example (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : cancel (cancel x) < (1 / 10 : ℝ) := by
  interval (depth := 7)

example (x y z w : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2)
    (hy : y ∈ Set.Icc (1 : ℝ) 2) (hz : z ∈ Set.Icc (1 : ℝ) 2)
    (hw : w ∈ Set.Icc (-5 : ℝ) (-4)) : fourth x y z w < (-3 : ℝ) := by interval

example (x : ℝ) (_hx : x ∈ Set.Icc (-1 : ℝ) 1) : True := by
  fail_if_success have : cancel x < (-1 : ℝ) := by interval (depth := 0)
  fail_if_success have : rootTwo < (1 : ℝ) := by interval
  trivial

example : ((Backend.binaryGrid {}).withExtensions {} [fourthEnclosure]).call? 0
    [point 0, point 0, point 0] = none := by decide +kernel

example : ((Backend.binaryGrid {}).withExtensions {} []).call? 0 [] = none := by decide +kernel

/-- A coarser certificate checks local and scoped overrides of theorem registrations. -/
@[expose] def coarseRootTwoBounds : ConstantBounds rootTwo where
  bounds _ := ⟨1, 2⟩
  valid _ := by norm_num [rootTwo]

section
attribute [local interval_extension] coarseRootTwoBounds

example : rootTwo < (21 / 10 : ℝ) := by interval
example : True := by
  fail_if_success have : rootTwo < (3 / 2 : ℝ) := by interval
  trivial
end

example : rootTwo < (3 / 2 : ℝ) := by interval

namespace Coarse
attribute [scoped interval_extension] coarseRootTwoBounds
end Coarse

section
open scoped Coarse

example : True := by
  fail_if_success have : rootTwo < (3 / 2 : ℝ) := by interval
  trivial
end

example : rootTwo < (3 / 2 : ℝ) := by interval

/-- Definitional aliases preserve registration recognition. -/
noncomputable abbrev rootTwoAlias : ℝ := rootTwo

example : rootTwoAlias < (3 / 2 : ℝ) := by interval

end FloatLibTests.Conformance.Numerics.IntervalExtensions
