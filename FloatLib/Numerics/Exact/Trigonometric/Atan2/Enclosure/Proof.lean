/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Argument
public import FloatLib.Numerics.Enclosure.Trigonometric.Termination

/-!
# Containment, convergence, and separation for the principal argument

The rational quadrant reduction gives both endpoint containment and convergence. Off the nonnegative
real axis the argument can't be rational, because its tangent is the rational slope, and the tangent
at a nonzero rational angle is irrational. That proves the adaptive comparison terminates at every
rational boundary, the vertical and negative real axes included.
-/

public section

namespace FloatLib.Numerics.TrigonometricComparison

open Filter
open scoped Topology

/-- The rational argument enclosure contains the exact principal value. -/
theorem contains_atan2Interval (x y : ℚ) (degree : Nat) :
    (atan2Interval x y degree).Contains (Complex.arg ⟨(x : ℝ), (y : ℝ)⟩) := by
  rw [← atan2Reduction_eq_arg]
  exact RationalInterval.contains_add
    (Enclosure.contains_atan (atan2Reduction x y).1 degree)
    (RationalInterval.contains_scale (Enclosure.contains_piQuarter degree)
      (atan2Reduction x y).2)

/-- Lower rational argument endpoints converge to the exact principal value. -/
theorem tendsto_atan2Interval_lo (x y : ℚ) :
    Tendsto (fun n => ((atan2Interval x y n).lo : ℝ)) atTop
      (𝓝 (Complex.arg ⟨(x : ℝ), (y : ℝ)⟩)) := by
  rw [← atan2Reduction_eq_arg]
  exact RationalInterval.tendsto_add_lo (Enclosure.tendsto_atan_lo (atan2Reduction x y).1)
    (RationalInterval.tendsto_scale_lo Enclosure.tendsto_piQuarter_lo
      Enclosure.tendsto_piQuarter_hi (atan2Reduction x y).2)

/-- Upper rational argument endpoints converge to the exact principal value. -/
theorem tendsto_atan2Interval_hi (x y : ℚ) :
    Tendsto (fun n => ((atan2Interval x y n).hi : ℝ)) atTop
      (𝓝 (Complex.arg ⟨(x : ℝ), (y : ℝ)⟩)) := by
  rw [← atan2Reduction_eq_arg]
  exact RationalInterval.tendsto_add_hi (Enclosure.tendsto_atan_hi (atan2Reduction x y).1)
    (RationalInterval.tendsto_scale_hi Enclosure.tendsto_piQuarter_lo
      Enclosure.tendsto_piQuarter_hi (atan2Reduction x y).2)

/-- A rational complex point outside the nonnegative real axis has no rational argument. -/
theorem arg_ne_ratCast (x y boundary : ℚ) (hnonzero : ¬ (0 ≤ x ∧ y = 0)) :
    Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ ≠ (boundary : ℝ) := by
  intro hequal
  by_cases hboundary : boundary = 0
  · subst boundary
    have hz := (Complex.arg_eq_zero_iff (z := ⟨(x : ℝ), (y : ℝ)⟩)).mp
      (by simpa only [Rat.cast_zero] using hequal)
    dsimp only [Complex.re, Complex.im] at hz
    apply hnonzero
    constructor
    · exact_mod_cast hz.1
    · exact_mod_cast hz.2
  · apply (Enclosure.irrational_tan_ratCast boundary hboundary).ne_rat (y / x)
    rw [← hequal, Complex.tan_arg, Rat.cast_div]

/-- Refinement eventually separates every rational boundary away from the exact zero branch. -/
theorem exists_atan2_separating (x y boundary : ℚ) (hnonzero : ¬ (0 ≤ x ∧ y = 0)) :
    ∃ n, Enclosure.Comparison.Separates (atan2Interval x y (2 ^ n)) boundary :=
  Enclosure.Comparison.exists_separating_two_pow boundary (arg_ne_ratCast x y boundary hnonzero)
    (tendsto_atan2Interval_lo x y)
    (tendsto_atan2Interval_hi x y)

end FloatLib.Numerics.TrigonometricComparison
