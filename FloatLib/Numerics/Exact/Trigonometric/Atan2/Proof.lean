/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Runtime
public import FloatLib.Numerics.Exact.Trigonometric.Pi.Proof

/-!
# Real semantics of two-coordinate arctangent comparisons

Both prepared and uncached comparators agree with the principal complex argument for every
rational pair and rational boundary. The mathematical convention at `(0, 0)` is zero; the
Posit invalid-input policy belongs to the format wrapper. Exact pi-scaled quadrant and
diagonal values are included in the comparison contract.
-/

public section

namespace FloatLib.Numerics.TrigonometricComparison

/-- Prepared radian comparisons agree with the exact principal complex argument. -/
theorem prepareAtan2_eq_real (x y : ℚ) (levels : Nat) (boundary : ℚ) :
    (prepareAtan2 x y levels).compare boundary =
      cmp (Complex.arg ⟨(x : ℝ), (y : ℝ)⟩) (boundary : ℝ) := by
  rw [prepareAtan2]
  split
  · rename_i hzero
    have harg : Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ = 0 := by
      apply Complex.arg_eq_zero_iff.mpr
      change (0 : ℝ) ≤ (x : ℝ) ∧ (y : ℝ) = 0
      exact ⟨by exact_mod_cast hzero.1, by exact_mod_cast hzero.2⟩
    simp [Enclosure.Comparison.Prepared.compare, harg, cmp, cmpUsing]
  · rw [Enclosure.Comparison.Prepared.compare]
    apply Enclosure.Comparison.compare_eq_real
    intro n
    simp only [Enclosure.Comparison.cacheIntervals_apply]
    exact contains_atan2Interval x y (2 ^ n)

/-- Radian comparisons use the exact principal branch, with no restriction on rational inputs. -/
theorem compareAtan2_eq_real (x y boundary : ℚ) :
    compareAtan2 x y boundary =
      cmp (Complex.arg ⟨(x : ℝ), (y : ℝ)⟩) (boundary : ℝ) :=
  prepareAtan2_eq_real x y 0 boundary

/-- Prepared pi-scaled comparisons preserve the exact quadrant shift and every equality case. -/
theorem prepareAtan2Pi_eq_real (x y : ℚ) (levels : Nat) (boundary : ℚ) :
    (prepareAtan2Pi x y levels).compare boundary =
      cmp (Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ / Real.pi) (boundary : ℝ) := by
  rw [prepareAtan2Pi, Enclosure.Comparison.Prepared.compare, prepareArctanPi_eq_real,
    ← atan2Reduction_eq_arg]
  push_cast
  have hshift :
      (Real.arctan ((atan2Reduction x y).1 : ℝ) +
          ((atan2Reduction x y).2 : ℝ) * (Real.pi / 4)) / Real.pi =
        Real.arctan ((atan2Reduction x y).1 : ℝ) / Real.pi +
          ((atan2Reduction x y).2 : ℝ) / 4 := by
    field_simp
  rw [hshift]
  simp only [cmp, cmpUsing, lt_sub_iff_add_lt, sub_lt_iff_lt_add]

/-- Pi-scaled comparisons agree with the exact argument divided by π. -/
theorem compareAtan2Pi_eq_real (x y boundary : ℚ) :
    compareAtan2Pi x y boundary =
      cmp (Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ / Real.pi) (boundary : ℝ) :=
  prepareAtan2Pi_eq_real x y 0 boundary

end FloatLib.Numerics.TrigonometricComparison
