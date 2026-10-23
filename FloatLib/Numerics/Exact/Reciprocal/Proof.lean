/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Reciprocal.Runtime
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Order

/-!
# Real semantics of reciprocal comparisons

On each half-line, inversion is strictly decreasing, so comparing `t⁻¹` with a boundary `b` of the
same sign is comparing `b⁻¹` with `t`. Boundaries of the other sign are decided by the sign of `t`.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- Given an exact comparator for a nonzero real `t`, `compareReciprocal` compares `t⁻¹`. -/
theorem compareReciprocal_eq_real (compare : ℚ → Ordering) (t : ℝ) (ht : t ≠ 0)
    (hcompare : ∀ q : ℚ, compare q = cmp t (q : ℝ)) (boundary : ℚ) :
    compareReciprocal compare boundary = cmp t⁻¹ (boundary : ℝ) := by
  unfold compareReciprocal
  rw [hcompare 0, Rat.cast_zero]
  rcases lt_trichotomy t 0 with hnegative | hzero | hpositive
  · rw [(cmp_eq_lt_iff _ _).mpr hnegative]
    dsimp only
    split
    · rename_i hboundary
      have hboundaryReal : (0 : ℝ) ≤ boundary := by exact_mod_cast hboundary
      exact ((cmp_eq_lt_iff _ _).mpr
        ((inv_lt_zero.mpr hnegative).trans_le hboundaryReal)).symm
    · rename_i hboundary
      have hboundaryReal : (boundary : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hboundary
      rw [hcompare, cmp_swap, Rat.cast_inv]
      simp only [cmp, cmpUsing, (inv_lt_of_neg hnegative hboundaryReal).symm,
        lt_inv_of_neg hnegative hboundaryReal]
  · exact absurd hzero ht
  · rw [(cmp_eq_gt_iff _ _).mpr hpositive]
    dsimp only
    split
    · rename_i hboundary
      have hboundaryReal : (boundary : ℝ) ≤ 0 := by exact_mod_cast hboundary
      exact ((cmp_eq_gt_iff _ _).mpr (hboundaryReal.trans_lt (inv_pos.mpr hpositive))).symm
    · rename_i hboundary
      have hboundaryReal : (0 : ℝ) < boundary := by exact_mod_cast lt_of_not_ge hboundary
      rw [hcompare, cmp_swap, Rat.cast_inv]
      simp only [cmp, cmpUsing, (inv_lt_comm₀ hpositive hboundaryReal).symm,
        lt_inv_comm₀ hpositive hboundaryReal]

end FloatLib.Numerics
