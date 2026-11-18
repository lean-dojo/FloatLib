/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Softplus.Runtime

/-!
# Real semantics of the Softplus comparator

Exponentiation and positive scaling preserve the comparison ordering.
The remaining branches use the strict lower bounds zero and the argument.
-/

public section

namespace FloatLib.Numerics.Softplus

/-- Dividing the exponentiated comparison by `exp(boundary)` preserves its ordering. -/
theorem cmp_log_one_add_exp (argument boundary : ℝ) :
    cmp (Real.log (1 + Real.exp argument)) boundary =
      cmp (Real.exp (argument - boundary) + Real.exp (-boundary)) 1 := by
  rw [← Real.exp_strictMono.cmp_map_eq, Real.exp_log (by positivity)]
  rw [← cmp_mul_pos_right (Real.exp_pos (-boundary))]
  simp only [add_mul, one_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    ← sub_eq_add_neg]
  rw [add_comm]

/-- The exact rational algorithm returns the real ordering of Softplus at every boundary. -/
theorem compare_eq_real (argument boundary : ℚ) :
    compare argument boundary = cmp (Real.log (1 + Real.exp (argument : ℝ))) (boundary : ℝ) := by
  unfold compare
  split
  · rename_i hpositive
    split
    · rename_i habove
      rw [Enclosure.Comparison.compare_eq_real _ _ _
        (Real.exp ((argument - boundary : ℚ) : ℝ) + Real.exp ((-boundary : ℚ) : ℝ))
        (fun level => contains_interval argument boundary (2 ^ level))]
      simpa only [Rat.cast_sub, Rat.cast_neg, Rat.cast_one] using
        (cmp_log_one_add_exp (argument : ℝ) (boundary : ℝ)).symm
    · rename_i habove
      have hle : (boundary : ℝ) ≤ (argument : ℝ) := by exact_mod_cast (le_of_not_gt habove)
      have hlt : (argument : ℝ) < Real.log (1 + Real.exp (argument : ℝ)) :=
        (Real.lt_log_iff_exp_lt (by positivity)).mpr (by linarith)
      have h := hle.trans_lt hlt
      simp [cmp, cmpUsing, h, not_lt_of_ge h.le]
  · rename_i hpositive
    have hle : (boundary : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hpositive)
    have hlt : 0 < Real.log (1 + Real.exp (argument : ℝ)) :=
      Real.log_pos (by linarith [Real.exp_pos (argument : ℝ)])
    have h := hle.trans_lt hlt
    simp [cmp, cmpUsing, h, not_lt_of_ge h.le]

end FloatLib.Numerics.Softplus
