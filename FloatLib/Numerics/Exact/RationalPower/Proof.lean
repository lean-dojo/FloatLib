/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.RationalPower.Runtime

/-!
# Real correctness of rational-power comparisons

The exact equality test is complete for positive bases, and the logarithm enclosures contain the
exact difference. Since the logarithm is strictly increasing on positive values, the sign of that
difference is the ordering of the power and the target. Zero bases, unit bases and zero exponents
are covered by direct evaluation.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalPower

/-- Comparing two rationals is comparing their real casts. -/
private theorem cmp_ratCast (value target : ℚ) :
    cmp value target = cmp (value : ℝ) (target : ℝ) := by
  have hlt : value < target ↔ (value : ℝ) < target := by norm_cast
  have hgt : target < value ↔ (target : ℝ) < value := by norm_cast
  simp only [cmp, cmpUsing, hlt, hgt]

/-- For every `base ≥ 0`, `compare` returns the ordering of the real power and the target. -/
theorem compare_eq_real (base exponent target : ℚ) (hbase : 0 ≤ base) :
    compare base exponent target = cmp ((base : ℝ) ^ (exponent : ℝ)) (target : ℝ) := by
  unfold compare
  split
  · rename_i hunit
    have hpower : (base : ℝ) ^ (exponent : ℝ) = ((1 : ℚ) : ℝ) := by
      rcases hunit with rfl | rfl <;> simp
    rw [hpower, cmp_ratCast]
  · rename_i hunit
    split
    · rename_i hpositive
      have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hpositive
      split
      · rename_i htarget
        have htargetReal : 0 < (target : ℝ) := by exact_mod_cast htarget
        split
        · rename_i hequal
          rw [(powEq_iff base exponent target hpositive).mp hequal, cmp_self_eq_eq]
        · rw [Enclosure.Comparison.compare_eq_real _ _ _ _
            (fun level => contains_logDifference base exponent target (2 ^ level)
              hpositive htarget), Rat.cast_zero, cmp_sub_zero]
          simp only [cmp, cmpUsing,
            Real.log_lt_log_iff (Real.rpow_pos_of_pos hbaseReal _) htargetReal,
            Real.log_lt_log_iff htargetReal (Real.rpow_pos_of_pos hbaseReal _)]
      · rename_i htarget
        have htargetReal : (target : ℝ) ≤ 0 := by exact_mod_cast le_of_not_gt htarget
        exact ((cmp_eq_gt_iff _ _).mpr
          (htargetReal.trans_lt (Real.rpow_pos_of_pos hbaseReal _))).symm
    · rename_i hpositive
      have hzero : base = 0 := le_antisymm (le_of_not_gt hpositive) hbase
      have hexponent : (exponent : ℝ) ≠ 0 := by
        exact_mod_cast fun h => hunit (Or.inr h)
      rw [hzero, Rat.cast_zero, Real.zero_rpow hexponent, cmp_ratCast, Rat.cast_zero]

end FloatLib.Numerics.RationalPower
