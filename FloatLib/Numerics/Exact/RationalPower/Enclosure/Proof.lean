/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.RationalPower.Enclosure.Runtime
public import FloatLib.Numerics.Exact.RationalPower.Proof
public import FloatLib.Numerics.Enclosure.Elementary.Proof

/-!
# Correctness of power comparison from logarithm bounds

The real logarithm is strictly increasing on positive values. Consequently a strict sign
certificate for the logarithm difference determines the original comparison. When no such
certificate is available, the exact denominator-clearing theorem supplies the result.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalPower

open RationalInterval

/-- The executable interval contains the exact difference of real logarithms. -/
theorem contains_logDifference (base exponent target : ℚ) (degree : Nat)
    (hbase : 0 < base) (htarget : 0 < target) :
    (logDifference base exponent target degree).Contains
      (Real.log ((base : ℝ) ^ (exponent : ℝ)) - Real.log (target : ℝ)) := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  simpa only [logDifference, Real.log_rpow hbaseReal] using
    contains_sub (contains_scale (Enclosure.contains_log base degree hbase) exponent)
      (Enclosure.contains_log target degree htarget)

/-- A strictly negative upper bound proves that the real power is below the target. -/
theorem rpow_lt_of_logDifference_hi_neg (base exponent target : ℚ) (degree : Nat)
    (hbase : 0 < base) (htarget : 0 < target)
    (hnegative : (logDifference base exponent target degree).hi < 0) :
    (base : ℝ) ^ (exponent : ℝ) < (target : ℝ) := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  have htargetReal : 0 < (target : ℝ) := by exact_mod_cast htarget
  have hbound := (contains_logDifference base exponent target degree hbase htarget).2
  have hnegativeReal : ((logDifference base exponent target degree).hi : ℝ) < 0 := by
    exact_mod_cast hnegative
  apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hbaseReal _) htargetReal).mp
  linarith

/-- A strictly positive lower bound proves that the target is below the real power. -/
theorem lt_rpow_of_logDifference_lo_pos (base exponent target : ℚ) (degree : Nat)
    (hbase : 0 < base) (htarget : 0 < target)
    (hpositive : 0 < (logDifference base exponent target degree).lo) :
    (target : ℝ) < (base : ℝ) ^ (exponent : ℝ) := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  have htargetReal : 0 < (target : ℝ) := by exact_mod_cast htarget
  have hbound := (contains_logDifference base exponent target degree hbase htarget).1
  have hpositiveReal : (0 : ℝ) < (logDifference base exponent target degree).lo := by
    exact_mod_cast hpositive
  apply (Real.log_lt_log_iff htargetReal (Real.rpow_pos_of_pos hbaseReal _)).mp
  linarith

/-- The bounds and exact fallback together always return the real-power ordering. -/
theorem compareWithEnclosure_eq_real (base exponent target : ℚ) (degree : Nat)
    (hbase : 0 < base) :
    compareWithEnclosure base exponent target degree =
      cmp ((base : ℝ) ^ (exponent : ℝ)) (target : ℝ) := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  unfold compareWithEnclosure
  split
  · rename_i hunit
    have hpower : (base : ℝ) ^ (exponent : ℝ) = 1 := by
      rcases hunit with rfl | rfl <;> simp
    rw [hpower]
    have hlt : (1 : ℚ) < target ↔ (1 : ℝ) < target := by norm_cast
    have hgt : target < (1 : ℚ) ↔ (target : ℝ) < 1 := by norm_cast
    simp only [cmp, cmpUsing, hlt, hgt]
  · split
    · rename_i htarget
      have htargetReal : (target : ℝ) ≤ 0 := by exact_mod_cast htarget
      exact (cmp_eq_gt_iff _ _).mpr
        (htargetReal.trans_lt (Real.rpow_pos_of_pos hbaseReal _)) |>.symm
    · rename_i htarget
      have ht : 0 < target := lt_of_not_ge htarget
      dsimp only
      split
      · rename_i hnegative
        exact (cmp_eq_lt_iff _ _).mpr
          (rpow_lt_of_logDifference_hi_neg base exponent target degree hbase ht hnegative) |>.symm
      · split
        · rename_i hpositive
          exact (cmp_eq_gt_iff _ _).mpr
            (lt_rpow_of_logDifference_lo_pos base exponent target degree hbase ht hpositive) |>.symm
        · exact compare_eq_real base exponent target hbase ht.le

end FloatLib.Numerics.RationalPower
