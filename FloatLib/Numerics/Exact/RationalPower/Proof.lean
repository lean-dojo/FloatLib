/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.RationalPower.Runtime

/-!
# Real correctness of rational-power comparisons

For positive bases the exact equality test is complete, and the logarithm enclosures contain the
exact difference. The logarithm is strictly increasing on positive values, so the sign of that
difference is the ordering of the power and the target. A direct comparison raises both sides to
the exponent's denominator, which keeps their order (`cmp_intPow_pow`). Zero bases, unit bases, and
zero exponents are covered by evaluation.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalPower

/-- Comparing two rationals is comparing their real casts. -/
private theorem cmp_ratCast (value target : ℚ) :
    cmp value target = cmp (value : ℝ) (target : ℝ) := by
  have hlt : value < target ↔ (value : ℝ) < target := by norm_cast
  have hgt : target < value ↔ (target : ℝ) < value := by norm_cast
  simp only [cmp, cmpUsing, hlt, hgt]

/-- `intPow` is the integer power. -/
theorem intPow_eq_zpow (base : ℚ) (exponent : ℤ) : intPow base exponent = base ^ exponent := by
  unfold intPow
  split
  · rename_i hnonneg
    conv_rhs => rw [← Int.toNat_of_nonneg hnonneg]
    rw [zpow_natCast]
  · rename_i hnegative
    have hexponent : exponent = -(exponent.natAbs : ℤ) := by omega
    conv_rhs => rw [hexponent]
    rw [zpow_neg, zpow_natCast, inv_pow]

/-- For a positive base and target and an exponent `n / d` in lowest terms, the order of
`base ^ n` and `target ^ d` is the order of the real power `base ^ (n / d)` and the target. -/
theorem cmp_intPow_pow (base exponent target : ℚ) (hbase : 0 < base) (htarget : 0 < target) :
    cmp (intPow base exponent.num) (target ^ exponent.den) =
      cmp ((base : ℝ) ^ (exponent : ℝ)) (target : ℝ) := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  have htargetReal : 0 < (target : ℝ) := by exact_mod_cast htarget
  have hden : (exponent.den : ℝ) ≠ 0 := by exact_mod_cast exponent.den_nz
  have hscaled : (exponent : ℝ) * (exponent.den : ℝ) = ((exponent.num : ℤ) : ℝ) := by
    rw [Rat.cast_def, div_mul_cancel₀ _ hden]
  have hpower : ((base : ℝ) ^ (exponent : ℝ)) ^ exponent.den = (base : ℝ) ^ exponent.num := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbaseReal.le, hscaled, Real.rpow_intCast]
  have hpositive := Real.rpow_pos_of_pos hbaseReal (exponent : ℝ)
  rw [cmp_ratCast, intPow_eq_zpow, Rat.cast_zpow, Rat.cast_pow, ← hpower]
  simp only [cmp, cmpUsing,
    pow_lt_pow_iff_left₀ hpositive.le htargetReal.le exponent.den_nz,
    pow_lt_pow_iff_left₀ htargetReal.le hpositive.le exponent.den_nz]

/-- For a positive base and target, the search returns the ordering of the real power and the
target. -/
theorem searchCompare_eq_real (base exponent target : ℚ) (hbase : 0 < base)
    (htarget : 0 < target) :
    searchCompare base exponent target hbase htarget =
      cmp ((base : ℝ) ^ (exponent : ℝ)) (target : ℝ) := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  have htargetReal : 0 < (target : ℝ) := by exact_mod_cast htarget
  unfold searchCompare
  split
  · rename_i hequal
    rw [(powEq_iff base exponent target hbase).mp hequal, cmp_self_eq_eq]
  · rw [Enclosure.Comparison.compare_eq_real _ _ _ _
      (fun level => contains_logDifference base exponent target (2 ^ level)
        hbase htarget), Rat.cast_zero, cmp_sub_zero]
    simp only [cmp, cmpUsing,
      Real.log_lt_log_iff (Real.rpow_pos_of_pos hbaseReal _) htargetReal,
      Real.log_lt_log_iff htargetReal (Real.rpow_pos_of_pos hbaseReal _)]

/-- For every `base ≥ 0`, `compare` returns the ordering of the real power and the target. At
`base = 0` with a negative exponent the real power is Mathlib's `0 ^ y = 0`, not a pole, so callers
that need the pole handle that case first. -/
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
        split
        · exact cmp_intPow_pow base exponent target hpositive htarget
        · exact searchCompare_eq_real base exponent target hpositive htarget
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
