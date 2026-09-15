/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.RationalPower.Runtime
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real correctness of rational-power comparisons

Raising a nonnegative real value to a positive integer power preserves strict and non-strict
order. Clearing the rational exponent denominator therefore turns comparison with an algebraic
real power into an exact rational computation, including equality cases.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalPower

/-- Clearing the exponent denominator gives an exact rational integer power. -/
theorem rpow_pow_den (base exponent : ℚ) (hbase : 0 < base) :
    ((base : ℝ) ^ (exponent : ℝ)) ^ exponent.den = ((base ^ exponent.num : ℚ) : ℝ) := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  have hden : (exponent.den : ℝ) ≠ 0 := by exact_mod_cast exponent.den_ne_zero
  have hexponent : (exponent : ℝ) * exponent.den = exponent.num := by
    rw [Rat.cast_def, div_mul_cancel₀ _ hden]
  rw [← Real.rpow_mul_natCast hbaseReal.le, hexponent, Real.rpow_intCast]
  norm_cast

/-- The executable strict comparison has the usual real-power meaning. -/
theorem pow_num_lt_pow_den_iff (base exponent target : ℚ)
    (hbase : 0 < base) (htarget : 0 ≤ target) :
    base ^ exponent.num < target ^ exponent.den ↔
      (base : ℝ) ^ (exponent : ℝ) < (target : ℝ) := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  have htargetReal : 0 ≤ (target : ℝ) := by exact_mod_cast htarget
  have hpower := rpow_pow_den base exponent hbase
  push_cast at hpower
  rw [← Rat.cast_lt (K := ℝ)]
  push_cast
  rw [← hpower,
    pow_lt_pow_iff_left₀ (Real.rpow_pos_of_pos hbaseReal _).le
      htargetReal exponent.den_ne_zero]

/-- Reversing the executable strict comparison reverses the real-power comparison. -/
theorem pow_den_lt_pow_num_iff (base exponent target : ℚ)
    (hbase : 0 < base) (htarget : 0 ≤ target) :
    target ^ exponent.den < base ^ exponent.num ↔
      (target : ℝ) < (base : ℝ) ^ (exponent : ℝ) := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  have htargetReal : 0 ≤ (target : ℝ) := by exact_mod_cast htarget
  have hpower := rpow_pow_den base exponent hbase
  push_cast at hpower
  rw [← Rat.cast_lt (K := ℝ)]
  push_cast
  rw [← hpower,
    pow_lt_pow_iff_left₀ htargetReal
      (Real.rpow_pos_of_pos hbaseReal _).le exponent.den_ne_zero]

/-- The non-strict executable comparison also handles exact equality. -/
theorem pow_num_le_pow_den_iff (base exponent target : ℚ)
    (hbase : 0 < base) (htarget : 0 ≤ target) :
    base ^ exponent.num ≤ target ^ exponent.den ↔
      (base : ℝ) ^ (exponent : ℝ) ≤ (target : ℝ) := by
  simpa only [not_lt] using not_congr (pow_den_lt_pow_num_iff base exponent target hbase htarget)

/-- The rational comparator returns exactly the ordering of the real power and target. -/
theorem compare_eq_real (base exponent target : ℚ)
    (hbase : 0 < base) (htarget : 0 ≤ target) :
    compare base exponent target = cmp ((base : ℝ) ^ (exponent : ℝ)) (target : ℝ) := by
  simp only [compare, cmp, cmpUsing,
    pow_num_lt_pow_den_iff base exponent target hbase htarget,
    pow_den_lt_pow_num_iff base exponent target hbase htarget]

end FloatLib.Numerics.RationalPower
