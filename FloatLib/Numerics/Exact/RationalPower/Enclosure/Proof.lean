/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.RationalPower.Enclosure.Runtime
public import FloatLib.Numerics.Enclosure.Comparison.Proof
public import FloatLib.Numerics.Enclosure.Elementary.Convergence
public import FloatLib.Numerics.Enclosure.Rational.AffineConvergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Containment and refinement of rational-power logarithm bounds

The logarithm enclosures contain the exact logarithms, and their endpoints converge as the degree
grows. Scaling and subtraction preserve both properties. Doubling the degree therefore separates
the logarithm difference from zero whenever the power differs from the target, and the comparison
that relies on this decides the equality case beforehand.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalPower

open Filter RationalInterval
open scoped Topology

/-- The executable interval contains the exact difference of real logarithms. -/
theorem contains_logDifference (base exponent target : ℚ) (degree : Nat)
    (hbase : 0 < base) (htarget : 0 < target) :
    (logDifference base exponent target degree).Contains
      (Real.log ((base : ℝ) ^ (exponent : ℝ)) - Real.log (target : ℝ)) := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  simpa only [logDifference, Real.log_rpow hbaseReal] using
    contains_sub (contains_scale (Enclosure.contains_log base degree hbase) exponent)
      (Enclosure.contains_log target degree htarget)

/-- Lower endpoints converge to the exact logarithm difference. -/
theorem tendsto_logDifference_lo (base exponent target : ℚ)
    (hbase : 0 < base) (htarget : 0 < target) :
    Tendsto (fun degree : Nat => ((logDifference base exponent target degree).lo : ℝ)) atTop
      (𝓝 (Real.log ((base : ℝ) ^ (exponent : ℝ)) - Real.log (target : ℝ))) := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  rw [Real.log_rpow hbaseReal]
  exact tendsto_sub_lo
    (tendsto_scale_lo (Enclosure.tendsto_log_lo base hbase)
      (Enclosure.tendsto_log_hi base hbase) exponent)
    (Enclosure.tendsto_log_hi target htarget)

/-- Upper endpoints converge to the exact logarithm difference. -/
theorem tendsto_logDifference_hi (base exponent target : ℚ)
    (hbase : 0 < base) (htarget : 0 < target) :
    Tendsto (fun degree : Nat => ((logDifference base exponent target degree).hi : ℝ)) atTop
      (𝓝 (Real.log ((base : ℝ) ^ (exponent : ℝ)) - Real.log (target : ℝ))) := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  rw [Real.log_rpow hbaseReal]
  exact tendsto_sub_hi
    (tendsto_scale_hi (Enclosure.tendsto_log_lo base hbase)
      (Enclosure.tendsto_log_hi base hbase) exponent)
    (Enclosure.tendsto_log_lo target htarget)

/--
When the power differs from the target, doubling the degree eventually gives a logarithm bound
that excludes zero.
-/
theorem exists_logDifference_separating (base exponent target : ℚ)
    (hbase : 0 < base) (htarget : 0 < target)
    (hne : (base : ℝ) ^ (exponent : ℝ) ≠ (target : ℝ)) :
    ∃ level, Enclosure.Comparison.Separates (logDifference base exponent target (2 ^ level)) 0 := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  have htargetReal : 0 < (target : ℝ) := by exact_mod_cast htarget
  have hdifference :
      Real.log ((base : ℝ) ^ (exponent : ℝ)) - Real.log (target : ℝ) ≠ ((0 : ℚ) : ℝ) := by
    rw [Rat.cast_zero, sub_ne_zero]
    intro hlog
    exact hne (Real.log_injOn_pos (Real.rpow_pos_of_pos hbaseReal _) htargetReal hlog)
  exact Enclosure.Comparison.exists_separating 0 hdifference
    ((tendsto_logDifference_lo base exponent target hbase htarget).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))
    ((tendsto_logDifference_hi base exponent target hbase htarget).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide)))

end FloatLib.Numerics.RationalPower
