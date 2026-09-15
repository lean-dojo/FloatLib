/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Proof
public import FloatLib.Numerics.Enclosure.Rational.Convergence
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Refinement of rational Taylor enclosures

The computed error radii tend to zero as the degree increases. These results justify arbitrary
accuracy of the enclosures; deciding a rounded result also requires handling exact rounding
boundaries.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure

open Filter
open scoped Topology

/-- A coarse degree-dependent exponential bound, useful for proving convergence. -/
theorem expRadius_le_two_div (x : ℚ) (n : Nat) (hx : |x| ≤ 1) (hn : 0 < n) :
    expRadius x n ≤ 2 / (n : ℚ) := by
  have hnpos : (0 : ℚ) < n := by exact_mod_cast hn
  have hone : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hfactor : (n : ℚ) ≤ (n.factorial : ℚ) := by
    exact_mod_cast Nat.self_le_factorial n
  have hfactorpos : (0 : ℚ) < n.factorial := by positivity
  have hpow : |x| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have hnumerator : |x| ^ n * ((n + 1 : Nat) : ℚ) ≤ 2 * n := by
    calc
      _ ≤ 1 * ((n + 1 : Nat) : ℚ) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ 2 * n := by push_cast; linarith
  rw [expRadius, div_le_div_iff₀ (mul_pos hfactorpos hnpos) hnpos]
  calc
    _ ≤ ((2 : ℚ) * n) * n := mul_le_mul_of_nonneg_right hnumerator hnpos.le
    _ ≤ 2 * ((n.factorial : ℚ) * n) := by
      nlinarith [mul_le_mul_of_nonneg_right hfactor hnpos.le]

/-- Increasing the Taylor degree drives the exponential remainder bound to zero. -/
theorem tendsto_expRadius (x : ℚ) (hx : |x| ≤ 1) :
    Tendsto (fun n : Nat => (expRadius x (n + 1) : ℝ)) atTop (𝓝 0) := by
  refine squeeze_zero (g := fun n : Nat => 2 / ((n : ℝ) + 1))
    (fun n => ?_) (fun n => ?_) ?_
  · rw [cast_expRadius]
    positivity
  · have h := (Rat.cast_le (K := ℝ)).mpr
      (expRadius_le_two_div x (n + 1) hx (Nat.succ_pos n))
    simpa using h
  · simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

/-- The logarithm remainder is a decaying geometric sequence on its convergence interval. -/
theorem tendsto_logOneSubRadius (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => (logOneSubRadius x n : ℝ)) atTop (𝓝 0) := by
  have hreal : |(x : ℝ)| < 1 := by exact_mod_cast hx
  have hpower :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg (x : ℝ)) hreal).mul_const
      |(x : ℝ)|
  simpa [logOneSubRadius, pow_succ] using hpower.div_const (1 - |(x : ℝ)|)

/-- The exact rational exponential polynomials converge to the real exponential. -/
theorem tendsto_expTaylor (x : ℚ) (hx : |x| ≤ 1) :
    Tendsto (fun n : Nat => (expTaylor x (n + 1) : ℝ)) atTop
      (𝓝 (Real.exp (x : ℝ))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (tendsto_expRadius x hx)
  simpa [Real.dist_eq, abs_sub_comm] using abs_exp_sub_expTaylor_le x n hx

/-- The lower small-exponential endpoints converge to the exact target. -/
theorem tendsto_expSmall_lo (x : ℚ) (hx : |x| ≤ 1) :
    Tendsto (fun n : Nat => ((expSmall x n).lo : ℝ)) atTop
      (𝓝 (Real.exp (x : ℝ))) := by
  simpa [expSmall, RationalInterval.around] using
    (tendsto_expTaylor x hx).sub (tendsto_expRadius x hx)

/-- The upper small-exponential endpoints converge to the exact target. -/
theorem tendsto_expSmall_hi (x : ℚ) (hx : |x| ≤ 1) :
    Tendsto (fun n : Nat => ((expSmall x n).hi : ℝ)) atTop
      (𝓝 (Real.exp (x : ℝ))) := by
  simpa [expSmall, RationalInterval.around] using
    (tendsto_expTaylor x hx).add (tendsto_expRadius x hx)

/-- After argument reduction, the lower exponential endpoints still approach the exact value. -/
theorem tendsto_exp_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((exp x n).lo : ℝ)) atTop
      (𝓝 (Real.exp (x : ℝ))) := by
  have hsmall := tendsto_expSmall_lo (x / 2 ^ expScale x)
    (abs_div_expScale_lt_one x).le
  simpa only [exp, exp_reduced_pow] using
    RationalInterval.tendsto_squareRepeat_lo hsmall (Real.exp_pos _).le (expScale x)

/-- After argument reduction, the upper exponential endpoints still approach the exact value. -/
theorem tendsto_exp_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((exp x n).hi : ℝ)) atTop
      (𝓝 (Real.exp (x : ℝ))) := by
  have hsmall := tendsto_expSmall_hi (x / 2 ^ expScale x)
    (abs_div_expScale_lt_one x).le
  simpa only [exp, exp_reduced_pow] using
    RationalInterval.tendsto_squareRepeat_hi hsmall (expScale x)

/-- The signed rational logarithm polynomials converge to the exact logarithm. -/
theorem tendsto_neg_logOneSubTaylor (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => -(logOneSubTaylor x n : ℝ)) atTop
      (𝓝 (Real.log (1 - (x : ℝ)))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (tendsto_logOneSubRadius x hx)
  rw [Real.dist_eq, show -(logOneSubTaylor x n : ℝ) - Real.log (1 - (x : ℝ)) =
    -(Real.log (1 - (x : ℝ)) + (logOneSubTaylor x n : ℝ)) by ring, abs_neg]
  exact abs_log_add_logOneSubTaylor_le x n hx

/-- The lower logarithm-series endpoints converge to the exact target. -/
theorem tendsto_logOneSub_lo (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => ((logOneSub x n).lo : ℝ)) atTop
      (𝓝 (Real.log (1 - (x : ℝ)))) := by
  simpa [logOneSub, RationalInterval.around] using
    (tendsto_neg_logOneSubTaylor x hx).sub (tendsto_logOneSubRadius x hx)

/-- The upper logarithm-series endpoints converge to the exact target. -/
theorem tendsto_logOneSub_hi (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => ((logOneSub x n).hi : ℝ)) atTop
      (𝓝 (Real.log (1 - (x : ℝ)))) := by
  simpa [logOneSub, RationalInterval.around] using
    (tendsto_neg_logOneSubTaylor x hx).add (tendsto_logOneSubRadius x hx)

/-- The lower logarithm endpoints converge for every positive rational argument. -/
theorem tendsto_logSeries_lo (x : ℚ) (hx : 0 < x) :
    Tendsto (fun n : Nat => ((logSeries x n).lo : ℝ)) atTop
      (𝓝 (Real.log (x : ℝ))) := by
  let t : ℚ := (x - 1) / (x + 1)
  have ht : |t| < 1 := abs_log_argument_lt_one x hx
  have hfirst := tendsto_logOneSub_lo (-t) (by simpa using ht)
  have hsecond := tendsto_logOneSub_hi t ht
  simpa only [logSeries, t, RationalInterval.sub, RationalInterval.add, RationalInterval.neg,
    Rat.cast_add, Rat.cast_sub, Rat.cast_neg, ← sub_eq_add_neg, sub_neg_eq_add,
    log_argument_identity x hx] using hfirst.sub hsecond

/-- The upper logarithm endpoints converge for every positive rational argument. -/
theorem tendsto_logSeries_hi (x : ℚ) (hx : 0 < x) :
    Tendsto (fun n : Nat => ((logSeries x n).hi : ℝ)) atTop
      (𝓝 (Real.log (x : ℝ))) := by
  let t : ℚ := (x - 1) / (x + 1)
  have ht : |t| < 1 := abs_log_argument_lt_one x hx
  have hfirst := tendsto_logOneSub_hi (-t) (by simpa using ht)
  have hsecond := tendsto_logOneSub_lo t ht
  simpa only [logSeries, t, RationalInterval.sub, RationalInterval.add, RationalInterval.neg,
    Rat.cast_add, Rat.cast_sub, Rat.cast_neg, ← sub_eq_add_neg, sub_neg_eq_add,
    log_argument_identity x hx] using hfirst.sub hsecond

/-- The lower endpoints retain convergence after binary logarithm reduction. -/
theorem tendsto_logLarge_lo (x : ℚ) (hx : 0 < x) :
    Tendsto (fun n : Nat => ((logLarge x n).lo : ℝ)) atTop
      (𝓝 (Real.log (x : ℝ))) := by
  have hfirst := tendsto_logSeries_lo (x / 2 ^ logScale x) (by positivity)
  have hsecond := (tendsto_logSeries_lo 2 (by norm_num)).const_mul (logScale x : ℝ)
  simpa only [logLarge, RationalInterval.add, RationalInterval.scaleNonnegative,
    Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, log_reduction_identity x hx] using
    hfirst.add hsecond

/-- The upper endpoints retain convergence after binary logarithm reduction. -/
theorem tendsto_logLarge_hi (x : ℚ) (hx : 0 < x) :
    Tendsto (fun n : Nat => ((logLarge x n).hi : ℝ)) atTop
      (𝓝 (Real.log (x : ℝ))) := by
  have hfirst := tendsto_logSeries_hi (x / 2 ^ logScale x) (by positivity)
  have hsecond := (tendsto_logSeries_hi 2 (by norm_num)).const_mul (logScale x : ℝ)
  simpa only [logLarge, RationalInterval.add, RationalInterval.scaleNonnegative,
    Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, log_reduction_identity x hx] using
    hfirst.add hsecond

/-- The lower reduced-logarithm endpoints converge for every positive rational argument. -/
theorem tendsto_log_lo (x : ℚ) (hx : 0 < x) :
    Tendsto (fun n : Nat => ((log x n).lo : ℝ)) atTop
      (𝓝 (Real.log (x : ℝ))) := by
  by_cases hlt : x < 1
  · simpa only [log, if_pos hlt, RationalInterval.neg, Rat.cast_neg,
      Rat.cast_inv, Real.log_inv, neg_neg] using
      (tendsto_logLarge_hi x⁻¹ (inv_pos.mpr hx)).neg
  · simpa only [log, if_neg hlt] using tendsto_logLarge_lo x hx

/-- The upper reduced-logarithm endpoints converge for every positive rational argument. -/
theorem tendsto_log_hi (x : ℚ) (hx : 0 < x) :
    Tendsto (fun n : Nat => ((log x n).hi : ℝ)) atTop
      (𝓝 (Real.log (x : ℝ))) := by
  by_cases hlt : x < 1
  · simpa only [log, if_pos hlt, RationalInterval.neg, Rat.cast_neg,
      Rat.cast_inv, Real.log_inv, neg_neg] using
      (tendsto_logLarge_lo x⁻¹ (inv_pos.mpr hx)).neg
  · simpa only [log, if_neg hlt] using tendsto_logLarge_hi x hx

end FloatLib.Numerics.Enclosure
