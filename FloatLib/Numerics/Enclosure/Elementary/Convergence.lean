/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Proof
public import FloatLib.Numerics.Enclosure.Rational.AffineConvergence
public import FloatLib.Numerics.Enclosure.Rational.Convergence
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Order.Floor

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

/--
For `|x| ≤ 1` and positive degree `n`, the exponential remainder radius is at most `2 / n`. This is
an explicit rate, unlike `tendsto_expRadius`: degree `n ≥ 2 / ε` gives radius at most `ε`.
-/
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

/--
Increasing the Taylor degree drives the exponential remainder bound to zero, for every rational
argument: factorial growth beats any fixed power.
-/
theorem tendsto_expRadius (x : ℚ) :
    Tendsto (fun n : Nat => (expRadius x (n + 1) : ℝ)) atTop (𝓝 0) := by
  have hfactorial := (FloorSemiring.tendsto_pow_div_factorial_atTop |(x : ℝ)|).comp
    (tendsto_add_atTop_nat 1)
  refine squeeze_zero
    (g := fun n : Nat => 2 * (|(x : ℝ)| ^ (n + 1) / ((n + 1).factorial : ℝ)))
    (fun n => ?_) (fun n => ?_) ?_
  · rw [cast_expRadius]
    positivity
  · rw [cast_expRadius]
    have hsize : (((n + 1 + 1 : Nat)) : ℝ) / ((n + 1 : Nat) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      push_cast
      linarith
    have hterm : 0 ≤ |(x : ℝ)| ^ (n + 1) / ((n + 1).factorial : ℝ) := by positivity
    calc
      |(x : ℝ)| ^ (n + 1) * (((n + 1 + 1 : Nat)) : ℝ) /
          (((n + 1).factorial : ℝ) * ((n + 1 : Nat) : ℝ)) =
          |(x : ℝ)| ^ (n + 1) / ((n + 1).factorial : ℝ) *
            ((((n + 1 + 1 : Nat)) : ℝ) / ((n + 1 : Nat) : ℝ)) := by ring
      _ ≤ |(x : ℝ)| ^ (n + 1) / ((n + 1).factorial : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left hsize hterm
      _ = 2 * (|(x : ℝ)| ^ (n + 1) / ((n + 1).factorial : ℝ)) := by ring
  · simpa [Function.comp_def] using hfactorial.const_mul 2

/-- The logarithm remainder is a decaying geometric sequence on its convergence interval. -/
theorem tendsto_logOneSubRadius (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => (logOneSubRadius x n : ℝ)) atTop (𝓝 0) := by
  have hreal : |(x : ℝ)| < 1 := by exact_mod_cast hx
  have hpower :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg (x : ℝ)) hreal).mul_const
      |(x : ℝ)|
  simpa [logOneSubRadius, pow_succ] using hpower.div_const (1 - |(x : ℝ)|)

/--
The exact rational exponential polynomials converge to the real exponential at every rational
argument.
-/
theorem tendsto_expTaylor (x : ℚ) :
    Tendsto (fun n : Nat => (expTaylor x (n + 1) : ℝ)) atTop
      (𝓝 (Real.exp (x : ℝ))) := by
  have hsum := (NormedSpace.expSeries_div_hasSum_exp (x : ℝ)).tendsto_sum_nat
  rw [← Real.exp_eq_exp_ℝ] at hsum
  simpa [cast_expTaylor, Function.comp_def] using hsum.comp (tendsto_add_atTop_nat 1)

/-- The lower small-exponential endpoints converge to the exact target. -/
theorem tendsto_expSmall_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((expSmall x n).lo : ℝ)) atTop
      (𝓝 (Real.exp (x : ℝ))) :=
  RationalInterval.tendsto_around_lo (tendsto_expTaylor x) (tendsto_expRadius x)

/-- The upper small-exponential endpoints converge to the exact target. -/
theorem tendsto_expSmall_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((expSmall x n).hi : ℝ)) atTop
      (𝓝 (Real.exp (x : ℝ))) :=
  RationalInterval.tendsto_around_hi (tendsto_expTaylor x) (tendsto_expRadius x)

/-- After argument reduction, the lower exponential endpoints still approach the exact value. -/
theorem tendsto_exp_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((exp x n).lo : ℝ)) atTop
      (𝓝 (Real.exp (x : ℝ))) := by
  have hsmall := tendsto_expSmall_lo (x / 2 ^ expScale x)
  simpa only [exp, exp_reduced_pow] using
    RationalInterval.tendsto_squareRepeat_lo hsmall (Real.exp_pos _).le (expScale x)

/-- After argument reduction, the upper exponential endpoints still approach the exact value. -/
theorem tendsto_exp_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((exp x n).hi : ℝ)) atTop
      (𝓝 (Real.exp (x : ℝ))) := by
  have hsmall := tendsto_expSmall_hi (x / 2 ^ expScale x)
  simpa only [exp, exp_reduced_pow] using
    RationalInterval.tendsto_squareRepeat_hi hsmall (expScale x)

/-- The signed rational logarithm polynomials converge to the exact logarithm. -/
theorem tendsto_neg_logOneSubTaylor (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => -(logOneSubTaylor x n : ℝ)) atTop
      (𝓝 (Real.log (1 - (x : ℝ)))) :=
  RationalInterval.tendsto_of_abs_sub_le
    (fun n => by simpa only [sub_neg_eq_add] using abs_log_add_logOneSubTaylor_le x n hx)
    (tendsto_logOneSubRadius x hx)

/-- The lower logarithm-series endpoints converge to the exact target. -/
theorem tendsto_logOneSub_lo (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => ((logOneSub x n).lo : ℝ)) atTop
      (𝓝 (Real.log (1 - (x : ℝ)))) :=
  RationalInterval.tendsto_around_lo (by simpa using tendsto_neg_logOneSubTaylor x hx)
    (tendsto_logOneSubRadius x hx)

/-- The upper logarithm-series endpoints converge to the exact target. -/
theorem tendsto_logOneSub_hi (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => ((logOneSub x n).hi : ℝ)) atTop
      (𝓝 (Real.log (1 - (x : ℝ)))) :=
  RationalInterval.tendsto_around_hi (by simpa using tendsto_neg_logOneSubTaylor x hx)
    (tendsto_logOneSubRadius x hx)

/-- The lower logarithm endpoints converge for every positive rational argument. -/
theorem tendsto_logSeries_lo (x : ℚ) (hx : 0 < x) :
    Tendsto (fun n : Nat => ((logSeries x n).lo : ℝ)) atTop
      (𝓝 (Real.log (x : ℝ))) := by
  have ht := abs_log_argument_lt_one x hx
  have h := RationalInterval.tendsto_sub_lo
    (tendsto_logOneSub_lo (-((x - 1) / (x + 1))) (by simpa using ht)) (tendsto_logOneSub_hi _ ht)
  rwa [Rat.cast_neg, sub_neg_eq_add, log_argument_identity x hx] at h

/-- The upper logarithm endpoints converge for every positive rational argument. -/
theorem tendsto_logSeries_hi (x : ℚ) (hx : 0 < x) :
    Tendsto (fun n : Nat => ((logSeries x n).hi : ℝ)) atTop
      (𝓝 (Real.log (x : ℝ))) := by
  have ht := abs_log_argument_lt_one x hx
  have h := RationalInterval.tendsto_sub_hi
    (tendsto_logOneSub_hi (-((x - 1) / (x + 1))) (by simpa using ht)) (tendsto_logOneSub_lo _ ht)
  rwa [Rat.cast_neg, sub_neg_eq_add, log_argument_identity x hx] at h

/-- The lower endpoints retain convergence after binary logarithm reduction. -/
theorem tendsto_logLarge_lo (x : ℚ) (hx : 0 < x) :
    Tendsto (fun n : Nat => ((logLarge x n).lo : ℝ)) atTop
      (𝓝 (Real.log (x : ℝ))) := by
  have h := RationalInterval.tendsto_add_lo
    (tendsto_logSeries_lo (x / 2 ^ logScale x) (by positivity))
    (RationalInterval.tendsto_scaleNonnegative_lo (tendsto_logSeries_lo 2 (by norm_num))
      (logScale x))
  rwa [Rat.cast_natCast, Rat.cast_ofNat, log_reduction_identity x hx] at h

/-- The upper endpoints retain convergence after binary logarithm reduction. -/
theorem tendsto_logLarge_hi (x : ℚ) (hx : 0 < x) :
    Tendsto (fun n : Nat => ((logLarge x n).hi : ℝ)) atTop
      (𝓝 (Real.log (x : ℝ))) := by
  have h := RationalInterval.tendsto_add_hi
    (tendsto_logSeries_hi (x / 2 ^ logScale x) (by positivity))
    (RationalInterval.tendsto_scaleNonnegative_hi (tendsto_logSeries_hi 2 (by norm_num))
      (logScale x))
  rwa [Rat.cast_natCast, Rat.cast_ofNat, log_reduction_identity x hx] at h

/-- The lower reduced-logarithm endpoints converge for every positive rational argument. -/
theorem tendsto_log_lo (x : ℚ) (hx : 0 < x) :
    Tendsto (fun n : Nat => ((log x n).lo : ℝ)) atTop
      (𝓝 (Real.log (x : ℝ))) := by
  by_cases hlt : x < 1
  · simpa only [log, ite_eq_left hlt, Rat.cast_inv, Real.log_inv, neg_neg] using
      RationalInterval.tendsto_neg_lo (tendsto_logLarge_hi x⁻¹ (inv_pos.mpr hx))
  · simpa only [log, ite_eq_right hlt] using tendsto_logLarge_lo x hx

/-- The upper reduced-logarithm endpoints converge for every positive rational argument. -/
theorem tendsto_log_hi (x : ℚ) (hx : 0 < x) :
    Tendsto (fun n : Nat => ((log x n).hi : ℝ)) atTop
      (𝓝 (Real.log (x : ℝ))) := by
  by_cases hlt : x < 1
  · simpa only [log, ite_eq_left hlt, Rat.cast_inv, Real.log_inv, neg_neg] using
      RationalInterval.tendsto_neg_hi (tendsto_logLarge_lo x⁻¹ (inv_pos.mpr hx))
  · simpa only [log, ite_eq_right hlt] using tendsto_logLarge_hi x hx

end FloatLib.Numerics.Enclosure
