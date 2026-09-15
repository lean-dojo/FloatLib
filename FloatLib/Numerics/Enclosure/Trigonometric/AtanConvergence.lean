/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.AtanProof
public import FloatLib.Numerics.Enclosure.Rational.Convergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergence of rational arctangent bounds

The geometric radius tends to zero on the open series domain. The exact reduction branches
depend only on the input, so interval addition, subtraction, scaling, and negation transfer
endpoint convergence to every rational argument.
-/

public section

namespace FloatLib.Numerics.Enclosure

open Filter
open scoped Topology

/-- The arctangent remainder tends to zero throughout the open series domain. -/
theorem tendsto_atanRadius (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => (atanRadius x (n + 1) : ℝ)) atTop (𝓝 0) := by
  have hreal : |(x : ℝ)| < 1 := by exact_mod_cast hx
  have hsq : (x : ℝ) ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one _).mpr hreal
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg (x : ℝ)) hsq).comp
    (tendsto_add_atTop_nat 1)
  simpa only [cast_atanRadius, Function.comp_def, mul_zero, zero_div] using
    (hp.const_mul |(x : ℝ)|).div_const (1 - (x : ℝ) ^ 2)

/-- Rational arctangent partial sums converge to the real arctangent. -/
theorem tendsto_atanTaylor (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => (atanTaylor x (n + 1) : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (tendsto_atanRadius x hx)
  simpa only [Real.dist_eq, abs_sub_comm] using abs_atan_sub_atanTaylor_le x (n + 1) hx

/-- The small arctangent lower endpoints converge to the exact value. -/
theorem tendsto_atanSmall_lo (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => ((atanSmall x n).lo : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  simpa [atanSmall, RationalInterval.around] using
    (tendsto_atanTaylor x hx).sub (tendsto_atanRadius x hx)

/-- The small arctangent upper endpoints converge to the exact value. -/
theorem tendsto_atanSmall_hi (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => ((atanSmall x n).hi : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  simpa [atanSmall, RationalInterval.around] using
    (tendsto_atanTaylor x hx).add (tendsto_atanRadius x hx)

/-- The lower rational bounds for π/4 approach π/4. -/
theorem tendsto_piQuarter_lo :
    Tendsto (fun n : Nat => ((piQuarter n).lo : ℝ)) atTop (𝓝 (Real.pi / 4)) := by
  simpa [piQuarter, RationalInterval.sub, RationalInterval.add, RationalInterval.neg,
    RationalInterval.scaleNonnegative, one_div, ← sub_eq_add_neg,
    Real.four_mul_arctan_inv_5_sub_arctan_inv_239] using
    ((tendsto_atanSmall_lo (1 / 5) (by norm_num)).const_mul 4).sub
      (tendsto_atanSmall_hi (1 / 239) (by norm_num))

/-- The upper rational bounds for π/4 approach π/4. -/
theorem tendsto_piQuarter_hi :
    Tendsto (fun n : Nat => ((piQuarter n).hi : ℝ)) atTop (𝓝 (Real.pi / 4)) := by
  simpa [piQuarter, RationalInterval.sub, RationalInterval.add, RationalInterval.neg,
    RationalInterval.scaleNonnegative, one_div, ← sub_eq_add_neg,
    Real.four_mul_arctan_inv_5_sub_arctan_inv_239] using
    ((tendsto_atanSmall_hi (1 / 5) (by norm_num)).const_mul 4).sub
      (tendsto_atanSmall_lo (1 / 239) (by norm_num))

/-- Arctangent reduction on `[0, 1]` preserves lower-endpoint convergence. -/
theorem tendsto_atanUnit_lo (x : ℚ) (hx : 0 ≤ x) (hone : x ≤ 1) :
    Tendsto (fun n : Nat => ((atanUnit x n).lo : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  by_cases h : x ≤ 1 / 2
  · have hsmall : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
    simpa only [atanUnit, if_pos h] using tendsto_atanSmall_lo x hsmall
  · have ht : |(x - 1) / (x + 1)| < 1 :=
      (abs_atan_unit_argument_le x (by linarith) hone).trans_lt (by norm_num)
    simpa only [atanUnit, if_neg h, RationalInterval.add, Rat.cast_add,
      atan_unit_identity x hx] using tendsto_piQuarter_lo.add
        (tendsto_atanSmall_lo ((x - 1) / (x + 1)) ht)

/-- Arctangent reduction on `[0, 1]` preserves upper-endpoint convergence. -/
theorem tendsto_atanUnit_hi (x : ℚ) (hx : 0 ≤ x) (hone : x ≤ 1) :
    Tendsto (fun n : Nat => ((atanUnit x n).hi : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  by_cases h : x ≤ 1 / 2
  · have hsmall : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
    simpa only [atanUnit, if_pos h] using tendsto_atanSmall_hi x hsmall
  · have ht : |(x - 1) / (x + 1)| < 1 :=
      (abs_atan_unit_argument_le x (by linarith) hone).trans_lt (by norm_num)
    simpa only [atanUnit, if_neg h, RationalInterval.add, Rat.cast_add,
      atan_unit_identity x hx] using tendsto_piQuarter_hi.add
        (tendsto_atanSmall_hi ((x - 1) / (x + 1)) ht)

private theorem atan_inversion_identity (x : ℚ) (hx : 0 < x) :
    2 * (Real.pi / 4) - Real.arctan ((x⁻¹ : ℚ) : ℝ) = Real.arctan (x : ℝ) := by
  have hreal : (0 : ℝ) < x := by exact_mod_cast hx
  rw [Rat.cast_inv, Real.arctan_inv_of_pos hreal]
  ring

/-- Inversion preserves lower-endpoint convergence for nonnegative inputs. -/
theorem tendsto_atanNonnegative_lo (x : ℚ) (hx : 0 ≤ x) :
    Tendsto (fun n : Nat => ((atanNonnegative x n).lo : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  by_cases h : x ≤ 1
  · simpa only [atanNonnegative, if_pos h] using tendsto_atanUnit_lo x hx h
  · have hi : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    simpa only [atanNonnegative, if_neg h, RationalInterval.sub, RationalInterval.add,
      RationalInterval.neg, RationalInterval.scaleNonnegative, Rat.cast_add, Rat.cast_neg,
      Rat.cast_mul, Rat.cast_ofNat, ← sub_eq_add_neg, Rat.cast_sub,
      atan_inversion_identity x (by linarith)] using
      (tendsto_piQuarter_lo.const_mul 2).sub
        (tendsto_atanUnit_hi x⁻¹ (inv_nonneg.mpr hx) hi)

/-- Inversion preserves upper-endpoint convergence for nonnegative inputs. -/
theorem tendsto_atanNonnegative_hi (x : ℚ) (hx : 0 ≤ x) :
    Tendsto (fun n : Nat => ((atanNonnegative x n).hi : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  by_cases h : x ≤ 1
  · simpa only [atanNonnegative, if_pos h] using tendsto_atanUnit_hi x hx h
  · have hi : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    simpa only [atanNonnegative, if_neg h, RationalInterval.sub, RationalInterval.add,
      RationalInterval.neg, RationalInterval.scaleNonnegative, Rat.cast_add, Rat.cast_neg,
      Rat.cast_mul, Rat.cast_ofNat, ← sub_eq_add_neg, Rat.cast_sub,
      atan_inversion_identity x (by linarith)] using
      (tendsto_piQuarter_hi.const_mul 2).sub
        (tendsto_atanUnit_lo x⁻¹ (inv_nonneg.mpr hx) hi)

/-- The lower enclosure endpoints converge for every rational arctangent input. -/
theorem tendsto_atan_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((atan x n).lo : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  by_cases h : x < 0
  · simpa only [atan, if_pos h, RationalInterval.neg, Rat.cast_neg,
      Real.arctan_neg, neg_neg] using (tendsto_atanNonnegative_hi (-x) (by linarith)).neg
  · simpa only [atan, if_neg h] using tendsto_atanNonnegative_lo x (by linarith)

/-- The upper enclosure endpoints converge for every rational arctangent input. -/
theorem tendsto_atan_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((atan x n).hi : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  by_cases h : x < 0
  · simpa only [atan, if_pos h, RationalInterval.neg, Rat.cast_neg,
      Real.arctan_neg, neg_neg] using (tendsto_atanNonnegative_lo (-x) (by linarith)).neg
  · simpa only [atan, if_neg h] using tendsto_atanNonnegative_hi x (by linarith)

end FloatLib.Numerics.Enclosure
