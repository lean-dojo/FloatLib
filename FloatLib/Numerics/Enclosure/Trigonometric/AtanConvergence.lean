/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.AtanProof
public import FloatLib.Numerics.Enclosure.Rational.AffineConvergence
public import FloatLib.Numerics.Enclosure.Rational.Convergence

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
      (𝓝 (Real.arctan (x : ℝ))) :=
  RationalInterval.tendsto_of_abs_sub_le (fun n => abs_atan_sub_atanTaylor_le x (n + 1) hx)
    (tendsto_atanRadius x hx)

/-- The small arctangent lower endpoints converge to the exact value. -/
theorem tendsto_atanSmall_lo (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => ((atanSmall x n).lo : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) :=
  RationalInterval.tendsto_around_lo (tendsto_atanTaylor x hx) (tendsto_atanRadius x hx)

/-- The small arctangent upper endpoints converge to the exact value. -/
theorem tendsto_atanSmall_hi (x : ℚ) (hx : |x| < 1) :
    Tendsto (fun n : Nat => ((atanSmall x n).hi : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) :=
  RationalInterval.tendsto_around_hi (tendsto_atanTaylor x hx) (tendsto_atanRadius x hx)

/-- The lower rational bounds for π/4 approach π/4. -/
theorem tendsto_piQuarter_lo :
    Tendsto (fun n : Nat => ((piQuarter n).lo : ℝ)) atTop (𝓝 (Real.pi / 4)) := by
  simpa [piQuarter, one_div, Real.four_mul_arctan_inv_5_sub_arctan_inv_239] using
    RationalInterval.tendsto_sub_lo
      (RationalInterval.tendsto_scaleNonnegative_lo (tendsto_atanSmall_lo (1 / 5) (by norm_num)) 4)
      (tendsto_atanSmall_hi (1 / 239) (by norm_num))

/-- The upper rational bounds for π/4 approach π/4. -/
theorem tendsto_piQuarter_hi :
    Tendsto (fun n : Nat => ((piQuarter n).hi : ℝ)) atTop (𝓝 (Real.pi / 4)) := by
  simpa [piQuarter, one_div, Real.four_mul_arctan_inv_5_sub_arctan_inv_239] using
    RationalInterval.tendsto_sub_hi
      (RationalInterval.tendsto_scaleNonnegative_hi (tendsto_atanSmall_hi (1 / 5) (by norm_num)) 4)
      (tendsto_atanSmall_lo (1 / 239) (by norm_num))

/-- Arctangent reduction preserves lower-endpoint convergence for every nonnegative input. -/
theorem tendsto_atanUnit_lo (x : ℚ) (hx : 0 ≤ x) :
    Tendsto (fun n : Nat => ((atanUnit x n).lo : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  by_cases h : x ≤ 1 / 2
  · have hsmall : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
    simpa only [atanUnit, ite_eq_left h] using tendsto_atanSmall_lo x hsmall
  · have ht : |(x - 1) / (x + 1)| < 1 := abs_atan_unit_argument_lt_one x (by linarith)
    simpa only [atanUnit, ite_eq_right h, atan_unit_identity x hx] using
      RationalInterval.tendsto_add_lo tendsto_piQuarter_lo (tendsto_atanSmall_lo _ ht)

/-- Arctangent reduction preserves upper-endpoint convergence for every nonnegative input. -/
theorem tendsto_atanUnit_hi (x : ℚ) (hx : 0 ≤ x) :
    Tendsto (fun n : Nat => ((atanUnit x n).hi : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  by_cases h : x ≤ 1 / 2
  · have hsmall : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
    simpa only [atanUnit, ite_eq_left h] using tendsto_atanSmall_hi x hsmall
  · have ht : |(x - 1) / (x + 1)| < 1 := abs_atan_unit_argument_lt_one x (by linarith)
    simpa only [atanUnit, ite_eq_right h, atan_unit_identity x hx] using
      RationalInterval.tendsto_add_hi tendsto_piQuarter_hi (tendsto_atanSmall_hi _ ht)

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
  · simpa only [atanNonnegative, ite_eq_left h] using tendsto_atanUnit_lo x hx
  · simpa only [atanNonnegative, ite_eq_right h, Rat.cast_ofNat,
      atan_inversion_identity x (by linarith)] using
      RationalInterval.tendsto_sub_lo (RationalInterval.tendsto_scaleNonnegative_lo
        tendsto_piQuarter_lo 2) (tendsto_atanUnit_hi x⁻¹ (inv_nonneg.mpr hx))

/-- Inversion preserves upper-endpoint convergence for nonnegative inputs. -/
theorem tendsto_atanNonnegative_hi (x : ℚ) (hx : 0 ≤ x) :
    Tendsto (fun n : Nat => ((atanNonnegative x n).hi : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  by_cases h : x ≤ 1
  · simpa only [atanNonnegative, ite_eq_left h] using tendsto_atanUnit_hi x hx
  · simpa only [atanNonnegative, ite_eq_right h, Rat.cast_ofNat,
      atan_inversion_identity x (by linarith)] using
      RationalInterval.tendsto_sub_hi (RationalInterval.tendsto_scaleNonnegative_hi
        tendsto_piQuarter_hi 2) (tendsto_atanUnit_lo x⁻¹ (inv_nonneg.mpr hx))

/-- The lower enclosure endpoints converge for every rational arctangent input. -/
theorem tendsto_atan_lo (x : ℚ) :
    Tendsto (fun n : Nat => ((atan x n).lo : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  by_cases h : x < 0
  · simpa only [atan, ite_eq_left h, Rat.cast_neg, Real.arctan_neg, neg_neg] using
      RationalInterval.tendsto_neg_lo (tendsto_atanNonnegative_hi (-x) (by linarith))
  · simpa only [atan, ite_eq_right h] using tendsto_atanNonnegative_lo x (by linarith)

/-- The upper enclosure endpoints converge for every rational arctangent input. -/
theorem tendsto_atan_hi (x : ℚ) :
    Tendsto (fun n : Nat => ((atan x n).hi : ℝ)) atTop
      (𝓝 (Real.arctan (x : ℝ))) := by
  by_cases h : x < 0
  · simpa only [atan, ite_eq_left h, Rat.cast_neg, Real.arctan_neg, neg_neg] using
      RationalInterval.tendsto_neg_hi (tendsto_atanNonnegative_lo (-x) (by linarith))
  · simpa only [atan, ite_eq_right h] using tendsto_atanNonnegative_hi x (by linarith)

end FloatLib.Numerics.Enclosure
