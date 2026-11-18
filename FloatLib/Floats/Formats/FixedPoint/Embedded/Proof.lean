/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Standard
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring

/-!
# N1169 grid arithmetic properties

WG14 N1169 (2006 TR 18037 draft), C clauses 7.18a.6.2–3. The absolute-value equation
identifies the stored coefficient with saturation of the mathematical absolute value.
The rounding theorem proves nearest coarse-grid selection before saturation and the
half-step bound for every tie rule. `roundfx_low_bits` separately handles the required
zero low bits when saturation is inactive.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics.Quantization

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.2: absolute value is exactly saturation
    on the coefficient grid. -/
theorem absfx_eq_clamp {format : Format} (value : format.Code) :
    bitsfx (absfx value) =
      Saturating.clamp format.integerFormat.minValue format.integerFormat.maxValue
        |bitsfx value| :=
  rfl

/-- The scaled integer distance is the rational coefficient-grid distance times its step. -/
private theorem grid_distance (coefficient index : Int) (step : ℚ) (hstep : 0 < step) :
    |(index : ℚ) * step - (coefficient : ℚ)| =
      |(index : ℚ) - (coefficient : ℚ) / step| * step := by
  calc
    _ = |((index : ℚ) - (coefficient : ℚ) / step) * step| := by
      rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hstep)]
    _ = _ := by rw [abs_mul, abs_of_pos hstep]

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.3: no other coefficient on the requested
    coarse grid is nearer. -/
theorem roundCoefficient_nearest (rounding : NearestRounding) (fractionalBits : Nat)
    (coefficient count index : Int) :
    |(roundCoefficient rounding fractionalBits coefficient count : ℚ) - (coefficient : ℚ)| ≤
      |((index * (2 : Int) ^ (fractionalBits - count.toNat) : Int) : ℚ) -
        (coefficient : ℚ)| := by
  let step : Int := 2 ^ (fractionalBits - count.toNat)
  have hsInt : (0 : Int) < step := pow_pos (by decide) _
  have hs : (0 : ℚ) < (step : ℚ) := by
    exact_mod_cast hsInt
  change |((rounding.run ((coefficient : ℚ) / (step : ℚ)) * step : Int) : ℚ) -
    (coefficient : ℚ)| ≤ |((index * step : Int) : ℚ) - (coefficient : ℚ)|
  simp only [Int.cast_mul]
  rw [grid_distance _ _ _ hs, grid_distance _ _ _ hs]
  exact mul_le_mul_of_nonneg_right (rounding.nearest _ index) hs.le

/-- Every allowed midpoint choice has at most half a coarse step of coefficient error. -/
theorem roundCoefficient_error_le_half (rounding : NearestRounding) (fractionalBits : Nat)
    (coefficient count : Int) :
    |(roundCoefficient rounding fractionalBits coefficient count : ℚ) - (coefficient : ℚ)| ≤
      (2 : ℚ) ^ (fractionalBits - count.toNat) / 2 := by
  let step : Int := 2 ^ (fractionalBits - count.toNat)
  have hsInt : (0 : Int) < step := pow_pos (by decide) _
  have hs : (0 : ℚ) < (step : ℚ) := by
    exact_mod_cast hsInt
  change |((rounding.run ((coefficient : ℚ) / (step : ℚ)) * step : Int) : ℚ) -
    (coefficient : ℚ)| ≤ _
  rw [Int.cast_mul, grid_distance _ _ _ hs]
  calc
    _ ≤ (1 / 2 : ℚ) * (step : ℚ) :=
      mul_le_mul_of_nonneg_right (rounding.error_le_half _) hs.le
    _ = (2 : ℚ) ^ (fractionalBits - count.toNat) / 2 := by
      simp only [step, Int.cast_pow, Int.cast_ofNat]
      ring

/-- The result rank is the larger operand rank, independently of sign and saturation. -/
theorem CType.common_rank (left right : CType) :
    (left.common right).rank = max left.rank right.rank := by
  unfold CType.common
  split
  · rename_i h
    exact (max_eq_right h).symm
  · rename_i h
    exact (max_eq_left (le_of_not_ge h)).symm

end FloatLib.Floats.Formats.FixedPoint.Embedded
