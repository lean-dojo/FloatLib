/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Decision
public import FloatLib.Floats.Formats.P3109.Projection.RealSelection

/-!
# Real meaning of the shared stochastic thresholds

P3109 interim report v4.1 (14 September 2026), §4.7.4, unapproved draft.
The exact-comparison policy equals the report's floor and nearest-even
formulas for any real value above its natural lower candidate. Square roots
and elementary functions use the same decision. No distribution of the
supplied random bits is assumed.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.RealRounding

/-- Guarding the floor threshold at exact integers preserves its fractional-part formula. -/
theorem floorThreshold_eq (value : ℝ) (lower scale random : Nat)
    (hrandom : random < scale) (hlower : (lower : ℝ) ≤ value) :
    (if decide (value = lower) then false
      else compare value (((lower * scale + (scale - random) : Nat) : ℝ) / scale) != .lt) =
      decide (scale ≤ ⌊(value - lower) * scale⌋₊ + random) := by
  by_cases he : value = lower
  · simp [he, Nat.not_le.mpr hrandom]
  · simp only [he, decide_false, Bool.false_eq_true, ite_false]
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, ne_eq, compare_lt_iff_lt, decide_eq_true_eq, not_lt]
    exact (floor_selection_iff value lower scale random hrandom hlower).symm

end FloatLib.Floats.Formats.P3109.RealRounding

namespace FloatLib.Floats.Formats.P3109.Format

/-- Stochastic A is the report's floor formula for the exact real fraction. -/
theorem roundMagnitudeUp_stochasticA (format : Format) (quantum : Int)
    (random : RandomBits) (value : ℝ) (lower : Nat) (hlower : (lower : ℝ) ≤ value) :
    roundMagnitudeUp format (.stochasticA random) quantum lower (decide (value = lower))
        (fun scale threshold => compare value ((threshold : ℝ) / scale)) =
      decide (2 ^ random.width ≤
        ⌊(value - lower) * 2 ^ random.width⌋₊ + random.toNat) := by
  simpa only [roundMagnitudeUp, Nat.cast_pow, Nat.cast_ofNat] using
    RealRounding.floorThreshold_eq value lower _ _
      (RationalRounding.random_lt_modulus random) hlower

/-- Stochastic B is the report's floor formula with doubled word and odd offset. -/
theorem roundMagnitudeUp_stochasticB (format : Format) (quantum : Int)
    (random : RandomBits) (value : ℝ) (lower : Nat) (hlower : (lower : ℝ) ≤ value) :
    roundMagnitudeUp format (.stochasticB random) quantum lower (decide (value = lower))
        (fun scale threshold => compare value ((threshold : ℝ) / scale)) =
      decide (2 ^ (random.width + 1) ≤
        ⌊(value - lower) * 2 ^ (random.width + 1)⌋₊ + (2 * random.toNat + 1)) := by
  have hr : 2 * random.toNat + 1 < 2 ^ (random.width + 1) := by
    have := RationalRounding.random_lt_modulus random
    rw [pow_succ]
    omega
  simpa only [roundMagnitudeUp, Nat.cast_pow, Nat.cast_ofNat] using
    RealRounding.floorThreshold_eq value lower _ _ hr hlower

/-- Stochastic C is nearest-even rounding of the real fraction, with the upper integer's parity. -/
theorem roundMagnitudeUp_stochasticC (format : Format) (quantum : Int)
    (random : RandomBits) (value : ℝ) (lower : Nat) (hlower : (lower : ℝ) ≤ value) :
    roundMagnitudeUp format (.stochasticC random) quantum lower (decide (value = lower))
        (fun scale threshold => compare value ((threshold : ℝ) / scale)) =
      decide (2 ^ random.width ≤
        RoundingFormula.nearestEven ((value - lower) * 2 ^ random.width) + random.toNat) := by
  have hr := RationalRounding.random_lt_modulus random
  by_cases he : value = lower
  · simp [roundMagnitudeUp, he, Nat.not_le.mpr hr, RoundingFormula.nearestEven]
  · simp only [roundMagnitudeUp, he, decide_false, Bool.false_eq_true, ite_false]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, compare_gt_iff_gt,
      compare_eq_iff_eq, decide_eq_true_eq]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
      (RealRounding.nearestEven_selection_iff value lower _ _ hr hlower).symm

/-- Every exact-threshold mode is the report's fractional-part decision on a real magnitude. -/
theorem roundMagnitudeUp_eq_fraction (format : Format) (mode : RoundingMode)
    (quantum : Int) (value : ℝ) (lower : Nat) (hlower : (lower : ℝ) ≤ value) :
    roundMagnitudeUp format mode quantum lower (decide (value = lower))
        (fun scale threshold => compare value ((threshold : ℝ) / scale)) =
      RoundingFormula.roundAway mode false (format.lowerCodeIsEven quantum lower)
        (value - lower) := by
  have hboundary : ((2 * (lower : ℝ) + 1) / 2) = (lower : ℝ) + 2⁻¹ := by
    ring
  have hle : (lower : ℝ) + 2⁻¹ ≤ value ↔ 2⁻¹ ≤ value - lower := by
    constructor <;> intro h <;> linarith
  have hlt : (lower : ℝ) + 2⁻¹ < value ↔ 2⁻¹ < value - lower := by
    constructor <;> intro h <;> linarith
  have heq : value = (lower : ℝ) + 2⁻¹ ↔ value - lower = 2⁻¹ := by
    constructor <;> intro h <;> linarith
  cases mode with
  | stochasticA random => exact format.roundMagnitudeUp_stochasticA quantum random _ _ hlower
  | stochasticB random => exact format.roundMagnitudeUp_stochasticB quantum random _ _ hlower
  | stochasticC random => exact format.roundMagnitudeUp_stochasticC quantum random _ _ hlower
  | _ =>
    by_cases hexact : value = lower
    · simp [roundMagnitudeUp, RoundingFormula.roundAway, hexact]
    · have hpositive : 0 < value - lower :=
        sub_pos.mpr (lt_of_le_of_ne hlower (Ne.symm hexact))
      apply Bool.eq_iff_iff.mpr
      simp [roundMagnitudeUp, RoundingFormula.roundAway, hexact, hpositive,
        hboundary, compare_lt_iff_lt, compare_gt_iff_gt,
        not_lt, hle, hlt, heq]

/-- Rational boundary comparisons give the same fractional decision after exact power scaling. -/
theorem roundMagnitudeUp_scaled_eq_fraction (format : Format) (mode : RoundingMode)
    (quantum : Int) (target : ℝ) (lower : Nat)
    (hlower : (lower : ℝ) * 2 ^ quantum ≤ target) :
    roundMagnitudeUp format mode quantum lower
        (cmp target (((lower : Rat) * 2 ^ quantum : Rat) : ℝ) == .eq)
        (fun scale threshold =>
          cmp target ((((threshold : Rat) / scale) * 2 ^ quantum : Rat) : ℝ)) =
      RoundingFormula.roundAway mode false (format.lowerCodeIsEven quantum lower)
        (target / 2 ^ quantum - lower) := by
  have hunit : (0 : ℝ) < 2 ^ quantum := zpow_pos (by norm_num) _
  have hcompare (boundary : Rat) :
      cmp target (((boundary * 2 ^ quantum : Rat)) : ℝ) =
        compare (target / 2 ^ quantum) (boundary : ℝ) := by
    push_cast
    rw [← cmp_eq_compare]
    simpa only [div_mul_cancel₀ _ hunit.ne'] using
      cmp_mul_pos_right hunit (target / 2 ^ quantum) (boundary : ℝ)
  have hexact :
      (cmp target (((lower : Rat) * 2 ^ quantum : Rat) : ℝ) == .eq) =
        decide (target / 2 ^ quantum = lower) := by
    rw [hcompare]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, compare_eq_iff_eq, Rat.cast_natCast, decide_eq_true_eq]
  have hthreshold (scale threshold : Nat) :
      cmp target ((((threshold : Rat) / scale) * 2 ^ quantum : Rat) : ℝ) =
        compare (target / 2 ^ quantum) ((threshold : ℝ) / scale) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using hcompare ((threshold : Rat) / scale)
  simp_rw [hexact, hthreshold]
  exact format.roundMagnitudeUp_eq_fraction mode quantum _ _
    ((le_div_iff₀ hunit).mpr hlower)

end FloatLib.Floats.Formats.P3109.Format
