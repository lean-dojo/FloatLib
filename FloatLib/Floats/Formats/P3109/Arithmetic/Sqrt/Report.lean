/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Selection
public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Report

/-!
# Independent report semantics for scalar square-root rounding

P3109 Interim Report v4.1, §§4.7.4 and 4.10.8 (unapproved draft).
The integer kernel equals the logarithmic real-quantum and fractional-part
formula on every nonnegative rational, at every descriptor and supplied mode.
The equality precedes saturation and imposes no no-overflow hypothesis.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

open BinaryInterchange.Model

/-- P3109 interim report v4.1, §4.7.4: floor division of the radicand exponent is the root's
    real integer log. -/
theorem sqrt_floorLog2_eq_log (numerator denominator : Nat)
    (hn : numerator ≠ 0) (hd : denominator ≠ 0) :
    RationalBinary.floorLog2 numerator denominator / 2 =
      Int.log 2 (Real.sqrt ((numerator : ℝ) / denominator)) := by
  have hpositive : 0 < Real.sqrt ((numerator : ℝ) / denominator) :=
    Real.sqrt_pos.mpr (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)))
  have h := sqrt_floorLog2_bounds numerator denominator hn hd
  change (2 : ℝ) ^ _ ≤ _ ∧ _ < (2 : ℝ) ^ _ at h
  have hl := (Int.zpow_le_iff_le_log (by decide : 1 < 2) hpositive).mp h.1
  have hu := (Int.lt_zpow_iff_log_lt (by decide : 1 < 2) hpositive).mp h.2
  omega

/-- P3109 interim report v4.1, §§4.7.4, 4.10.8: integer square-root rounding equals the
    independent real formula,
before saturation, for every valid descriptor and every supplied rounding word. -/
theorem roundSqrtRatToPrecision_eq_report (format : Format) (mode : RoundingMode)
    (radicand : Rat) (h : 0 ≤ radicand) :
    roundSqrtRatToPrecision format mode radicand =
      ComparisonRounding.reportRounded format mode (Real.sqrt (radicand : ℝ)) := by
  by_cases hzero : radicand = 0
  · simp [roundSqrtRatToPrecision, ComparisonRounding.reportRounded, hzero]
  have hn : radicand.num.natAbs ≠ 0 := by simpa using hzero
  have hroot : 0 < Real.sqrt (radicand : ℝ) :=
    Real.sqrt_pos.mpr (Rat.cast_pos.mpr (lt_of_le_of_ne h (Ne.symm hzero)))
  have hquantum :
      sqrtQuantum format radicand.num.natAbs radicand.den =
        max (Int.log 2 (Real.sqrt (radicand : ℝ))) format.minimumNormalExponent -
          format.precision + 1 := by
    unfold sqrtQuantum
    rw [sqrt_floorLog2_eq_log _ _ hn radicand.den_nz,
      nonnegative_rat_eq_ratio radicand h]
    rfl
  have hscaled := sqrt_scaled_radicand format radicand h
  change Real.sqrt (_ / _) =
    Real.sqrt (radicand : ℝ) *
      (2 : ℝ) ^ (-sqrtQuantum format radicand.num.natAbs radicand.den) at hscaled
  have hscaled' :
      let quantum := sqrtQuantum format radicand.num.natAbs radicand.den
      let scaled :=
        RationalBinary.scaleByPowerOfTwo radicand.num.natAbs radicand.den (-2 * quantum)
      Real.sqrt ((scaled.1 : ℝ) / scaled.2) =
        Real.sqrt (radicand : ℝ) / (2 : ℝ) ^ quantum := by
    simpa only [zpow_neg, div_eq_mul_inv] using hscaled
  rw [roundSqrtRatToPrecision_eq_real]
  unfold roundSqrtRealToPrecision ComparisonRounding.reportRounded
  simp only [beq_iff_eq, hn, hroot.ne', ite_false, abs_of_nonneg hroot.le,
    not_lt_of_ge hroot.le, decide_false]
  unfold sqrtRoundAwayReal
  rw [format.roundMagnitudeUp_eq_fraction mode _ _ _ (Nat.floor_le (Real.sqrt_nonneg _))]
  rw [hscaled']
  simp only [hquantum]

/-- P3109 interim report v4.1, §§4.7.4, 4.10.8: the same independent root formula survives every
    saturation policy. -/
theorem sqrtValue_finite_eq_report (format : Format) (policy : ProjectionPolicy)
    (radicand : Rat) (h : 0 ≤ radicand) :
    sqrtValue format policy (.finite radicand) =
      ComparisonRounding.reportValue format policy (Real.sqrt (radicand : ℝ)) := by
  simp [sqrtValue, sqrtRounded, not_lt_of_ge h, ComparisonRounding.reportValue,
    roundSqrtRatToPrecision_eq_report format policy.rounding radicand h]

end FloatLib.Floats.Formats.P3109.Arithmetic

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

/-- P3109 interim report v4.1, §§4.7.4, 4.10.8: the encoded scalar root delivers the independent
    report
formula for a nonnegative rational radicand, at every destination and policy. -/
theorem decode_projectSqrt_report {format : Format} (radicand : Rat) (h : 0 ≤ radicand)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum
      (decode (projectSqrt (format := format) (.finite radicand) mode saturation))
      (ComparisonRounding.reportValue format { rounding := mode, saturation }
        (Real.sqrt (radicand : ℝ))) := by
  rw [← Arithmetic.sqrtValue_finite_eq_report format _ radicand h,
    Arithmetic.sqrtValue_eq_real]
  exact decode_projectSqrt _ _ _

/-- P3109 interim report v4.1, §4.10.8: a finite nonnegative source root uses the independent
    report formula
at an independently chosen destination descriptor. -/
theorem decode_sqrt_report {source : Format} (value : ExecFloat.P3109 source)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode)
    (radicand : Rat) (hv : value.toClosedRat = .finite radicand) (h : 0 ≤ radicand) :
    Format.SameDatum (decode (Sqrt value target mode saturation))
      (ComparisonRounding.reportValue target ⟨mode, saturation⟩
        (Real.sqrt (radicand : ℝ))) := by
  simpa only [Sqrt, hv] using
    decode_projectSqrt_report (format := target) radicand h mode saturation

/-- P3109 interim report v4.1, §4.10.8: a positive finite reciprocal root uses the report formula
on the exact reciprocal, without intermediate rounding. -/
theorem decode_rsqrt_report {source : Format} (value : ExecFloat.P3109 source)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode)
    (radicand : Rat) (hv : value.toClosedRat = .finite radicand) (h : 0 < radicand) :
    Format.SameDatum (decode (RSqrt value target mode saturation))
      (ComparisonRounding.reportValue target ⟨mode, saturation⟩
        (1 / Real.sqrt (radicand : ℝ))) := by
  simpa only [RSqrt, hv, (Arithmetic.rsqrtRadicand_finite_real h).1,
    (Arithmetic.rsqrtRadicand_finite_real h).2] using
    decode_projectSqrt_report (format := target) (1 / radicand)
      (div_nonneg zero_le_one h.le) mode saturation

/-- P3109 interim report v4.1, §4.10.14: independently encoded finite operands are squared and
    added exactly
before one root projection by the independent report formula. -/
theorem decode_hypot_report {leftFormat rightFormat : Format}
    (left : ExecFloat.P3109 leftFormat) (right : ExecFloat.P3109 rightFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode)
    (x y : Rat) (hx : left.toClosedRat = .finite x) (hy : right.toClosedRat = .finite y) :
    Format.SameDatum (decode (Hypot left right target mode saturation))
      (ComparisonRounding.reportValue target ⟨mode, saturation⟩
        (Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))) := by
  simpa [Hypot, hx, hy, Arithmetic.hypotRadicand, pow_two] using
    decode_projectSqrt_report (format := target) (x * x + y * y)
      (add_nonneg (mul_self_nonneg x) (mul_self_nonneg y)) mode saturation

end FloatLib.Floats.ExecFloat.P3109
