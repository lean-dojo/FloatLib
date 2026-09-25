/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Parsing
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact

/-!
# Decimal exponent clamping preserves binary conversion

`convertDecimalText` clamps the written decimal exponent before forming the exact rational. Far
above the overflow threshold every rational rounds to the same overflow result with the same
flags, and far below the least subnormal every positive rational rounds to the same tiny result
with the same flags. This file proves both saturation facts for scaled rationals and concludes
`convertDecimalText_eq_exact`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

private theorem bpow_eq_two_zpow (e : Int) : bpow e = (2 : ℝ) ^ e := by
  simp [bpow, FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

private theorem toReal_lt_bpow_lead (v : Numerics.Dyadic) (hv : v.negative = false) :
    v.toReal < bpow (dyadicLeadingExponent v + 1) := by
  have hs : (v.significand : ℝ) < (2 : ℝ) ^ (v.significand.log2 + 1) := by
    exact_mod_cast Nat.lt_log2_self
  rw [bpow_eq_two_zpow, dyadicLeadingExponent, add_right_comm, zpow_add₀ (by norm_num)]
  simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hv]
  have hp : (0 : ℝ) < (2 : ℝ) ^ v.exponent := zpow_pos (by norm_num) _
  have : ((v.significand.log2 : Int) + 1) = ((v.significand.log2 + 1 : Nat) : Int) := by
    push_cast; rfl
  rw [this, zpow_natCast]
  simpa [mul_comm] using mul_lt_mul_of_pos_right hs hp

private theorem bpow_lead_le_toReal (v : Numerics.Dyadic) (hv : v.negative = false)
    (hs : v.significand ≠ 0) :
    bpow (dyadicLeadingExponent v) ≤ v.toReal := by
  have hle : (2 : ℝ) ^ v.significand.log2 ≤ (v.significand : ℝ) := by
    exact_mod_cast Nat.log2_self_le hs
  rw [bpow_eq_two_zpow, dyadicLeadingExponent, zpow_add₀ (by norm_num), zpow_natCast]
  simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hv]
  have hp : (0 : ℝ) < (2 : ℝ) ^ v.exponent := zpow_pos (by norm_num) _
  simpa using mul_le_mul_of_nonneg_right hle hp.le

/-! ## Saturated rounding values -/

/-- Above `decimalSaturationHigh`, the rounded value does not depend on the exact rational. -/
theorem roundRatWithRoundingScaled_eq_of_high (fmt : FloatFormat) (mode : IEEERoundingMode)
    (sign : Bool) {n₁ d₁ n₂ d₂ : Nat} {e₁ e₂ : Int}
    (hn₁ : n₁ ≠ 0) (hd₁ : d₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hd₂ : d₂ ≠ 0)
    (h₁ : decimalSaturationHigh fmt ≤ RationalBinary.floorLog2 n₁ d₁ + e₁)
    (h₂ : decimalSaturationHigh fmt ≤ RationalBinary.floorLog2 n₂ d₂ + e₂) :
    roundRatWithRoundingScaled fmt mode sign n₁ d₁ e₁ =
      roundRatWithRoundingScaled fmt mode sign n₂ d₂ e₂ := by
  simp only [decimalSaturationHigh, max_le_iff] at h₁ h₂
  have a₁ : fmt.maxNormalExponent < RationalBinary.floorLog2 n₁ d₁ + e₁ := by omega
  have b₁ : (FloatFormat.ieeeMaxNormalExponent fmt : Int) <
      RationalBinary.floorLog2 n₁ d₁ + e₁ := by omega
  have a₂ : fmt.maxNormalExponent < RationalBinary.floorLog2 n₂ d₂ + e₂ := by omega
  have b₂ : (FloatFormat.ieeeMaxNormalExponent fmt : Int) <
      RationalBinary.floorLog2 n₂ d₂ + e₂ := by omega
  cases mode <;>
    simp [roundRatWithRoundingScaled, roundRatScaled, ieeeRoundRatScaled,
      roundRatScaledGeneral, roundRatMagnitudeDirectedScaled, hn₁, hd₁, hn₂, hd₂,
      a₁, b₁, a₂, b₂]

/-- Below `decimalSaturationLow`, the rounded value does not depend on the exact rational. -/
theorem roundRatWithRoundingScaled_eq_of_low (fmt : FloatFormat) (mode : IEEERoundingMode)
    (sign : Bool) {n₁ d₁ n₂ d₂ : Nat} {e₁ e₂ : Int}
    (hn₁ : n₁ ≠ 0) (hd₁ : d₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hd₂ : d₂ ≠ 0)
    (h₁ : RationalBinary.floorLog2 n₁ d₁ + e₁ ≤ decimalSaturationLow fmt)
    (h₂ : RationalBinary.floorLog2 n₂ d₂ + e₂ ≤ decimalSaturationLow fmt) :
    roundRatWithRoundingScaled fmt mode sign n₁ d₁ e₁ =
      roundRatWithRoundingScaled fmt mode sign n₂ d₂ e₂ := by
  simp only [decimalSaturationLow, le_min_iff] at h₁ h₂
  have a₁ : ¬ fmt.maxNormalExponent < RationalBinary.floorLog2 n₁ d₁ + e₁ := by omega
  have b₁ : ¬ (FloatFormat.ieeeMaxNormalExponent fmt : Int) <
      RationalBinary.floorLog2 n₁ d₁ + e₁ := by omega
  have c₁ : RationalBinary.floorLog2 n₁ d₁ + e₁ + 1 < fmt.minSubnormalExponent := by omega
  have c₁' : RationalBinary.floorLog2 n₁ d₁ + e₁ < fmt.minSubnormalExponent := by omega
  have k₁ : RationalBinary.floorLog2 n₁ d₁ + e₁ <
      -(FloatFormat.normalMantissaExpOffset fmt : Int) := by omega
  have a₂ : ¬ fmt.maxNormalExponent < RationalBinary.floorLog2 n₂ d₂ + e₂ := by omega
  have b₂ : ¬ (FloatFormat.ieeeMaxNormalExponent fmt : Int) <
      RationalBinary.floorLog2 n₂ d₂ + e₂ := by omega
  have c₂ : RationalBinary.floorLog2 n₂ d₂ + e₂ + 1 < fmt.minSubnormalExponent := by omega
  have c₂' : RationalBinary.floorLog2 n₂ d₂ + e₂ < fmt.minSubnormalExponent := by omega
  have k₂ : RationalBinary.floorLog2 n₂ d₂ + e₂ <
      -(FloatFormat.normalMantissaExpOffset fmt : Int) := by omega
  cases mode <;>
    simp [roundRatWithRoundingScaled, roundRatScaled, ieeeRoundRatScaled,
      roundRatScaledGeneral, roundRatMagnitudeDirectedScaled, hn₁, hd₁, hn₂, hd₂,
      a₁, b₁, a₂, b₂, c₁, c₂, c₁', c₂', k₁, k₂]

/-! ## Saturated status classification -/

private theorem compare_gt_of_lead {n d : Nat} {e : Int} (v : Numerics.Dyadic)
    (hn : n ≠ 0) (hd : d ≠ 0) (hv : v.negative = false) (hs : v.significand ≠ 0)
    (h : dyadicLeadingExponent v + 1 ≤ RationalBinary.floorLog2 n d + e) :
    RationalBinary.compareDyadicScaled? false n d e v = some .gt := by
  rw [compareDyadicScaled?_false_eq_compare _ _ _ _ hd hv hs]
  congr 1
  apply compare_gt_iff_gt.mpr
  calc v.toReal < bpow (dyadicLeadingExponent v + 1) := toReal_lt_bpow_lead v hv
    _ ≤ bpow (RationalBinary.floorLog2 n d + e) := bpow_le_bpow_of_le h
    _ ≤ scaledRatToReal n d e := (scaledRatToReal_floorLog2_bounds n d e hn hd).1

private theorem compare_lt_of_lead {n d : Nat} {e : Int} (v : Numerics.Dyadic)
    (hn : n ≠ 0) (hd : d ≠ 0) (hv : v.negative = false) (hs : v.significand ≠ 0)
    (h : RationalBinary.floorLog2 n d + e + 1 ≤ dyadicLeadingExponent v) :
    RationalBinary.compareDyadicScaled? false n d e v = some .lt := by
  rw [compareDyadicScaled?_false_eq_compare _ _ _ _ hd hv hs]
  congr 1
  apply compare_lt_iff_lt.mpr
  calc scaledRatToReal n d e < bpow (RationalBinary.floorLog2 n d + e + 1) :=
        (scaledRatToReal_floorLog2_bounds n d e hn hd).2
    _ ≤ bpow (dyadicLeadingExponent v) := bpow_le_bpow_of_le h
    _ ≤ v.toReal := bpow_lead_le_toReal v hv hs

private theorem overflowMidpoint_significand_ne_zero (fmt : FloatFormat) :
    (overflowMidpoint fmt).significand ≠ 0 := by
  simp [overflowMidpoint]

private theorem overflowLimit_significand_ne_zero (fmt : FloatFormat) :
    (overflowLimit fmt).significand ≠ 0 := by
  simp [overflowLimit]

private theorem pow2_pos' (k : Nat) : 0 < pow2 k := by
  simp [pow2, Nat.shiftLeft_eq]

private theorem underflowMidpoint_significand_ne_zero (fmt : FloatFormat) :
    (underflowMidpoint fmt).significand ≠ 0 := by
  have := pow2_pos' fmt.fracWidth
  simp only [underflowMidpoint]
  omega

private theorem minNormalDyadic_significand_ne_zero (fmt : FloatFormat) :
    (minNormalDyadic fmt).significand ≠ 0 := by
  simpa [minNormalDyadic] using (pow2_pos' fmt.fracWidth).ne'

private theorem underflowPredecessor_significand_ne_zero (fmt : FloatFormat) :
    (underflowPredecessor fmt).significand ≠ 0 := by
  have := pow2_pos' fmt.fracWidth
  simp only [underflowPredecessor]
  omega

/-- Above `decimalSaturationHigh`, every rounding direction reports overflow. -/
theorem rationalRoundingOverflowsScaled_of_high (fmt : FloatFormat) (mode : IEEERoundingMode)
    (sign : Bool) {n d : Nat} {e : Int} (hn : n ≠ 0) (hd : d ≠ 0)
    (h : decimalSaturationHigh fmt ≤ RationalBinary.floorLog2 n d + e) :
    rationalRoundingOverflowsScaled fmt mode sign n d e = true := by
  simp only [decimalSaturationHigh, max_le_iff] at h
  have hm := compare_gt_of_lead (e := e) (overflowMidpoint fmt) hn hd (by simp [overflowMidpoint])
    (overflowMidpoint_significand_ne_zero fmt) (by omega)
  have hl := compare_gt_of_lead (e := e) (overflowLimit fmt) hn hd (by simp [overflowLimit])
    (overflowLimit_significand_ne_zero fmt) (by omega)
  have a : fmt.maxNormalExponent < RationalBinary.floorLog2 n d + e := by omega
  have hmag : rationalMagnitudeOverflowsScaled fmt n d e = true := by
    simp [rationalMagnitudeOverflowsScaled, hn, hd, a, not_lt_of_gt a]
  cases mode <;> cases sign <;>
    simp [rationalRoundingOverflowsScaled, rationalNearestEvenOverflowsScaled,
      rationalTruncationOverflowsScaled, hm, hl, hmag]

/-- Below `decimalSaturationLow`, no rounding direction reports overflow. -/
theorem rationalRoundingOverflowsScaled_of_low (fmt : FloatFormat) (mode : IEEERoundingMode)
    (sign : Bool) {n d : Nat} {e : Int} (hn : n ≠ 0) (hd : d ≠ 0)
    (h : RationalBinary.floorLog2 n d + e ≤ decimalSaturationLow fmt) :
    rationalRoundingOverflowsScaled fmt mode sign n d e = false := by
  simp only [decimalSaturationLow, le_min_iff] at h
  have hm := compare_lt_of_lead (e := e) (overflowMidpoint fmt) hn hd (by simp [overflowMidpoint])
    (overflowMidpoint_significand_ne_zero fmt) (by omega)
  have hl := compare_lt_of_lead (e := e) (overflowLimit fmt) hn hd (by simp [overflowLimit])
    (overflowLimit_significand_ne_zero fmt) (by omega)
  have a : RationalBinary.floorLog2 n d + e < fmt.maxNormalExponent := by omega
  have hmag : rationalMagnitudeOverflowsScaled fmt n d e = false := by
    simp [rationalMagnitudeOverflowsScaled, hn, hd, a]
  cases mode <;> cases sign <;>
    simp [rationalRoundingOverflowsScaled, rationalNearestEvenOverflowsScaled,
      rationalTruncationOverflowsScaled, hm, hl, hmag]

/-- Below `decimalSaturationLow`, every result is tiny after rounding. -/
theorem rationalIsTinyAfterRoundingScaled_of_low (fmt : FloatFormat)
    (mode : IEEERoundingMode) (sign : Bool) {n d : Nat} {e : Int} (hn : n ≠ 0) (hd : d ≠ 0)
    (h : RationalBinary.floorLog2 n d + e ≤ decimalSaturationLow fmt) (rounded : Model fmt) :
    rationalIsTinyAfterRoundingScaled fmt mode sign n d e rounded = true := by
  simp only [decimalSaturationLow, le_min_iff] at h
  have hm := compare_lt_of_lead (e := e) (underflowMidpoint fmt) hn hd (by simp [underflowMidpoint])
    (underflowMidpoint_significand_ne_zero fmt) (by omega)
  have hl := compare_lt_of_lead (e := e) (minNormalDyadic fmt) hn hd (by simp [minNormalDyadic])
    (minNormalDyadic_significand_ne_zero fmt) (by omega)
  have hp := compare_lt_of_lead (e := e) (underflowPredecessor fmt) hn hd
    (by simp [underflowPredecessor]) (underflowPredecessor_significand_ne_zero fmt) (by omega)
  cases mode <;> cases sign <;>
    simp [rationalIsTinyAfterRoundingScaled, roundsAwayFromZero, hm, hl, hp]

/-- Below `decimalSaturationLow`, a positive rational never equals a finite result. -/
theorem rationalEqualsDyadicScaled_finite_of_low (fmt : FloatFormat) (sign : Bool)
    {n d : Nat} {e : Int} (hn : n ≠ 0) (hd : d ≠ 0)
    (h : RationalBinary.floorLog2 n d + e ≤ decimalSaturationLow fmt)
    (rounded : Model fmt) (hfinite : isFinite rounded = true) :
    rationalEqualsDyadicScaled sign n d e (finiteDyadic rounded hfinite) = false := by
  simp only [decimalSaturationLow, le_min_iff] at h
  have hdec : toDyadic? rounded = some (finiteDyadic rounded hfinite) := by
    simp [finiteDyadic]
  have hexp := minSubnormalExponent_le_toDyadic? rounded hdec
  generalize finiteDyadic rounded hfinite = a at hexp ⊢
  by_cases hs : a.significand = 0
  · simp only [rationalEqualsDyadicScaled, RationalBinary.compareDyadicScaled?, hs]
    split_ifs <;> simp_all
  · have hlt := compare_lt_of_lead (e := e) { a with negative := false } hn hd rfl hs
      (by simp only [dyadicLeadingExponent]; omega)
    simp only [rationalEqualsDyadicScaled]
    simp only [RationalBinary.compareDyadicScaled?] at hlt ⊢
    cases sign <;> cases hneg : a.negative <;> simp_all <;> split_ifs at hlt ⊢ <;> simp_all

/-- Above `decimalSaturationHigh`, the status does not depend on the exact rational. -/
theorem rationalRoundingStatusScaled_eq_of_high (fmt : FloatFormat) (mode : IEEERoundingMode)
    (sign : Bool) {n₁ d₁ n₂ d₂ : Nat} {e₁ e₂ : Int}
    (hn₁ : n₁ ≠ 0) (hd₁ : d₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hd₂ : d₂ ≠ 0)
    (h₁ : decimalSaturationHigh fmt ≤ RationalBinary.floorLog2 n₁ d₁ + e₁)
    (h₂ : decimalSaturationHigh fmt ≤ RationalBinary.floorLog2 n₂ d₂ + e₂)
    (r₁ r₂ : Model fmt) :
    rationalRoundingStatusScaled fmt mode sign n₁ d₁ e₁ r₁ =
      rationalRoundingStatusScaled fmt mode sign n₂ d₂ e₂ r₂ := by
  simp [rationalRoundingStatusScaled,
    rationalRoundingOverflowsScaled_of_high fmt mode sign hn₁ hd₁ h₁,
    rationalRoundingOverflowsScaled_of_high fmt mode sign hn₂ hd₂ h₂]

/-- Below `decimalSaturationLow`, the status does not depend on the exact rational. -/
theorem rationalRoundingStatusScaled_eq_of_low (fmt : FloatFormat) (mode : IEEERoundingMode)
    (sign : Bool) {n₁ d₁ n₂ d₂ : Nat} {e₁ e₂ : Int}
    (hn₁ : n₁ ≠ 0) (hd₁ : d₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hd₂ : d₂ ≠ 0)
    (h₁ : RationalBinary.floorLog2 n₁ d₁ + e₁ ≤ decimalSaturationLow fmt)
    (h₂ : RationalBinary.floorLog2 n₂ d₂ + e₂ ≤ decimalSaturationLow fmt)
    (rounded : Model fmt) :
    rationalRoundingStatusScaled fmt mode sign n₁ d₁ e₁ rounded =
      rationalRoundingStatusScaled fmt mode sign n₂ d₂ e₂ rounded := by
  unfold rationalRoundingStatusScaled
  rw [rationalRoundingOverflowsScaled_of_low fmt mode sign hn₁ hd₁ h₁,
    rationalRoundingOverflowsScaled_of_low fmt mode sign hn₂ hd₂ h₂]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · next hfinite =>
      simp only [rationalEqualsDyadicScaled_finite_of_low fmt sign hn₁ hd₁ h₁ rounded hfinite,
        rationalEqualsDyadicScaled_finite_of_low fmt sign hn₂ hd₂ h₂ rounded hfinite,
        rationalIsTinyAfterRoundingScaled_of_low fmt mode sign hn₁ hd₁ h₁,
        rationalIsTinyAfterRoundingScaled_of_low fmt mode sign hn₂ hd₂ h₂]
  · rfl

/-! ## Decimal magnitudes -/

/-- The exact rational denoted by a decimal significand and exponent. -/
private abbrev decimalMagnitude (x : DecimalText.Decimal) : ℚ :=
  (x.significand : ℚ) * (10 : ℚ) ^ x.exponent

private theorem decimalMagnitude_num_ne_zero (x : DecimalText.Decimal)
    (hx : x.significand ≠ 0) : (decimalMagnitude x).num.natAbs ≠ 0 := by
  have : decimalMagnitude x ≠ 0 := by
    simp only [decimalMagnitude]
    exact mul_ne_zero (by exact_mod_cast hx) (zpow_ne_zero _ (by norm_num))
  simpa [Int.natAbs_eq_zero, Rat.num_eq_zero] using this

private theorem floorLog2_decimalMagnitude (x : DecimalText.Decimal)
    (hx : x.significand ≠ 0) :
    RationalBinary.floorLog2 (decimalMagnitude x).num.natAbs (decimalMagnitude x).den =
      Int.log 2 ((x.significand : ℝ) * (10 : ℝ) ^ x.exponent) := by
  rw [floorLog2_eq_int_log _ _ (decimalMagnitude_num_ne_zero x hx) (Rat.den_nz _)]
  congr 1
  have hnonneg : 0 ≤ (decimalMagnitude x).num :=
    Rat.num_nonneg.mpr (by simp only [decimalMagnitude]; positivity)
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hnonneg),
    ← Rat.cast_def]
  push_cast
  rfl

private theorem three_mul_le_log_decimal (s : Nat) (hs : s ≠ 0) (k : Nat) :
    3 * (k : Int) ≤ Int.log 2 ((s : ℝ) * (10 : ℝ) ^ (k : Int)) := by
  have hpos : (0 : ℝ) < (s : ℝ) * (10 : ℝ) ^ (k : Int) := by
    have : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs
    positivity
  rw [← Int.zpow_le_iff_le_log (by norm_num) hpos]
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs
  have h8 : ((2 : Nat) : ℝ) ^ (3 * (k : Int)) = (8 : ℝ) ^ k := by
    rw [zpow_mul]
    norm_num
  rw [h8, zpow_natCast]
  calc (8 : ℝ) ^ k ≤ (10 : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
    _ = 1 * (10 : ℝ) ^ k := (one_mul _).symm
    _ ≤ (s : ℝ) * (10 : ℝ) ^ k := by gcongr

private theorem log_decimal_le (s : Nat) (hs : s ≠ 0) (k : Nat) :
    Int.log 2 ((s : ℝ) * (10 : ℝ) ^ (-(k : Int))) ≤ (s.log2 : Int) - 3 * (k : Int) := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hpos : (0 : ℝ) < (s : ℝ) * (10 : ℝ) ^ (-(k : Int)) := by positivity
  have hlt : (s : ℝ) * (10 : ℝ) ^ (-(k : Int)) <
      ((2 : Nat) : ℝ) ^ ((s.log2 : Int) - 3 * (k : Int) + 1) := by
    have hsl : (s : ℝ) < (2 : ℝ) ^ (s.log2 + 1) := by exact_mod_cast Nat.lt_log2_self
    have h10 : (10 : ℝ) ^ (-(k : Int)) ≤ (8 : ℝ) ^ (-(k : Int)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) (by norm_num) k)
    have hrw : ((2 : Nat) : ℝ) ^ ((s.log2 : Int) - 3 * (k : Int) + 1) =
        (2 : ℝ) ^ (s.log2 + 1) * (8 : ℝ) ^ (-(k : Int)) := by
      have : ((s.log2 : Int) - 3 * (k : Int) + 1) =
          ((s.log2 + 1 : Nat) : Int) + 3 * (-(k : Int)) := by
        push_cast; ring
      rw [this, zpow_add₀ (by norm_num), zpow_mul, zpow_natCast]
      norm_num
    rw [hrw]
    calc (s : ℝ) * (10 : ℝ) ^ (-(k : Int)) ≤ (s : ℝ) * (8 : ℝ) ^ (-(k : Int)) := by gcongr
      _ < (2 : ℝ) ^ (s.log2 + 1) * (8 : ℝ) ^ (-(k : Int)) := by gcongr
  have := (Int.lt_zpow_iff_log_lt (by norm_num) hpos).mp hlt
  omega

private theorem high_le_log_decimal (fmt : FloatFormat) (s : Nat) (hs : s ≠ 0) (e : Int)
    (he : decimalSaturationHigh fmt / 3 + 1 ≤ e) (he0 : 0 ≤ e) :
    decimalSaturationHigh fmt ≤ Int.log 2 ((s : ℝ) * (10 : ℝ) ^ e) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le he0
  have := three_mul_le_log_decimal s hs k
  omega

private theorem log_decimal_le_low (fmt : FloatFormat) (s : Nat) (hs : s ≠ 0) (e : Int)
    (he : e ≤ (decimalSaturationLow fmt - (s.log2 : Int) - 1) / 3) (he0 : e ≤ 0) :
    Int.log 2 ((s : ℝ) * (10 : ℝ) ^ e) ≤ decimalSaturationLow fmt := by
  obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat he0
  have := log_decimal_le s hs k
  omega

private theorem convertDecimalTextExact_eq_of_high (fmt : FloatFormat)
    (mode : IEEERoundingMode) (x y : DecimalText.Decimal) (hneg : x.negative = y.negative)
    (hx : x.significand ≠ 0) (hy : y.significand ≠ 0)
    (hxH : decimalSaturationHigh fmt ≤ Int.log 2 ((x.significand : ℝ) * (10 : ℝ) ^ x.exponent))
    (hyH : decimalSaturationHigh fmt ≤ Int.log 2 ((y.significand : ℝ) * (10 : ℝ) ^ y.exponent)) :
    convertDecimalTextExact fmt mode x = convertDecimalTextExact fmt mode y := by
  have h₁ := floorLog2_decimalMagnitude x hx
  have h₂ := floorLog2_decimalMagnitude y hy
  simp only [decimalMagnitude] at h₁ h₂
  simp only [convertDecimalTextExact, roundRatWithRounding, rationalRoundingStatus, hneg]
  rw [roundRatWithRoundingScaled_eq_of_high fmt mode y.negative
    (decimalMagnitude_num_ne_zero x hx) (Rat.den_nz _)
    (decimalMagnitude_num_ne_zero y hy) (Rat.den_nz _)
    (by rw [add_zero, h₁]; exact hxH) (by rw [add_zero, h₂]; exact hyH)]
  rw [rationalRoundingStatusScaled_eq_of_high fmt mode y.negative
    (decimalMagnitude_num_ne_zero x hx) (Rat.den_nz _)
    (decimalMagnitude_num_ne_zero y hy) (Rat.den_nz _)
    (by rw [add_zero, h₁]; exact hxH) (by rw [add_zero, h₂]; exact hyH)]

private theorem convertDecimalTextExact_eq_of_low (fmt : FloatFormat)
    (mode : IEEERoundingMode) (x y : DecimalText.Decimal) (hneg : x.negative = y.negative)
    (hx : x.significand ≠ 0) (hy : y.significand ≠ 0)
    (hxL : Int.log 2 ((x.significand : ℝ) * (10 : ℝ) ^ x.exponent) ≤ decimalSaturationLow fmt)
    (hyL : Int.log 2 ((y.significand : ℝ) * (10 : ℝ) ^ y.exponent) ≤ decimalSaturationLow fmt) :
    convertDecimalTextExact fmt mode x = convertDecimalTextExact fmt mode y := by
  have h₁ := floorLog2_decimalMagnitude x hx
  have h₂ := floorLog2_decimalMagnitude y hy
  simp only [decimalMagnitude] at h₁ h₂
  simp only [convertDecimalTextExact, roundRatWithRounding, rationalRoundingStatus, hneg]
  rw [roundRatWithRoundingScaled_eq_of_low fmt mode y.negative
    (decimalMagnitude_num_ne_zero x hx) (Rat.den_nz _)
    (decimalMagnitude_num_ne_zero y hy) (Rat.den_nz _)
    (by rw [add_zero, h₁]; exact hxL) (by rw [add_zero, h₂]; exact hyL)]
  rw [rationalRoundingStatusScaled_eq_of_low fmt mode y.negative
    (decimalMagnitude_num_ne_zero x hx) (Rat.den_nz _)
    (decimalMagnitude_num_ne_zero y hy) (Rat.den_nz _)
    (by rw [add_zero, h₁]; exact hxL) (by rw [add_zero, h₂]; exact hyL)]

/-! ## The clamp preserves every outcome -/

/--
Clamping the decimal exponent never changes the value or status of a binary conversion.

Outside the clamp range the exact rational is either above every overflow threshold or below every
underflow threshold, and the rounded value and flags depend only on that side.
-/
theorem convertDecimalTextExact_clampDecimalExponent (fmt : FloatFormat)
    (mode : IEEERoundingMode) (x : DecimalText.Decimal) :
    convertDecimalTextExact fmt mode (clampDecimalExponent fmt x) =
      convertDecimalTextExact fmt mode x := by
  unfold clampDecimalExponent
  by_cases hs : x.significand = 0
  · simp [convertDecimalTextExact, hs]
  · simp only [hs, ↓reduceIte]
    by_cases hhi : max 0 (decimalSaturationHigh fmt / 3 + 1) < x.exponent
    · rw [min_eq_left hhi.le, max_eq_right ((min_le_left _ _).trans (le_max_left _ _))]
      refine convertDecimalTextExact_eq_of_high fmt mode _ x rfl hs hs ?_ ?_
      · exact high_le_log_decimal fmt _ hs _ (le_max_right _ _) (le_max_left _ _)
      · exact high_le_log_decimal fmt _ hs _ ((le_max_right _ _).trans hhi.le)
          ((le_max_left _ _).trans hhi.le)
    · by_cases hlo : x.exponent <
          min 0 ((decimalSaturationLow fmt - (x.significand.log2 : Int) - 1) / 3)
      · rw [min_eq_right ((hlo.le.trans (min_le_left _ _)).trans (le_max_left _ _)),
          max_eq_left hlo.le]
        refine convertDecimalTextExact_eq_of_low fmt mode _ x rfl hs hs ?_ ?_
        · exact log_decimal_le_low fmt _ hs _ (min_le_right _ _) (min_le_left _ _)
        · exact log_decimal_le_low fmt _ hs _ (hlo.le.trans (min_le_right _ _))
            (hlo.le.trans (min_le_left _ _))
      · simp only [not_lt] at hhi hlo
        rw [min_eq_right hhi, max_eq_right hlo]

/-- The fast decimal conversion agrees with the exact reference conversion on every input. -/
theorem convertDecimalText_eq_exact (fmt : FloatFormat) (mode : IEEERoundingMode)
    (x : DecimalText.Decimal) :
    convertDecimalText fmt mode x = convertDecimalTextExact fmt mode x :=
  convertDecimalTextExact_clampDecimalExponent fmt mode x

end FloatLib.Floats.Formats.BinaryInterchange.Model
