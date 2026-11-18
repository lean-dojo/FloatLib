/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Proof
public import Mathlib.Data.Int.Log

/-!
# Logarithmic meaning of the positive-code quantum

For every descriptor and every positive real in a consecutive-code bracket,
the decoder's spacing exponent equals the logarithmic quantum of P3109 interim report v4.1,
14 September 2026, §4.7.4 (unapproved draft). The decoder is defined for all
natural indices, so this theorem does not impose a finite-encoding bound.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.ComparisonRounding

/-- A positive target's code bracket determines the report's logarithmic quantum. -/
theorem decodeQuantum_eq_log (format : Format) (index : Nat) (target : ℝ)
    (hpositive : 0 < target)
    (hlower : ((format.decodePositiveFinite index).toRat : ℝ) ≤ target)
    (hupper : target < ((format.decodePositiveFinite (index + 1)).toRat : ℝ)) :
    format.decodeQuantum index =
      max (Int.log 2 target) format.minimumNormalExponent - format.precision + 1 := by
  have hunit : 0 < 2 ^ format.trailingBits := Nat.two_pow_pos _
  have hpow (exponent : Int) (bits : Nat) :
      (2 : ℝ) ^ (exponent + bits) = 2 ^ bits * 2 ^ exponent := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp [mul_comm]
  have hminimum :
      format.minimumQuantumExponent + (format.trailingBits : Int) =
        format.minimumNormalExponent := by
    rw [format.minimumQuantumExponent_eq]
    simp only [Int.ofNat_eq_natCast]
    omega
  have hprecision : (format.trailingBits : Int) = (format.precision : Int) - 1 := by
    simpa only [Int.ofNat_eq_natCast] using format.trailingBits_int
  by_cases hsubnormal : index < 2 ^ format.trailingBits
  · have hquantum : format.decodeQuantum index = format.minimumQuantumExponent := by
      simpa using format.decodeQuantum_add_mul index 0 hsubnormal
    have hfirst : (1 : Int) - format.exponentBias + 1 - format.precision =
        format.minimumQuantumExponent := by
      unfold Format.minimumQuantumExponent
      simp only [Int.ofNat_eq_natCast]
      omega
    have hvalue :
        ((format.decodePositiveFinite (2 ^ format.trailingBits)).toRat : ℝ) =
          (2 : ℝ) ^ format.minimumNormalExponent := by
      have hv := format.decodePositiveFinite_toRat_add_mul 0 1 hunit (by decide)
      simp only [Nat.zero_add, Nat.one_mul, Nat.add_zero, Nat.cast_one] at hv
      rw [hv]
      push_cast
      rw [hfirst, ← hpow, hminimum]
    have hbound : target < (2 : ℝ) ^ format.minimumNormalExponent := by
      rw [← hvalue]
      exact hupper.trans_le (Rat.cast_le.mpr
        (format.decodePositiveFinite_strictMono.monotone (by omega)))
    have hlog := (Int.lt_zpow_iff_log_lt (by decide : 1 < 2) hpositive).mp hbound
    rw [max_eq_right hlog.le, hquantum]
    omega
  · have hnonzero : index ≠ 0 := by omega
    have hrow : index / 2 ^ format.trailingBits ≠ 0 :=
      (Nat.div_pos (by omega) hunit).ne'
    have hsignificand :
        2 ^ format.trailingBits ≤ (format.decodePositiveFinite index).significand := by
      simp [Format.decodePositiveFinite, hnonzero, hrow]
    have hsignificandUpper := format.decodePositiveFinite_significand_lt_precision index
    rw [format.decodePositiveFinite_succ_toRat,
      format.decodePositiveFinite_toRat_eq_significand_mul] at hupper
    rw [format.decodePositiveFinite_toRat_eq_significand_mul] at hlower
    push_cast at hlower hupper
    have hquantumPositive : (0 : ℝ) < 2 ^ format.decodeQuantum index :=
      zpow_pos (by norm_num) _
    have hleadingLower :
        (2 : ℝ) ^ (format.decodeQuantum index + format.trailingBits) ≤ target := by
      rw [hpow]
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hsignificand)
        hquantumPositive.le).trans hlower
    have hleadingUpper :
        target < (2 : ℝ) ^ (format.decodeQuantum index + format.precision) := by
      rw [hpow]
      have hcoefficient :
          ((format.decodePositiveFinite index).significand : ℝ) + 1 ≤
            (2 : ℝ) ^ format.precision := by
        exact_mod_cast (by omega :
          (format.decodePositiveFinite index).significand + 1 ≤ 2 ^ format.precision)
      exact hupper.trans_le (by nlinarith)
    have hlogLower :=
      (Int.zpow_le_iff_le_log (by decide : 1 < 2) hpositive).mp hleadingLower
    have hlogUpper :=
      (Int.lt_zpow_iff_log_lt (by decide : 1 < 2) hpositive).mp hleadingUpper
    have hminimumQuantum := minimumQuantumExponent_le_decodeQuantum format index
    have hnormal : format.minimumNormalExponent ≤ Int.log 2 target := by omega
    rw [max_eq_left hnormal]
    omega

end FloatLib.Floats.Formats.P3109.ComparisonRounding
