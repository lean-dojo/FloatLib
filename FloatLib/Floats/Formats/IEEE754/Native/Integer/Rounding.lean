/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.RoundingKernel.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.RoundToIntegral
public import Init.Data.SInt.Float
public import Init.Data.SInt.Float32

/-!
# Shared integer rounding at the native boundary

Here we show that Lean's integer conversion kernels compute the same results as FloatLib's
rational quantizer and dyadic integral rounder. No argument depends on a machine integer width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics
open Float.Model.UnpackedFloat

private theorem roundQuotientEven_scale_den_one (n p : Nat) :
    let scaled := RationalBinary.scaleByPowerOfTwo n 1 ((p : Int) - n.log2)
    roundQuotientEven scaled.1 scaled.2 =
      if p ≤ n.log2 then roundShiftRightEven n (n.log2 - p)
      else n <<< (p - n.log2) := by
  by_cases h : p ≤ n.log2
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    rw [hk]
    cases k with
    | zero =>
        simp [RationalBinary.scaleByPowerOfTwo, roundQuotientEven, Nat.mod_one,
          Numerics.roundShiftRightEven_def]
    | succ k =>
        have he : (p : Int) - (p + (k + 1)) = Int.negSucc k := by omega
        simp [he, RationalBinary.scaleByPowerOfTwo, Nat.shiftLeft_eq,
          ← roundShiftRightEven_eq_roundQuotientEven]
  · have he : (p : Int) - n.log2 = Int.ofNat (p - n.log2) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    simp [he, RationalBinary.scaleByPowerOfTwo, roundQuotientEven, Nat.mod_one, h]

/--
Rounding an integer magnitude as a denominator-one rational gives the same complete word as
dyadic rounding, in every format. The equality includes nearest-even ties and overflow. Outside
the IEEE encodings both sides use the descriptor-aware integer algorithms, and a nonzero integer
always lies in the normal range because the bias is positive.
-/
theorem roundRat_den_one_eq_roundDyadic (fmt : FloatFormat) (sign : Bool) (n : Nat) :
    roundRat fmt sign n 1 =
      roundDyadic fmt { negative := sign, significand := n, exponent := 0 } := by
  by_cases hfmt : fmt.isIEEE = true
  swap
  · rw [roundDyadic, ite_eq_right hfmt]
    by_cases hn : n = 0
    · subst n
      simp [roundRat, roundRatScaled, hfmt, roundRatScaledGeneral, roundDyadicGeneral]
    have hbias := fmt.exponentBias_pos
    have hnormal : ¬ (n.log2 : Int) < fmt.minNormalExponent := by
      unfold FloatFormat.minNormalExponent
      simp only [Int.ofNat_eq_natCast]
      omega
    have hunder : ¬ (n.log2 : Int) + 1 < fmt.minSubnormalExponent := by
      unfold FloatFormat.minSubnormalExponent FloatFormat.minNormalExponent
      simp only [Int.ofNat_eq_natCast]
      omega
    simp only [roundRat, roundRatScaled, hfmt, ↓reduceDIte, roundRatScaledGeneral,
      roundDyadicGeneral, beq_iff_eq, hn, Nat.one_ne_zero, ite_false,
      floorLog2_den_one n hn, Int.add_zero, hnormal, hunder, Bool.false_eq_true]
    simp only [Int.ofNat_eq_natCast, roundQuotientEven_scale_den_one]
  rw [roundDyadic, ite_eq_left hfmt, ieeeRoundDyadic_eq_internal]
  by_cases hn : n = 0
  · subst n
    simp [roundRat, roundRatScaled, hfmt, ieeeRoundRatScaled, Internal.ieeeRoundDyadic]
  have hmin : FloatFormat.ieeeMinNormalExponent fmt ≤ 0 := by
    have hbias := fmt.bias_pos
    unfold FloatFormat.ieeeMinNormalExponent
    simp only [Int.ofNat_eq_natCast]
    omega
  have hnormal : ¬ (n.log2 : Int) < FloatFormat.ieeeMinNormalExponent fmt := by omega
  have hunder : ¬ (n.log2 : Int) < -Int.ofNat (FloatFormat.normalMantissaExpOffset fmt) :=
    by simp only [Int.ofNat_eq_natCast]; omega
  simp only [roundRat, roundRatScaled, hfmt, ↓reduceDIte, ieeeRoundRatScaled,
    Internal.ieeeRoundDyadic, beq_iff_eq, hn, Nat.one_ne_zero, ite_false,
    floorLog2_den_one n hn, Int.add_zero, hnormal, hunder]
  simp only [Int.ofNat_eq_natCast, roundQuotientEven_scale_den_one]
  split_ifs <;> first | rfl | omega

/-- Lean's integer constructor is FloatLib's nearest-even dyadic rounding of that integer. -/
theorem ofModel_ofInt_eq_roundDyadic (fmt : FloatFormat)
    (hfmt : fmt.isIEEE = true) (n : Int) :
    ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel n) =
      roundDyadic fmt (Dyadic.ofScaledInt n 0) := by
  unfold Float.Model.UnpackedFloat.ofInt Float.Model.UnpackedFloat.normalize
  rw [roundDyadic, ite_eq_left hfmt]
  cases n with
  | ofNat n =>
      cases n with
      | zero => simp [Dyadic.ofScaledInt, ieeeRoundDyadic, modelSign]
      | succ n =>
          have hp : (0 : Int) < Int.ofNat (n + 1) := by simp
          have hc := Int.compare_eq_gt.mpr hp
          rw [hc]
          change ofModel fmt (Float.Model.UnpackedFloat.round fmt.toModel .positive
              (n + 1) 0) =
            ofModel fmt (Float.Model.UnpackedFloat.round fmt.toModel
              (modelSign (decide (Int.ofNat (n + 1) < 0))) (n + 1) 0)
          rw [decide_eq_false (not_lt.mpr hp.le)]
          rfl
  | negSucc n =>
      simp [Dyadic.ofScaledInt, ieeeRoundDyadic, modelSign, Int.compare_eq_lt.mpr]

/--
Lean's finite conversion kernel truncates toward zero the same dyadic that FloatLib decodes.
No rounding of the floating-point value happens before the truncation.
-/
theorem roundToInt_eq_roundDyadicToInt (sign : Sign) (mantissa : Nat) (exponent : Int) :
    Float.Model.UnpackedFloat.roundToInt sign mantissa exponent =
      roundDyadicToInt .towardZero
        { negative := modelSignBit sign, significand := mantissa, exponent } := by
  unfold Float.Model.UnpackedFloat.roundToInt decreaseExponent shiftToExponent
  simp only [extendedMantissa_shiftRight_mantissa, ExtendedMantissa.ofMantissaAndAccuracy]
  cases exponent <;> cases sign <;>
    simp [roundDyadicToInt, modelSignBit, Sign.apply, Nat.shiftRight_eq_div_pow] <;>
    intro h <;> simp [h]

end FloatLib.Floats.Formats.BinaryInterchange.Model
