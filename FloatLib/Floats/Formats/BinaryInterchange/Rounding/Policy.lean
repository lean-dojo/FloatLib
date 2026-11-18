/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Grid

import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Dyadic.Packing

/-!
# Nearest-even rounding under every binary encoding policy

A finite executable dyadic result is the real grid rounding for IEEE, finite-with-NaN and
unsigned-zero encodings. Fully finite encodings clip that grid result to the signed finite
endpoints. The proof follows subnormal packing, normal packing, carry and overflow once for
arbitrary descriptors. Clipping is 1-Lipschitz and its displacement is the distance outside
the finite interval.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats FloatLib.Floats.Formats.Flocq FloatLib.Numerics

/-- A finite native overflow is necessarily saturation, including custom descriptor biases. -/
theorem encoding_finite_of_nativeOverflow {fmt : FloatFormat} (sign : Bool)
    (hfinite : isFinite (nativeOverflow fmt sign) = true) : fmt.encoding = .finite := by
  cases hencoding : fmt.encoding with
  | ieee =>
    have hinf : fmt.supportsInfinity = true := by simp [FloatFormat.supportsInfinity, hencoding]
    cases sign <;> simp [nativeOverflow, hencoding, isFinite_posInf fmt hinf,
      isFinite_negInf fmt hinf] at hfinite
  | finiteMaxNaN =>
    have hnan : isNaN (nativeOverflow fmt sign) = true := by
      simpa [nativeOverflow, hencoding] using
        isNaN_propagatedNaN fmt sign 0 (by simp [hencoding])
    have := isFinite_eq_false_of_isNaN hnan
    simp_all
  | finiteUnsignedZero =>
    have hnan : isNaN (nativeOverflow fmt sign) = true := by
      simp [nativeOverflow, invalidResult, negZero, isNaN, hencoding, ofBits]
    have := isFinite_eq_false_of_isNaN hnan
    simp_all
  | finite => rfl

/-- Packing the rounded subnormal interval preserves its signed grid value, including zero
and carry to the least normal value, for every descriptor. -/
theorem toReal_packRoundedSubnormal (fmt : FloatFormat) (sign : Bool) (r : Nat)
    (hr : r ≤ pow2 fmt.fracWidth) :
    toReal (packRoundedSubnormal fmt sign (zero fmt sign) r) =
      (if sign then (-1 : ℝ) else 1) * (r : ℝ) * Flocq.bpow binaryRadix
        fmt.minSubnormalExponent := by
  by_cases hzero : r = 0
  · simp [packRoundedSubnormal, hzero]
  by_cases hnormal : pow2 fmt.fracWidth ≤ r
  · have heq : r = pow2 fmt.fracWidth := Nat.le_antisymm hr hnormal
    simp only [packRoundedSubnormal, beq_iff_eq, hzero, ite_false, hnormal, ite_true]
    rw [heq, toReal_ofFields_normal fmt sign 1 0 one_ne_zero
      (FloatFormat.one_lt_expAllOnesNat fmt) (Nat.two_pow_pos _)]
    simp [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent]
  · simp only [packRoundedSubnormal, beq_iff_eq, hzero, ite_false, hnormal]
    exact toReal_ofFields_subnormal fmt sign r hzero
      (by simpa [pow2_eq_two_pow] using (lt_of_not_ge hnormal))

/-- Closed real value of either largest finite endpoint. -/
theorem toReal_maxFinite (fmt : FloatFormat) (sign : Bool) :
    toReal (maxFinite fmt sign) =
      (if sign then (-1 : ℝ) else 1) * toReal (posMaxFinite fmt) := by
  rw [show maxFinite fmt sign =
      ofFields fmt sign fmt.maxFiniteExpField fmt.maxFiniteFracField from rfl,
    toReal_ofFields_normal_of_isFinite fmt sign fmt.maxFiniteExpField
      fmt.maxFiniteFracField (Nat.ne_of_gt fmt.maxFiniteExpField_pos)
      fmt.maxFiniteExpField_lt_two_pow fmt.maxFiniteFracField_lt_two_pow
      (isFinite_maxFinite fmt sign), toReal_posMaxFinite]
  simp only [FloatFormat.maxNormalExponent, Int.ofNat_eq_natCast, mul_assoc]

/-- Finite native overflow delivers the signed finite endpoint. -/
theorem toReal_nativeOverflow_of_isFinite {fmt : FloatFormat} (sign : Bool)
    (hfinite : isFinite (nativeOverflow fmt sign) = true) :
    toReal (nativeOverflow fmt sign) =
      (if sign then (-1 : ℝ) else 1) * toReal (posMaxFinite fmt) := by
  rw [nativeOverflow, encoding_finite_of_nativeOverflow sign hfinite]
  exact toReal_maxFinite fmt sign

/-- Native overflow is finite exactly for a fully finite encoding. -/
theorem isFinite_nativeOverflow_eq (fmt : FloatFormat) (sign : Bool) :
    isFinite (nativeOverflow fmt sign) = decide (fmt.encoding = .finite) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ⟨encoding_finite_of_nativeOverflow sign, fun h => by
    simpa only [nativeOverflow, h] using isFinite_maxFinite fmt sign⟩

/-- A normalized significand has magnitude at least its leading power of two. -/
theorem bpow_le_normalizedMagnitude (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hlow : pow2 fmt.fracWidth ≤ mantissa) :
    Flocq.bpow binaryRadix exponent ≤ (mantissa : ℝ) * Flocq.bpow binaryRadix (exponent -
      fmt.fracWidth) := by
  calc
    Flocq.bpow binaryRadix exponent =
        (pow2 fmt.fracWidth : ℝ) * Flocq.bpow binaryRadix (exponent - fmt.fracWidth) := by
      rw [natCast_pow2_eq_bpow]
      rw [← Flocq.bpow.add_exp]
      congr 1
      omega
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hlow) (bpow_nonneg _)

/-- An exponent beyond the finite range gives a magnitude strictly above the endpoint. -/
theorem posMaxFinite_lt_normalizedMagnitude_of_exponent (fmt : FloatFormat)
    (mantissa : Nat) (exponent : Int) (hlow : pow2 fmt.fracWidth ≤ mantissa)
    (hover : fmt.maxNormalExponent < exponent) :
    toReal (posMaxFinite fmt) <
      (mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - fmt.fracWidth) :=
  (toReal_posMaxFinite_lt_bpow fmt).trans_le
    ((bpow_le_bpow_of_le (by omega)).trans
      (bpow_le_normalizedMagnitude fmt mantissa exponent hlow))

/-- The reserved-fraction packing guard detects a magnitude strictly above the endpoint. -/
theorem posMaxFinite_lt_normalizedMagnitude_of_guard (fmt : FloatFormat)
    (mantissa : Nat) (exponent : Int) (hlow : pow2 fmt.fracWidth ≤ mantissa)
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hmax : exponent ≤ fmt.maxNormalExponent)
    (hguard :
      (decide ((exponent + Int.ofNat fmt.exponentBias).toNat > fmt.maxFiniteExpField) ||
        (exponent + Int.ofNat fmt.exponentBias).toNat == fmt.maxFiniteExpField &&
          decide (mantissa - pow2 fmt.fracWidth > fmt.maxFiniteFracField)) = true) :
    toReal (posMaxFinite fmt) <
      (mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - fmt.fracWidth) := by
  have hexponent := encodedExponent_le_maxFiniteExpField fmt exponent hmax
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hguard
  have hfield :
      Int.toNat (exponent + Int.ofNat fmt.exponentBias) = fmt.maxFiniteExpField ∧
        fmt.maxFiniteFracField < mantissa - pow2 fmt.fracWidth := by omega
  have htotal : exponent = fmt.maxNormalExponent := by
    have hfieldInt := congrArg Int.ofNat hfield.1
    rw [ofNat_toNat_biasedExponent fmt exponent hmin] at hfieldInt
    unfold FloatFormat.maxNormalExponent
    omega
  rw [toReal_posMaxFinite, ← htotal]
  apply mul_lt_mul_of_pos_right _ (bpow_pos _)
  exact_mod_cast (show pow2 fmt.fracWidth + fmt.maxFiniteFracField < mantissa by omega)

/-- A full significand carry renormalizes to the leading bit at the next exponent. -/
theorem packRoundedNormal_carry (fmt : FloatFormat) (sign : Bool)
    (overflow : Model fmt) (exponent : Int) :
    packRoundedNormal fmt sign overflow exponent (pow2 (fmt.fracWidth + 1)) =
      packRoundedNormal fmt sign overflow (exponent + 1) (pow2 fmt.fracWidth) := by
  simp only [packRoundedNormal, beq_iff_eq,
    Nat.ne_of_lt (pow2_lt_pow2_succ fmt.fracWidth), ite_false, ite_true]

/-- Renormalizing a full significand carry preserves its real magnitude. -/
theorem normalizedMagnitude_carry (fmt : FloatFormat) (exponent : Int) :
    (pow2 fmt.fracWidth : ℝ) * Flocq.bpow binaryRadix (exponent + 1 - fmt.fracWidth) =
      (pow2 (fmt.fracWidth + 1) : ℝ) *
        Flocq.bpow binaryRadix (exponent - fmt.fracWidth) := by
  rw [natCast_pow2_eq_bpow, natCast_pow2_eq_bpow,
    ← Flocq.bpow.add_exp, ← Flocq.bpow.add_exp]
  congr 1
  omega

/-- Packing a normalized significand with a finite overflow endpoint clips its magnitude.
An exceptional overflow preserves the grid value whenever the packed result is finite. -/
theorem toReal_packRoundedNormal_normalized (fmt : FloatFormat) (sign : Bool)
    (overflow : Model fmt)
    (mantissa : Nat) (exponent : Int)
    (hlow : pow2 fmt.fracWidth ≤ mantissa)
    (hhigh : mantissa < pow2 (fmt.fracWidth + 1))
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hoverflow : isFinite overflow = true →
      toReal overflow = (if sign then (-1 : ℝ) else 1) * toReal (posMaxFinite fmt))
    (hfinite : isFinite
      (packRoundedNormal fmt sign overflow exponent mantissa) = true) :
    toReal (packRoundedNormal fmt sign overflow exponent mantissa) =
      (if sign then (-1 : ℝ) else 1) *
        (if isFinite overflow then
          min ((mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - fmt.fracWidth))
            (toReal (posMaxFinite fmt))
        else (mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - fmt.fracWidth)) := by
  simp only [packRoundedNormal, beq_iff_eq, (Nat.ne_of_lt hhigh), ite_false] at hfinite ⊢
  by_cases hover : fmt.maxNormalExponent < exponent
  · simp only [hover, ite_true] at hfinite ⊢
    have hm :=
      (posMaxFinite_lt_normalizedMagnitude_of_exponent fmt mantissa exponent hlow hover).le
    rw [hoverflow hfinite]
    simp only [hfinite, ite_true, min_eq_right hm]
  · simp only [hover, ite_false] at hfinite ⊢
    by_cases hguard :
        (decide ((exponent + Int.ofNat fmt.exponentBias).toNat > fmt.maxFiniteExpField) ||
          (exponent + Int.ofNat fmt.exponentBias).toNat == fmt.maxFiniteExpField &&
            decide (mantissa - pow2 fmt.fracWidth > fmt.maxFiniteFracField)) = true
    · rw [ite_eq_left hguard] at hfinite ⊢
      have hm := (posMaxFinite_lt_normalizedMagnitude_of_guard fmt mantissa exponent
        hlow hmin (le_of_not_gt hover) hguard).le
      rw [hoverflow hfinite]
      simp only [hfinite, ite_true, min_eq_right hm]
    · rw [ite_eq_right hguard] at hfinite ⊢
      have hvalue := toReal_ofFields_normalized_signed fmt sign mantissa exponent
        hlow hhigh hmin (le_of_not_gt hover) hfinite
      simp only [Int.ofNat_eq_natCast] at hvalue
      have hm := abs_toReal_le_posMaxFinite_of_isFinite _ hfinite
      simp only [Int.ofNat_eq_natCast] at hm ⊢
      rw [hvalue] at hm
      have habs :
          |(if sign then (-1 : ℝ) else 1) * (mantissa : ℝ) *
              Flocq.bpow binaryRadix (exponent - fmt.fracWidth)| =
            (mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - fmt.fracWidth) := by
        cases sign <;> simp [abs_mul, abs_of_nonneg (bpow_nonneg _)]
      rw [habs] at hm
      rw [hvalue, min_eq_left hm]
      simp only [ite_self, mul_assoc]

/-- Carry preserves the grid value with any overflow result satisfying the endpoint contract. -/
theorem toReal_packRoundedNormal_of_overflow (fmt : FloatFormat) (sign : Bool)
    (overflow : Model fmt)
    (mantissa : Nat) (exponent : Int)
    (hlow : pow2 fmt.fracWidth ≤ mantissa)
    (hhigh : mantissa ≤ pow2 (fmt.fracWidth + 1))
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hoverflow : isFinite overflow = true →
      toReal overflow = (if sign then (-1 : ℝ) else 1) * toReal (posMaxFinite fmt))
    (hfinite : isFinite
      (packRoundedNormal fmt sign overflow exponent mantissa) = true) :
    toReal (packRoundedNormal fmt sign overflow exponent mantissa) =
      (if sign then (-1 : ℝ) else 1) *
        (if isFinite overflow then
          min ((mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - fmt.fracWidth))
            (toReal (posMaxFinite fmt))
        else (mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - fmt.fracWidth)) := by
  by_cases hcarry : mantissa = pow2 (fmt.fracWidth + 1)
  · rw [hcarry, packRoundedNormal_carry] at hfinite ⊢
    rw [toReal_packRoundedNormal_normalized fmt sign overflow _ _ le_rfl
      (pow2_lt_pow2_succ fmt.fracWidth) (by omega) hoverflow hfinite]
    rw [normalizedMagnitude_carry]
  · exact toReal_packRoundedNormal_normalized fmt sign overflow mantissa exponent
      hlow (lt_of_le_of_ne hhigh hcarry) hmin hoverflow hfinite

/-- Carry renormalization preserves the rounded grid value; only fully finite formats saturate. -/
theorem toReal_packRoundedNormal (fmt : FloatFormat) (sign : Bool)
    (mantissa : Nat) (exponent : Int)
    (hlow : pow2 fmt.fracWidth ≤ mantissa)
    (hhigh : mantissa ≤ pow2 (fmt.fracWidth + 1))
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hfinite : isFinite
      (packRoundedNormal fmt sign (nativeOverflow fmt sign) exponent mantissa) = true) :
    toReal (packRoundedNormal fmt sign (nativeOverflow fmt sign) exponent mantissa) =
      (if sign then (-1 : ℝ) else 1) *
        (if fmt.encoding = .finite then
          min ((mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - fmt.fracWidth))
            (toReal (posMaxFinite fmt))
        else (mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - fmt.fracWidth)) := by
  simpa only [isFinite_nativeOverflow_eq, decide_eq_true_eq] using
    toReal_packRoundedNormal_of_overflow fmt sign (nativeOverflow fmt sign)
      mantissa exponent hlow hhigh hmin (toReal_nativeOverflow_of_isFinite sign) hfinite

/-- Clipping to the signed finite endpoints of a descriptor. -/
noncomputable def clampAt (fmt : FloatFormat) (x : ℝ) : ℝ :=
  max (-toReal (posMaxFinite fmt)) (min x (toReal (posMaxFinite fmt)))

/-- Signed nonnegative magnitudes clip by taking their minimum with the positive endpoint. -/
theorem clampAt_signedMagnitude (fmt : FloatFormat) (sign : Bool) {v : ℝ}
    (hv : 0 ≤ v) :
    clampAt fmt ((if sign then (-1 : ℝ) else 1) * v) =
      (if sign then (-1 : ℝ) else 1) * min v (toReal (posMaxFinite fmt)) := by
  have hM := (toReal_posMaxFinite_pos fmt).le
  cases sign
  · simp only [Bool.false_eq_true, ite_false, one_mul, clampAt]
    exact max_eq_right (le_trans (neg_nonpos.mpr hM) (le_min hv hM))
  · simp only [ite_true, neg_one_mul, clampAt]
    rw [min_eq_left ((neg_nonpos.mpr hv).trans hM), max_neg_neg, min_comm]

/-- Clipping fixes every real value between the finite endpoints. -/
theorem clampAt_eq_self (fmt : FloatFormat) {x : ℝ}
    (hx : |x| ≤ toReal (posMaxFinite fmt)) : clampAt fmt x = x := by
  rcases abs_le.mp hx with ⟨hlo, hhi⟩
  exact (congrArg (max (-toReal (posMaxFinite fmt))) (min_eq_left hhi)).trans
    (max_eq_right hlo)

/-- The smallest normal magnitude is within the descriptor's finite endpoints. -/
theorem bpow_minNormal_le_posMaxFinite (fmt : FloatFormat) :
    Flocq.bpow binaryRadix fmt.minNormalExponent ≤ toReal (posMaxFinite fmt) := by
  apply (bpow_le_bpow_of_le (minNormalExponent_le_maxNormalExponent fmt)).trans
  have h := bpow_le_normalizedMagnitude fmt
    (pow2 fmt.fracWidth + fmt.maxFiniteFracField) fmt.maxNormalExponent (Nat.le_add_right _ _)
  simpa [toReal_posMaxFinite] using h

/-- Every rounded subnormal magnitude, including its carry, is within the finite range. -/
theorem subnormalMagnitude_le_posMaxFinite (fmt : FloatFormat) (mantissa : Nat)
    (hm : mantissa ≤ pow2 fmt.fracWidth) :
    (mantissa : ℝ) * Flocq.bpow binaryRadix fmt.minSubnormalExponent ≤
      toReal (posMaxFinite fmt) := by
  calc
    _ ≤ (pow2 fmt.fracWidth : ℝ) * Flocq.bpow binaryRadix fmt.minSubnormalExponent :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (bpow_nonneg _)
    _ = Flocq.bpow binaryRadix fmt.minNormalExponent := by
      rw [natCast_pow2_eq_bpow, ← Flocq.bpow.add_exp]
      congr 1
      have := minSubnormalExponent_add_fracWidth fmt
      simp only [Int.ofNat_eq_natCast] at this
      omega
    _ ≤ _ := bpow_minNormal_le_posMaxFinite fmt

/-- Above the subnormal range, real rounding uses the normalized significand rounder. -/
theorem roundAt_dyadic_normal (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hnormal : fmt.minNormalExponent ≤ (d.significand.log2 : Int) + d.exponent) :
    roundAt fmt d.toReal =
      (if d.negative then (-1 : ℝ) else 1) *
        (roundMantissaToLeadingBitEven d.significand fmt.fracWidth : ℝ) *
          Flocq.bpow binaryRadix ((d.significand.log2 : Int) + d.exponent - fmt.fracWidth) := by
  have htarget :
      max ((d.significand.log2 : Int) + d.exponent - fmt.fracWidth)
        fmt.minSubnormalExponent =
      (d.significand.log2 : Int) + d.exponent - fmt.fracWidth := by
    apply max_eq_left
    unfold FloatFormat.minSubnormalExponent
    simp only [Int.ofNat_eq_natCast]
    omega
  rw [roundAt_dyadic_grid, htarget,
    roundMantissaAtExponentEven_eq_roundMantissaToLeadingBitEven]

/-- Finite nearest-even dyadic rounding follows the descriptor's actual overflow policy.
Fully finite encodings clip the real grid result; every other encoding preserves that result. -/
theorem toReal_roundDyadic_policy (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hfinite : isFinite (roundDyadic fmt d) = true) :
    toReal (roundDyadic fmt d) =
      if fmt.encoding = .finite then clampAt fmt (roundAt fmt d.toReal)
      else roundAt fmt d.toReal := by
  rw [← roundDyadicGeneral_eq_roundDyadic] at hfinite ⊢
  by_cases hm : d.significand = 0
  · have hz : d.toReal = 0 := by
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hm]
    have hM := (toReal_posMaxFinite_pos fmt).le
    simp [roundDyadicGeneral, hm, hz, clampAt, hM]
  by_cases hover : fmt.maxNormalExponent < (d.significand.log2 : Int) + d.exponent
  · simp only [roundDyadicGeneral, beq_iff_eq, hm, ite_false, hover, ite_true] at hfinite ⊢
    have hnormal : fmt.minNormalExponent ≤ (d.significand.log2 : Int) + d.exponent :=
      (minNormalExponent_le_maxNormalExponent fmt).trans hover.le
    have hmag : toReal (posMaxFinite fmt) ≤
        (roundMantissaToLeadingBitEven d.significand fmt.fracWidth : ℝ) *
          Flocq.bpow binaryRadix ((d.significand.log2 : Int) + d.exponent - fmt.fracWidth) :=
      (toReal_posMaxFinite_lt_bpow fmt).le.trans
        ((bpow_le_bpow_of_le (by omega)).trans
          (bpow_le_normalizedMagnitude fmt _ _
            (pow2_le_roundMantissaToLeadingBitEven _ _ hm)))
    rw [toReal_nativeOverflow_of_isFinite d.negative hfinite,
      ite_eq_left (encoding_finite_of_nativeOverflow d.negative hfinite),
      roundAt_dyadic_normal fmt d hnormal, mul_assoc,
      clampAt_signedMagnitude fmt d.negative
        (mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _)), min_eq_right hmag]
  by_cases hsub : (d.significand.log2 : Int) + d.exponent < fmt.minNormalExponent
  · simp only [roundDyadicGeneral, beq_iff_eq, hm, ite_false, hover, hsub, ite_true]
      at hfinite ⊢
    change toReal (packRoundedSubnormal fmt d.negative (zero fmt d.negative)
      (match d.exponent - fmt.minSubnormalExponent with
      | .ofNat shift => d.significand <<< shift
      | .negSucc shift => Numerics.roundShiftRightEven d.significand (shift + 1))) = _
    have halign :
        (match d.exponent - fmt.minSubnormalExponent with
        | .ofNat shift => d.significand <<< shift
        | .negSucc shift => Numerics.roundShiftRightEven d.significand (shift + 1)) =
          roundMantissaAtExponentEven d.significand d.exponent fmt.minSubnormalExponent :=
      (roundMantissaAtExponentEven_eq_match d.significand d.exponent
        fmt.minSubnormalExponent).symm
    rw [halign]
    have hr : roundMantissaAtExponentEven d.significand d.exponent
        fmt.minSubnormalExponent ≤ pow2 fmt.fracWidth := by
      apply roundMantissaAtExponentEven_le_pow2_of_below
      simpa only [← minSubnormalExponent_add_fracWidth fmt, Int.ofNat_eq_natCast] using hsub
    have htarget :
        max ((d.significand.log2 : Int) + d.exponent - fmt.fracWidth)
          fmt.minSubnormalExponent = fmt.minSubnormalExponent := by
      apply max_eq_right
      unfold FloatFormat.minSubnormalExponent at *
      simp only [Int.ofNat_eq_natCast] at *
      omega
    have hround := roundAt_dyadic_grid fmt d
    dsimp only at hround
    rw [htarget] at hround
    have hmag :
        (roundMantissaAtExponentEven d.significand d.exponent fmt.minSubnormalExponent : ℝ) *
          Flocq.bpow binaryRadix fmt.minSubnormalExponent ≤ toReal (posMaxFinite fmt) :=
      subnormalMagnitude_le_posMaxFinite fmt _ hr
    have hbounded : |roundAt fmt d.toReal| ≤ toReal (posMaxFinite fmt) := by
      rw [hround]
      cases d.negative <;>
        simpa [abs_mul, abs_of_nonneg (bpow_nonneg _)] using hmag
    rw [toReal_packRoundedSubnormal fmt d.negative _ hr,
      clampAt_eq_self fmt hbounded, hround]
    simp only [ite_self]
  · have hnormal := le_of_not_gt hsub
    simp only [roundDyadicGeneral, beq_iff_eq, hm, ite_false, hover, hsub] at hfinite ⊢
    change toReal (packRoundedNormal fmt d.negative (nativeOverflow fmt d.negative)
      ((d.significand.log2 : Int) + d.exponent)
      (roundMantissaToLeadingBitEven d.significand fmt.fracWidth)) = _
    change isFinite (packRoundedNormal fmt d.negative (nativeOverflow fmt d.negative)
      ((d.significand.log2 : Int) + d.exponent)
      (roundMantissaToLeadingBitEven d.significand fmt.fracWidth)) = true at hfinite
    rw [toReal_packRoundedNormal fmt d.negative _ _
      (pow2_le_roundMantissaToLeadingBitEven _ _ hm)
      (roundMantissaToLeadingBitEven_le_pow2_succ _ _) hnormal hfinite,
      roundAt_dyadic_normal fmt d hnormal, mul_assoc,
      clampAt_signedMagnitude fmt d.negative
        (mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _))]
    by_cases henc : fmt.encoding = .finite <;> simp [henc]

/-- Clipping to finite endpoints is 1-Lipschitz. -/
theorem abs_clampAt_sub_clampAt_le (fmt : FloatFormat) (x y : ℝ) :
    |clampAt fmt x - clampAt fmt y| ≤ |x - y| := by
  unfold clampAt
  rw [max_comm (-toReal (posMaxFinite fmt)) (min x _),
    max_comm (-toReal (posMaxFinite fmt)) (min y _)]
  apply (abs_max_sub_max_le_abs _ _ _).trans
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (x - y))] using
    abs_min_sub_min_le_max x (toReal (posMaxFinite fmt)) y (toReal (posMaxFinite fmt))

/-- Clipping loses exactly the distance outside the finite interval. -/
theorem abs_clampAt_sub_self (fmt : FloatFormat) (x : ℝ) :
    |clampAt fmt x - x| = max 0 (|x| - toReal (posMaxFinite fmt)) := by
  have hM := (toReal_posMaxFinite_pos fmt).le
  by_cases hlo : x ≤ -toReal (posMaxFinite fmt)
  · have hxm : x ≤ toReal (posMaxFinite fmt) := by linarith
    have hx0 : x ≤ 0 := by linarith
    simp only [clampAt, min_eq_left hxm, max_eq_left hlo, abs_of_nonpos hx0]
    rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
    ring
  by_cases hhi : toReal (posMaxFinite fmt) ≤ x
  · have hx0 : 0 ≤ x := hM.trans hhi
    simp only [clampAt, min_eq_right hhi, max_eq_right (by linarith :
      -toReal (posMaxFinite fmt) ≤ toReal (posMaxFinite fmt)), abs_of_nonneg hx0]
    rw [abs_of_nonpos (by linarith), max_eq_right (by exact sub_nonneg.mpr hhi)]
    exact neg_sub _ _
  · have hx : |x| ≤ toReal (posMaxFinite fmt) :=
      abs_le.mpr ⟨(not_le.mp hlo).le, (not_le.mp hhi).le⟩
    rw [clampAt_eq_self fmt hx, sub_self, abs_zero, max_eq_left (sub_nonpos.mpr hx)]

end FloatLib.Floats.Formats.BinaryInterchange.Model
