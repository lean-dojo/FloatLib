/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.PositiveBounds
public import FloatLib.Floats.Formats.BinaryInterchange.Model.SignedERealSemantics

/-!
# Signed bounds for conventional IEEE directed dyadic rounding

Here the semantic contracts of `roundDyadicDown` and `roundDyadicUp` become outward bounds for
signed dyadics. For every exact signed dyadic and conventional IEEE `FloatFormat`, executable
downward rounding is an extended-real lower bound and executable upward rounding is an
extended-real upper bound.

Infinities are handled by the positive-magnitude results. Upward rounding of a negative input swaps
the magnitude rounders and reverses order under negation. In a format with signed zeros, downward
rounding is the negation of upward rounding of the negated input
(`roundDyadicDown_eq_neg_roundDyadicUp_neg`), so its non-NaN and lower-bound theorems follow from
the upward ones.

For every descriptor, the directed rounders, the nearest-even general rounder and the packing
helpers they share turn a nonnegative exact value into a value with a nonnegative real meaning. A
value that is not finite denotes zero, and that covers the NaN a finite-unsigned-zero encoding
delivers on overflow.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats

section

/-- Overflow results of opposite signs are negations of each other, in every encoding. -/
theorem nativeOverflow_true_eq_neg_false (fmt : FloatFormat) :
    nativeOverflow fmt true = neg (nativeOverflow fmt false) := by
  cases hencoding : fmt.encoding with
  | ieee => simp [nativeOverflow, hencoding]
  | finiteMaxNaN =>
      rw [show nativeOverflow fmt false =
          ofFields fmt false fmt.expAllOnesNat fmt.fracMaskNat by
        simp [nativeOverflow, propagatedNaN, hencoding]]
      rw [neg_ofFields_of_supportsSignedZero fmt
        (by simp [FloatFormat.supportsSignedZero, hencoding])]
      simp [nativeOverflow, propagatedNaN, hencoding]
  | finiteUnsignedZero =>
      have hnan : isNaN (negZero fmt) = true := by
        simp [isNaN, hencoding, negZero, ofBits]
      simp only [nativeOverflow, invalidResult, hencoding]
      exact (neg_eq_self_of_not_supportsSignedZero_of_isNaN (negZero fmt)
        (by simp [FloatFormat.supportsSignedZero, hencoding]) hnan).symm
  | finite => simp [nativeOverflow, hencoding]

/--
Negating a positive packed word with in-range fields sets the sign of the same fields, unless the
word is zero. This holds in every encoding. At zero an unsigned-zero format keeps its single zero.
-/
private theorem neg_ofFields_false_of_isZero_eq_false (fmt : FloatFormat)
    (exponent fraction : Nat)
    (hexponent : exponent < 2 ^ fmt.expWidth) (hfraction : fraction < 2 ^ fmt.fracWidth)
    (hzero : isZero (ofFields fmt false exponent fraction) = false) :
    neg (ofFields fmt false exponent fraction) = ofFields fmt true exponent fraction := by
  by_cases hsigned : fmt.supportsSignedZero = true
  · exact neg_ofFields_of_supportsSignedZero fmt hsigned false exponent fraction
  · have hencoding : fmt.encoding = .finiteUnsignedZero := by
      simpa [FloatFormat.supportsSignedZero] using hsigned
    have hfinite : isFinite (ofFields fmt false exponent fraction) = true := by
      rw [isFinite_ofFields fmt false exponent fraction hexponent hfraction, hencoding]
      rfl
    rw [neg_eq_toggleSign_of_isNaN_eq_false_of_isZero_eq_false _
      (isNaN_eq_false_of_isFinite_eq_true _ hfinite) hzero, toggleSign_ofFields]
    rfl

/-- Downward magnitude rounding written with the named alignment and normalization helpers. -/
private theorem roundDyadicMagnitudeDown_eq_helpers
    (fmt : FloatFormat) (sign : Bool) (mantissa : Nat) (exponent : Int) :
    roundDyadicMagnitudeDown fmt sign mantissa exponent =
      if Int.ofNat mantissa.log2 + exponent > fmt.maxNormalExponent then
        maxFinite fmt sign
      else if Int.ofNat mantissa.log2 + exponent < fmt.minSubnormalExponent then
        zero fmt sign
      else if Int.ofNat mantissa.log2 + exponent < fmt.minNormalExponent then
        if roundMantissaAtExponentDown mantissa exponent fmt.minSubnormalExponent == 0 then
          zero fmt sign
        else
          ofFields fmt sign 0
            (roundMantissaAtExponentDown mantissa exponent fmt.minSubnormalExponent)
      else if Int.toNat (Int.ofNat mantissa.log2 + exponent + Int.ofNat fmt.exponentBias) >
            fmt.maxFiniteExpField ||
          (Int.toNat (Int.ofNat mantissa.log2 + exponent + Int.ofNat fmt.exponentBias) ==
              fmt.maxFiniteExpField &&
            roundMantissaToLeadingBitDown mantissa fmt.fracWidth - pow2 fmt.fracWidth >
              fmt.maxFiniteFracField) then
        maxFinite fmt sign
      else
        ofFields fmt sign
          (Int.toNat (Int.ofNat mantissa.log2 + exponent + Int.ofNat fmt.exponentBias))
          (roundMantissaToLeadingBitDown mantissa fmt.fracWidth - pow2 fmt.fracWidth) := by
  rw [roundMantissaAtExponentDown_eq_match]
  rfl

/--
Rounding a magnitude downward and attaching a negative sign is the negation of the same rounded
magnitude with a positive sign, in every encoding. A format with a single zero rounds both signs of
a vanishing magnitude to that zero.
-/
theorem roundDyadicMagnitudeDown_true_eq_neg_false
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) :
    roundDyadicMagnitudeDown fmt true mantissa exponent =
      neg (roundDyadicMagnitudeDown fmt false mantissa exponent) := by
  have hzero : zero fmt true = neg (zero fmt false) := by
    rw [show zero fmt false = posZero fmt by simp [zero], neg_posZero]
  have hexponentWidth := fmt.maxFiniteExpField_lt_two_pow
  have hfractionLt := roundMantissaAtExponentDown_minSubnormal_lt_pow2 fmt mantissa exponent
  have hroundedHigh := roundMantissaToLeadingBitDown_lt_pow2_succ mantissa fmt.fracWidth
  rw [roundDyadicMagnitudeDown_eq_helpers, roundDyadicMagnitudeDown_eq_helpers]
  generalize roundMantissaAtExponentDown mantissa exponent fmt.minSubnormalExponent = fraction
    at hfractionLt ⊢
  generalize roundMantissaToLeadingBitDown mantissa fmt.fracWidth = rounded at hroundedHigh ⊢
  rw [pow2_eq_two_pow] at hfractionLt
  rw [pow2_eq_two_pow, pow_succ] at hroundedHigh
  split_ifs with hoverflow hunderflow hsubnormal hfraction hguard
  · simp
  · exact hzero
  · exact hzero
  · have hlt := hfractionLt (by simpa only [Int.ofNat_eq_natCast] using hsubnormal)
    rw [beq_iff_eq] at hfraction
    apply (neg_ofFields_false_of_isZero_eq_false fmt 0 _ (Nat.two_pow_pos _) hlt _).symm
    rw [isZero_ofFields fmt false 0 _ (Nat.two_pow_pos _) hlt]
    cases fmt.encoding <;> simp [hfraction]
  · simp
  · have hnormal : fmt.minNormalExponent ≤ Int.ofNat mantissa.log2 + exponent :=
      le_of_not_gt hsubnormal
    have hencodedNe := encodedExponent_ne_zero fmt _ hnormal
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
      not_or, not_and, not_lt] at hguard
    have hexponent :
        Int.toNat (Int.ofNat mantissa.log2 + exponent + Int.ofNat fmt.exponentBias) <
          2 ^ fmt.expWidth := by
      omega
    have hfractionField : rounded - pow2 fmt.fracWidth < 2 ^ fmt.fracWidth := by
      rw [pow2_eq_two_pow]
      omega
    apply (neg_ofFields_false_of_isZero_eq_false fmt _ _ hexponent hfractionField _).symm
    rw [isZero_ofFields fmt false _ _ hexponent hfractionField]
    have hencodedNe' :
        (Int.toNat (Int.ofNat mantissa.log2 + exponent + Int.ofNat fmt.exponentBias) == 0) =
          false := by
      simpa using hencodedNe
    cases fmt.encoding <;> simp only [hencodedNe', Bool.and_false, Bool.false_and]

/--
Rounding a magnitude upward and attaching a negative sign is the negation of the same rounded
magnitude with a positive sign, in a format with signed zeros.
-/
theorem roundDyadicMagnitudeUp_true_eq_neg_false
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hsigned : fmt.supportsSignedZero = true) :
    roundDyadicMagnitudeUp fmt true mantissa exponent =
      neg (roundDyadicMagnitudeUp fmt false mantissa exponent) := by
  have hoverflow := nativeOverflow_true_eq_neg_false fmt
  have hmin : ofFields fmt true 0 1 = neg (ofFields fmt false 0 1) := by
    rw [neg_ofFields_of_supportsSignedZero fmt hsigned]
    rfl
  have hsubnormal (fraction : Nat) :
      packRoundedSubnormal fmt true (ofFields fmt true 0 1) fraction =
        neg (packRoundedSubnormal fmt false (ofFields fmt false 0 1) fraction) := by
    simp only [packRoundedSubnormal, neg_ite]
    simp only [← hmin, neg_ofFields_of_supportsSignedZero fmt hsigned,
      Bool.not_false]
  have hnormal (totalExponent : Int) (roundedMantissa : Nat) :
      packRoundedNormal fmt true (nativeOverflow fmt true)
          totalExponent roundedMantissa =
        neg (packRoundedNormal fmt false (nativeOverflow fmt false)
          totalExponent roundedMantissa) := by
    simp only [packRoundedNormal, neg_ite]
    simp only [← hoverflow, neg_ofFields_of_supportsSignedZero fmt hsigned,
      Bool.not_false]
  simp only [roundDyadicMagnitudeUp, neg_ite]
  simp only [← hmin, ← hoverflow, ← hsubnormal, ← hnormal]

/--
Directed-down rounding of a nonzero negative dyadic negates upward rounding of its magnitude, in a
format with signed zeros.
-/
theorem roundDyadicDown_eq_neg_roundDyadicPosUp_of_negative
    (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hsigned : fmt.supportsSignedZero = true)
    (hmant : d.significand ≠ 0) (hsign : d.negative = true) :
    roundDyadicDown fmt d = neg (roundDyadicPosUp fmt d.significand d.exponent) := by
  simp only [roundDyadicDown, beq_iff_eq, hmant, ite_false, hsign, ite_true, roundDyadicPosUp]
  exact roundDyadicMagnitudeUp_true_eq_neg_false fmt d.significand d.exponent hsigned

/--
Directed-up rounding of a nonzero negative dyadic negates downward rounding of its magnitude, in
every encoding.
-/
theorem roundDyadicUp_eq_neg_roundDyadicPosDown_of_negative
    (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hmant : d.significand ≠ 0) (hsign : d.negative = true) :
    roundDyadicUp fmt d = neg (roundDyadicPosDown fmt d.significand d.exponent) := by
  simp only [roundDyadicUp, beq_iff_eq, hmant, ite_false, hsign, ite_true, roundDyadicPosDown]
  exact roundDyadicMagnitudeDown_true_eq_neg_false fmt d.significand d.exponent

/-- Negating a dyadic negates its real value. -/
theorem Dyadic.toReal_neg (d : Numerics.Dyadic) : d.neg.toReal = -d.toReal := by
  cases hsign : d.negative <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hsign]

/--
In a format with signed zeros, directed-down rounding is negated directed-up rounding of the
negated dyadic, signed zeros included, because negation exchanges the downward magnitude rounder
with the upward one. Only `roundDyadicMagnitudeUp_true_eq_neg_false` needs the signed-zero
premise. The downward magnitude reflection holds in every encoding.
-/
theorem roundDyadicDown_eq_neg_roundDyadicUp_neg (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hsigned : fmt.supportsSignedZero = true) :
    roundDyadicDown fmt d = neg (roundDyadicUp fmt d.neg) := by
  rcases d with ⟨negative, significand, exponent⟩
  by_cases hmant : significand = 0
  · subst hmant
    cases negative <;>
      simp [roundDyadicDown, roundDyadicUp, zero, hsigned, neg_negZero_of_supportsSignedZero]
  · cases negative
    · simp [roundDyadicDown, roundDyadicUp, hmant, roundDyadicMagnitudeDown_true_eq_neg_false]
    · simp [roundDyadicDown, roundDyadicUp, hmant,
        roundDyadicMagnitudeUp_true_eq_neg_false fmt _ _ hsigned]

/-- In a conventional IEEE format, directed-up rounding of an exact dyadic never produces a NaN. -/
theorem isNaN_roundDyadicUp_eq_false
    (fmt : FloatFormat) (d : Numerics.Dyadic) (hfmt : fmt.isIEEE = true) :
    isNaN (roundDyadicUp fmt d) = false := by
  by_cases hmant : d.significand = 0
  · cases hsign : d.negative <;> simp [roundDyadicUp, hmant, hsign]
  · cases hsign : d.negative
    · rw [show roundDyadicUp fmt d =
          roundDyadicPosUp fmt d.significand d.exponent by
        simp [roundDyadicUp, roundDyadicPosUp, hmant, hsign]]
      exact isNaN_roundDyadicPosUp_eq_false fmt d.significand d.exponent hfmt hmant
    · rw [roundDyadicUp_eq_neg_roundDyadicPosDown_of_negative fmt d hmant hsign]
      simpa using isNaN_roundDyadicPosDown_eq_false
        fmt d.significand d.exponent

/--
In a conventional IEEE format, directed-down rounding of an exact dyadic never produces a NaN.
-/
theorem isNaN_roundDyadicDown_eq_false
    (fmt : FloatFormat) (d : Numerics.Dyadic) (hfmt : fmt.isIEEE = true) :
    isNaN (roundDyadicDown fmt d) = false := by
  rw [roundDyadicDown_eq_neg_roundDyadicUp_neg fmt d
      (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt), isNaN_neg]
  exact isNaN_roundDyadicUp_eq_false fmt d.neg hfmt

/--
In a conventional IEEE format, the exact signed dyadic value never exceeds directed-up dyadic
rounding in the extended reals.
-/
theorem le_toEReal_roundDyadicUp (fmt : FloatFormat) (d : Numerics.Dyadic) :
    fmt.isIEEE = true →
    (d.toReal : EReal) ≤ toEReal (roundDyadicUp fmt d) := by
  intro hfmt
  by_cases hmant : d.significand = 0
  · simp [roundDyadicUp, Numerics.Dyadic.toReal, hmant]
  · by_cases hsign : d.negative
    · have hbound :=
        toEReal_roundDyadicPosDown_le fmt d.significand d.exponent hmant
      have hnan :=
        isNaN_roundDyadicPosDown_eq_false fmt d.significand d.exponent
      rw [roundDyadicUp_eq_neg_roundDyadicPosDown_of_negative fmt d hmant hsign]
      rw [toEReal_neg_of_isNaN_eq_false _ hnan]
      simpa [Numerics.Dyadic.toReal, hsign,
        bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
        EReal.neg_le_neg_iff.mpr hbound
    · simpa [roundDyadicUp, roundDyadicPosUp,
        Numerics.Dyadic.toReal, hmant, hsign,
        bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
        le_toEReal_roundDyadicPosUp fmt d.significand d.exponent hfmt hmant

/--
In a conventional IEEE format, directed-down dyadic rounding never exceeds the exact signed dyadic
value in the extended reals.
-/
theorem toEReal_roundDyadicDown_le (fmt : FloatFormat) (d : Numerics.Dyadic) :
    fmt.isIEEE = true →
    toEReal (roundDyadicDown fmt d) ≤ (d.toReal : EReal) := by
  intro hfmt
  rw [roundDyadicDown_eq_neg_roundDyadicUp_neg fmt d
      (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt),
    toEReal_neg_of_isNaN_eq_false _ (isNaN_roundDyadicUp_eq_false fmt d.neg hfmt)]
  have hupper := le_toEReal_roundDyadicUp fmt d.neg hfmt
  rw [Dyadic.toReal_neg, EReal.coe_neg] at hupper
  exact EReal.neg_le.mp hupper

/-! ## Nonnegative results of positive rounding -/

/--
The total interpretation `toReal` sends every value that is not finite, a NaN or an infinity, to
zero.
-/
theorem toReal_eq_zero_of_isFinite_eq_false {fmt : FloatFormat} {x : Model fmt}
    (hfinite : isFinite x = false) : toReal x = 0 := by
  simp [toReal_eq, toDyadic?_eq_none_of_isFinite_eq_false hfinite]

/-- A value with a clear sign bit has a nonnegative real value, whether or not it is finite. -/
theorem toReal_nonneg_of_signBit_eq_false {fmt : FloatFormat} {x : Model fmt}
    (hsign : signBit x = false) : 0 ≤ toReal x := by
  cases hdecode : toDyadic? x with
  | none => simp [toReal_eq, hdecode]
  | some d =>
      have hnegative : d.negative = false :=
        (sign_eq_signBit_of_toDyadic?_some hdecode).trans hsign
      have hreal : toReal x = d.toReal := by
        simp [toReal_eq, hdecode]
      rw [hreal]
      exact Dyadic.toReal_nonneg_of_negative_eq_false hnegative

/-- The positive native overflow value has a nonnegative real value in every encoding. -/
theorem toReal_nativeOverflow_false_nonneg (fmt : FloatFormat) :
    0 ≤ toReal (nativeOverflow fmt false) := by
  cases hencoding : fmt.encoding with
  | ieee =>
      exact toReal_nonneg_of_signBit_eq_false (by simp [nativeOverflow, hencoding])
  | finiteMaxNaN =>
      exact toReal_nonneg_of_signBit_eq_false (by simp [nativeOverflow, propagatedNaN, hencoding])
  | finiteUnsignedZero =>
      rw [toReal_eq_zero_of_isFinite_eq_false]
      apply isFinite_eq_false_of_isNaN
      simp [nativeOverflow, invalidResult, negZero, isNaN, hencoding, ofBits]
  | finite =>
      exact toReal_nonneg_of_signBit_eq_false (by simp [nativeOverflow, hencoding])

/--
Packing a positive normal significand, with the positive native overflow value as the overflow
result, gives a nonnegative value.
-/
private theorem toReal_packRoundedNormal_nativeOverflow_false_nonneg (fmt : FloatFormat)
    (totalExponent : Int) (roundedMantissa : Nat) :
    0 ≤ toReal
      (packRoundedNormal fmt false (nativeOverflow fmt false) totalExponent roundedMantissa) := by
  unfold packRoundedNormal
  dsimp only
  split_ifs <;> first
    | exact toReal_nativeOverflow_false_nonneg fmt
    | exact toReal_nonneg_of_signBit_eq_false (by simp)

/--
Packing a positive subnormal significand gives a nonnegative value when the zero result has a
clear sign bit.
-/
private theorem toReal_packRoundedSubnormal_false_nonneg (fmt : FloatFormat)
    (zeroResult : Model fmt) (fraction : Nat) (hzero : signBit zeroResult = false) :
    0 ≤ toReal (packRoundedSubnormal fmt false zeroResult fraction) := by
  unfold packRoundedSubnormal
  split_ifs <;> exact toReal_nonneg_of_signBit_eq_false (by simp [hzero])

/-- Rounding a positive magnitude downward gives a nonnegative value. -/
theorem toReal_roundDyadicMagnitudeDown_false_nonneg (fmt : FloatFormat) (mantissa : Nat)
    (exponent : Int) : 0 ≤ toReal (roundDyadicMagnitudeDown fmt false mantissa exponent) := by
  apply toReal_nonneg_of_signBit_eq_false
  unfold roundDyadicMagnitudeDown
  dsimp only
  split_ifs <;> simp

/-- Rounding a positive magnitude upward gives a nonnegative value. -/
theorem toReal_roundDyadicMagnitudeUp_false_nonneg (fmt : FloatFormat) (mantissa : Nat)
    (exponent : Int) : 0 ≤ toReal (roundDyadicMagnitudeUp fmt false mantissa exponent) := by
  unfold roundDyadicMagnitudeUp
  dsimp only
  split_ifs <;> first
    | with_reducible exact toReal_nativeOverflow_false_nonneg fmt
    | with_reducible exact toReal_packRoundedSubnormal_false_nonneg fmt _ _ (by simp)
    | with_reducible exact toReal_packRoundedNormal_nativeOverflow_false_nonneg fmt _ _
    | exact toReal_nonneg_of_signBit_eq_false (by simp)

/-- Nearest-even rounding of a nonnegative dyadic gives a nonnegative value. -/
theorem toReal_roundDyadicGeneral_nonneg (fmt : FloatFormat) (value : Numerics.Dyadic)
    (hvalue : value.negative = false) : 0 ≤ toReal (roundDyadicGeneral fmt value) := by
  unfold roundDyadicGeneral
  dsimp only
  rw [hvalue]
  split_ifs <;> first
    | with_reducible exact toReal_nativeOverflow_false_nonneg fmt
    | with_reducible exact toReal_packRoundedSubnormal_false_nonneg fmt _ _ (by simp)
    | with_reducible exact toReal_packRoundedNormal_nativeOverflow_false_nonneg fmt _ _
    | exact toReal_nonneg_of_signBit_eq_false (by simp)

/-- Rounding a nonnegative dyadic upward gives a nonnegative value. -/
theorem toReal_roundDyadicUp_nonneg (fmt : FloatFormat) (value : Numerics.Dyadic)
    (hvalue : value.negative = false) : 0 ≤ toReal (roundDyadicUp fmt value) := by
  unfold roundDyadicUp
  rw [hvalue]
  split_ifs <;> first
    | with_reducible exact toReal_roundDyadicMagnitudeUp_false_nonneg fmt _ _
    | exact toReal_nonneg_of_signBit_eq_false (by simp)
    | simp_all

/-- Rounding a nonnegative dyadic downward gives a nonnegative value. -/
theorem toReal_roundDyadicDown_nonneg (fmt : FloatFormat) (value : Numerics.Dyadic)
    (hvalue : value.negative = false) : 0 ≤ toReal (roundDyadicDown fmt value) := by
  unfold roundDyadicDown
  rw [hvalue]
  split_ifs <;> first
    | with_reducible exact toReal_roundDyadicMagnitudeDown_false_nonneg fmt _ _
    | exact toReal_nonneg_of_signBit_eq_false (by simp)
    | simp_all

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
