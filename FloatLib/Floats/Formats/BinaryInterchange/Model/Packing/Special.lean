/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.RealSemantics

/-!
# Packing special values in Lean's float model

In Lean's IEEE model, these packing identities keep the sign of zero and infinity. They hold at
any field widths, but classifying the result under a descriptor also needs the relevant encoding
support. Under FNUZ, for instance, `negZero` is a NaN word, and under finite-only policies
`posInf` and `negInf` need not denote infinities.

With these shared lemmas, operation proofs handle zero and overflow results without unfolding
their exponent and significand fields.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model
open Float.Model.UnpackedFloat

private theorem one_lt_two_pow_expWidth (fmt : FloatFormat) :
    1 < 2 ^ fmt.expWidth := by
  have := FloatFormat.one_lt_expAllOnesNat fmt
  unfold FloatFormat.expAllOnesNat at this
  omega

private theorem zero_ne_expAllOnesNat (fmt : FloatFormat) :
    (0 : Nat) ≠ FloatFormat.expAllOnesNat fmt :=
  (FloatFormat.expAllOnesNat_pos fmt).ne

private theorem expAllOnes_lt_two_pow (fmt : FloatFormat) :
    2 ^ fmt.expWidth - 1 < 2 ^ fmt.expWidth := by
  have hpos : 0 < 2 ^ fmt.expWidth := Nat.pow_pos (by decide)
  omega

private theorem expMaskNat_lt_two_pow_bitWidth (fmt : FloatFormat) :
    FloatFormat.expMaskNat fmt < 2 ^ fmt.bitWidth := by
  unfold FloatFormat.expMaskNat FloatFormat.expAllOnesNat FloatFormat.bitWidth
  have hfracPos : 0 < 2 ^ fmt.fracWidth := Nat.pow_pos (by decide)
  have hones : 2 ^ fmt.expWidth - 1 < 2 ^ fmt.expWidth :=
    expAllOnes_lt_two_pow fmt
  have hmaskLt :
      (2 ^ fmt.expWidth - 1) * 2 ^ fmt.fracWidth <
        2 ^ fmt.expWidth * 2 ^ fmt.fracWidth :=
    Nat.mul_lt_mul_of_pos_right hones hfracPos
  have hproductPos : 0 < 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth :=
    mul_pos (Nat.pow_pos (by decide)) hfracPos
  rw [show 2 ^ (1 + fmt.expWidth + fmt.fracWidth) =
    2 * 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth by ring]
  nlinarith

/-- Packing and unpacking an infinity preserves its sign. -/
@[simp] theorem unpack_pack_infinity (spec : Format) (sign : Sign) :
    Float.Model.UnpackedFloat.unpack spec
        (Float.Model.UnpackedFloat.pack spec (.infinity sign)) =
      .infinity sign := by
  unfold Float.Model.UnpackedFloat.pack packedInfinity
    Float.Model.UnpackedFloat.unpack
  simp only [unpackExponent_packComponents, unpackMantissa_packComponents,
    unpackSign_packComponents]
  have hsign : Sign.ofBitVec sign.toBitVec = sign := by
    cases sign <;> rfl
  simp [hsign]

private theorem expMask_eq_packedInfinity_positive (fmt : FloatFormat) :
    FloatFormat.expMask fmt =
      packedInfinity (FloatFormat.toModel fmt) .positive := by
  unfold FloatFormat.expMask FloatFormat.expMaskNat FloatFormat.expAllOnesNat
    FloatFormat.ofWordNat FloatFormat.toModel FloatFormat.bitWidth
    packedInfinity packComponents Sign.toBitVec
  apply BitVec.toNat_inj.mp
  simp only [BitVec.toNat_ofNat, BitVec.toNat_append, BitVec.toNat_neg,
    Nat.shiftLeft_eq]
  simp only [Nat.zero_mod, Nat.zero_mul, Nat.zero_or]
  rw [Nat.mod_eq_of_lt (by
    simpa [FloatFormat.expMaskNat, FloatFormat.expAllOnesNat,
      FloatFormat.bitWidth] using expMaskNat_lt_two_pow_bitWidth fmt)]
  simp [Nat.mod_eq_of_lt (one_lt_two_pow_expWidth fmt),
    Nat.mod_eq_of_lt (expAllOnes_lt_two_pow fmt)]

private theorem signMask_or_expMask_eq_packedInfinity_negative (fmt : FloatFormat) :
    FloatFormat.signMask fmt ||| FloatFormat.expMask fmt =
      packedInfinity (FloatFormat.toModel fmt) .negative := by
  apply BitVec.toNat_inj.mp
  unfold FloatFormat.expMask
  rw [BitVec.toNat_or, FloatFormat.signMask_toNat]
  unfold FloatFormat.ofWordNat FloatFormat.expMaskNat FloatFormat.expAllOnesNat
  rw [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by
    simpa [FloatFormat.expMaskNat, FloatFormat.expAllOnesNat] using
      expMaskNat_lt_two_pow_bitWidth fmt)]
  unfold packedInfinity packComponents Sign.toBitVec
  change
    2 ^ (FloatFormat.bitWidth fmt - 1) |||
        (2 ^ fmt.expWidth - 1) * 2 ^ fmt.fracWidth =
      ((1#1 ++ -1#fmt.expWidth) ++ 0#fmt.fracWidth).toNat
  rw [BitVec.toNat_append, BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_neg, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (one_lt_two_pow_expWidth fmt),
    Nat.mod_eq_of_lt (expAllOnes_lt_two_pow fmt)]
  rw [show 2 ^ (FloatFormat.bitWidth fmt - 1) = 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth from
    (FloatFormat.signMaskNat_eq_two_pow fmt).trans (pow_add _ _ _)]
  norm_num
  simpa [Nat.shiftLeft_eq] using
    (Nat.shiftLeft_or_distrib
      (a := 2 ^ fmt.expWidth)
      (b := 2 ^ fmt.expWidth - 1)
      (i := fmt.fracWidth)).symm

/-- Positive executable infinity is Lean's positive packed infinity. -/
theorem posInf_eq_ofModel_infinity (fmt : FloatFormat) :
    posInf fmt = ofModel fmt (.infinity .positive) := by
  unfold posInf ofBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
  rw [expMask_eq_packedInfinity_positive]

/-- Negative executable infinity is Lean's negative packed infinity. -/
theorem negInf_eq_ofModel_infinity (fmt : FloatFormat) :
    negInf fmt = ofModel fmt (.infinity .negative) := by
  unfold negInf ofBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
  rw [signMask_or_expMask_eq_packedInfinity_negative]

/-- Model packing exposes the all-ones exponent field for either infinity sign. -/
@[simp] theorem expField_ofModel_infinity (fmt : FloatFormat) (sign : Sign) :
    expField (ofModel fmt (.infinity sign)) =
      FloatFormat.expAllOnesNat fmt := by
  rw [← unpackExponent_toNat]
  unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    packedInfinity
  rw [unpackExponent_packComponents]
  exact toNat_neg_one_exponentBits fmt

/-- Model packing exposes a zero fraction field for either infinity sign. -/
@[simp] theorem fracField_ofModel_infinity (fmt : FloatFormat) (sign : Sign) :
    fracField (ofModel fmt (.infinity sign)) = 0 := by
  rw [← unpackMantissa_toNat]
  unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    packedInfinity
  rw [unpackMantissa_packComponents]
  rfl

/-- Model packing preserves the sign bit of an infinity. -/
@[simp] theorem signBit_ofModel_infinity (fmt : FloatFormat) (sign : Sign) :
    signBit (ofModel fmt (.infinity sign)) = modelSignBit sign := by
  rw [← modelSignBit_ofBitVec_unpackSign]
  unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    packedInfinity
  rw [unpackSign_packComponents]
  cases sign <;> rfl

/-- A model-packed infinity is classified as infinity by every infinity-bearing descriptor. -/
@[simp] theorem isInf_ofModel_infinity
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) (sign : Sign) :
    isInf (ofModel fmt (.infinity sign)) = true := by
  have hencoding : fmt.encoding = .ieee := by
    simpa [FloatFormat.supportsInfinity] using hfmt
  simp [isInf, IEEE.isInf, hencoding]

/-- A model-packed infinity is not finite under an infinity-bearing descriptor. -/
@[simp] theorem isFinite_ofModel_infinity
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) (sign : Sign) :
    isFinite (ofModel fmt (.infinity sign)) = false := by
  have hencoding : fmt.encoding = .ieee := by
    simpa [FloatFormat.supportsInfinity] using hfmt
  simp [isFinite, IEEE.isFinite, hencoding]

/-- Re-decoding a model-packed infinity recovers the same logical value. -/
@[simp] theorem toModel_ofModel_infinity (fmt : FloatFormat) (sign : Sign) :
    toModel (ofModel fmt (.infinity sign)) = .infinity sign := by
  unfold toModel ofModel toModelBits ofModelBits
  exact unpack_pack_infinity _ _

/-- Positive executable infinity has positive sign. -/
@[simp] theorem signBit_posInf (fmt : FloatFormat) :
    signBit (posInf fmt) = false := by
  rw [posInf_eq_ofModel_infinity]
  exact signBit_ofModel_infinity fmt .positive

/-- Negative executable infinity has negative sign. -/
@[simp] theorem signBit_negInf (fmt : FloatFormat) :
    signBit (negInf fmt) = true := by
  rw [negInf_eq_ofModel_infinity]
  exact signBit_ofModel_infinity fmt .negative

/-- Positive executable infinity is classified as infinity whenever the format supports it. -/
@[simp] theorem isInf_posInf
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    isInf (posInf fmt) = true := by
  rw [posInf_eq_ofModel_infinity]
  exact isInf_ofModel_infinity fmt hfmt .positive

/-- Negative executable infinity is classified as infinity whenever the format supports it. -/
@[simp] theorem isInf_negInf
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    isInf (negInf fmt) = true := by
  rw [negInf_eq_ofModel_infinity]
  exact isInf_ofModel_infinity fmt hfmt .negative

/-- Positive executable infinity is not finite whenever the format supports infinity. -/
@[simp] theorem isFinite_posInf
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    isFinite (posInf fmt) = false := by
  rw [posInf_eq_ofModel_infinity]
  exact isFinite_ofModel_infinity fmt hfmt .positive

/-- Negative executable infinity is not finite whenever the format supports infinity. -/
@[simp] theorem isFinite_negInf
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    isFinite (negInf fmt) = false := by
  rw [negInf_eq_ofModel_infinity]
  exact isFinite_ofModel_infinity fmt hfmt .negative

/-- Decoding positive executable infinity recovers positive logical infinity. -/
@[simp] theorem toModel_posInf (fmt : FloatFormat) :
    toModel (posInf fmt) = .infinity .positive := by
  rw [posInf_eq_ofModel_infinity]
  simp

/-- Decoding negative executable infinity recovers negative logical infinity. -/
@[simp] theorem toModel_negInf (fmt : FloatFormat) :
    toModel (negInf fmt) = .infinity .negative := by
  rw [negInf_eq_ofModel_infinity]
  simp

/-- Packing and unpacking a signed zero preserves its sign. -/
@[simp] theorem unpack_pack_zero (spec : Format) (sign : Sign) :
    unpack spec (pack spec (.zero sign)) = .zero sign := by
  unfold Float.Model.UnpackedFloat.pack Float.Model.UnpackedFloat.packedZero
    Float.Model.UnpackedFloat.unpack
  simp only [unpackExponent_packComponents, unpackMantissa_packComponents,
    unpackSign_packComponents]
  have hExponent : (0#spec.exponentBits) ≠ (-1#spec.exponentBits) := by
    rw [ne_eq, BitVec.zero_eq_neg_one_iff]
    exact Nat.ne_zero_of_lt spec.he
  have hsign : Sign.ofBitVec sign.toBitVec = sign := by
    cases sign <;> rfl
  simp [hExponent, hsign]

/-- Model packing exposes a zero exponent field for either signed zero. -/
@[simp] theorem expField_ofModel_zero (fmt : FloatFormat) (sign : Sign) :
    expField (ofModel fmt (.zero sign)) = 0 := by
  rw [← unpackExponent_toNat]
  unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    packedZero
  rw [unpackExponent_packComponents]
  rfl

/-- Model packing exposes a zero fraction field for either signed zero. -/
@[simp] theorem fracField_ofModel_zero (fmt : FloatFormat) (sign : Sign) :
    fracField (ofModel fmt (.zero sign)) = 0 := by
  rw [← unpackMantissa_toNat]
  unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    packedZero
  rw [unpackMantissa_packComponents]
  rfl

/-- Model packing preserves the sign bit of zero. -/
@[simp] theorem signBit_ofModel_zero (fmt : FloatFormat) (sign : Sign) :
    signBit (ofModel fmt (.zero sign)) = modelSignBit sign := by
  rw [← modelSignBit_ofBitVec_unpackSign]
  unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    packedZero
  rw [unpackSign_packComponents]
  cases sign <;> rfl

/-- A model-packed signed zero is classified as zero by a conventional IEEE descriptor. -/
@[simp] theorem isZero_ofModel_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Sign) :
    isZero (ofModel fmt (.zero sign)) = true := by
  have hencoding := (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt |>.1
  simp [isZero, IEEE.isZero, hencoding]

/-- A model-packed signed zero is not infinity in any encoding. -/
@[simp] theorem isInf_ofModel_zero (fmt : FloatFormat) (sign : Sign) :
    isInf (ofModel fmt (.zero sign)) = false := by
  have hne := zero_ne_expAllOnesNat fmt
  cases hencoding : fmt.encoding <;> simp [isInf, IEEE.isInf, hencoding, hne]

/-- A model-packed signed zero is not NaN under a conventional IEEE descriptor. -/
@[simp] theorem isNaN_ofModel_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Sign) :
    isNaN (ofModel fmt (.zero sign)) = false := by
  have hencoding := (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt |>.1
  simp [isNaN, IEEE.isNaN, hencoding]

/-- A model-packed signed zero is finite under a conventional IEEE descriptor. -/
@[simp] theorem isFinite_ofModel_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Sign) :
    isFinite (ofModel fmt (.zero sign)) = true := by
  have hencoding := (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt |>.1
  have hne := zero_ne_expAllOnesNat fmt
  simp [isFinite, IEEE.isFinite, hencoding, hne]

/-- Re-decoding a model-packed signed zero recovers the same logical value. -/
@[simp] theorem toModel_ofModel_zero (fmt : FloatFormat) (sign : Sign) :
    toModel (ofModel fmt (.zero sign)) = .zero sign := by
  unfold toModel ofModel toModelBits ofModelBits
  exact unpack_pack_zero _ _

/-- Positive executable zero is Lean's positive packed zero. -/
theorem posZero_eq_ofModel_zero (fmt : FloatFormat) :
    posZero fmt = ofModel fmt (.zero .positive) := by
  unfold posZero ofNatBits ofBits ofModel ofModelBits
    Float.Model.UnpackedFloat.pack Float.Model.UnpackedFloat.packedZero
    Float.Model.UnpackedFloat.packComponents Float.Model.UnpackedFloat.Sign.toBitVec
    FloatFormat.ofWordNat FloatFormat.toModel FloatFormat.bitWidth
  congr 1
  apply BitVec.toNat_inj.mp
  simp

/-- Negative executable zero is Lean's negative packed zero. -/
theorem negZero_eq_ofModel_zero (fmt : FloatFormat) :
    negZero fmt = ofModel fmt (.zero .negative) := by
  unfold negZero ofBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    Float.Model.UnpackedFloat.packedZero Float.Model.UnpackedFloat.packComponents
    Float.Model.UnpackedFloat.Sign.toBitVec FloatFormat.toModel
  congr 1
  apply BitVec.toNat_inj.mp
  rw [FloatFormat.signMask_toNat, show 2 ^ (FloatFormat.bitWidth fmt - 1) =
      2 ^ fmt.expWidth * 2 ^ fmt.fracWidth from
    (FloatFormat.signMaskNat_eq_two_pow fmt).trans (pow_add _ _ _)]
  unfold FloatFormat.bitWidth
  simp [BitVec.toNat_append, Nat.shiftLeft_eq]

/-- Positive executable zero has positive sign. -/
@[simp] theorem signBit_posZero (fmt : FloatFormat) :
    signBit (posZero fmt) = false := by
  rw [posZero_eq_ofModel_zero]
  exact signBit_ofModel_zero fmt .positive

/-- Negative executable zero has negative sign. -/
@[simp] theorem signBit_negZero (fmt : FloatFormat) :
    signBit (negZero fmt) = true := by
  rw [negZero_eq_ofModel_zero]
  exact signBit_ofModel_zero fmt .negative

/--
The policy-aware zero constructor keeps the requested sign if and only if signed zero is supported.
-/
@[simp] theorem signBit_zero (fmt : FloatFormat) (sign : Bool) :
    signBit (zero fmt sign) = (sign && fmt.supportsSignedZero) := by
  cases sign
  · simp [zero]
  · cases hfmt : fmt.supportsSignedZero <;> simp [zero, hfmt]

/-- The canonical positive-zero word is classified as zero in every supported encoding. -/
@[simp] theorem isZero_posZero (fmt : FloatFormat) :
    isZero (posZero fmt) = true := by
  cases hencoding : fmt.encoding <;>
    simp [isZero, IEEE.isZero, hencoding, posZero, ofNatBits, ofBits,
      FloatFormat.ofWordNat, expField, fracField]

/-- Positive executable zero has a zero exponent field. -/
@[simp] theorem expField_posZero (fmt : FloatFormat) :
    expField (posZero fmt) = 0 := by
  rw [posZero_eq_ofModel_zero]
  exact expField_ofModel_zero fmt .positive

/-- Positive executable zero has a zero fraction field. -/
@[simp] theorem fracField_posZero (fmt : FloatFormat) :
    fracField (posZero fmt) = 0 := by
  rw [posZero_eq_ofModel_zero]
  exact fracField_ofModel_zero fmt .positive

/-- Negative executable zero has a zero exponent field. -/
@[simp] theorem expField_negZero (fmt : FloatFormat) :
    expField (negZero fmt) = 0 := by
  rw [negZero_eq_ofModel_zero]
  exact expField_ofModel_zero fmt .negative

/-- Negative executable zero has a zero fraction field. -/
@[simp] theorem fracField_negZero (fmt : FloatFormat) :
    fracField (negZero fmt) = 0 := by
  rw [negZero_eq_ofModel_zero]
  exact fracField_ofModel_zero fmt .negative

/-- A model-packed infinity is not classified as NaN in any encoding. -/
@[simp] theorem isNaN_ofModel_infinity (fmt : FloatFormat) (sign : Sign) :
    isNaN (ofModel fmt (.infinity sign)) = false := by
  have hfrac := fracField_ofModel_infinity fmt sign
  cases hencoding : fmt.encoding
  · simp [isNaN, IEEE.isNaN, hencoding, hfrac]
  · simp [isNaN, hencoding, hfrac, (FloatFormat.fracMaskNat_pos fmt).ne]
  · simp only [isNaN, hencoding, beq_eq_false_iff_ne]
    intro hbits
    have hzero : ofModel fmt (.infinity sign) = negZero fmt := by
      change _ = ofBits _
      rw [← hbits]
      rfl
    have hexp := expField_ofModel_infinity fmt sign
    rw [hzero, expField_negZero] at hexp
    exact zero_ne_expAllOnesNat fmt hexp
  · simp [isNaN, hencoding]

/-- Positive executable infinity is not a NaN in any encoding. -/
@[simp] theorem isNaN_posInf (fmt : FloatFormat) :
    isNaN (posInf fmt) = false := by
  rw [posInf_eq_ofModel_infinity]
  exact isNaN_ofModel_infinity fmt .positive

/-- Negative executable infinity is not a NaN in any encoding. -/
@[simp] theorem isNaN_negInf (fmt : FloatFormat) :
    isNaN (negInf fmt) = false := by
  rw [negInf_eq_ofModel_infinity]
  exact isNaN_ofModel_infinity fmt .negative

/--
In an encoding with two zero words, negative executable zero is classified as zero.

Under the finite-unsigned-zero encoding the negative-zero word is the NaN, so the hypothesis
cannot be dropped.
-/
@[simp] theorem isZero_negZero (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    isZero (negZero fmt) = true := by
  cases hencoding : fmt.encoding
  · simp [isZero, IEEE.isZero, hencoding]
  · simp [isZero, IEEE.isZero, hencoding]
  · exact absurd hfmt (by simp [FloatFormat.supportsSignedZero, hencoding])
  · simp [isZero, IEEE.isZero, hencoding]

/-- Positive executable zero is not a NaN in any encoding. -/
@[simp] theorem isNaN_posZero (fmt : FloatFormat) :
    isNaN (posZero fmt) = false := by
  have hne := zero_ne_expAllOnesNat fmt
  have hbits : (posZero fmt).bits ≠ FloatFormat.signMask fmt :=
    fun hzero => FloatFormat.signMask_ne_zero fmt hzero.symm
  cases hencoding : fmt.encoding
  · simp [isNaN, IEEE.isNaN, hencoding]
  · simp [isNaN, hencoding, hne]
  · simp [isNaN, hencoding, hbits]
  · simp [isNaN, hencoding]

/--
Negative executable zero is not a NaN when the encoding has two zero words.

Under the finite-unsigned-zero encoding the negative-zero word is the NaN, so the hypothesis
cannot be dropped.
-/
@[simp] theorem isNaN_negZero (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    isNaN (negZero fmt) = false := by
  have hne := zero_ne_expAllOnesNat fmt
  cases hencoding : fmt.encoding
  · simp [isNaN, IEEE.isNaN, hencoding]
  · simp [isNaN, hencoding, hne]
  · exact absurd hfmt (by simp [FloatFormat.supportsSignedZero, hencoding])
  · simp [isNaN, hencoding]

/-- Positive executable zero is not infinity in any encoding. -/
@[simp] theorem isInf_posZero (fmt : FloatFormat) :
    isInf (posZero fmt) = false := by
  have hne := zero_ne_expAllOnesNat fmt
  cases hencoding : fmt.encoding <;> simp [isInf, IEEE.isInf, hencoding, hne]

/-- Negative executable zero is not infinity in any encoding. -/
@[simp] theorem isInf_negZero (fmt : FloatFormat) :
    isInf (negZero fmt) = false := by
  have hne := zero_ne_expAllOnesNat fmt
  cases hencoding : fmt.encoding <;> simp [isInf, IEEE.isInf, hencoding, hne]

/-- Positive executable zero is finite in any encoding. -/
@[simp] theorem isFinite_posZero (fmt : FloatFormat) :
    isFinite (posZero fmt) = true := by
  have hne := zero_ne_expAllOnesNat fmt
  have hnan := isNaN_posZero fmt
  cases hencoding : fmt.encoding <;> simp [isFinite, IEEE.isFinite, hencoding, hne, hnan]

/--
Negative executable zero is finite when the encoding has two zero words.

Under the finite-unsigned-zero encoding the negative-zero word is the NaN, so the hypothesis
cannot be dropped.
-/
@[simp] theorem isFinite_negZero (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    isFinite (negZero fmt) = true := by
  have hne := zero_ne_expAllOnesNat fmt
  have hnan := isNaN_negZero fmt hfmt
  cases hencoding : fmt.encoding <;> simp [isFinite, IEEE.isFinite, hencoding, hne, hnan]

/-- Decoding positive executable zero recovers positive logical zero. -/
@[simp] theorem toModel_posZero (fmt : FloatFormat) :
    toModel (posZero fmt) = .zero .positive := by
  rw [posZero_eq_ofModel_zero]
  simp

/-- Decoding negative executable zero recovers negative logical zero. -/
@[simp] theorem toModel_negZero (fmt : FloatFormat) :
    toModel (negZero fmt) = .zero .negative := by
  rw [negZero_eq_ofModel_zero]
  simp

/-- Positive zero denotes real zero in every encoding. -/
@[simp] theorem toReal_posZero (fmt : FloatFormat) :
    toReal (posZero fmt) = 0 :=
  toReal_eq_zero_of_isZero _ (isZero_posZero fmt)

/--
Negative zero denotes real zero in every format with a signed zero.

Without one (the finite-unsigned-zero encoding) the negative-zero word is the NaN, so the
hypothesis cannot be dropped without turning this into a statement about how `toReal` totalizes
NaN. `toReal_zero` covers the zero `zero fmt sign` chosen for the format, in every encoding.
-/
@[simp] theorem toReal_negZero (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    toReal (negZero fmt) = 0 :=
  toReal_eq_zero_of_isZero _ (isZero_negZero fmt hfmt)

/-- Either signed-zero constructor has real value zero in a format with a signed zero. -/
@[simp] theorem toReal_signedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) (negative : Bool) :
    toReal (if negative then negZero fmt else posZero fmt) = 0 := by
  cases negative <;> simp [hfmt]

/--
Model packing preserves the real value of either signed zero in a format with a signed zero.

Without one, packing the negative zero gives the NaN word, as for `toReal_negZero`.
-/
@[simp] theorem toReal_ofModel_zero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) (sign : Sign) :
    toReal (ofModel fmt (.zero sign)) = 0 := by
  cases sign
  · rw [← negZero_eq_ofModel_zero, toReal_negZero fmt hfmt]
  · rw [← posZero_eq_ofModel_zero, toReal_posZero]

/-- Finite values are not infinities. -/
theorem isInf_eq_false_of_isFinite_eq_true {fmt : FloatFormat} (x : Model fmt)
    (hx : isFinite x = true) :
    isInf x = false := by
  cases hencoding : fmt.encoding with
  | ieee =>
      have hxIEEE : IEEE.isFinite x = true := by
        simpa [isFinite, hencoding] using hx
      have hexp : expField x ≠ FloatFormat.expAllOnesNat fmt :=
        (bne_iff_ne).1 hxIEEE
      simp [isInf, hencoding, IEEE.isInf, hexp]
  | finiteMaxNaN | finiteUnsignedZero | finite =>
      simp [isInf, hencoding]

/-! ## Quiet NaNs -/

/-- Setting the quiet bit of a word sets bit `fracWidth - 1` of its fraction field. -/
theorem fracField_or_quietBit {fmt : FloatFormat} (b : FloatFormat.ExecWord fmt) :
    fracField (ofBits (fmt := fmt) (b ||| FloatFormat.quietBit fmt)) =
      fracField (ofBits (fmt := fmt) b) ||| 2 ^ (fmt.fracWidth - 1) := by
  have hfw := fmt.fracWidth_pos
  unfold fracField ofBits FloatFormat.quietBit FloatFormat.fracMask FloatFormat.ofWordNat
    FloatFormat.quietBitNat FloatFormat.fracMaskNat
  simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow]
  unfold FloatFormat.bitWidth
  by_cases h1 : i < fmt.fracWidth <;> by_cases h2 : fmt.fracWidth - 1 = i <;> simp [h1, h2] <;> omega

/-- Setting the quiet bit of a word leaves its exponent field unchanged. -/
theorem expField_or_quietBit {fmt : FloatFormat} (b : FloatFormat.ExecWord fmt) :
    expField (ofBits (fmt := fmt) (b ||| FloatFormat.quietBit fmt)) = expField (ofBits (fmt := fmt) b) := by
  have hfw := fmt.fracWidth_pos
  unfold expField ofBits FloatFormat.quietBit FloatFormat.expAllOnes FloatFormat.ofWordNat
    FloatFormat.quietBitNat FloatFormat.expAllOnesNat
  simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow, Nat.testBit_shiftRight]
  unfold FloatFormat.bitWidth
  have : ¬ fmt.fracWidth - 1 = fmt.fracWidth + i := by omega
  by_cases h1 : i < fmt.expWidth <;> simp [h1, this]

/--
Quieting preserves the NaN classification in every encoding: a NaN stays a NaN and a non-NaN value
stays non-NaN. `quietNaN_eq_self_of_isNaN_eq_false` shows that a non-NaN value is returned
unchanged.
-/
@[simp] theorem isNaN_quietNaN {fmt : FloatFormat} (x : Model fmt) :
    isNaN (quietNaN x) = isNaN x := by
  cases hencoding : fmt.encoding <;> simp only [quietNaN, hencoding]
  by_cases hnan : IEEE.isNaN x = true
  · have hfields := hnan
    simp only [IEEE.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hfields
    have hor : fracField x ||| 2 ^ (fmt.fracWidth - 1) ≠ 0 := fun h =>
      hfields.2 (Nat.or_eq_zero_iff.mp h).1
    rw [ite_eq_left hnan]
    simp only [isNaN, hencoding]
    rw [hnan]
    simp only [IEEE.isNaN, expField_or_quietBit, fracField_or_quietBit]
    change (expField x == _ && fracField x ||| _ != 0) = true
    simp [hfields.1, hor]
  · rw [ite_eq_right hnan]

/-- Quieting returns every non-NaN value unchanged, in every encoding. -/
theorem quietNaN_eq_self_of_isNaN_eq_false {fmt : FloatFormat} (x : Model fmt)
    (hx : isNaN x = false) : quietNaN x = x := by
  cases hencoding : fmt.encoding <;> simp only [quietNaN, hencoding]
  have hnan : IEEE.isNaN x = false := by simpa [isNaN, hencoding] using hx
  simp [hnan]

/-- The canonical NaN word is a NaN under the IEEE encoding. -/
theorem isNaN_canonicalNaN {fmt : FloatFormat} (hencoding : fmt.encoding = .ieee) :
    isNaN (canonicalNaN fmt) = true := by
  have hexp : expField (posInf fmt) = FloatFormat.expAllOnesNat fmt := by
    rw [posInf_eq_ofModel_infinity, expField_ofModel_infinity]
  have hfrac : fracField (posInf fmt) = 0 := by
    rw [posInf_eq_ofModel_infinity, fracField_ofModel_infinity]
  simp only [isNaN, hencoding, IEEE.isNaN, canonicalNaN]
  rw [expField_or_quietBit, fracField_or_quietBit]
  change (expField (posInf fmt) == _ && fracField (posInf fmt) ||| _ != 0) = true
  simp [hexp, hfrac]

/-- Under a conventional IEEE descriptor the invalid-operation result is not finite: it is the
canonical NaN (`invalidResult_eq_canonicalNaN_of_isIEEE`). -/
theorem isFinite_invalidResult {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) :
    isFinite (invalidResult fmt) = false := by
  rw [invalidResult_eq_canonicalNaN_of_isIEEE fmt hfmt]
  exact isFinite_eq_false_of_isNaN
    (isNaN_canonicalNaN ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1)

/-- NaN selection for one operand returns only a quieted NaN. -/
theorem isNaN_of_chooseNaN1_eq_some {fmt : FloatFormat} {x nan : Model fmt}
    (h : chooseNaN1 x = some nan) : isNaN nan = true := by
  unfold chooseNaN1 at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simpa
  · simp at h

/-- Every signaling NaN is a NaN. Non-IEEE policies have no signaling NaNs. -/
theorem isNaN_of_isSNaN {fmt : FloatFormat} {x : Model fmt} (hx : isSNaN x = true) :
    isNaN x = true := by
  cases hn : isNaN x
  · have := isSNaN_eq_false_of_isNaN_eq_false x hn
    simp [hx] at this
  · rfl

/-- NaN selection for two operands returns only a quieted NaN operand. -/
theorem isNaN_of_chooseNaN2_eq_some {fmt : FloatFormat} {x y nan : Model fmt}
    (h : chooseNaN2 x y = some nan) : isNaN nan = true := by
  unfold chooseNaN2 at h
  split_ifs at h with h₁ h₂ h₃ h₄ <;> simp only [Option.some.injEq] at h <;>
    subst h <;> simp [isNaN_of_isSNaN, *]

/-- NaN selection for three operands returns only a quieted NaN operand. -/
theorem isNaN_of_chooseNaN3_eq_some {fmt : FloatFormat} {x y z nan : Model fmt}
    (h : chooseNaN3 x y z = some nan) : isNaN nan = true := by
  unfold chooseNaN3 at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;>
    subst h <;> simp [isNaN_of_isSNaN, *]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
