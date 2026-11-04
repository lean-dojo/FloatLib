/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Numerics.Bitwise
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Special
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Optimized -- shake: keep

/-!
# Correctness of packed field access

These packed-field laws say how `Model.ofFields` decodes. They are uniform in the format, and they
keep in one place the bit-layout reasoning that rounding, status-flag and interval proofs need.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
The sign bit is set if and only if the storage word is in the upper half of the format's code space.
-/
theorem signBit_eq_true_iff_signMaskNat_le
    {fmt : FloatFormat} (x : Model fmt) :
    signBit x = true ↔ fmt.signMaskNat ≤ x.toNatBits := by
  let index := fmt.expWidth + fmt.fracWidth
  have hwidth : fmt.bitWidth = index + 1 := by
    unfold index FloatFormat.bitWidth
    omega
  have hfit : x.toNatBits < 2 ^ (index + 1) := by
    simpa [hwidth] using toNatBits_lt_two_pow x
  rw [signBit_eq_internal_apply]
  unfold Internal.signBit
  rw [Nat.testBit_eq_true_iff_two_pow_le_of_lt hfit, FloatFormat.signMaskNat_eq_two_pow]

/--
The sign bit is clear if and only if the storage word is in the lower half of the format's code
space.
-/
theorem signBit_eq_false_iff_toNatBits_lt_signMaskNat
    {fmt : FloatFormat} (x : Model fmt) :
    signBit x = false ↔ x.toNatBits < fmt.signMaskNat := by
  constructor
  · intro hfalse
    have hnotTrue : signBit x ≠ true := by
      simp [hfalse]
    have hnotLe : ¬fmt.signMaskNat ≤ x.toNatBits := by
      intro hle
      exact hnotTrue <|
        (signBit_eq_true_iff_signMaskNat_le x).2 hle
    omega
  · intro hlt
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    have hle :=
      (signBit_eq_true_iff_signMaskNat_le x).1 htrue
    omega

/-- In-range fields have the bit pattern of the zero of sign `zeroSign` if and only if they are its
fields. -/
private theorem ofFields_bits_eq_zeroFields_iff
    (fmt : FloatFormat) (sign zeroSign : Bool) (exponent fraction : Nat)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    (ofFields fmt sign exponent fraction).bits = (ofFields fmt zeroSign 0 0).bits ↔
      sign = zeroSign ∧ exponent = 0 ∧ fraction = 0 := by
  constructor
  · intro hbits
    have hvalue : ofFields fmt sign exponent fraction = ofFields fmt zeroSign 0 0 :=
      calc
        ofFields fmt sign exponent fraction =
            ofBits (ofFields fmt sign exponent fraction).bits :=
          (ofBits_toBits _).symm
        _ = ofBits (ofFields fmt zeroSign 0 0).bits := by rw [hbits]
        _ = ofFields fmt zeroSign 0 0 := ofBits_toBits _
    have hsign : sign = zeroSign := by
      simpa only [signBit_ofFields] using congrArg signBit hvalue
    have hexp : exponent = 0 := by
      simpa only [
        expField_ofFields_of_lt fmt sign exponent fraction hexponent,
        expField_ofFields_of_lt fmt zeroSign 0 0 (Nat.two_pow_pos fmt.expWidth)
      ] using congrArg expField hvalue
    have hfrac : fraction = 0 := by
      simpa only [
        fracField_ofFields_of_lt fmt sign exponent fraction hfraction,
        fracField_ofFields_of_lt fmt zeroSign 0 0 (Nat.two_pow_pos fmt.fracWidth)
      ] using congrArg fracField hvalue
    exact ⟨hsign, hexp, hfrac⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private theorem ofFields_bits_eq_zero_iff
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    (ofFields fmt sign exponent fraction).bits = 0 ↔
      sign = false ∧ exponent = 0 ∧ fraction = 0 := by
  have h := ofFields_bits_eq_zeroFields_iff fmt sign false exponent fraction hexponent hfraction
  rwa [ofFields_false_zero_zero,
    show (posZero fmt).bits = 0 by simp [posZero, ofNatBits, ofBits, FloatFormat.ofWordNat]] at h

private theorem ofFields_bits_eq_signMask_iff
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    (ofFields fmt sign exponent fraction).bits = fmt.signMask ↔
      sign = true ∧ exponent = 0 ∧ fraction = 0 := by
  have h := ofFields_bits_eq_zeroFields_iff fmt sign true exponent fraction hexponent hfraction
  rwa [ofFields_true_zero_zero, show (negZero fmt).bits = fmt.signMask by simp [negZero, ofBits]]
    at h

/-! ## Field classification -/

/-- Classification of an in-range field tuple as zero. -/
theorem isZero_ofFields
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    isZero (ofFields fmt sign exponent fraction) =
      match fmt.encoding with
      | .finiteUnsignedZero => !sign && exponent == 0 && fraction == 0
      | .ieee | .finiteMaxNaN | .finite => exponent == 0 && fraction == 0 := by
  have hExp := expField_ofFields_of_lt fmt sign exponent fraction hexponent
  have hFrac := fracField_ofFields_of_lt fmt sign exponent fraction hfraction
  cases hencoding : fmt.encoding
  · simp [isZero, hencoding, IEEE.isZero, hExp, hFrac]
  · simp [isZero, hencoding, IEEE.isZero, hExp, hFrac]
  · apply Bool.eq_iff_iff.mpr
    simp only [isZero, hencoding, beq_iff_eq, Bool.and_eq_true]
    rw [ofFields_bits_eq_zero_iff fmt sign exponent fraction hexponent hfraction]
    cases sign <;> simp
  · simp [isZero, hencoding, IEEE.isZero, hExp, hFrac]

/-- Classification of an in-range field tuple as finite. -/
theorem isFinite_ofFields
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    isFinite (ofFields fmt sign exponent fraction) =
      match fmt.encoding with
      | .ieee => exponent != fmt.expAllOnesNat
      | .finiteMaxNaN =>
          !(exponent == fmt.expAllOnesNat && fraction == fmt.fracMaskNat)
      | .finiteUnsignedZero => !(sign && exponent == 0 && fraction == 0)
      | .finite => true := by
  have hExp := expField_ofFields_of_lt fmt sign exponent fraction hexponent
  have hFrac := fracField_ofFields_of_lt fmt sign exponent fraction hfraction
  cases hencoding : fmt.encoding
  · simp [isFinite, hencoding, IEEE.isFinite, hExp]
  · simp [isFinite, isNaN, hencoding, hExp, hFrac]
  · have hnan :
        isNaN (ofFields fmt sign exponent fraction) =
          (sign && exponent == 0 && fraction == 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [isNaN, hencoding, beq_iff_eq, Bool.and_eq_true]
      rw [ofFields_bits_eq_signMask_iff fmt sign exponent fraction
        hexponent hfraction]
      cases sign <;> simp
    simp only [isFinite, hencoding, hnan]
  · simp [isFinite, hencoding]

/--
An IEEE field tuple is finite whenever its exponent is not the reserved all-ones pattern.

`ofFields` truncates the supplied fraction to the descriptor width, so this specialization needs
no separate fraction bound.
-/
theorem isFinite_ofFields_ieee
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (exponent fraction : Nat)
    (hexponent : exponent < fmt.expAllOnesNat) :
    isFinite (ofFields fmt sign exponent fraction) = true := by
  have hencoding :=
    (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt |>.1
  have hexponentWidth : exponent < 2 ^ fmt.expWidth := by
    unfold FloatFormat.expAllOnesNat at hexponent
    omega
  simp only [isFinite, hencoding, IEEE.isFinite, expField_ofFields,
    Nat.mod_eq_of_lt hexponentWidth, bne_iff_ne]
  exact Nat.ne_of_lt hexponent

/-- The maximum-magnitude finite encoding is finite for either sign. -/
@[simp] theorem isFinite_maxFinite (fmt : FloatFormat) (sign : Bool) :
    isFinite (maxFinite fmt sign) = true := by
  rw [maxFinite, isFinite_ofFields fmt sign fmt.maxFiniteExpField
    fmt.maxFiniteFracField fmt.maxFiniteExpField_lt_two_pow
    fmt.maxFiniteFracField_lt_two_pow]
  have hfracMaskPos := fmt.fracMaskNat_pos
  have hfracPred : fmt.fracMaskNat - 1 ≠ fmt.fracMaskNat := by
    omega
  have hexponentFour := fmt.four_le_two_pow_expWidth
  cases hencoding : fmt.encoding
  · simp [FloatFormat.maxFiniteExpField,
      FloatFormat.Encoding.maxFiniteExponent, FloatFormat.expAllOnesNat,
      hencoding]
    omega
  · simp [FloatFormat.maxFiniteExpField, FloatFormat.maxFiniteFracField,
      FloatFormat.Encoding.maxFiniteExponent, FloatFormat.expAllOnesNat,
      hencoding, hfracPred]
  · simp [FloatFormat.maxFiniteExpField, FloatFormat.maxFiniteFracField,
      FloatFormat.Encoding.maxFiniteExponent,
      hencoding, Nat.ne_of_gt hfracMaskPos]
  · simp

/-- The largest positive finite encoding is finite. -/
@[simp] theorem isFinite_posMaxFinite (fmt : FloatFormat) :
    isFinite (posMaxFinite fmt) = true :=
  isFinite_maxFinite fmt false

/-- Under a conventional IEEE descriptor the overflow result is an infinity, so it is not finite. -/
theorem isFinite_nativeOverflow {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (sign : Bool) :
    isFinite (nativeOverflow fmt sign) = false := by
  have hs := FloatFormat.supportsInfinity_eq_true_of_isIEEE fmt hfmt
  cases sign <;> simp [nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt,
    isFinite_posInf fmt hs, isFinite_negInf fmt hs]

/--
A normal field pair at or below the descriptor's greatest finite field pair is finite.
-/
theorem isFinite_ofFields_normal_of_le_maxFinite
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponentPos : exponent ≠ 0)
    (hfraction : fraction < 2 ^ fmt.fracWidth)
    (hmax :
      exponent < fmt.maxFiniteExpField ∨
        exponent = fmt.maxFiniteExpField ∧
          fraction ≤ fmt.maxFiniteFracField) :
    isFinite (ofFields fmt sign exponent fraction) = true := by
  have hexponent : exponent < 2 ^ fmt.expWidth := by
    have := fmt.maxFiniteExpField_lt_two_pow
    omega
  rw [isFinite_ofFields fmt sign exponent fraction hexponent hfraction]
  have hexpPow := fmt.four_le_two_pow_expWidth
  have hfracPow : 2 ≤ 2 ^ fmt.fracWidth := by
    simpa using
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) fmt.fracWidth_pos
  cases hencoding : fmt.encoding
  · simp [hencoding, FloatFormat.maxFiniteExpField,
      FloatFormat.maxFiniteFracField,
      FloatFormat.Encoding.maxFiniteExponent, FloatFormat.expAllOnesNat,
      FloatFormat.fracMaskNat] at hmax ⊢
    omega
  · simp [hencoding, FloatFormat.maxFiniteExpField,
      FloatFormat.maxFiniteFracField,
      FloatFormat.Encoding.maxFiniteExponent, FloatFormat.expAllOnesNat,
      FloatFormat.fracMaskNat] at hmax ⊢
    omega
  · simp [hexponentPos]
  · simp

/-! ## Finite field decoding -/

/--
Decode in-range fields known to denote a finite value.

The exact exponent uses the bias declared by the complete format descriptor. This includes
all-ones exponent fields when the selected non-IEEE encoding treats them as finite.
-/
theorem toDyadic?_ofFields_of_isFinite
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth)
    (hfinite : isFinite (ofFields fmt sign exponent fraction) = true) :
    toDyadic? (ofFields fmt sign exponent fraction) =
      if exponent = 0 then
        if fraction = 0 then
          some { negative := sign, significand := 0, exponent := 0 }
        else
          some {
            negative := sign
            significand := fraction
            exponent := fmt.minSubnormalExponent }
      else
        some {
          negative := sign
          significand := pow2 fmt.fracWidth + fraction
          exponent := Int.ofNat exponent - Int.ofNat fmt.exponentBias -
            Int.ofNat fmt.fracWidth } := by
  have hExp := expField_ofFields_of_lt fmt sign exponent fraction hexponent
  have hFrac := fracField_ofFields_of_lt fmt sign exponent fraction hfraction
  have hSign := signBit_ofFields fmt sign exponent fraction
  have hZero := isZero_ofFields fmt sign exponent fraction hexponent hfraction
  by_cases hieee : fmt.isIEEE = true
  · obtain ⟨hencoding, hbias⟩ := (FloatFormat.isIEEE_eq_true_iff fmt).mp hieee
    have hfiniteIEEE :
        IEEE.isFinite (ofFields fmt sign exponent fraction) = true := by
      simpa [isFinite, hencoding] using hfinite
    have hnotAllOnes : exponent ≠ fmt.expAllOnesNat := by
      intro hexponentAll
      have : expField (ofFields fmt sign exponent fraction) =
          fmt.expAllOnesNat := hExp.trans hexponentAll
      simp [IEEE.isFinite, this] at hfiniteIEEE
    simp [toDyadic?, hieee, ieeeToDyadic?, IEEE.isNaN, IEEE.isInf,
      hExp, hFrac, hSign, hnotAllOnes, FloatFormat.ieeeMinSubnormalExponent,
      FloatFormat.ieeeNormalMantissaExpOffset, FloatFormat.minSubnormalExponent,
      FloatFormat.minNormalExponent, hbias, sub_sub]
  · simp only [toDyadic?, hieee, Bool.false_eq_true, ite_false]
    rw [hfinite]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [hZero, hExp, hFrac, hSign]
    by_cases hexponentZero : exponent = 0
    · subst exponent
      by_cases hfractionZero : fraction = 0
      · subst fraction
        rw [isFinite_ofFields fmt sign 0 0 (Nat.two_pow_pos fmt.expWidth)
          (Nat.two_pow_pos fmt.fracWidth)] at hfinite
        cases hencoding : fmt.encoding <;> cases sign <;>
          simp_all
      · cases hencoding : fmt.encoding <;> cases sign <;>
          simp_all
    · cases hencoding : fmt.encoding <;> cases sign <;>
        simp_all

/--
The three shapes of a decoded finite word: a zero, a subnormal whose significand is the nonzero
fraction field at the minimum subnormal exponent, or a normal number whose significand carries the
implicit bit and whose exponent is the unbiased field.
-/
theorem toDyadic?_some_cases {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) :
    (d.significand = 0 ∧ d.exponent = 0) ∨
      (expField x = 0 ∧ fracField x ≠ 0 ∧ d.significand = fracField x ∧
        d.exponent = fmt.minSubnormalExponent) ∨
      (expField x ≠ 0 ∧ d.significand = pow2 fmt.fracWidth + fracField x ∧
        d.exponent =
          Int.ofNat (expField x) - Int.ofNat fmt.exponentBias - Int.ofNat fmt.fracWidth) := by
  have hfin : isFinite x = true := isFinite_eq_true_of_toDyadic?_some hd
  have hdecode := toDyadic?_ofFields_of_isFinite fmt (signBit x) (expField x) (fracField x)
    (expField_lt_pow2 x) (fracField_lt_pow2 x)
    (by simpa only [ofFields_signBit_expField_fracField] using hfin)
  rw [ofFields_signBit_expField_fracField, hd] at hdecode
  by_cases he : expField x = 0
  · by_cases hf : fracField x = 0
    · simp only [he, hf, ite_true, Option.some.injEq] at hdecode
      exact Or.inl ⟨by rw [hdecode], by rw [hdecode]⟩
    · simp only [he, hf, ite_true, ite_false, Option.some.injEq] at hdecode
      exact Or.inr (Or.inl ⟨he, hf, by rw [hdecode], by rw [hdecode]⟩)
  · simp only [he, ite_false, Option.some.injEq] at hdecode
    exact Or.inr (Or.inr ⟨he, by rw [hdecode], by rw [hdecode]⟩)

/--
The decoded dyadic of a word has a significand below `2^(fracWidth + 1)` and an exponent no smaller
than the minimum subnormal exponent. These bounds describe the format's precision and exponent grid.
-/
theorem toDyadic?_significand_lt_and_minSubnormalExponent_le
    {fmt : FloatFormat} (x : Model fmt) {d : Numerics.Dyadic}
    (hd : toDyadic? x = some d) :
    d.significand < 2 ^ (fmt.fracWidth + 1) ∧
      fmt.minSubnormalExponent ≤ d.exponent := by
  have hfrac := fracField_lt_pow2 x
  rcases toDyadic?_some_cases hd with ⟨hs, he⟩ | ⟨_, _, hs, he⟩ | ⟨_, hs, he⟩ <;> rw [hs, he]
  · refine ⟨Nat.two_pow_pos _, ?_⟩
    have := fmt.exponentBias_pos
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    omega
  · exact ⟨hfrac.trans (Nat.pow_lt_pow_right (by decide) (by omega)), le_rfl⟩
  · refine ⟨?_, ?_⟩
    · simp only [pow2_eq_two_pow, pow_succ] at hfrac ⊢
      omega
    · simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast]
      omega

/-- An in-range nonzero fraction at biased exponent zero decodes as a subnormal. -/
theorem toDyadic?_ofFields_subnormal (fmt : FloatFormat) (sign : Bool)
    (fraction : Nat) (hfractionPos : fraction ≠ 0)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    toDyadic? (ofFields fmt sign 0 fraction) =
      some {
        negative := sign
        significand := fraction
        exponent := fmt.minSubnormalExponent } := by
  have hexponent : 0 < 2 ^ fmt.expWidth := Nat.two_pow_pos fmt.expWidth
  have hzeroAll : (0 : Nat) ≠ fmt.expAllOnesNat :=
    (FloatFormat.expAllOnesNat_pos fmt).ne
  have hfinite : isFinite (ofFields fmt sign 0 fraction) = true := by
    rw [isFinite_ofFields fmt sign 0 fraction hexponent hfraction]
    cases hencoding : fmt.encoding <;> cases sign <;>
      simp [hfractionPos, hzeroAll]
  simpa [hfractionPos] using
    toDyadic?_ofFields_of_isFinite fmt sign 0 fraction hexponent hfraction hfinite

/-- In-range nonexceptional fields with nonzero biased exponent decode as a normal value. -/
theorem toDyadic?_ofFields_normal (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) (hexponentPos : exponent ≠ 0)
    (hexponent : exponent < FloatFormat.expAllOnesNat fmt)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    toDyadic? (ofFields fmt sign exponent fraction) =
      some {
        negative := sign
        significand := pow2 fmt.fracWidth + fraction
        exponent := Int.ofNat exponent - Int.ofNat fmt.exponentBias -
          Int.ofNat fmt.fracWidth } := by
  have hexponentWidth : exponent < 2 ^ fmt.expWidth := by
    unfold FloatFormat.expAllOnesNat at hexponent
    omega
  have hfinite : isFinite (ofFields fmt sign exponent fraction) = true := by
    rw [isFinite_ofFields fmt sign exponent fraction hexponentWidth hfraction]
    cases hencoding : fmt.encoding <;>
      simp [Nat.ne_of_lt hexponent, hexponentPos]
  simpa [hexponentPos] using
    toDyadic?_ofFields_of_isFinite fmt sign exponent fraction hexponentWidth
      hfraction hfinite

/-! ## Closed-form real semantics -/

/--
Closed-form real value of a packed subnormal, a zero exponent field with a nonzero fraction, in
every encoding. A zero fraction gives `posZero` or `negZero` (`ofFields_false_zero_zero`,
`ofFields_true_zero_zero`). In a format without a signed zero `negZero` is the NaN, and in a
format with one `toReal_signedZero` gives value zero.
-/
theorem toReal_ofFields_subnormal (fmt : FloatFormat) (sign : Bool)
    (fraction : Nat) (hfractionPos : fraction ≠ 0)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    toReal (ofFields fmt sign 0 fraction) =
      (if sign then (-1 : ℝ) else 1) * (fraction : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
          fmt.minSubnormalExponent := by
  rw [toReal_eq,
    toDyadic?_ofFields_subnormal fmt sign fraction hfractionPos hfraction]
  exact Dyadic.toReal_mk _ _ _

/-- Closed-form real value of packed normal fields. -/
theorem toReal_ofFields_normal (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) (hexponentPos : exponent ≠ 0)
    (hexponent : exponent < FloatFormat.expAllOnesNat fmt)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    toReal (ofFields fmt sign exponent fraction) =
      (if sign then (-1 : ℝ) else 1) *
        ((pow2 fmt.fracWidth + fraction : Nat) : ℝ) *
          FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
            (Int.ofNat exponent - Int.ofNat fmt.exponentBias -
              Int.ofNat fmt.fracWidth) := by
  rw [toReal_eq,
    toDyadic?_ofFields_normal fmt sign exponent fraction hexponentPos
      hexponent hfraction]
  exact Dyadic.toReal_mk _ _ _

/--
Closed-form real value of finite normal fields, including all-ones exponent fields when the
selected encoding treats them as finite.
-/
theorem toReal_ofFields_normal_of_isFinite
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponentPos : exponent ≠ 0)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth)
    (hfinite : isFinite (ofFields fmt sign exponent fraction) = true) :
    toReal (ofFields fmt sign exponent fraction) =
      (if sign then (-1 : ℝ) else 1) *
        ((pow2 fmt.fracWidth + fraction : Nat) : ℝ) *
          FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
            (Int.ofNat exponent - Int.ofNat fmt.exponentBias -
              Int.ofNat fmt.fracWidth) := by
  rw [toReal_eq,
    toDyadic?_ofFields_of_isFinite fmt sign exponent fraction hexponent
      hfraction hfinite]
  simpa [hexponentPos] using Dyadic.toReal_mk sign (pow2 fmt.fracWidth + fraction)
    (Int.ofNat exponent - Int.ofNat fmt.exponentBias - Int.ofNat fmt.fracWidth)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
