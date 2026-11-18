/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# Word fields and signed magnitudes for adjacency

The field decomposition and sign mask identify zero, endpoint and magnitude words for every binary
descriptor. These lemmas supply the encoded-word facts used by the discrete rank, order and NaN-
stability proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

private theorem bitWidth_pos (fmt : FloatFormat) :
    0 < fmt.bitWidth := by
  unfold FloatFormat.bitWidth
  omega

/-- Incrementing a word adds one to its natural encoding when the sum fits. -/
theorem toNatBits_ofBits_add_one
    {fmt : FloatFormat} (x : Model fmt)
    (hfit : x.toNatBits + 1 < 2 ^ fmt.bitWidth) :
    toNatBits (ofBits (x.bits + 1)) = x.toNatBits + 1 := by
  have hone : ((1 : BitVec fmt.bitWidth).toNat) = 1 :=
    BitVec.toNat_one (bitWidth_pos fmt)
  simpa only [toNatBits, ofBits, hone] using
    BitVec.toNat_add_of_lt (x := x.bits) (y := 1)
      (by simpa only [toNatBits, hone] using hfit)

/-- Decrementing a nonzero word subtracts one from its natural encoding. -/
theorem toNatBits_ofBits_sub_one
    {fmt : FloatFormat} (x : Model fmt)
    (hpos : 0 < x.toNatBits) :
    toNatBits (ofBits (x.bits - 1)) = x.toNatBits - 1 := by
  have hone : ((1 : BitVec fmt.bitWidth).toNat) = 1 :=
    BitVec.toNat_one (bitWidth_pos fmt)
  simpa only [toNatBits, ofBits, hone] using
    BitVec.toNat_sub_of_le (x := x.bits) (y := 1)
      (by simpa only [toNatBits, BitVec.le_def, hone] using Nat.succ_le_of_lt hpos)

private theorem shiftLeft_or_lowMask (a k : Nat) :
    a.shiftLeft k ||| (2 ^ k - 1) = a.shiftLeft k + (2 ^ k - 1) := by
  change (a <<< k) ||| (2 ^ k - 1) = (a <<< k) + (2 ^ k - 1)
  exact (Nat.shiftLeft_add_eq_or_of_lt
    (Nat.sub_lt (Nat.two_pow_pos k) (by decide : 0 < (1 : Nat))) a).symm

private theorem shiftLeft_eq_mul_pow (a k : Nat) :
    a.shiftLeft k = a * 2 ^ k := by
  change a <<< k = a * 2 ^ k
  exact Nat.shiftLeft_eq a k

/-- The sign bit divides the storage words into two equally sized halves. -/
theorem two_mul_signMaskNat_eq_two_pow_bitWidth
    (fmt : FloatFormat) :
    2 * fmt.signMaskNat = 2 ^ fmt.bitWidth := by
  unfold FloatFormat.signMaskNat FloatFormat.signBitIndex
    FloatFormat.bitWidth
  rw [show 1 + fmt.expWidth + fmt.fracWidth - 1 =
      fmt.expWidth + fmt.fracWidth by omega]
  rw [show 1 + fmt.expWidth + fmt.fracWidth =
      (fmt.expWidth + fmt.fracWidth) + 1 by omega]
  simp [pow_succ, Nat.mul_comm]

/-- The sign-bit mask fits in the format's storage width. -/
theorem signMaskNat_lt_two_pow_bitWidth (fmt : FloatFormat) :
    fmt.signMaskNat < 2 ^ fmt.bitWidth := by
  have hsignPos : 0 < fmt.signMaskNat := by
    unfold FloatFormat.signMaskNat
    positivity
  have hwidth := two_mul_signMaskNat_eq_two_pow_bitWidth fmt
  omega

/-- Positive zero has natural encoding zero. -/
@[simp] theorem toNatBits_posZero (fmt : FloatFormat) :
    (posZero fmt).toNatBits = 0 := by
  simp [posZero, toNatBits, ofNatBits, ofBits,
    FloatFormat.ofWordNat]

/-- The least positive subnormal has natural encoding one. -/
@[simp] theorem toNatBits_posMinSubnormal (fmt : FloatFormat) :
    (posMinSubnormal fmt).toNatBits = 1 := by
  apply toNatBits_ofNatBits_of_lt
  have hwidth : 0 < fmt.bitWidth := bitWidth_pos fmt
  exact Nat.one_lt_two_pow (Nat.ne_of_gt hwidth)

/-- The negative-zero word consists of the sign-bit mask. -/
@[simp] theorem toNatBits_negZero (fmt : FloatFormat) :
    (negZero fmt).toNatBits = fmt.signMaskNat := by
  unfold negZero toNatBits ofBits
  rw [FloatFormat.signMask_toNat]
  rfl

/-- The least negative subnormal has the sign-bit mask followed by one. -/
@[simp] theorem toNatBits_negMinSubnormal (fmt : FloatFormat) :
    (negMinSubnormal fmt).toNatBits = fmt.signMaskNat + 1 := by
  unfold negMinSubnormal toNatBits ofBits
  rw [BitVec.toNat_or, FloatFormat.signMask_toNat]
  have hone :
      (FloatFormat.ofWordNat fmt 1).toNat = 1 := by
    unfold FloatFormat.ofWordNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.one_lt_two_pow (Nat.ne_of_gt (bitWidth_pos fmt))
  rw [hone]
  unfold FloatFormat.signMaskNat FloatFormat.signBitIndex
  have hwidth : fmt.bitWidth - 1 ≠ 0 := by
    have hexponent := fmt.expWidth_ge_two
    have hfraction := fmt.fracWidth_pos
    unfold FloatFormat.bitWidth
    omega
  rw [Nat.or_comm, Nat.or_two_pow_eq_add_of_lt
    (Nat.one_lt_two_pow hwidth)]
  omega

/-- A zero word has zero exponent and fraction fields, in every encoding. -/
theorem fields_eq_zero_of_isZero {fmt : FloatFormat} {x : Model fmt}
    (hx : isZero x = true) : expField x = 0 ∧ fracField x = 0 := by
  cases hencoding : fmt.encoding with
  | finiteUnsignedZero =>
      have hbits : x.bits = 0 := by simpa [isZero, hencoding] using hx
      have hvalue : x = posZero fmt := by
        cases x
        simp_all [posZero, ofNatBits, ofBits, FloatFormat.ofWordNat]
      subst hvalue
      simp
  | ieee | finiteMaxNaN | finite =>
      have hbool : (expField x == 0) = true ∧ (fracField x == 0) = true := by
        simpa [isZero, hencoding, IEEE.isZero, Bool.and_eq_true] using hx
      exact ⟨beq_iff_eq.mp hbool.1, beq_iff_eq.mp hbool.2⟩

private theorem upperPositiveCode_eq_ofFields_allOnes
    (fmt : FloatFormat) :
    ofNatBits (fmt.signMaskNat - 1) =
      ofFields fmt false fmt.expAllOnesNat fmt.fracMaskNat := by
  unfold ofNatBits ofFields
  apply congrArg ofBits
  rw [mkBits_eq_internal_apply]
  apply BitVec.eq_of_toNat_eq
  unfold Internal.mkBits FloatFormat.signMaskNat FloatFormat.signBitIndex
    FloatFormat.expAllOnesNat FloatFormat.fracMaskNat
    FloatFormat.ofWordNat FloatFormat.bitWidth
  simp only [BitVec.ofNatLT_eq_ofNat, BitVec.toNat_ofNat,
    Bool.false_eq_true, ite_false, Nat.zero_or]
  simp only [Nat.and_self]
  rw [Nat.mod_eq_of_lt]
  · rw [shiftLeft_or_lowMask]
    rw [show 1 + fmt.expWidth + fmt.fracWidth - 1 =
        fmt.expWidth + fmt.fracWidth by omega]
    rw [shiftLeft_eq_mul_pow, pow_add, Nat.sub_mul]
    simp only [one_mul]
    have hexponent : 0 < 2 ^ fmt.expWidth := Nat.two_pow_pos _
    have hfraction : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
    have hstorage :
        2 ^ (1 + fmt.expWidth + fmt.fracWidth) =
          2 * (2 ^ fmt.expWidth * 2 ^ fmt.fracWidth) := by
      rw [show 1 + fmt.expWidth + fmt.fracWidth =
          1 + (fmt.expWidth + fmt.fracWidth) by omega]
      simp [pow_add]
    have hfractionLeProduct :
        2 ^ fmt.fracWidth ≤
          2 ^ fmt.expWidth * 2 ^ fmt.fracWidth :=
      Nat.le_mul_of_pos_left _ hexponent
    rw [hstorage]
    rw [Nat.mod_eq_of_lt]
    · exact (Nat.sub_add_sub_cancel
        hfractionLeProduct hfraction).symm
    · have hproduct :
          0 < 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth :=
        Nat.mul_pos hexponent hfraction
      rw [Nat.sub_add_sub_cancel hfractionLeProduct hfraction]
      omega
  · rw [show 1 + fmt.expWidth + fmt.fracWidth - 1 =
        fmt.expWidth + fmt.fracWidth by omega]
    have hpow :
        2 ^ (fmt.expWidth + fmt.fracWidth) <
          2 ^ (1 + fmt.expWidth + fmt.fracWidth) := by
      apply Nat.pow_lt_pow_right (by decide)
      omega
    have hsmall : 0 < 2 ^ (fmt.expWidth + fmt.fracWidth) :=
      Nat.two_pow_pos _
    omega

private theorem topCode_eq_ofFields_allOnes
    (fmt : FloatFormat) :
    ofNatBits (2 ^ fmt.bitWidth - 1) =
      ofFields fmt true fmt.expAllOnesNat fmt.fracMaskNat := by
  unfold ofNatBits ofFields
  apply congrArg ofBits
  rw [mkBits_eq_internal_apply]
  apply BitVec.eq_of_toNat_eq
  unfold Internal.mkBits FloatFormat.expAllOnesNat FloatFormat.fracMaskNat
    FloatFormat.ofWordNat FloatFormat.bitWidth
  simp only [BitVec.ofNatLT_eq_ofNat, BitVec.toNat_ofNat,
    ite_true, Nat.and_self]
  rw [Nat.or_assoc]
  rw [shiftLeft_or_lowMask]
  rw [shiftLeft_eq_mul_pow
    (2 ^ fmt.expWidth - 1) fmt.fracWidth]
  rw [Nat.sub_mul]
  simp only [one_mul]
  have hexponent : 0 < 2 ^ fmt.expWidth := Nat.two_pow_pos _
  have hfraction : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  have hfractionLeProduct :
      2 ^ fmt.fracWidth ≤
        2 ^ fmt.expWidth * 2 ^ fmt.fracWidth :=
    Nat.le_mul_of_pos_left _ hexponent
  rw [Nat.sub_add_sub_cancel hfractionLeProduct hfraction]
  have hhalf :
      2 ^ (fmt.expWidth + fmt.fracWidth) =
        2 ^ fmt.expWidth * 2 ^ fmt.fracWidth := by
    rw [pow_add]
  rw [← hhalf]
  have hlower :
      2 ^ (fmt.expWidth + fmt.fracWidth) - 1 <
        2 ^ (fmt.expWidth + fmt.fracWidth) := by
    have hpos : 0 < 2 ^ (fmt.expWidth + fmt.fracWidth) :=
      Nat.two_pow_pos _
    omega
  rw [shiftLeft_eq_mul_pow 1 (fmt.expWidth + fmt.fracWidth)]
  simp only [one_mul]
  rw [Nat.or_comm (2 ^ (fmt.expWidth + fmt.fracWidth))
    (2 ^ (fmt.expWidth + fmt.fracWidth) - 1)]
  rw [Nat.or_two_pow_eq_add_of_lt hlower]
  have hstorage :
      2 ^ (1 + fmt.expWidth + fmt.fracWidth) =
        2 * 2 ^ (fmt.expWidth + fmt.fracWidth) := by
    rw [show 1 + fmt.expWidth + fmt.fracWidth =
        1 + (fmt.expWidth + fmt.fracWidth) by omega]
    simp [pow_add]
  rw [hstorage]
  have hhalfPos : 0 < 2 ^ (fmt.expWidth + fmt.fracWidth) :=
    Nat.two_pow_pos _
  rw [Nat.mod_eq_of_lt]
  · rw [Nat.mod_eq_of_lt]
    · omega
    · omega
  · omega

/--
The all-ones exponent and fraction fields, with either sign, are a NaN when the encoding has NaN
fields there and otherwise the largest finite value of that sign in a format without infinities.
-/
private theorem ofFields_allOnes_isNaN_or_maxFinite (fmt : FloatFormat) (sign : Bool) :
    isNaN (ofFields fmt sign fmt.expAllOnesNat fmt.fracMaskNat) = true ∨
      (fmt.supportsInfinity = false ∧
        ofFields fmt sign fmt.expAllOnesNat fmt.fracMaskNat = maxFinite fmt sign) := by
  have hexponentFit :
      fmt.expAllOnesNat < 2 ^ fmt.expWidth := by
    unfold FloatFormat.expAllOnesNat
    have hpow : 0 < 2 ^ fmt.expWidth := Nat.two_pow_pos _
    omega
  have hfractionFit :
      fmt.fracMaskNat < 2 ^ fmt.fracWidth := by
    unfold FloatFormat.fracMaskNat
    have hpow : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
    omega
  cases hencoding : fmt.encoding with
  | ieee =>
      left
      simp [isNaN, IEEE.isNaN, hencoding,
        Nat.mod_eq_of_lt hexponentFit,
        Nat.mod_eq_of_lt hfractionFit,
        (FloatFormat.fracMaskNat_pos fmt).ne']
  | finiteMaxNaN =>
      left
      simp [isNaN, hencoding,
        Nat.mod_eq_of_lt hexponentFit,
        Nat.mod_eq_of_lt hfractionFit]
  | finiteUnsignedZero | finite =>
      right
      constructor
      · simp [FloatFormat.supportsInfinity, hencoding]
      · simp [maxFinite, FloatFormat.maxFiniteExpField,
          FloatFormat.maxFiniteFracField, FloatFormat.Encoding.maxFiniteExponent,
          FloatFormat.expAllOnesNat, hencoding]

private theorem upperPositiveCode_isNaN_or_posMaxFinite
    {fmt : FloatFormat} (x : Model fmt)
    (hraw : x.toNatBits + 1 = fmt.signMaskNat) :
    isNaN x = true ∨
      (fmt.supportsInfinity = false ∧ x = posMaxFinite fmt) := by
  have hvalue : x = ofNatBits (fmt.signMaskNat - 1) := by
    rw [← ofNatBits_toNatBits x]
    congr 1
    omega
  rw [hvalue, upperPositiveCode_eq_ofFields_allOnes]
  exact ofFields_allOnes_isNaN_or_maxFinite fmt false

private theorem topCode_isNaN_or_negMaxFinite
    {fmt : FloatFormat} (x : Model fmt)
    (hraw : x.toNatBits + 1 = 2 ^ fmt.bitWidth) :
    isNaN x = true ∨
      (fmt.supportsInfinity = false ∧ x = negMaxFinite fmt) := by
  have hvalue : x = ofNatBits (2 ^ fmt.bitWidth - 1) := by
    rw [← ofNatBits_toNatBits x]
    congr 1
    omega
  rw [hvalue, topCode_eq_ofFields_allOnes]
  exact ofFields_allOnes_isNaN_or_maxFinite fmt true

private theorem signMaskCode_isZero_or_isNaN
    {fmt : FloatFormat} (x : Model fmt)
    (hraw : x.toNatBits = fmt.signMaskNat) :
    isZero x = true ∨ isNaN x = true := by
  have hvalue : x = negZero fmt := by
    calc
      x = ofNatBits x.toNatBits :=
        (ofNatBits_toNatBits x).symm
      _ = ofNatBits fmt.signMaskNat := by rw [hraw]
      _ = ofNatBits (negZero fmt).toNatBits := by
        rw [toNatBits_negZero]
      _ = negZero fmt := ofNatBits_toNatBits _
  rw [hvalue]
  cases hencoding : fmt.encoding with
  | finiteUnsignedZero =>
      right
      simp [isNaN, hencoding, negZero, ofBits]
  | ieee | finiteMaxNaN | finite =>
      left
      rw [← ofFields_true_zero_zero]
      rw [isZero_ofFields fmt true 0 0
        (Nat.two_pow_pos _) (Nat.two_pow_pos _)]
      simp [hencoding]

/-- A word that does not classify as zero has positive natural encoding. -/
theorem toNatBits_pos_of_isZero_eq_false
    {fmt : FloatFormat} (x : Model fmt)
    (hzero : isZero x = false) :
    0 < x.toNatBits := by
  apply Nat.pos_of_ne_zero
  intro hraw
  have hvalue : x = posZero fmt := by
    calc
      x = ofNatBits x.toNatBits :=
        (ofNatBits_toNatBits x).symm
      _ = ofNatBits 0 := by rw [hraw]
      _ = posZero fmt := rfl
  subst x
  have hzeroTrue := isZero_posZero fmt
  simp [hzero] at hzeroTrue

/-- A negative word other than zero or NaN lies strictly above the sign-bit mask. -/
theorem signMaskNat_lt_toNatBits_of_nonzero_nonNaN
    {fmt : FloatFormat} (x : Model fmt)
    (hsign : signBit x = true)
    (hzero : isZero x = false)
    (hnan : isNaN x = false) :
    fmt.signMaskNat < x.toNatBits := by
  have hle :=
    (signBit_eq_true_iff_signMaskNat_le x).1 hsign
  apply hle.lt_of_ne
  intro heq
  rcases signMaskCode_isZero_or_isNaN x heq.symm with
    hzero' | hnan'
  · simp [hzero] at hzero'
  · simp [hnan] at hnan'

/-- Incrementing a positive non-NaN word below saturation stays below the sign bit. -/
theorem toNatBits_add_one_lt_signMaskNat
    {fmt : FloatFormat} (x : Model fmt)
    (hsign : signBit x = false)
    (hnan : isNaN x = false)
    (hmax :
      fmt.supportsInfinity = false → x ≠ posMaxFinite fmt) :
    x.toNatBits + 1 < fmt.signMaskNat := by
  have hlt :=
    (signBit_eq_false_iff_toNatBits_lt_signMaskNat x).1 hsign
  apply Nat.lt_of_le_of_ne (by omega)
  intro heq
  rcases upperPositiveCode_isNaN_or_posMaxFinite x heq with
    hnan' | ⟨hinfinity, hvalue⟩
  · simp [hnan] at hnan'
  · exact hmax hinfinity hvalue

/-- Incrementing a non-NaN word below negative saturation fits in the storage width. -/
theorem toNatBits_add_one_lt_two_pow_of_negative
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false)
    (hmin :
      fmt.supportsInfinity = false → x ≠ negMaxFinite fmt) :
    x.toNatBits + 1 < 2 ^ fmt.bitWidth := by
  have hlt := toNatBits_lt_two_pow x
  apply Nat.lt_of_le_of_ne (by omega)
  intro heq
  rcases topCode_isNaN_or_negMaxFinite x heq with
    hnan' | ⟨hinfinity, hvalue⟩
  · simp [hnan] at hnan'
  · exact hmin hinfinity hvalue

/-- Equal stored words represent equal values of the same binary format. -/
theorem eq_of_bits_eq
    {fmt : FloatFormat} {x y : Model fmt}
    (hbits : x.bits = y.bits) :
    x = y := by
  cases x
  cases y
  simp_all

/-! ## Exact rank steps -/

/-- A value other than an endpoint `y` fails the saturating-endpoint test against `y`. -/
theorem endpointTest_eq_false {fmt : FloatFormat} {x y : Model fmt}
    (h : fmt.supportsInfinity = false → x ≠ y) :
    (!fmt.supportsInfinity && (x.bits == y.bits)) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hendpoint
  have hparts : !fmt.supportsInfinity = true ∧ (x.bits == y.bits) = true := by
    simpa [Bool.and_eq_true] using hendpoint
  exact h (by simpa using hparts.1) (eq_of_bits_eq (beq_iff_eq.mp hparts.2))

/-- The storage word without its sign bit: the biased exponent and fraction fields together. -/
def magnitudeBits {fmt : FloatFormat} (x : Model fmt) : Nat :=
  expField x * 2 ^ fmt.fracWidth + fracField x

/-- The sign-bit place value is the product of the exponent and fraction ranges. -/
theorem signMaskNat_eq_mul (fmt : FloatFormat) :
    fmt.signMaskNat = 2 ^ fmt.fracWidth * 2 ^ fmt.expWidth := by
  unfold FloatFormat.signMaskNat FloatFormat.signBitIndex FloatFormat.bitWidth
  rw [← pow_add]
  congr 1
  omega

private theorem magnitude_eq_mod {fmt : FloatFormat} (x : Model fmt) :
    magnitudeBits x = x.toNatBits % fmt.signMaskNat := by
  unfold magnitudeBits
  rw [expField_eq_internal_apply, fracField_eq_internal_apply]
  unfold Internal.expField Internal.fracField FloatFormat.expAllOnesNat FloatFormat.fracMaskNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    signMaskNat_eq_mul, Nat.mod_mul]
  ac_rfl

/-- The unsigned magnitude occupies only the bits below the sign bit. -/
theorem magnitude_lt {fmt : FloatFormat} (x : Model fmt) :
    magnitudeBits x < fmt.signMaskNat := by
  rw [magnitude_eq_mod]
  apply Nat.mod_lt
  unfold FloatFormat.signMaskNat
  positivity

/-- A storage word is its sign-bit place value, when the sign is set, plus its magnitude. -/
theorem toNatBits_eq_magnitude {fmt : FloatFormat} (x : Model fmt) :
    x.toNatBits = (if signBit x then fmt.signMaskNat else 0) + magnitudeBits x := by
  rw [magnitude_eq_mod]
  have hlt := toNatBits_lt_two_pow x
  rw [← two_mul_signMaskNat_eq_two_pow_bitWidth] at hlt
  cases hs : signBit x
  · have := (signBit_eq_false_iff_toNatBits_lt_signMaskNat x).1 hs
    simp [Nat.mod_eq_of_lt this]
  · have := (signBit_eq_true_iff_signMaskNat_le x).1 hs
    simp only [ite_true]
    rw [Nat.mod_eq_sub_mod this, Nat.mod_eq_of_lt (by omega)]
    omega

/-- A word below the sign-bit place value has a clear sign and is its own magnitude. -/
theorem signBit_magnitude_of_toNatBits_lt {fmt : FloatFormat} (x : Model fmt)
    (hx : x.toNatBits < fmt.signMaskNat) :
    signBit x = false ∧ magnitudeBits x = x.toNatBits := by
  have hs := (signBit_eq_false_iff_toNatBits_lt_signMaskNat x).2 hx
  have h := toNatBits_eq_magnitude x
  simp only [hs, Bool.false_eq_true, ite_false, Nat.zero_add] at h
  exact ⟨hs, h.symm⟩

/-- A word at or above the sign-bit place value has a set sign and the rest as its magnitude. -/
theorem signBit_magnitude_of_signMaskNat_le {fmt : FloatFormat} (x : Model fmt)
    (hx : fmt.signMaskNat ≤ x.toNatBits) :
    signBit x = true ∧ magnitudeBits x = x.toNatBits - fmt.signMaskNat := by
  have hs := (signBit_eq_true_iff_signMaskNat_le x).2 hx
  have h := toNatBits_eq_magnitude x
  simp only [hs, ite_true] at h
  exact ⟨hs, by omega⟩

/-- Two words with the same sign bit and magnitude are equal. -/
theorem eq_of_signBit_eq_of_magnitude_eq {fmt : FloatFormat} {x y : Model fmt}
    (hs : signBit x = signBit y) (hm : magnitudeBits x = magnitudeBits y) : x = y := by
  have hn : x.toNatBits = y.toNatBits := by
    rw [toNatBits_eq_magnitude x, toNatBits_eq_magnitude y, hs, hm]
  rw [← ofNatBits_toNatBits x, hn, ofNatBits_toNatBits]

/-- A biased exponent field below `c` is a magnitude below `c` fraction-field periods. -/
theorem expField_lt_iff {fmt : FloatFormat} (x : Model fmt) (c : Nat) :
    expField x < c ↔ magnitudeBits x < c * 2 ^ fmt.fracWidth := by
  have hf := fracField_lt_pow2 x
  unfold magnitudeBits
  constructor
  · intro h
    have : (expField x + 1) * 2 ^ fmt.fracWidth ≤ c * 2 ^ fmt.fracWidth :=
      Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · intro h
    by_contra hc
    have : c * 2 ^ fmt.fracWidth ≤ expField x * 2 ^ fmt.fracWidth :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- A zero magnitude has zero exponent and fraction fields. -/
theorem fields_eq_zero_of_magnitude_eq_zero {fmt : FloatFormat} {x : Model fmt}
    (hm : magnitudeBits x = 0) : expField x = 0 ∧ fracField x = 0 := by
  have he := (expField_lt_iff x 1).2 (by rw [hm]; simp)
  refine ⟨by omega, ?_⟩
  unfold magnitudeBits at hm
  omega

/-- Every word that classifies as zero has zero unsigned magnitude. -/
theorem magnitude_eq_zero_of_isZero {fmt : FloatFormat} {x : Model fmt}
    (hx : isZero x = true) : magnitudeBits x = 0 := by
  obtain ⟨hexponent, hfraction⟩ := fields_eq_zero_of_isZero hx
  simp [magnitudeBits, hexponent, hfraction]

/--
A number whose magnitude is zero is a zero. In FNUZ the sign-mask word has magnitude zero too, and
it is the NaN that the hypothesis excludes.
-/
theorem isZero_of_magnitude_eq_zero {fmt : FloatFormat} {x : Model fmt}
    (hnan : isNaN x = false) (hm : magnitudeBits x = 0) : isZero x = true := by
  obtain ⟨he, hf⟩ := fields_eq_zero_of_magnitude_eq_zero hm
  cases hencoding : fmt.encoding with
  | finiteUnsignedZero =>
      have hn := toNatBits_eq_magnitude x
      rw [hm] at hn
      cases hs : signBit x
      · have hbits : x.bits = 0 := by
          apply BitVec.eq_of_toNat_eq
          simpa [toNatBits, hs] using hn
        simp [isZero, hencoding, hbits]
      · have hbits : x.bits = FloatFormat.signMask fmt := by
          apply BitVec.eq_of_toNat_eq
          rw [FloatFormat.signMask_toNat]
          simpa [toNatBits, hs, FloatFormat.signMaskNat, FloatFormat.signBitIndex] using hn
        simp [isNaN, hencoding, hbits] at hnan
  | ieee | finiteMaxNaN | finite =>
      simp [isZero, hencoding, IEEE.isZero, he, hf]

/-- Signed magnitude of a word: its magnitude, negated when the sign bit is set. -/
def signedMagnitude {fmt : FloatFormat} (x : Model fmt) : Int :=
  if signBit x then -(magnitudeBits x : Int) else magnitudeBits x

end Model
end FloatLib.Floats.Formats.BinaryInterchange
