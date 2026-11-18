/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Adjacent.Proof.Order

/-!
# NaN stability of adjacent-value operations

For every binary descriptor, `nextUp` and `nextDown` return a NaN exactly when their input is a
NaN. The proof distinguishes the IEEE, maximum-NaN and unsigned-zero encodings through their
magnitude boundaries. Rank and order contracts are provided by the imported adjacency subjects.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- A word whose magnitude reaches the all-ones exponent field has that exponent field. -/
private theorem expField_eq_expAllOnesNat_of_le {fmt : FloatFormat} (x : Model fmt)
    (h : fmt.expAllOnesNat * 2 ^ fmt.fracWidth ≤ magnitudeBits x) :
    expField x = fmt.expAllOnesNat := by
  have he := expField_lt_pow2 x
  have hge : ¬expField x < fmt.expAllOnesNat := fun h' => by
    have := (expField_lt_iff x fmt.expAllOnesNat).1 h'
    omega
  unfold FloatFormat.expAllOnesNat at hge ⊢
  omega

/-- In the IEEE encoding a word is a NaN just when its magnitude exceeds the infinities'. -/
private theorem isNaN_iff_of_ieee {fmt : FloatFormat} (x : Model fmt)
    (hencoding : fmt.encoding = .ieee) :
    isNaN x = true ↔ fmt.expAllOnesNat * 2 ^ fmt.fracWidth < magnitudeBits x := by
  simp only [isNaN, hencoding, IEEE.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨hexp, hfrac⟩
    unfold magnitudeBits
    rw [hexp]
    omega
  · intro h
    have hexp := expField_eq_expAllOnesNat_of_le x h.le
    refine ⟨hexp, ?_⟩
    unfold magnitudeBits at h
    rw [hexp] at h
    omega

/-- The all-ones exponent field and a full fraction period fill the magnitude range. -/
private theorem expAllOnesNat_mul_add (fmt : FloatFormat) :
    fmt.expAllOnesNat * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth = fmt.signMaskNat := by
  have hexp : 0 < 2 ^ fmt.expWidth := Nat.two_pow_pos _
  rw [signMaskNat_eq_mul, Nat.mul_comm (2 ^ fmt.fracWidth) (2 ^ fmt.expWidth)]
  unfold FloatFormat.expAllOnesNat
  conv_rhs => rw [show 2 ^ fmt.expWidth = (2 ^ fmt.expWidth - 1) + 1 by omega]
  rw [Nat.add_mul, Nat.one_mul]

/-- In the maximum-NaN encoding a word is a NaN just when it has the largest magnitude. -/
private theorem isNaN_iff_of_finiteMaxNaN {fmt : FloatFormat} (x : Model fmt)
    (hencoding : fmt.encoding = .finiteMaxNaN) :
    isNaN x = true ↔ magnitudeBits x + 1 = fmt.signMaskNat := by
  have hf := fracField_lt_pow2 x
  have hfill := expAllOnesNat_mul_add fmt
  have hP : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  simp only [isNaN, hencoding, Bool.and_eq_true, beq_iff_eq]
  unfold FloatFormat.fracMaskNat
  constructor
  · rintro ⟨hexp, hfrac⟩
    unfold magnitudeBits
    rw [hexp, hfrac]
    omega
  · intro h
    have hexp := expField_eq_expAllOnesNat_of_le x (by omega)
    refine ⟨hexp, ?_⟩
    unfold magnitudeBits at h
    rw [hexp] at h
    omega

/-- In the FNUZ encoding the NaN is the negative word of magnitude zero. -/
private theorem isNaN_iff_of_finiteUnsignedZero {fmt : FloatFormat} (x : Model fmt)
    (hencoding : fmt.encoding = .finiteUnsignedZero) :
    isNaN x = true ↔ signBit x = true ∧ magnitudeBits x = 0 := by
  have hn := toNatBits_eq_magnitude x
  simp only [isNaN, hencoding, beq_iff_eq]
  constructor
  · intro hbits
    have hraw : x.toNatBits = fmt.signMaskNat := by
      rw [toNatBits, hbits, FloatFormat.signMask_toNat]
      rfl
    have hs : signBit x = true := (signBit_eq_true_iff_signMaskNat_le x).2 hraw.ge
    simp only [hs, ite_true] at hn
    exact ⟨hs, by omega⟩
  · rintro ⟨hs, hzero⟩
    apply BitVec.eq_of_toNat_eq
    rw [FloatFormat.signMask_toNat]
    change x.toNatBits = _
    simpa [hs, hzero, FloatFormat.signMaskNat, FloatFormat.signBitIndex] using hn

/-- The largest finite value of the maximum-NaN encoding sits just below the NaN magnitude. -/
private theorem magnitude_maxFinite_of_finiteMaxNaN {fmt : FloatFormat}
    (hencoding : fmt.encoding = .finiteMaxNaN) (sign : Bool) :
    magnitudeBits (maxFinite fmt sign) + 2 = fmt.signMaskNat := by
  have hfill := expAllOnesNat_mul_add fmt
  have hP : 2 ≤ 2 ^ fmt.fracWidth := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) fmt.fracWidth_pos
  unfold magnitudeBits maxFinite
  rw [expField_ofFields_of_lt _ _ _ _ fmt.maxFiniteExpField_lt_two_pow,
    fracField_ofFields_of_lt _ _ _ _ fmt.maxFiniteFracField_lt_two_pow]
  simp only [FloatFormat.maxFiniteExpField, FloatFormat.maxFiniteFracField, hencoding,
    FloatFormat.Encoding.maxFiniteExponent, FloatFormat.fracMaskNat]
  unfold FloatFormat.expAllOnesNat at hfill
  omega

/-- The negative subnormal of least magnitude has magnitude one. -/
private theorem magnitude_negMinSubnormal (fmt : FloatFormat) :
    magnitudeBits (negMinSubnormal fmt) = 1 := by
  have hP : 2 ≤ 2 ^ fmt.fracWidth := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) fmt.fracWidth_pos
  rw [negMinSubnormal_eq_ofFields]
  unfold magnitudeBits
  rw [expField_ofFields_of_lt _ _ _ _ (Nat.two_pow_pos _),
    fracField_ofFields_of_lt _ _ _ _ (by omega)]
  simp

/--
A word one magnitude step below a number is not a NaN, in every encoding except for the
unsigned-zero NaN: the negative word of zero magnitude.
-/
private theorem isNaN_eq_false_of_magnitude_add_one_eq {fmt : FloatFormat} {x z : Model fmt}
    (hx : isNaN x = false) (hm : magnitudeBits z + 1 = magnitudeBits x)
    (hfnuz : fmt.encoding = .finiteUnsignedZero → ¬(signBit z = true ∧ magnitudeBits z = 0)) :
    isNaN z = false := by
  have hxS := magnitude_lt x
  cases hencoding : fmt.encoding with
  | ieee =>
      have hle := magnitude_le_of_isNaN_eq_false hencoding hx
      cases hzn : isNaN z
      · rfl
      · have := (isNaN_iff_of_ieee _ hencoding).1 hzn
        omega
  | finiteMaxNaN =>
      cases hzn : isNaN z
      · rfl
      · have := (isNaN_iff_of_finiteMaxNaN _ hencoding).1 hzn
        omega
  | finiteUnsignedZero =>
      cases hzn : isNaN z
      · rfl
      · exact absurd ((isNaN_iff_of_finiteUnsignedZero _ hencoding).1 hzn) (hfnuz hencoding)
  | finite => simp [isNaN, hencoding]

/--
A word one magnitude step above a non-infinite number is not a NaN, in every encoding except
above the largest finite value of the maximum-NaN encoding.
-/
private theorem isNaN_eq_false_of_magnitude_eq_add_one {fmt : FloatFormat} {x z : Model fmt}
    (hx : isNaN x = false) (hinf : isInfinite x = false)
    (hm : magnitudeBits z = magnitudeBits x + 1)
    (hmax : fmt.encoding = .finiteMaxNaN → x ≠ maxFinite fmt (signBit x)) :
    isNaN z = false := by
  cases hencoding : fmt.encoding with
  | ieee =>
      have hlt := magnitude_lt_of_isFinite hencoding
        (isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x hx hinf)
      cases hzn : isNaN z
      · rfl
      · have := (isNaN_iff_of_ieee _ hencoding).1 hzn
        omega
  | finiteMaxNaN =>
      cases hzn : isNaN z
      · rfl
      · have hfull := (isNaN_iff_of_finiteMaxNaN _ hencoding).1 hzn
        have hmaxm := magnitude_maxFinite_of_finiteMaxNaN hencoding (signBit x)
        exact absurd (eq_of_signBit_eq_of_magnitude_eq (by simp) (by omega)) (hmax hencoding)
  | finiteUnsignedZero =>
      cases hzn : isNaN z
      · rfl
      · have := ((isNaN_iff_of_finiteUnsignedZero _ hencoding).1 hzn).2
        omega
  | finite => simp [isNaN, hencoding]

/-- `nextUp` returns a NaN just for a NaN input, because from a number it steps to a number. -/
@[simp] theorem isNaN_nextUp {fmt : FloatFormat} (x : Model fmt) :
    isNaN (nextUp x) = isNaN x := by
  cases hnan : isNaN x
  · change isNaN (Internal.Value.nextUp x) = false
    unfold Internal.Value.nextUp
    simp only [hnan, Bool.false_eq_true, ite_false]
    split_ifs with hinf hzero hfnuz hmax hsign
    · exact hnan
    · exact isNaN_posMinSubnormal fmt
    · exact isNaN_posZero fmt
    · exact hnan
    · have hzeroFalse : isZero x = false := by simpa using hzero
      have hraw := signMaskNat_lt_toNatBits_of_nonzero_nonNaN x hsign hzeroFalse hnan
      have hz := toNatBits_ofBits_sub_one x (by omega)
      obtain ⟨-, hzm⟩ := signBit_magnitude_of_signMaskNat_le (ofBits (x.bits - 1))
        (by rw [hz]; omega)
      obtain ⟨-, hxm⟩ := signBit_magnitude_of_signMaskNat_le x hraw.le
      rw [hz] at hzm
      apply isNaN_eq_false_of_magnitude_add_one_eq hnan (by omega)
      rintro hencoding ⟨-, hzeroMagnitude⟩
      have hvalue : x = negMinSubnormal fmt :=
        eq_of_signBit_eq_of_magnitude_eq (by simp [hsign])
          (by rw [magnitude_negMinSubnormal]; omega)
      exact absurd (by simp [FloatFormat.supportsSignedZero, hencoding, hvalue]) hfnuz
    · have hsignFalse : signBit x = false := by simpa using hsign
      have hinfFalse : isInfinite x = false := by simpa [hsignFalse] using hinf
      have hmaxNe : fmt.supportsInfinity = false → x ≠ posMaxFinite fmt := by
        intro hsupports hvalue
        exact hmax (by simp [hsupports, hvalue])
      have hraw := toNatBits_add_one_lt_signMaskNat x hsignFalse hnan hmaxNe
      have hz := toNatBits_ofBits_add_one x (hraw.trans (signMaskNat_lt_two_pow_bitWidth fmt))
      obtain ⟨-, hzm⟩ := signBit_magnitude_of_toNatBits_lt (ofBits (x.bits + 1))
        (by rw [hz]; exact hraw)
      obtain ⟨-, hxm⟩ := signBit_magnitude_of_toNatBits_lt x (by omega)
      rw [hz] at hzm
      exact isNaN_eq_false_of_magnitude_eq_add_one hnan hinfFalse (by omega) fun hencoding => by
        rw [hsignFalse]
        exact hmaxNe (by simp [FloatFormat.supportsInfinity, hencoding])
  · simp [nextUp, Internal.Value.nextUp, hnan]

/-- `nextDown` returns a NaN just for a NaN input, because from a number it steps to a number. -/
@[simp] theorem isNaN_nextDown {fmt : FloatFormat} (x : Model fmt) :
    isNaN (nextDown x) = isNaN x := by
  cases hnan : isNaN x
  · change isNaN (Internal.Value.nextDown x) = false
    unfold Internal.Value.nextDown
    simp only [hnan, Bool.false_eq_true, ite_false]
    split_ifs with hinf hzero hmin hsign
    · exact hnan
    · exact isNaN_negMinSubnormal fmt
    · exact hnan
    · have hinfFalse : isInfinite x = false := by simpa [hsign] using hinf
      have hminNe : fmt.supportsInfinity = false → x ≠ negMaxFinite fmt := by
        intro hsupports hvalue
        exact hmin (by simp [hsupports, hvalue])
      have hfit := toNatBits_add_one_lt_two_pow_of_negative x hnan hminNe
      have hz := toNatBits_ofBits_add_one x hfit
      have hneg := (signBit_eq_true_iff_signMaskNat_le x).1 hsign
      obtain ⟨-, hzm⟩ := signBit_magnitude_of_signMaskNat_le (ofBits (x.bits + 1))
        (by rw [hz]; omega)
      obtain ⟨-, hxm⟩ := signBit_magnitude_of_signMaskNat_le x hneg
      rw [hz] at hzm
      exact isNaN_eq_false_of_magnitude_eq_add_one hnan hinfFalse (by omega) fun hencoding => by
        rw [hsign]
        exact hminNe (by simp [FloatFormat.supportsInfinity, hencoding])
    · have hsignFalse : signBit x = false := by simpa using hsign
      have hzeroFalse : isZero x = false := by simpa using hzero
      have hpos := toNatBits_pos_of_isZero_eq_false x hzeroFalse
      have hlt := (signBit_eq_false_iff_toNatBits_lt_signMaskNat x).1 hsignFalse
      have hz := toNatBits_ofBits_sub_one x hpos
      obtain ⟨hzs, hzm⟩ := signBit_magnitude_of_toNatBits_lt (ofBits (x.bits - 1))
        (by rw [hz]; omega)
      obtain ⟨-, hxm⟩ := signBit_magnitude_of_toNatBits_lt x hlt
      rw [hz] at hzm
      apply isNaN_eq_false_of_magnitude_add_one_eq hnan (by omega)
      rintro - ⟨hzsign, -⟩
      rw [hzs] at hzsign
      exact absurd hzsign Bool.false_ne_true
  · simp [nextDown, Internal.Value.nextDown, hnan]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
