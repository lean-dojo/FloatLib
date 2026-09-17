/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Core.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import FloatLib.Kernels.LimbArray.Shift.Proof

/-!
# Wide-limb storage

The limb carrier of `Core.Runtime` represents the exact-width proof model through a bounded
storage invariant. The storage invariant `topLimbFits` is shown equivalent to the value lying
below `2 ^ bitWidth` (`topLimbFits_iff`), which gives the codec laws `toModel_ofModel` and
`ofModel_toModel`. The field accessors then agree with `Model.signBit`, `Model.expField`, and
`Model.fracField`, so the compact finite decoder `FiniteKernel.decode?` of a stored value is
read off the limbs (`decode?_toModel`). Finally `toModel_pack` states the exact model that
`pack` produces; every arithmetic kernel of this backend ends in `pack`, so this is the contract
each refinement proof uses. The main storage and packing results are `Value.toNat_lt` and
`toModel_pack`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

variable {fmt : FloatFormat}

/-! ## Layout facts -/

/-- An eligible descriptor uses the conventional IEEE encoding and bias. -/
theorem Eligible.isIEEE (h : Eligible fmt) : fmt.isIEEE = true := h.1

/-- An eligible descriptor is wider than 128 bits. -/
theorem Eligible.width_gt (h : Eligible fmt) : 128 < fmt.bitWidth := h.2.1

/-- An eligible exponent field fits one machine word. -/
theorem Eligible.exp_le (h : Eligible fmt) : fmt.expWidth ≤ 32 := h.2.2

/-- Every descriptor has at least three encoded bits. -/
theorem three_le_bitWidth (fmt : FloatFormat) : 3 ≤ fmt.bitWidth := by
  unfold FloatFormat.bitWidth
  have := fmt.expWidth_ge_two
  have := fmt.fracWidth_pos
  omega

/-- The limb count covers the encoded width. -/
theorem bitWidth_le_limbBits (fmt : FloatFormat) : fmt.bitWidth ≤ 32 * limbCount fmt := by
  unfold limbCount
  omega

/-- The top limb holds at least one encoded bit. -/
theorem limbBits_lt_bitWidth (fmt : FloatFormat) : 32 * (limbCount fmt - 1) < fmt.bitWidth := by
  unfold limbCount
  have := three_le_bitWidth fmt
  omega

/-- Every descriptor needs at least one limb; backend eligibility is not required. -/
theorem limbCount_pos (fmt : FloatFormat) : 0 < limbCount fmt := by
  unfold limbCount
  have := three_le_bitWidth fmt
  omega

/-- The encoded width fits the limbs as a power of two. -/
theorem two_pow_bitWidth_le (fmt : FloatFormat) :
    2 ^ fmt.bitWidth ≤ LimbArray.radix ^ limbCount fmt := by
  rw [LimbArray.radix_pow]
  exact Nat.pow_le_pow_right (by decide) (bitWidth_le_limbBits fmt)

/-- The fraction offset lies strictly below the top limb boundary. -/
theorem fracWidth_div_lt (fmt : FloatFormat) : fmt.fracWidth / 32 + 1 ≤ limbCount fmt := by
  have hw := bitWidth_le_limbBits fmt
  unfold FloatFormat.bitWidth at hw
  omega

/-- The sign offset lies strictly below the top limb boundary. -/
theorem signIndex_div_lt (fmt : FloatFormat) :
    (fmt.expWidth + fmt.fracWidth) / 32 + 1 ≤ limbCount fmt := by
  have hw := bitWidth_le_limbBits fmt
  unfold FloatFormat.bitWidth at hw
  omega

/-- The bit width is the sign bit plus the exponent and fraction widths. -/
theorem bitWidth_eq (fmt : FloatFormat) : fmt.bitWidth = fmt.expWidth + fmt.fracWidth + 1 := by
  unfold FloatFormat.bitWidth
  omega

/-! ## The storage invariant -/

/-- The spare-bit test decides whether the value lies below `2 ^ bitWidth`. -/
theorem topLimbFits_iff (v : LimbArray) (hsize : v.size = limbCount fmt) :
    topLimbFits fmt v = true ↔ v.toNat < 2 ^ fmt.bitWidth := by
  set L := limbCount fmt with hL
  set k := fmt.bitWidth - 32 * (L - 1) with hk
  have hLpos : 0 < L := limbCount_pos fmt
  have hkpos : 1 ≤ k := by
    have := limbBits_lt_bitWidth fmt
    omega
  have hkle : k ≤ 32 := by
    have := bitWidth_le_limbBits fmt
    omega
  have hshift : (v.limb (L - 1)).toUInt64 >>> UInt64.ofNat k =
      UInt64.ofNat ((v.limb (L - 1)).toNat / 2 ^ k) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      UInt32.toNat_toUInt64, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (by omega : k < 64), Nat.shiftRight_eq_div_pow]
    symm
    apply Nat.mod_eq_of_lt
    have := LimbArray.limb_toNat_lt v (L - 1)
    have hdiv := Nat.div_le_self (v.limb (L - 1)).toNat (2 ^ k)
    unfold LimbArray.radix at this
    omega
  unfold topLimbFits
  rw [← hL, ← hk, hshift, beq_iff_eq]
  have hdivFits : (v.limb (L - 1)).toNat / 2 ^ k < 2 ^ 64 := by
    have := LimbArray.limb_toNat_lt v (L - 1)
    unfold LimbArray.radix at this
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    calc
      (v.limb (L - 1)).toNat / 2 ^ k ≤ (v.limb (L - 1)).toNat := Nat.div_le_self _ _
      _ < 2 ^ 64 := by omega
  have hzero : UInt64.ofNat ((v.limb (L - 1)).toNat / 2 ^ k) = 0 ↔
      (v.limb (L - 1)).toNat / 2 ^ k = 0 := by
    rw [← UInt64.toNat_inj, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hdivFits]
    rfl
  rw [hzero, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)]
  have hvalue : v.toNat = LimbArray.segment v 0 (L - 1) +
      (v.limb (L - 1)).toNat * LimbArray.radix ^ (L - 1) := by
    have hback := LimbArray.segment_succ_back v 0 (L - 1)
    rw [Nat.zero_add, show L - 1 + 1 = L by omega] at hback
    rw [← hback, LimbArray.toNat, hsize]
  have hlow := LimbArray.segment_lt v 0 (L - 1)
  have hpow : 2 ^ fmt.bitWidth = LimbArray.radix ^ (L - 1) * 2 ^ k := by
    rw [LimbArray.radix_pow, ← pow_add]
    congr 1
    omega
  rw [hvalue, hpow]
  have hRpos : 0 < LimbArray.radix ^ (L - 1) := Nat.pow_pos (by decide)
  rw [Nat.mul_comm (LimbArray.radix ^ (L - 1)), ← Nat.div_lt_iff_lt_mul hRpos,
    Nat.add_mul_div_right _ _ hRpos, Nat.div_eq_of_lt hlow, Nat.zero_add]

/-- A stored value has exactly `limbCount fmt` limbs. -/
theorem Value.size_eq (v : Value fmt) : v.1.size = limbCount fmt := v.2.1

/-- A stored value lies below `2 ^ bitWidth`. -/
theorem Value.toNat_lt (v : Value fmt) : v.1.toNat < 2 ^ fmt.bitWidth :=
  (topLimbFits_iff v.1 v.2.1).mp v.2.2

/-- A well-sized array below `2 ^ bitWidth` is stored unchanged. -/
theorem ofLimbs_val (w : LimbArray) (hsize : w.size = limbCount fmt)
    (hlt : w.toNat < 2 ^ fmt.bitWidth) :
    (ofLimbs fmt w).1 = w := by
  unfold ofLimbs
  rw [dite_eq_left ⟨hsize, (topLimbFits_iff w hsize).mpr hlt⟩]

/-- The model of a stored value has the stored bit pattern. -/
theorem toNatBits_toModel (v : Value fmt) : (toModel v).toNatBits = v.1.toNat :=
  Model.toNatBits_ofNatBits_of_lt _ v.toNat_lt

/-! ## Codec laws -/

/-- Storing and reading back a model value is the identity. -/
theorem toModel_ofModel (x : Model fmt) : toModel (ofModel x) = x := by
  unfold toModel ofModel
  have hlt : x.toNatBits < 2 ^ fmt.bitWidth := Model.toNatBits_lt_two_pow x
  have hvalue : (LimbArray.ofNat x.toNatBits (limbCount fmt)).toNat = x.toNatBits :=
    LimbArray.toNat_ofNat_of_lt (lt_of_lt_of_le hlt (two_pow_bitWidth_le fmt))
  rw [ofLimbs_val _ (LimbArray.size_ofNat _ _) (by rw [hvalue]; exact hlt), hvalue,
    Model.ofNatBits_toNatBits]

/-- Reading a stored value and storing it again is the identity. -/
theorem ofModel_toModel (v : Value fmt) : ofModel (toModel v) = v := by
  apply Subtype.ext
  unfold ofModel
  rw [toNatBits_toModel]
  have hvalue : (LimbArray.ofNat v.1.toNat (limbCount fmt)).toNat = v.1.toNat :=
    LimbArray.toNat_ofNat_of_lt (lt_of_lt_of_le v.toNat_lt (two_pow_bitWidth_le fmt))
  rw [ofLimbs_val _ (LimbArray.size_ofNat _ _) (by rw [hvalue]; exact v.toNat_lt)]
  have h := LimbArray.ofNat_toNat v.1
  rwa [v.size_eq] at h

/-- Two stored values with the same model are equal. -/
theorem toModel_injective {v w : Value fmt} (h : toModel v = toModel w) : v = w := by
  rw [← ofModel_toModel v, ← ofModel_toModel w, h]

/-! ## Field access -/

/-- The stored sign bit is the model sign. -/
theorem signBit_eq (v : Value fmt) : signBit v = Model.signBit (toModel v) := by
  rw [Model.signBit_eq_signBitImpl_apply, Model.signBitImpl, toNatBits_toModel, signBit,
    LimbArray.testBit_eq]

/-- The exponent mask has `expWidth` low bits set, for exponent widths of at most 32. -/
theorem expMask32_toNat (h : fmt.expWidth ≤ 32) : (expMask32 fmt).toNat = 2 ^ fmt.expWidth - 1 := by
  unfold expMask32
  by_cases hlt : fmt.expWidth < 32
  · rw [ite_eq_left hlt, LimbArray.lowMask32_toNat _ hlt]
  · rw [ite_eq_right hlt]
    have : fmt.expWidth = 32 := by omega
    rw [this]
    decide

/-- The all-ones exponent word is the descriptor's all-ones exponent. -/
theorem expAllOnes_toNat (h : fmt.expWidth ≤ 32) : (expAllOnes fmt).toNat = fmt.expAllOnesNat := by
  unfold expAllOnes FloatFormat.expAllOnesNat
  exact expMask32_toNat h

/-- A nonzero, finite exponent word gives a normal exponent field. -/
theorem normalExponent_of_expWord (h : Eligible fmt) (v : Value fmt) (hzero : expWord v ≠ 0)
    (hfinite : expWord v ≠ expAllOnes fmt) :
    expField v ≠ 0 ∧ expField v ≠ fmt.expAllOnesNat := by
  constructor
  · intro hc
    apply hzero
    apply UInt32.toNat_inj.mp
    simpa [expField] using hc
  · intro hc
    apply hfinite
    apply UInt32.toNat_inj.mp
    rw [expAllOnes_toNat h.exp_le]
    exact hc

/-- The stored exponent field is the model exponent field. -/
theorem expField_eq (v : Value fmt) (h : fmt.expWidth ≤ 32) :
    expField v = Model.expField (toModel v) := by
  rw [Model.expField_eq_expFieldImpl_apply, Model.expFieldImpl, toNatBits_toModel, expField, expWord,
    UInt32.toNat_and, LimbArray.bitsAt32_toNat, expMask32_toNat h, FloatFormat.expAllOnesNat,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, LimbArray.radix_eq,
    Nat.shiftRight_eq_div_pow]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)

/-- The stored exponent word denotes the exponent field. -/
theorem expWord_toNat (v : Value fmt) (h : fmt.expWidth ≤ 32) :
    (expWord v).toNat = Model.expField (toModel v) :=
  expField_eq v h

/-- The exponent field is below `2 ^ expWidth`. -/
theorem expField_lt (v : Value fmt) (h : fmt.expWidth ≤ 32) :
    expField v < 2 ^ fmt.expWidth := by
  rw [expField_eq v h]
  exact Model.expField_lt_pow2 _

/-- The fraction limbs denote the model fraction field. -/
theorem fraction_toNat (v : Value fmt) : (fraction v).toNat = Model.fracField (toModel v) := by
  rw [Model.fracField_eq_fracFieldImpl_apply, Model.fracFieldImpl, toNatBits_toModel, fraction,
    LimbArray.toNat_lowBits, FloatFormat.fracMaskNat, Nat.and_two_pow_sub_one_eq_mod]

/-- The fraction of a stored value has the format's limb count. -/
@[simp] theorem size_fraction (v : Value fmt) : (fraction v).size = limbCount fmt := by
  rw [fraction, LimbArray.size_lowBits, v.size_eq]

/-- The fraction limbs lie below `2 ^ fracWidth`. -/
theorem fraction_toNat_lt (v : Value fmt) : (fraction v).toNat < 2 ^ fmt.fracWidth := by
  rw [fraction_toNat]
  exact Model.fracField_lt_pow2 _

/-- The normal significand is the fraction with the implicit bit. -/
theorem normalMantissa_toNat (v : Value fmt) :
    (normalMantissa v).toNat = 2 ^ fmt.fracWidth + Model.fracField (toModel v) := by
  unfold normalMantissa
  have hfrac := fraction_toNat_lt v
  have hw := bitWidth_le_limbBits fmt
  have hbits := bitWidth_eq fmt
  rw [LimbArray.toNat_addAt _ _ _ (by rw [size_fraction]; exact fracWidth_div_lt fmt),
    fraction_toNat, UInt32.toNat_one, Nat.one_mul, Nat.add_comm]
  rw [size_fraction, fraction_toNat, UInt32.toNat_one, Nat.one_mul]
  calc
    Model.fracField (toModel v) + 2 ^ fmt.fracWidth < 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by
      rw [← fraction_toNat]
      omega
    _ = 2 ^ (fmt.fracWidth + 1) := by ring
    _ ≤ 2 ^ fmt.bitWidth := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ LimbArray.radix ^ limbCount fmt := two_pow_bitWidth_le fmt

/-- The normal significand, fraction plus implicit bit, has the format's limb count. -/
@[simp] theorem size_normalMantissa (v : Value fmt) :
    (normalMantissa v).size = limbCount fmt := by
  rw [normalMantissa, LimbArray.size_addAt, size_fraction]

/-- The normal significand occupies exactly `fracWidth + 1` bits. -/
theorem normalMantissa_bounds (v : Value fmt) :
    2 ^ fmt.fracWidth ≤ (normalMantissa v).toNat ∧
      (normalMantissa v).toNat < 2 ^ (fmt.fracWidth + 1) := by
  rw [normalMantissa_toNat]
  have := Model.fracField_lt_pow2 (toModel v)
  constructor
  · omega
  · rw [pow_succ]
    omega

/-! ## Finite decoding -/

/-- For a conventional IEEE descriptor, finiteness is the exponent field being below all ones. -/
theorem isFinite_toModel (v : Value fmt) (hieee : fmt.isIEEE = true) (h : fmt.expWidth ≤ 32) :
    Model.isFinite (toModel v) = (expField v != fmt.expAllOnesNat) := by
  have hencoding : fmt.encoding = .ieee := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hieee).1
  rw [Model.isFinite, hencoding, Model.IEEE.isFinite, expField_eq v h]

/--
The compact finite decoder of a stored value with a finite exponent field reads its sign, exponent,
and significand from the limbs.
-/
theorem decode?_toModel (v : Value fmt) (hieee : fmt.isIEEE = true) (h : fmt.expWidth ≤ 32)
    (hfinite : expField v ≠ fmt.expAllOnesNat) :
    FiniteKernel.decode? (toModel v) =
      some ⟨signBit v, expField v,
        FiniteKernel.decodeMantissa fmt (expField v) (fraction v).toNat⟩ := by
  unfold FiniteKernel.decode?
  rw [isFinite_toModel v hieee h, ite_eq_right (by simpa using hfinite), signBit_eq,
    expField_eq v h,
    fraction_toNat]

/-- The decoded significand of a normal stored value is its limb significand. -/
theorem decodeMantissa_eq_normalMantissa (v : Value fmt) (hnormal : expField v ≠ 0) :
    FiniteKernel.decodeMantissa fmt (expField v) (fraction v).toNat = (normalMantissa v).toNat := by
  unfold FiniteKernel.decodeMantissa
  rw [ite_eq_right (by simpa using hnormal), normalMantissa_toNat, fraction_toNat, pow2_eq_two_pow]

/-! ## Packing -/

/-- The exponent word masked to the exponent field. -/
theorem expWord_and_mask_toNat (exponent : UInt32) (h : fmt.expWidth ≤ 32) :
    (exponent &&& expMask32 fmt).toNat = exponent.toNat % 2 ^ fmt.expWidth := by
  rw [UInt32.toNat_and, expMask32_toNat h, Nat.and_two_pow_sub_one_eq_mod]

/-- The limbs produced by `pack`, before the storage wrapper. -/
theorem pack_limbs_toNat (sign : Bool) (exponent : UInt32) (fraction : LimbArray)
    (h : fmt.expWidth ≤ 32) :
    let base := (fraction.lowBits fmt.fracWidth).resize (limbCount fmt)
    let withExponent := base.addAt fmt.fracWidth (exponent &&& expMask32 fmt)
    let limbs := if sign then withExponent.addAt (fmt.expWidth + fmt.fracWidth) 1 else withExponent
    limbs.toNat = fraction.toNat % 2 ^ fmt.fracWidth +
        exponent.toNat % 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth +
        (if sign then 2 ^ (fmt.expWidth + fmt.fracWidth) else 0) ∧
      limbs.size = limbCount fmt ∧ limbs.toNat < 2 ^ fmt.bitWidth := by
  intro base withExponent limbs
  have hbits := bitWidth_eq fmt
  have hradix := two_pow_bitWidth_le fmt
  have hfrac : fraction.toNat % 2 ^ fmt.fracWidth < 2 ^ fmt.fracWidth :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hexp : exponent.toNat % 2 ^ fmt.expWidth < 2 ^ fmt.expWidth :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hexpPow : exponent.toNat % 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth ≤
      2 ^ (fmt.expWidth + fmt.fracWidth) := by
    rw [pow_add]
    have := Nat.mul_le_mul_right (2 ^ fmt.fracWidth) (Nat.succ_le_of_lt hexp)
    rw [Nat.succ_mul] at this
    exact this
  have hsumLt : fraction.toNat % 2 ^ fmt.fracWidth +
      exponent.toNat % 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth +
      (if sign then 2 ^ (fmt.expWidth + fmt.fracWidth) else 0) < 2 ^ fmt.bitWidth := by
    rw [hbits, pow_succ]
    split <;> omega
  have hbase : base.toNat = fraction.toNat % 2 ^ fmt.fracWidth := by
    rw [LimbArray.toNat_resize, LimbArray.toNat_lowBits]
    apply Nat.mod_eq_of_lt
    calc
      fraction.toNat % 2 ^ fmt.fracWidth < 2 ^ fmt.fracWidth := hfrac
      _ ≤ 2 ^ fmt.bitWidth := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ LimbArray.radix ^ limbCount fmt := hradix
  have hbaseSize : base.size = limbCount fmt := LimbArray.size_resize _ _
  have hwithExponent : withExponent.toNat = fraction.toNat % 2 ^ fmt.fracWidth +
      exponent.toNat % 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth := by
    rw [LimbArray.toNat_addAt _ _ _ (by rw [hbaseSize]; exact fracWidth_div_lt fmt), hbase,
      expWord_and_mask_toNat _ h]
    rw [hbaseSize, hbase, expWord_and_mask_toNat _ h]
    have : fraction.toNat % 2 ^ fmt.fracWidth + exponent.toNat % 2 ^ fmt.expWidth *
        2 ^ fmt.fracWidth < 2 ^ fmt.bitWidth := by
      have hs := hsumLt
      split at hs <;> omega
    exact lt_of_lt_of_le this hradix
  have hwithExponentSize : withExponent.size = limbCount fmt := by
    rw [LimbArray.size_addAt, hbaseSize]
  refine ⟨?_, ?_, ?_⟩
  · unfold limbs
    cases sign
    · simp [hwithExponent]
    · simp only [ite_true]
      rw [LimbArray.toNat_addAt _ _ _ (by rw [hwithExponentSize]; exact signIndex_div_lt fmt),
        hwithExponent, UInt32.toNat_one, Nat.one_mul]
      rw [hwithExponentSize, hwithExponent, UInt32.toNat_one, Nat.one_mul]
      have hs := hsumLt
      simp only [ite_true] at hs
      exact lt_of_lt_of_le hs hradix
  · unfold limbs
    split
    · rw [LimbArray.size_addAt, hwithExponentSize]
    · exact hwithExponentSize
  · unfold limbs
    cases sign
    · simp only [Bool.false_eq_true, ite_false]
      rw [hwithExponent]
      have hs := hsumLt
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hs
      exact hs
    · simp only [ite_true]
      rw [LimbArray.toNat_addAt _ _ _ (by rw [hwithExponentSize]; exact signIndex_div_lt fmt),
        hwithExponent, UInt32.toNat_one, Nat.one_mul]
      · have hs := hsumLt
        simp only [ite_true] at hs
        exact hs
      · rw [hwithExponentSize, hwithExponent, UInt32.toNat_one, Nat.one_mul]
        have hs := hsumLt
        simp only [ite_true] at hs
        exact lt_of_lt_of_le hs hradix

/-- `pack` produces exactly the model field constructor on the masked fields. -/
theorem toModel_pack (sign : Bool) (exponent : UInt32) (fraction : LimbArray)
    (h : fmt.expWidth ≤ 32) :
    toModel (pack fmt sign exponent fraction) =
      Model.ofFields fmt sign (exponent.toNat % 2 ^ fmt.expWidth)
        (fraction.toNat % 2 ^ fmt.fracWidth) := by
  obtain ⟨hvalue, hsize, hlt⟩ := pack_limbs_toNat (fmt := fmt) sign exponent fraction h
  unfold pack toModel
  rw [ofLimbs_val _ hsize hlt, hvalue]
  rw [Model.ofFields_eq_ofFieldsImpl]
  unfold Model.ofFieldsImpl Model.mkBitsImpl Model.ofNatBits
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNatLT, FloatFormat.ofWordNat, BitVec.toNat_ofNat]
  have hfrac : fraction.toNat % 2 ^ fmt.fracWidth < 2 ^ fmt.fracWidth :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hexp : exponent.toNat % 2 ^ fmt.expWidth < 2 ^ fmt.expWidth :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hexpMask : exponent.toNat % 2 ^ fmt.expWidth &&& FloatFormat.expAllOnesNat fmt =
      exponent.toNat % 2 ^ fmt.expWidth := by
    unfold FloatFormat.expAllOnesNat
    exact Nat.and_two_pow_sub_one_of_lt_two_pow hexp
  have hfracMask : fraction.toNat % 2 ^ fmt.fracWidth &&& FloatFormat.fracMaskNat fmt =
      fraction.toNat % 2 ^ fmt.fracWidth := by
    unfold FloatFormat.fracMaskNat
    exact Nat.and_two_pow_sub_one_of_lt_two_pow hfrac
  have hmiddle : (exponent.toNat % 2 ^ fmt.expWidth) <<< fmt.fracWidth |||
      fraction.toNat % 2 ^ fmt.fracWidth =
        exponent.toNat % 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth +
          fraction.toNat % 2 ^ fmt.fracWidth := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hfrac, Nat.shiftLeft_eq]
  have hmiddleLt : exponent.toNat % 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth +
      fraction.toNat % 2 ^ fmt.fracWidth < 2 ^ (fmt.expWidth + fmt.fracWidth) := by
    rw [pow_add]
    have := Nat.mul_le_mul_right (2 ^ fmt.fracWidth) (Nat.succ_le_of_lt hexp)
    rw [Nat.succ_mul] at this
    omega
  rw [hexpMask, hfracMask]
  simp only [Nat.shiftLeft_eq']
  rw [Nat.or_assoc, hmiddle]
  have hsum : (if sign = true then 1 <<< (fmt.expWidth + fmt.fracWidth) else 0) |||
      (exponent.toNat % 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth + fraction.toNat % 2 ^ fmt.fracWidth) =
        fraction.toNat % 2 ^ fmt.fracWidth + exponent.toNat % 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth +
          (if sign = true then 2 ^ (fmt.expWidth + fmt.fracWidth) else 0) := by
    cases sign
    · simp only [Bool.false_eq_true, ite_false, Nat.zero_or, Nat.add_zero]
      ring
    · simp only [ite_true, Nat.shiftLeft_eq, Nat.one_mul]
      have hor := Nat.two_pow_add_eq_or_of_lt hmiddleLt 1
      rw [Nat.mul_one] at hor
      rw [← hor]
      ring
  rw [hsum]
  apply Nat.mod_eq_of_lt
  rw [hvalue] at hlt
  exact hlt

/-- `pack` on in-range fields produces exactly the model field constructor. -/
theorem toModel_pack_of_lt (sign : Bool) (exponent : UInt32) (fraction : LimbArray)
    (h : fmt.expWidth ≤ 32) (hexp : exponent.toNat < 2 ^ fmt.expWidth)
    (hfrac : fraction.toNat < 2 ^ fmt.fracWidth) :
    toModel (pack fmt sign exponent fraction) =
      Model.ofFields fmt sign exponent.toNat fraction.toNat := by
  rw [toModel_pack sign exponent fraction h, Nat.mod_eq_of_lt hexp, Nat.mod_eq_of_lt hfrac]

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
