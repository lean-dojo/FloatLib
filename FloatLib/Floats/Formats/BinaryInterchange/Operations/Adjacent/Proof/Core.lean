/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core

/-!
# Rank semantics of adjacent-value operations

Numerical ranks specify `nextUp` and `nextDown` for every binary format descriptor. The central
device is `adjacencyRank`: it reverses the raw encoding order for negative values, preserves it
for positive values, and assigns both signed-zero words one rank. The unsigned-zero policy has
one reserved NaN word at the sign boundary; `nextUp` skips that word explicitly.

The public contracts show that each ordinary step changes the rank by exactly one, so no
representable numerical rank lies between the input and output. Exceptional values, saturating
endpoints, and non-strict rank inequalities are stated separately in `Adjacent.Proof.Boundaries`.

No theorem depends on a named format or fixed field width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Discrete rank used to state adjacency of representable numerical values.

The two signed-zero encodings have the same rank. NaN words are intentionally not assigned
numerical semantics; public stepping theorems therefore state their NaN preconditions explicitly.
-/
def adjacencyRank {fmt : FloatFormat} (x : Model fmt) : Nat :=
  if signBit x then
    2 ^ fmt.bitWidth - x.toNatBits
  else
    fmt.signMaskNat + x.toNatBits

private theorem bitWidth_pos (fmt : FloatFormat) :
    0 < fmt.bitWidth := by
  unfold FloatFormat.bitWidth
  omega

private theorem toNatBits_ofBits_add_one
    {fmt : FloatFormat} (x : Model fmt)
    (hfit : x.toNatBits + 1 < 2 ^ fmt.bitWidth) :
    toNatBits (ofBits (x.bits + 1)) = x.toNatBits + 1 := by
  unfold toNatBits ofBits
  rw [BitVec.toNat_add]
  have hone : ((1 : BitVec fmt.bitWidth).toNat) = 1 :=
    BitVec.toNat_one (bitWidth_pos fmt)
  rw [hone]
  exact Nat.mod_eq_of_lt hfit

private theorem toNatBits_ofBits_sub_one
    {fmt : FloatFormat} (x : Model fmt)
    (hpos : 0 < x.toNatBits) :
    toNatBits (ofBits (x.bits - 1)) = x.toNatBits - 1 := by
  unfold toNatBits ofBits
  rw [BitVec.toNat_sub]
  have hone : ((1 : BitVec fmt.bitWidth).toNat) = 1 :=
    BitVec.toNat_one (bitWidth_pos fmt)
  rw [hone]
  have hfit := toNatBits_lt_two_pow x
  change 0 < x.bits.toNat at hpos
  change x.bits.toNat < 2 ^ fmt.bitWidth at hfit
  have hpowPos : 0 < 2 ^ fmt.bitWidth := Nat.two_pow_pos _
  have hrearrange :
      2 ^ fmt.bitWidth - 1 + x.bits.toNat =
        (x.bits.toNat - 1) + 2 ^ fmt.bitWidth := by
    omega
  rw [hrearrange, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

private theorem two_mul_signMaskNat_eq_two_pow_bitWidth
    (fmt : FloatFormat) :
    2 * fmt.signMaskNat = 2 ^ fmt.bitWidth := by
  unfold FloatFormat.signMaskNat FloatFormat.signBitIndex
    FloatFormat.bitWidth
  rw [show 1 + fmt.expWidth + fmt.fracWidth - 1 =
      fmt.expWidth + fmt.fracWidth by omega]
  rw [show 1 + fmt.expWidth + fmt.fracWidth =
      (fmt.expWidth + fmt.fracWidth) + 1 by omega]
  simp [pow_succ, Nat.mul_comm]

private theorem signMaskNat_lt_two_pow_bitWidth (fmt : FloatFormat) :
    fmt.signMaskNat < 2 ^ fmt.bitWidth := by
  have hsignPos : 0 < fmt.signMaskNat := by
    unfold FloatFormat.signMaskNat
    positivity
  have hwidth := two_mul_signMaskNat_eq_two_pow_bitWidth fmt
  omega

@[simp] private theorem toNatBits_posZero (fmt : FloatFormat) :
    (posZero fmt).toNatBits = 0 := by
  simp [posZero, toNatBits, ofNatBits, ofBits,
    FloatFormat.ofWordNat]

@[simp] private theorem toNatBits_posMinSubnormal (fmt : FloatFormat) :
    (posMinSubnormal fmt).toNatBits = 1 := by
  apply toNatBits_ofNatBits_of_lt
  have hwidth : 0 < fmt.bitWidth := bitWidth_pos fmt
  exact Nat.one_lt_two_pow (Nat.ne_of_gt hwidth)

@[simp] private theorem toNatBits_negZero (fmt : FloatFormat) :
    (negZero fmt).toNatBits = fmt.signMaskNat := by
  unfold negZero toNatBits ofBits
  rw [FloatFormat.signMask_toNat]
  rfl

@[simp] private theorem toNatBits_negMinSubnormal (fmt : FloatFormat) :
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

@[simp] private theorem adjacencyRank_posZero (fmt : FloatFormat) :
    adjacencyRank (posZero fmt) = fmt.signMaskNat := by
  simp [adjacencyRank]

@[simp] private theorem adjacencyRank_negZero (fmt : FloatFormat) :
    adjacencyRank (negZero fmt) = fmt.signMaskNat := by
  simp only [adjacencyRank, signBit_negZero, ite_true,
    toNatBits_negZero]
  have hwidth := two_mul_signMaskNat_eq_two_pow_bitWidth fmt
  omega

@[simp] private theorem adjacencyRank_posMinSubnormal (fmt : FloatFormat) :
    adjacencyRank (posMinSubnormal fmt) = fmt.signMaskNat + 1 := by
  simp [adjacencyRank]

@[simp] private theorem adjacencyRank_negMinSubnormal (fmt : FloatFormat) :
    adjacencyRank (negMinSubnormal fmt) = fmt.signMaskNat - 1 := by
  simp only [adjacencyRank, signBit_negMinSubnormal, ite_true,
    toNatBits_negMinSubnormal]
  have hwidth := two_mul_signMaskNat_eq_two_pow_bitWidth fmt
  have hsignPos : 0 < fmt.signMaskNat := by
    unfold FloatFormat.signMaskNat
    positivity
  omega

private theorem adjacencyRank_eq_signMaskNat_of_isZero
    {fmt : FloatFormat} (x : Model fmt)
    (hzero : isZero x = true) :
    adjacencyRank x = fmt.signMaskNat := by
  cases hencoding : fmt.encoding with
  | finiteUnsignedZero =>
      have hbits : x.bits = 0 := by
        simpa [isZero, hencoding] using hzero
      have hvalue : x = posZero fmt := by
        cases x
        simp_all [posZero, ofNatBits, ofBits,
          FloatFormat.ofWordNat]
      subst x
      exact adjacencyRank_posZero fmt
  | ieee | finiteMaxNaN | finite =>
      have hparts :
          expField x = 0 ∧ fracField x = 0 := by
        have hbool :
            (expField x == 0) = true ∧ (fracField x == 0) = true := by
          simpa [isZero, hencoding, IEEE.isZero,
            Bool.and_eq_true] using hzero
        exact ⟨beq_iff_eq.mp hbool.1, beq_iff_eq.mp hbool.2⟩
      have hreconstruct := ofFields_signBit_expField_fracField x
      cases hsign : signBit x
      · have hvalue : x = posZero fmt := by
          rw [hparts.1, hparts.2, hsign] at hreconstruct
          simpa using hreconstruct.symm
        subst x
        exact adjacencyRank_posZero fmt
      · have hvalue : x = negZero fmt := by
          rw [hparts.1, hparts.2, hsign] at hreconstruct
          simpa using hreconstruct.symm
        subst x
        exact adjacencyRank_negZero fmt

private theorem shiftLeft_or_lowMask (a k : Nat) :
    a.shiftLeft k ||| (2 ^ k - 1) =
      a.shiftLeft k + (2 ^ k - 1) := by
  change (a <<< k) ||| (2 ^ k - 1) =
    (a <<< k) + (2 ^ k - 1)
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show k + 1 = Nat.succ k by rfl]
      rw [Nat.shiftLeft_succ]
      have hmask :
          2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
        rw [pow_succ]
        have hpow : 0 < 2 ^ k := Nat.two_pow_pos _
        omega
      rw [hmask]
      change Nat.bit false (a <<< k) |||
          Nat.bit true (2 ^ k - 1) =
        Nat.bit false (a <<< k) + Nat.bit true (2 ^ k - 1)
      rw [Nat.lor_bit, ih]
      simp only [Bool.false_or, Nat.bit_false, Nat.bit_true]
      omega

private theorem shiftLeft_eq_mul_pow (a k : Nat) :
    a.shiftLeft k = a * 2 ^ k := by
  change (a <<< k) = a * 2 ^ k
  exact Nat.shiftLeft_eq a k

private theorem upperPositiveCode_eq_ofFields_allOnes
    (fmt : FloatFormat) :
    ofNatBits (fmt.signMaskNat - 1) =
      ofFields fmt false fmt.expAllOnesNat fmt.fracMaskNat := by
  unfold ofNatBits ofFields
  apply congrArg ofBits
  rw [mkBits_eq_mkBitsImpl_apply]
  apply BitVec.eq_of_toNat_eq
  unfold mkBitsImpl FloatFormat.signMaskNat FloatFormat.signBitIndex
    FloatFormat.expAllOnesNat FloatFormat.fracMaskNat
    FloatFormat.ofWordNat FloatFormat.bitWidth
  simp only [BitVec.ofNatLT_eq_ofNat, BitVec.toNat_ofNat,
    Bool.false_eq_true, ite_false, Nat.zero_or]
  simp only [Nat.and_self]
  rw [Nat.mod_eq_of_lt]
  · rw [shiftLeft_or_lowMask (2 ^ fmt.expWidth - 1) fmt.fracWidth]
    rw [show 1 + fmt.expWidth + fmt.fracWidth - 1 =
        fmt.expWidth + fmt.fracWidth by omega]
    rw [shiftLeft_eq_mul_pow, pow_add, Nat.sub_mul]
    simp only [one_mul]
    have hexponent : 0 < 2 ^ fmt.expWidth := Nat.two_pow_pos _
    have hfraction : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
    have hfractionPred :
        2 ^ fmt.fracWidth - 1 + 1 = 2 ^ fmt.fracWidth :=
      Nat.sub_add_cancel hfraction
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
  rw [mkBits_eq_mkBitsImpl_apply]
  apply BitVec.eq_of_toNat_eq
  unfold mkBitsImpl FloatFormat.expAllOnesNat FloatFormat.fracMaskNat
    FloatFormat.ofWordNat FloatFormat.bitWidth
  simp only [BitVec.ofNatLT_eq_ofNat, BitVec.toNat_ofNat,
    ite_true, Nat.and_self]
  rw [Nat.or_assoc]
  rw [shiftLeft_or_lowMask (2 ^ fmt.expWidth - 1) fmt.fracWidth]
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
  | finiteUnsignedZero =>
      right
      constructor
      · simp [FloatFormat.supportsInfinity, hencoding]
      · simp [posMaxFinite, maxFinite, FloatFormat.maxFiniteExpField,
        FloatFormat.maxFiniteFracField, FloatFormat.Encoding.maxFiniteExponent,
        FloatFormat.expAllOnesNat, hencoding]
  | finite =>
      right
      constructor
      · simp [FloatFormat.supportsInfinity, hencoding]
      · simp [posMaxFinite, maxFinite, FloatFormat.maxFiniteExpField,
        FloatFormat.maxFiniteFracField, FloatFormat.Encoding.maxFiniteExponent,
        FloatFormat.expAllOnesNat, hencoding]

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
  | finiteUnsignedZero =>
      right
      constructor
      · simp [FloatFormat.supportsInfinity, hencoding]
      · simp [negMaxFinite, maxFinite,
          FloatFormat.maxFiniteExpField,
          FloatFormat.maxFiniteFracField,
          FloatFormat.Encoding.maxFiniteExponent,
          FloatFormat.expAllOnesNat, hencoding]
  | finite =>
      right
      constructor
      · simp [FloatFormat.supportsInfinity, hencoding]
      · simp [negMaxFinite, maxFinite,
          FloatFormat.maxFiniteExpField,
          FloatFormat.maxFiniteFracField,
          FloatFormat.Encoding.maxFiniteExponent,
          FloatFormat.expAllOnesNat, hencoding]

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

private theorem toNatBits_pos_of_isZero_eq_false
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

private theorem signMaskNat_lt_toNatBits_of_nonzero_nonNaN
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

private theorem toNatBits_add_one_lt_signMaskNat
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

private theorem toNatBits_add_one_lt_two_pow_of_negative
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

private theorem adjacencyRank_ofBits_add_one
    {fmt : FloatFormat} (x : Model fmt)
    (hraw : x.toNatBits + 1 < fmt.signMaskNat) :
    adjacencyRank (ofBits (x.bits + 1)) = adjacencyRank x + 1 := by
  have hsign : signBit x = false :=
    (signBit_eq_false_iff_toNatBits_lt_signMaskNat x).2 (by omega)
  have hfit : x.toNatBits + 1 < 2 ^ fmt.bitWidth :=
    hraw.trans (signMaskNat_lt_two_pow_bitWidth fmt)
  have hnat := toNatBits_ofBits_add_one x hfit
  have hsignNext :
      signBit (ofBits (x.bits + 1)) = false := by
    apply (signBit_eq_false_iff_toNatBits_lt_signMaskNat _).2
    rw [hnat]
    exact hraw
  simp only [adjacencyRank, hsign, hsignNext, Bool.false_eq_true, ite_false]
  rw [hnat]
  omega

private theorem adjacencyRank_ofBits_sub_one
    {fmt : FloatFormat} (x : Model fmt)
    (hraw : fmt.signMaskNat < x.toNatBits) :
    adjacencyRank (ofBits (x.bits - 1)) = adjacencyRank x + 1 := by
  have hsign : signBit x = true :=
    (signBit_eq_true_iff_signMaskNat_le x).2 hraw.le
  have hpos : 0 < x.toNatBits := by
    have hsignPos : 0 < fmt.signMaskNat := by
      unfold FloatFormat.signMaskNat
      positivity
    omega
  have hnat := toNatBits_ofBits_sub_one x hpos
  have hsignNext :
      signBit (ofBits (x.bits - 1)) = true := by
    apply (signBit_eq_true_iff_signMaskNat_le _).2
    rw [hnat]
    omega
  simp only [adjacencyRank, hsign, hsignNext, ite_true]
  rw [hnat]
  have hfit := toNatBits_lt_two_pow x
  omega

private theorem adjacencyRank_ofBits_sub_one_of_positive
    {fmt : FloatFormat} (x : Model fmt)
    (hpositive : 0 < x.toNatBits)
    (hsign : signBit x = false) :
    adjacencyRank (ofBits (x.bits - 1)) + 1 =
      adjacencyRank x := by
  have hnat := toNatBits_ofBits_sub_one x hpositive
  have hsignNext :
      signBit (ofBits (x.bits - 1)) = false := by
    apply (signBit_eq_false_iff_toNatBits_lt_signMaskNat _).2
    rw [hnat]
    have hlt :=
      (signBit_eq_false_iff_toNatBits_lt_signMaskNat x).1 hsign
    omega
  simp only [adjacencyRank, hsign, hsignNext,
    Bool.false_eq_true, ite_false]
  rw [hnat]
  omega

private theorem adjacencyRank_ofBits_add_one_of_negative
    {fmt : FloatFormat} (x : Model fmt)
    (hnegative : fmt.signMaskNat ≤ x.toNatBits)
    (hfit : x.toNatBits + 1 < 2 ^ fmt.bitWidth) :
    adjacencyRank (ofBits (x.bits + 1)) + 1 =
      adjacencyRank x := by
  have hsign : signBit x = true :=
    (signBit_eq_true_iff_signMaskNat_le x).2 hnegative
  have hnat := toNatBits_ofBits_add_one x hfit
  have hsignNext :
      signBit (ofBits (x.bits + 1)) = true := by
    apply (signBit_eq_true_iff_signMaskNat_le _).2
    rw [hnat]
    omega
  simp only [adjacencyRank, hsign, hsignNext, ite_true]
  rw [hnat]
  omega

private theorem eq_of_bits_eq
    {fmt : FloatFormat} {x y : Model fmt}
    (hbits : x.bits = y.bits) :
    x = y := by
  cases x
  cases y
  simp_all

/-! ## Exact rank steps -/

/--
Away from NaNs and a saturating positive endpoint, `nextUp` advances exactly one adjacency rank.

The infinity premise excludes positive infinity while permitting negative infinity, whose next
value is finite. The final premise matters only for formats that do not represent infinity.
-/
theorem adjacencyRank_nextUp
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false)
    (hinfinity :
      isInf x = true → signBit x = true)
    (hmax :
      fmt.supportsInfinity = false → x ≠ posMaxFinite fmt) :
    adjacencyRank (nextUp x) = adjacencyRank x + 1 := by
  have hpositiveInfinity :
      (isInf x && !signBit x) = false := by
    cases hinf : isInf x
    · simp
    · have hsign := hinfinity hinf
      simp [hsign]
  have hupperEndpoint :
      (!fmt.supportsInfinity &&
          (x.bits == (posMaxFinite fmt).bits)) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hendpoint
    have hparts :
        !fmt.supportsInfinity = true ∧
          (x.bits == (posMaxFinite fmt).bits) = true := by
      simpa [Bool.and_eq_true] using hendpoint
    have hnoInfinity : fmt.supportsInfinity = false := by
      simpa using hparts.1
    have hvalue : x = posMaxFinite fmt :=
      eq_of_bits_eq (beq_iff_eq.mp hparts.2)
    exact hmax hnoInfinity hvalue
  cases hzero : isZero x
  · cases hfnuz :
        (!fmt.supportsSignedZero &&
          (x.bits == (negMinSubnormal fmt).bits))
    · cases hsign : signBit x
      · have hinfFalse : isInf x = false := by
          cases hinf : isInf x
          · rfl
          · have hsignTrue := hinfinity hinf
            simp [hsign] at hsignTrue
        have hraw :=
          toNatBits_add_one_lt_signMaskNat x hsign hnan hmax
        simpa [nextUp, hnan, hinfFalse, hzero,
          hfnuz, hupperEndpoint, hsign] using
          adjacencyRank_ofBits_add_one x hraw
      · have hraw :=
          signMaskNat_lt_toNatBits_of_nonzero_nonNaN
            x hsign hzero hnan
        simpa [nextUp, hnan, hpositiveInfinity, hzero,
          hfnuz, hupperEndpoint, hsign] using
          adjacencyRank_ofBits_sub_one x hraw
    · have hparts :
          !fmt.supportsSignedZero = true ∧
            (x.bits == (negMinSubnormal fmt).bits) = true := by
        simpa [Bool.and_eq_true] using hfnuz
      have hvalue : x = negMinSubnormal fmt :=
        eq_of_bits_eq (beq_iff_eq.mp hparts.2)
      have hsignedZero : fmt.supportsSignedZero = false := by
        simpa using hparts.1
      subst x
      simp [nextUp, hsignedZero, adjacencyRank]
      have hwidth :=
        two_mul_signMaskNat_eq_two_pow_bitWidth fmt
      have hsignPositive : 0 < fmt.signMaskNat := by
        unfold FloatFormat.signMaskNat
        positivity
      omega
  · simp [nextUp, hnan, hpositiveInfinity, hzero,
      adjacencyRank_eq_signMaskNat_of_isZero]

/--
Away from NaNs and a saturating negative endpoint, `nextDown` retreats exactly one adjacency rank.

The infinity premise excludes negative infinity while permitting positive infinity, whose previous
value is finite. The final premise matters only for formats that do not represent infinity.
-/
theorem adjacencyRank_nextDown
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false)
    (hinfinity :
      isInf x = true → signBit x = false)
    (hmin :
      fmt.supportsInfinity = false → x ≠ negMaxFinite fmt) :
    adjacencyRank (nextDown x) + 1 = adjacencyRank x := by
  have hnegativeInfinity :
      (isInf x && signBit x) = false := by
    cases hinf : isInf x
    · simp
    · have hsign := hinfinity hinf
      simp [hsign]
  have hlowerEndpoint :
      (!fmt.supportsInfinity &&
          (x.bits == (negMaxFinite fmt).bits)) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hendpoint
    have hparts :
        !fmt.supportsInfinity = true ∧
          (x.bits == (negMaxFinite fmt).bits) = true := by
      simpa [Bool.and_eq_true] using hendpoint
    have hnoInfinity : fmt.supportsInfinity = false := by
      simpa using hparts.1
    have hvalue : x = negMaxFinite fmt :=
      eq_of_bits_eq (beq_iff_eq.mp hparts.2)
    exact hmin hnoInfinity hvalue
  cases hzero : isZero x
  · cases hsign : signBit x
    · have hpositive := toNatBits_pos_of_isZero_eq_false x hzero
      simpa [nextDown, hnan, hnegativeInfinity, hzero,
        hlowerEndpoint, hsign] using
        adjacencyRank_ofBits_sub_one_of_positive
          x hpositive hsign
    · have hinfFalse : isInf x = false := by
        cases hinf : isInf x
        · rfl
        · have hsignFalse := hinfinity hinf
          simp [hsign] at hsignFalse
      have hnegative :=
        (signBit_eq_true_iff_signMaskNat_le x).1 hsign
      have hfit :=
        toNatBits_add_one_lt_two_pow_of_negative
          x hnan hmin
      simpa [nextDown, hnan, hinfFalse, hzero,
        hlowerEndpoint, hsign] using
        adjacencyRank_ofBits_add_one_of_negative
          x hnegative hfit
  · simp [nextDown, hnan, hnegativeInfinity, hzero,
      adjacencyRank_eq_signMaskNat_of_isZero]
    have hwidth :=
      two_mul_signMaskNat_eq_two_pow_bitWidth fmt
    have hsignPositive : 0 < fmt.signMaskNat := by
      unfold FloatFormat.signMaskNat
      positivity
    omega

/-- No representable numerical rank lies strictly between `x` and its `nextUp` result. -/
theorem no_rank_between_nextUp
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false)
    (hinfinity :
      isInf x = true → signBit x = true)
    (hmax :
      fmt.supportsInfinity = false → x ≠ posMaxFinite fmt) :
    ¬ ∃ y : Model fmt,
        adjacencyRank x < adjacencyRank y ∧
          adjacencyRank y < adjacencyRank (nextUp x) := by
  rw [adjacencyRank_nextUp x hnan hinfinity hmax]
  omega

/-- No representable numerical rank lies strictly between a `nextDown` result and its input. -/
theorem no_rank_between_nextDown
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false)
    (hinfinity :
      isInf x = true → signBit x = false)
    (hmin :
      fmt.supportsInfinity = false → x ≠ negMaxFinite fmt) :
    ¬ ∃ y : Model fmt,
        adjacencyRank (nextDown x) < adjacencyRank y ∧
          adjacencyRank y < adjacencyRank x := by
  rw [← adjacencyRank_nextDown x hnan hinfinity hmin]
  omega

end Model
end FloatLib.Floats.Formats.BinaryInterchange
