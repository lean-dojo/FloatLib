/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# Rank semantics of adjacent-value operations

Numerical ranks specify `nextUp` and `nextDown` for every binary format descriptor. The central
device is `adjacencyRank`: it reverses the raw encoding order for negative values, preserves it
for positive values, and assigns both signed-zero words one rank. The unsigned-zero policy has
one reserved NaN word at the sign boundary, which `nextUp` skips.

The public contracts show that each ordinary step changes the rank by exactly one, that the rank
orders non-NaN values as their extended reals (`adjacencyRank_lt_adjacencyRank_iff`, with equal
ranks exactly for equal values, so the two zeros share one), and that a step from a number never
lands on a NaN (`isNaN_nextUp`, `isNaN_nextDown`). Exceptional values, saturating endpoints,
non-strict rank inequalities, and the absence of a represented value between the input and output
are in `Adjacent.Proof.Boundaries`.

No theorem depends on a named format or fixed field width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Discrete rank used to state adjacency of representable numerical values.

The two signed-zero encodings have the same rank. On non-NaN words the rank orders the
extended-real values (`adjacencyRank_lt_adjacencyRank_iff`). NaN words are not given numerical
meaning, so the stepping theorems state their NaN preconditions.
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

/-- A zero word has zero exponent and fraction fields, in every encoding. -/
private theorem fields_eq_zero_of_isZero {fmt : FloatFormat} {x : Model fmt}
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

private theorem adjacencyRank_eq_signMaskNat_of_isZero
    {fmt : FloatFormat} (x : Model fmt)
    (hzero : isZero x = true) :
    adjacencyRank x = fmt.signMaskNat := by
  obtain ⟨hexponent, hfraction⟩ := fields_eq_zero_of_isZero hzero
  have hreconstruct := ofFields_signBit_expField_fracField x
  rw [hexponent, hfraction] at hreconstruct
  cases hsign : signBit x
  · have hvalue : x = posZero fmt := by
      rw [hsign] at hreconstruct
      simpa using hreconstruct.symm
    subst x
    exact adjacencyRank_posZero fmt
  · have hvalue : x = negZero fmt := by
      rw [hsign] at hreconstruct
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
  rw [mkBits_eq_internal_apply]
  apply BitVec.eq_of_toNat_eq
  unfold Internal.mkBits FloatFormat.signMaskNat FloatFormat.signBitIndex
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
  rw [mkBits_eq_internal_apply]
  apply BitVec.eq_of_toNat_eq
  unfold Internal.mkBits FloatFormat.expAllOnesNat FloatFormat.fracMaskNat
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

/-- A value other than an endpoint `y` fails the saturating-endpoint test against `y`. -/
private theorem endpointTest_eq_false {fmt : FloatFormat} {x y : Model fmt}
    (h : fmt.supportsInfinity = false → x ≠ y) :
    (!fmt.supportsInfinity && (x.bits == y.bits)) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hendpoint
  have hparts : !fmt.supportsInfinity = true ∧ (x.bits == y.bits) = true := by
    simpa [Bool.and_eq_true] using hendpoint
  exact h (by simpa using hparts.1) (eq_of_bits_eq (beq_iff_eq.mp hparts.2))

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
  have hupperEndpoint := endpointTest_eq_false hmax
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
        simpa [nextUp, Internal.Value.nextUp, hnan, hinfFalse, hzero,
          hfnuz, hupperEndpoint, hsign] using
          adjacencyRank_ofBits_add_one x hraw
      · have hraw :=
          signMaskNat_lt_toNatBits_of_nonzero_nonNaN
            x hsign hzero hnan
        simpa [nextUp, Internal.Value.nextUp, hnan, hpositiveInfinity, hzero,
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
      simp [nextUp, Internal.Value.nextUp, hsignedZero, adjacencyRank]
      have hwidth :=
        two_mul_signMaskNat_eq_two_pow_bitWidth fmt
      have hsignPositive : 0 < fmt.signMaskNat := by
        unfold FloatFormat.signMaskNat
        positivity
      omega
  · simp [nextUp, Internal.Value.nextUp, hnan, hpositiveInfinity, hzero,
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
  have hlowerEndpoint := endpointTest_eq_false hmin
  cases hzero : isZero x
  · cases hsign : signBit x
    · have hpositive := toNatBits_pos_of_isZero_eq_false x hzero
      simpa [nextDown, Internal.Value.nextDown, hnan, hnegativeInfinity, hzero,
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
      simpa [nextDown, Internal.Value.nextDown, hnan, hinfFalse, hzero,
        hlowerEndpoint, hsign] using
        adjacencyRank_ofBits_add_one_of_negative
          x hnegative hfit
  · simp [nextDown, Internal.Value.nextDown, hnan, hnegativeInfinity, hzero,
      adjacencyRank_eq_signMaskNat_of_isZero]
    have hwidth :=
      two_mul_signMaskNat_eq_two_pow_bitWidth fmt
    have hsignPositive : 0 < fmt.signMaskNat := by
      unfold FloatFormat.signMaskNat
      positivity
    omega

/-! ## Rank and numerical order

A storage word is its sign-bit place value, when the sign is set, plus its magnitude: the exponent
and fraction fields read as one number. The rank adds the magnitude to the sign-bit place value
for a clear sign and subtracts it for a set sign. A finite word denotes its grid index, negated for
a set sign, times the least subnormal spacing, and the grid index increases strictly with the
magnitude, so the rank orders finite values numerically. An infinity has the largest magnitude
among the numbers of its sign, and both zero words have magnitude zero, so they share one rank.
-/

/-- The storage word without its sign bit: the biased exponent and fraction fields together. -/
private def magnitudeBits {fmt : FloatFormat} (x : Model fmt) : Nat :=
  expField x * 2 ^ fmt.fracWidth + fracField x

private theorem signMaskNat_eq_mul (fmt : FloatFormat) :
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
  ring

private theorem magnitude_lt {fmt : FloatFormat} (x : Model fmt) :
    magnitudeBits x < fmt.signMaskNat := by
  rw [magnitude_eq_mod]
  apply Nat.mod_lt
  unfold FloatFormat.signMaskNat
  positivity

/-- A storage word is its sign-bit place value, when the sign is set, plus its magnitude. -/
private theorem toNatBits_eq_magnitude {fmt : FloatFormat} (x : Model fmt) :
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
private theorem signBit_magnitude_of_toNatBits_lt {fmt : FloatFormat} (x : Model fmt)
    (hx : x.toNatBits < fmt.signMaskNat) :
    signBit x = false ∧ magnitudeBits x = x.toNatBits := by
  have hs := (signBit_eq_false_iff_toNatBits_lt_signMaskNat x).2 hx
  have h := toNatBits_eq_magnitude x
  simp only [hs, Bool.false_eq_true, ite_false, Nat.zero_add] at h
  exact ⟨hs, h.symm⟩

/-- A word at or above the sign-bit place value has a set sign and the rest as its magnitude. -/
private theorem signBit_magnitude_of_signMaskNat_le {fmt : FloatFormat} (x : Model fmt)
    (hx : fmt.signMaskNat ≤ x.toNatBits) :
    signBit x = true ∧ magnitudeBits x = x.toNatBits - fmt.signMaskNat := by
  have hs := (signBit_eq_true_iff_signMaskNat_le x).2 hx
  have h := toNatBits_eq_magnitude x
  simp only [hs, ite_true] at h
  exact ⟨hs, by omega⟩

/-- Two words with the same sign bit and magnitude are equal. -/
private theorem eq_of_signBit_eq_of_magnitude_eq {fmt : FloatFormat} {x y : Model fmt}
    (hs : signBit x = signBit y) (hm : magnitudeBits x = magnitudeBits y) : x = y := by
  have hn : x.toNatBits = y.toNatBits := by
    rw [toNatBits_eq_magnitude x, toNatBits_eq_magnitude y, hs, hm]
  rw [← ofNatBits_toNatBits x, hn, ofNatBits_toNatBits]

/-- A biased exponent field below `c` is a magnitude below `c` fraction-field periods. -/
private theorem expField_lt_iff {fmt : FloatFormat} (x : Model fmt) (c : Nat) :
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

private theorem fields_eq_zero_of_magnitude_eq_zero {fmt : FloatFormat} {x : Model fmt}
    (hm : magnitudeBits x = 0) : expField x = 0 ∧ fracField x = 0 := by
  have he := (expField_lt_iff x 1).2 (by rw [hm]; simp)
  refine ⟨by omega, ?_⟩
  unfold magnitudeBits at hm
  omega

private theorem magnitude_eq_zero_of_isZero {fmt : FloatFormat} {x : Model fmt}
    (hx : isZero x = true) : magnitudeBits x = 0 := by
  obtain ⟨hexponent, hfraction⟩ := fields_eq_zero_of_isZero hx
  simp [magnitudeBits, hexponent, hfraction]

/-- A number whose magnitude is zero is a zero; the sign-mask word of FNUZ is its NaN. -/
private theorem isZero_of_magnitude_eq_zero {fmt : FloatFormat} {x : Model fmt}
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
private def signedMagnitude {fmt : FloatFormat} (x : Model fmt) : Int :=
  if signBit x then -(magnitudeBits x : Int) else magnitudeBits x

/-- The adjacency rank is the sign-bit place value shifted by the signed magnitude. -/
private theorem adjacencyRank_eq_signedMagnitude {fmt : FloatFormat} (x : Model fmt) :
    (adjacencyRank x : Int) = fmt.signMaskNat + signedMagnitude x := by
  have h := toNatBits_eq_magnitude x
  have hm := magnitude_lt x
  have hw := two_mul_signMaskNat_eq_two_pow_bitWidth fmt
  unfold adjacencyRank signedMagnitude
  cases hs : signBit x <;> simp only [hs, ite_true, ite_false, Bool.false_eq_true] at h ⊢ <;>
    omega

/--
Multiple of the least subnormal spacing denoted by a positive word with biased exponent `e` and
fraction `f`.
-/
private def gridIndex (fmt : FloatFormat) (e f : Nat) : Nat :=
  if e = 0 then f else (2 ^ fmt.fracWidth + f) * 2 ^ (e - 1)

/-- The grid index index increases strictly with the field pair read as one number. -/
private theorem gridIndex_lt_gridIndex (fmt : FloatFormat) {e f e' f' : Nat}
    (hf : f < 2 ^ fmt.fracWidth) (hf' : f' < 2 ^ fmt.fracWidth)
    (h : e * 2 ^ fmt.fracWidth + f < e' * 2 ^ fmt.fracWidth + f') :
    gridIndex fmt e f < gridIndex fmt e' f' := by
  have hP : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  have hle : e ≤ e' := by
    by_contra hlt
    have : (e' + 1) * 2 ^ fmt.fracWidth ≤ e * 2 ^ fmt.fracWidth :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  rcases hle.lt_or_eq with hlt | heq
  · have hbelow : gridIndex fmt e f < 2 ^ fmt.fracWidth * 2 ^ e := by
      unfold gridIndex
      split_ifs with he
      · subst he
        simpa using hf
      · calc (2 ^ fmt.fracWidth + f) * 2 ^ (e - 1)
            < (2 * 2 ^ fmt.fracWidth) * 2 ^ (e - 1) :=
              Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
          _ = 2 ^ fmt.fracWidth * 2 ^ e := by
            rw [show e = (e - 1) + 1 by omega, pow_succ]
            simp only [Nat.add_sub_cancel]
            ring
    have habove : 2 ^ fmt.fracWidth * 2 ^ e ≤ gridIndex fmt e' f' := by
      have he' : e' ≠ 0 := by omega
      simp only [gridIndex, he', ite_false]
      calc 2 ^ fmt.fracWidth * 2 ^ e ≤ 2 ^ fmt.fracWidth * 2 ^ (e' - 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
        _ ≤ (2 ^ fmt.fracWidth + f') * 2 ^ (e' - 1) :=
            Nat.mul_le_mul_right _ (by omega)
    omega
  · subst heq
    unfold gridIndex
    split_ifs
    · omega
    · exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)

/-- Grid index of a word, read from its stored fields. -/
private def wordGridIndex {fmt : FloatFormat} (x : Model fmt) : Nat :=
  gridIndex fmt (expField x) (fracField x)

private theorem wordGridIndex_lt_wordGridIndex {fmt : FloatFormat} {x y : Model fmt}
    (h : magnitudeBits x < magnitudeBits y) : wordGridIndex x < wordGridIndex y :=
  gridIndex_lt_gridIndex fmt (fracField_lt_pow2 x) (fracField_lt_pow2 y) h

private theorem wordGridIndex_eq_zero_iff {fmt : FloatFormat} (x : Model fmt) :
    wordGridIndex x = 0 ↔ magnitudeBits x = 0 := by
  constructor
  · intro h
    by_contra hm
    have hzero : magnitudeBits (posZero fmt) = 0 := by simp [magnitudeBits]
    have hlt := wordGridIndex_lt_wordGridIndex (x := posZero fmt) (y := x) (by omega)
    have h0 : wordGridIndex (posZero fmt) = 0 := by simp [wordGridIndex, gridIndex]
    omega
  · intro h
    obtain ⟨he, hf⟩ := fields_eq_zero_of_magnitude_eq_zero h
    simp [wordGridIndex, gridIndex, he, hf]

/-- Signed grid index index: the grid index index, negated when the sign bit is set. -/
private def signedGridIndex {fmt : FloatFormat} (x : Model fmt) : Int :=
  if signBit x then -(wordGridIndex x : Int) else wordGridIndex x

/-- Signed grid index indices are ordered as signed keys. -/
private theorem signedGridIndex_lt_signedGridIndex {fmt : FloatFormat} {x y : Model fmt}
    (h : signedMagnitude x < signedMagnitude y) : signedGridIndex x < signedGridIndex y := by
  have hzx := wordGridIndex_eq_zero_iff x
  have hzy := wordGridIndex_eq_zero_iff y
  unfold signedMagnitude at h
  unfold signedGridIndex
  cases hsx : signBit x <;> cases hsy : signBit y <;>
    simp only [hsx, hsy, ite_true, ite_false, Bool.false_eq_true] at h ⊢
  · have := wordGridIndex_lt_wordGridIndex (x := x) (y := y) (by omega)
    omega
  · omega
  · omega
  · have := wordGridIndex_lt_wordGridIndex (x := y) (y := x) (by omega)
    omega

/-- A finite word denotes its signed grid index index times the least subnormal spacing. -/
private theorem toReal_eq_signedGridIndex {fmt : FloatFormat} {x : Model fmt}
    (hx : isFinite x = true) :
    toReal x = (signedGridIndex x : ℝ) * (2 : ℝ) ^ fmt.minSubnormalExponent := by
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hx
  have hsign := sign_eq_signBit_of_toDyadic?_some hd
  rw [toReal_eq, hd]
  simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand, hsign, signedGridIndex,
    wordGridIndex]
  rcases toDyadic?_some_cases hd with ⟨hs, -⟩ | ⟨he, _, hs, hexp⟩ | ⟨he, hs, hexp⟩
  · have hz := fields_eq_zero_of_magnitude_eq_zero <| magnitude_eq_zero_of_isZero
      (isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hd hs)
    cases signBit x <;> simp [hs, hz.1, hz.2, gridIndex]
  · cases signBit x <;> simp [hs, hexp, he, gridIndex]
  · rw [hs, hexp]
    simp only [gridIndex, he, ite_false, pow2_eq_two_pow]
    have hexpEq : (Int.ofNat (expField x) - Int.ofNat fmt.exponentBias -
        Int.ofNat fmt.fracWidth) = ((expField x - 1 : Nat) : Int) + fmt.minSubnormalExponent := by
      unfold FloatFormat.minSubnormalExponent FloatFormat.minNormalExponent
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hexpEq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
    cases signBit x <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> push_cast <;> ring

/-- Only an IEEE encoding has infinities, which have the all-ones exponent and zero fraction. -/
private theorem encoding_eq_ieee_and_magnitude_of_isInf {fmt : FloatFormat} {x : Model fmt}
    (hx : isInf x = true) :
    fmt.encoding = .ieee ∧ magnitudeBits x = fmt.expAllOnesNat * 2 ^ fmt.fracWidth := by
  cases hencoding : fmt.encoding with
  | ieee =>
      have hfields : expField x = fmt.expAllOnesNat ∧ fracField x = 0 := by
        simpa [isInf, hencoding, IEEE.isInf, Bool.and_eq_true] using hx
      exact ⟨rfl, by simp [magnitudeBits, hfields.1, hfields.2]⟩
  | finiteMaxNaN | finiteUnsignedZero | finite =>
      simp [isInf, hencoding] at hx

/-- A finite IEEE word has a magnitude below that of the infinities. -/
private theorem magnitude_lt_of_isFinite {fmt : FloatFormat} {x : Model fmt}
    (hencoding : fmt.encoding = .ieee) (hx : isFinite x = true) :
    magnitudeBits x < fmt.expAllOnesNat * 2 ^ fmt.fracWidth := by
  have hne : expField x ≠ fmt.expAllOnesNat := by
    simpa [isFinite, hencoding, IEEE.isFinite] using hx
  have hlt := expField_lt_pow2 x
  exact (expField_lt_iff x _).1 (by unfold FloatFormat.expAllOnesNat at hne ⊢; omega)

/-- A number in an IEEE encoding has magnitude at most that of the infinities. -/
private theorem magnitude_le_of_isNaN_eq_false {fmt : FloatFormat} {x : Model fmt}
    (hencoding : fmt.encoding = .ieee) (hnan : isNaN x = false) :
    magnitudeBits x ≤ fmt.expAllOnesNat * 2 ^ fmt.fracWidth := by
  cases hinf : isInf x
  · exact (magnitude_lt_of_isFinite hencoding
      (isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnan hinf)).le
  · exact (encoding_eq_ieee_and_magnitude_of_isInf hinf).2.le

/-- A finite word denotes a real number in the extended reals; an infinity denotes its endpoint. -/
private theorem toEReal_of_isInf {fmt : FloatFormat} {x : Model fmt} (hx : isInf x = true) :
    toEReal x = if signBit x then ⊥ else ⊤ := by
  rw [toEReal_eq_ite, isNaN_eq_false_of_isInf_eq_true x hx]
  simp [hx]

/-- Numbers are ordered in the extended reals as their signed keys. -/
private theorem toEReal_lt_toEReal_of_signedMagnitude_lt {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = false) (hy : isNaN y = false) (h : signedMagnitude x < signedMagnitude y) :
    toEReal x < toEReal y := by
  cases hxinf : isInf x <;> cases hyinf : isInf y
  · have hxf := isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hx hxinf
    have hyf := isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hy hyinf
    rw [toEReal_eq_coe_toReal_of_isFinite x hxf, toEReal_eq_coe_toReal_of_isFinite y hyf,
      EReal.coe_lt_coe_iff, toReal_eq_signedGridIndex hxf, toReal_eq_signedGridIndex hyf]
    have hu : (0 : ℝ) < (2 : ℝ) ^ fmt.minSubnormalExponent := by positivity
    exact mul_lt_mul_of_pos_right (by exact_mod_cast signedGridIndex_lt_signedGridIndex h) hu
  · obtain ⟨henc, hmy⟩ := encoding_eq_ieee_and_magnitude_of_isInf hyinf
    have hxf := isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hx hxinf
    have hmx := magnitude_lt_of_isFinite henc hxf
    rw [toEReal_eq_coe_toReal_of_isFinite x hxf, toEReal_of_isInf hyinf]
    cases hsy : signBit y
    · simp
    · unfold signedMagnitude at h
      cases hsx : signBit x <;>
        simp only [hsx, hsy, ite_true, ite_false, Bool.false_eq_true] at h <;> omega
  · obtain ⟨henc, hmx⟩ := encoding_eq_ieee_and_magnitude_of_isInf hxinf
    have hyf := isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hy hyinf
    have hmy := magnitude_lt_of_isFinite henc hyf
    rw [toEReal_eq_coe_toReal_of_isFinite y hyf, toEReal_of_isInf hxinf]
    cases hsx : signBit x
    · unfold signedMagnitude at h
      cases hsy : signBit y <;>
        simp only [hsx, hsy, ite_true, ite_false, Bool.false_eq_true] at h <;> omega
    · simp
  · obtain ⟨-, hmx⟩ := encoding_eq_ieee_and_magnitude_of_isInf hxinf
    obtain ⟨-, hmy⟩ := encoding_eq_ieee_and_magnitude_of_isInf hyinf
    rw [toEReal_of_isInf hxinf, toEReal_of_isInf hyinf]
    unfold signedMagnitude at h
    cases hsx : signBit x <;> cases hsy : signBit y <;>
      simp only [hsx, hsy, ite_true, ite_false, Bool.false_eq_true] at h ⊢ <;>
      first | omega | exact bot_lt_top

/-- Numbers with equal signed keys denote the same extended real. -/
private theorem toEReal_eq_toEReal_of_signedMagnitude_eq {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = false) (hy : isNaN y = false) (h : signedMagnitude x = signedMagnitude y) :
    toEReal x = toEReal y := by
  unfold signedMagnitude at h
  by_cases hs : signBit x = signBit y
  · have hm : magnitudeBits x = magnitudeBits y := by
      rw [hs] at h
      cases hsy : signBit y <;> simp only [hsy, ite_true, ite_false, Bool.false_eq_true] at h <;>
        omega
    rw [eq_of_signBit_eq_of_magnitude_eq hs hm]
  · have hm : magnitudeBits x = 0 ∧ magnitudeBits y = 0 := by
      cases hsx : signBit x <;> cases hsy : signBit y <;>
        simp only [hsx, hsy, ite_true, ite_false, Bool.false_eq_true, not_true_eq_false,
          not_false_eq_true] at h hs <;> omega
    have hxz := isZero_of_magnitude_eq_zero hx hm.1
    have hyz := isZero_of_magnitude_eq_zero hy hm.2
    rw [toEReal_eq_coe_toReal_of_isFinite x (isFinite_eq_true_of_isZero_eq_true x hxz),
      toEReal_eq_coe_toReal_of_isFinite y (isFinite_eq_true_of_isZero_eq_true y hyz),
      toReal_eq_zero_of_isZero x hxz, toReal_eq_zero_of_isZero y hyz]

/--
On non-NaN values the adjacency rank is a strict order embedding of the extended-real values:
a smaller rank is a smaller number, including at both infinities and across the two zeros.
-/
theorem adjacencyRank_lt_adjacencyRank_iff {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = false) (hy : isNaN y = false) :
    adjacencyRank x < adjacencyRank y ↔ toEReal x < toEReal y := by
  have hkey : adjacencyRank x < adjacencyRank y ↔ signedMagnitude x < signedMagnitude y := by
    have := adjacencyRank_eq_signedMagnitude x
    have := adjacencyRank_eq_signedMagnitude y
    omega
  rw [hkey]
  refine ⟨toEReal_lt_toEReal_of_signedMagnitude_lt hx hy, fun hlt => ?_⟩
  rcases lt_trichotomy (signedMagnitude x) (signedMagnitude y) with hk | hk | hk
  · exact hk
  · exact absurd (toEReal_eq_toEReal_of_signedMagnitude_eq hx hy hk) hlt.ne
  · exact absurd (toEReal_lt_toEReal_of_signedMagnitude_lt hy hx hk) (not_lt.mpr hlt.le)

/--
Two non-NaN values have the same adjacency rank exactly when they denote the same extended real.
The two signed-zero words therefore share a rank, and every other number has a rank of its own.
-/
theorem adjacencyRank_eq_adjacencyRank_iff {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = false) (hy : isNaN y = false) :
    adjacencyRank x = adjacencyRank y ↔ toEReal x = toEReal y := by
  constructor
  · intro h
    apply toEReal_eq_toEReal_of_signedMagnitude_eq hx hy
    have := adjacencyRank_eq_signedMagnitude x
    have := adjacencyRank_eq_signedMagnitude y
    omega
  · intro h
    rcases lt_trichotomy (adjacencyRank x) (adjacencyRank y) with hr | hr | hr
    · exact absurd h ((adjacencyRank_lt_adjacencyRank_iff hx hy).1 hr).ne
    · exact hr
    · exact absurd h.symm ((adjacencyRank_lt_adjacencyRank_iff hy hx).1 hr).ne

/-- On non-NaN values a weakly smaller adjacency rank is a weakly smaller extended real. -/
theorem adjacencyRank_le_adjacencyRank_iff {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = false) (hy : isNaN y = false) :
    adjacencyRank x ≤ adjacencyRank y ↔ toEReal x ≤ toEReal y := by
  rw [← not_lt, ← not_lt, adjacencyRank_lt_adjacencyRank_iff hy hx]

/-! ## Steps between numbers -/

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

/-- In the IEEE encoding a word is a NaN exactly when its magnitude exceeds the infinities'. -/
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

/-- In the maximum-NaN encoding a word is a NaN exactly when it has the largest magnitude. -/
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
  have hm := magnitude_lt x
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
    (hx : isNaN x = false) (hinf : isInf x = false)
    (hm : magnitudeBits z = magnitudeBits x + 1)
    (hmax : fmt.encoding = .finiteMaxNaN → x ≠ maxFinite fmt (signBit x)) :
    isNaN z = false := by
  cases hencoding : fmt.encoding with
  | ieee =>
      have hlt := magnitude_lt_of_isFinite hencoding
        (isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hx hinf)
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

/-- `nextUp` returns a NaN exactly for a NaN input: from a number it always steps to a number. -/
@[simp] theorem isNaN_nextUp {fmt : FloatFormat} (x : Model fmt) :
    isNaN (nextUp x) = isNaN x := by
  cases hnan : isNaN x
  · show isNaN (Internal.Value.nextUp x) = false
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
      have hinfFalse : isInf x = false := by simpa [hsignFalse] using hinf
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

/-- `nextDown` returns a NaN exactly for a NaN input: from a number it always steps to a number. -/
@[simp] theorem isNaN_nextDown {fmt : FloatFormat} (x : Model fmt) :
    isNaN (nextDown x) = isNaN x := by
  cases hnan : isNaN x
  · show isNaN (Internal.Value.nextDown x) = false
    unfold Internal.Value.nextDown
    simp only [hnan, Bool.false_eq_true, ite_false]
    split_ifs with hinf hzero hmin hsign
    · exact hnan
    · exact isNaN_negMinSubnormal fmt
    · exact hnan
    · have hinfFalse : isInf x = false := by simpa [hsign] using hinf
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
