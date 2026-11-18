/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Adjacent.Proof.Encoding

/-!
# Discrete ranks of adjacent binary values

`adjacencyRank` orders positive words by their encoding and reverses negative words. Both signed
zeros have the same rank. Each nonsaturating ordinary `nextUp` or `nextDown` step changes this
rank by one.
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

/--
Away from NaNs and a saturating positive endpoint, `nextUp` advances by one adjacency rank.

The infinity premise excludes positive infinity while permitting negative infinity, whose next
value is finite. The final premise matters only for formats that do not represent infinity.
-/
theorem adjacencyRank_nextUp
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false)
    (hinfinity :
      isInfinite x = true → signBit x = true)
    (hmax :
      fmt.supportsInfinity = false → x ≠ posMaxFinite fmt) :
    adjacencyRank (nextUp x) = adjacencyRank x + 1 := by
  have hpositiveInfinity :
      (isInfinite x && !signBit x) = false := by
    cases hinf : isInfinite x
    · simp
    · have hsign := hinfinity hinf
      simp [hsign]
  have hupperEndpoint := endpointTest_eq_false hmax
  cases hzero : isZero x
  · cases hfnuz :
        (!fmt.supportsSignedZero &&
          (x.bits == (negMinSubnormal fmt).bits))
    · cases hsign : signBit x
      · have hinfFalse : isInfinite x = false := by
          cases hinf : isInfinite x
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
      simp only [adjacencyRank, nextUp, Internal.Value.nextUp, isNaN_negMinSubnormal,
        Bool.false_eq_true, ↓reduceIte, isInfinite_negMinSubnormal, signBit_negMinSubnormal,
        Bool.not_true, Bool.and_self, isZero_negMinSubnormal, hsignedZero, Bool.not_false,
        BEq.rfl, signBit_posZero, toNatBits_posZero, add_zero, toNatBits_negMinSubnormal]
      have hwidth :=
        two_mul_signMaskNat_eq_two_pow_bitWidth fmt
      have hsignPositive : 0 < fmt.signMaskNat := by
        unfold FloatFormat.signMaskNat
        positivity
      omega
  · simp [nextUp, Internal.Value.nextUp, hnan, hpositiveInfinity, hzero,
      adjacencyRank_eq_signMaskNat_of_isZero]

/--
Away from NaNs and a saturating negative endpoint, `nextDown` retreats by one adjacency rank.

The infinity premise excludes negative infinity while permitting positive infinity, whose previous
value is finite. The final premise matters only for formats that do not represent infinity.
-/
theorem adjacencyRank_nextDown
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false)
    (hinfinity :
      isInfinite x = true → signBit x = false)
    (hmin :
      fmt.supportsInfinity = false → x ≠ negMaxFinite fmt) :
    adjacencyRank (nextDown x) + 1 = adjacencyRank x := by
  have hnegativeInfinity :
      (isInfinite x && signBit x) = false := by
    cases hinf : isInfinite x
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
    · have hinfFalse : isInfinite x = false := by
        cases hinf : isInfinite x
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
  · simp only [nextDown, Internal.Value.nextDown, hnan, Bool.false_eq_true, ↓reduceIte,
    hnegativeInfinity, hzero, adjacencyRank_negMinSubnormal,
    adjacencyRank_eq_signMaskNat_of_isZero]
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

/-- The adjacency rank is the sign-bit place value shifted by the signed magnitude. -/
theorem adjacencyRank_eq_signedMagnitude {fmt : FloatFormat} (x : Model fmt) :
    (adjacencyRank x : Int) = fmt.signMaskNat + signedMagnitude x := by
  have h := toNatBits_eq_magnitude x
  have hm := magnitude_lt x
  have hw := two_mul_signMaskNat_eq_two_pow_bitWidth fmt
  unfold adjacencyRank signedMagnitude
  cases hs : signBit x <;> simp only [hs, ite_true, ite_false, Bool.false_eq_true] at h ⊢ <;>
    omega

end Model
end FloatLib.Floats.Formats.BinaryInterchange
