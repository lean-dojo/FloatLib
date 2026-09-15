/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Decode.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.GuardSticky.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Shared.GuardSticky.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Proof
public import FloatLib.Kernels.FixedWord.DyadicCompare.Proof
public import FloatLib.Kernels.FixedWord.LimbRound.Proof

/-!
# Correctness of direct two-limb guard-and-sticky rounding

`candidateCarrierLawful` proves that the `UInt128` candidate carrier satisfies the shared carrier
laws at capacity 128. The shared theorems then give the packing and rounding refinement; the
remaining proofs connect the two-limb entry points, which add the zero test, the exact
minimum-positive comparison, and exact-width sign restoration, to the arbitrary-width direct
rounder.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbRounding.GuardSticky

open FloatLib.Numerics

private theorem pred_mul_mod
    (modulus factor : Nat) (hmodulus : 0 < modulus)
    (hfactor : 0 < factor) :
    (modulus * factor - 1) % modulus = modulus - 1 := by
  have hfactorDecompose : factor - 1 + 1 = factor :=
    Nat.sub_add_cancel hfactor
  have hproductDecompose :
      modulus * factor - 1 =
        modulus * (factor - 1) + (modulus - 1) := by
    calc
      modulus * factor - 1 =
          modulus * (factor - 1 + 1) - 1 := by rw [hfactorDecompose]
      _ = (modulus * (factor - 1) + modulus) - 1 := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = modulus * (factor - 1) + (modulus - 1) :=
        Nat.add_sub_assoc hmodulus _
  rw [hproductDecompose, Nat.add_comm, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (Nat.sub_lt hmodulus (by decide))

/--
Natural-number laws of the two-limb candidate carrier at capacity 128.

Bit and suffix reads are exact at every width. The arithmetic laws hold under the bounds the
shared rounder establishes: shifts stay below 128 positions, sums and successors fit two limbs,
and masks are narrower than two limbs.
-/
theorem candidateCarrierLawful :
    GuardStickyCarrier.LawfulCandidateCarrier candidateCarrier FixedWord.UInt128.toNat 128 where
  bitAt_eq_testBit := NativeLimb.bitAt_eq_testBit
  hasLowBits_eq value width := by
    dsimp only [candidateCarrier, hasLowBits]
    by_cases hremainder : value.toNat % 2 ^ width = 0
    · have hzeroNat :
          (NativeLimb.lowBits value width).toNat = 0 := by
        rw [NativeLimb.lowBits_toNat]
        exact hremainder
      have hzero :
          NativeLimb.isZero (NativeLimb.lowBits value width) = true :=
        (NativeLimb.isZero_eq_true_iff _).2 hzeroNat
      simp [hzero, hremainder]
    · have hnonzeroNat :
          (NativeLimb.lowBits value width).toNat ≠ 0 := by
        rw [NativeLimb.lowBits_toNat]
        exact hremainder
      have hnotZero :
          NativeLimb.isZero (NativeLimb.lowBits value width) ≠ true := by
        intro hzero
        exact hnonzeroNat ((NativeLimb.isZero_eq_true_iff _).1 hzero)
      have hzeroFalse :
          NativeLimb.isZero (NativeLimb.lowBits value width) = false :=
        Bool.eq_false_of_not_eq_true hnotZero
      simp [hzeroFalse, hremainder]
  toNat_lt := FixedWord.UInt128.toNat_lt
  toNat_ofWord word := by
    show (FixedWord.UInt128.mk 0 word).toNat = word.toNat
    simp only [FixedWord.UInt128.toNat, UInt64.toNat_zero, zero_mul, add_zero]
  shiftLeft_toNat value shift hshift hfit := by
    show (shiftLeft value shift).toNat = value.toNat <<< shift
    unfold shiftLeft
    rw [ite_eq_left hshift]
    exact FixedWord.UInt128.shiftLeft_toNat value shift hshift hfit
  shiftRight_toNat value shift _ := by
    show (FixedWord.UInt128.shiftRight value shift).toNat = value.toNat >>> shift
    rw [FixedWord.UInt128.shiftRight_toNat, Nat.shiftRight_eq_div_pow]
  fractionBelow_toNat value leading _ hlower hupper := by
    show (NativeLimb.lowBits value leading).toNat = value.toNat - 2 ^ leading
    rw [NativeLimb.lowBits_toNat, Nat.mod_eq_sub_mod hlower, Nat.mod_eq_of_lt]
    have hpower : 2 ^ (leading + 1) = 2 ^ leading * 2 := by
      rw [pow_succ]
    omega
  add_toNat left right hfit := FixedWord.add128_value_toNat_of_lt left right hfit
  lowOnes_toNat width hwidth := by
    show (NativeLimb.lowBits ⟨0xffffffffffffffff, 0xffffffffffffffff⟩ width).toNat =
      2 ^ width - 1
    have hmax :
        (FixedWord.UInt128.mk 0xffffffffffffffff 0xffffffffffffffff).toNat = 2 ^ 128 - 1 :=
      rfl
    have hpow : 2 ^ 128 = 2 ^ width * 2 ^ (128 - width) := by
      rw [← pow_add, Nat.add_sub_of_le hwidth.le]
    rw [NativeLimb.lowBits_toNat, hmax, hpow]
    exact pred_mul_mod (2 ^ width) (2 ^ (128 - width))
      (Nat.two_pow_pos width) (Nat.two_pow_pos (128 - width))
  increment_toNat := FixedWord.UInt128.increment_toNat
  isOdd_eq := FixedWord.UInt128.lowBitIsNonzero_eq_odd
  log2_eq := FixedWord.UInt128.log2_toNat

/-- Under two-limb eligibility the payload is shorter than the carrier. -/
theorem payloadBits_lt_of_eligible
    (format : Format) (heligible : NativeLimb.Eligible format) :
    format.payloadBits < 128 := by
  unfold NativeLimb.Eligible Format.payloadBits at *
  omega

/-- The fixed-pair minimum-positive comparison is the exact dyadic comparison. -/
theorem isLessMinPositive_eq
    (format : Format)
    (significand : FloatLib.Numerics.FixedWord.UInt128)
    (exponent : Int) :
    isLessMinPositive format significand exponent =
      ({ negative := false
         significand := significand.toNat
         exponent } : FloatLib.Numerics.Dyadic).isLess
        (DyadicRounding.minPositive format) := by
  rw [DyadicRounding.minPositive_eq_fields]
  unfold isLessMinPositive
  dsimp only
  rw [FixedWord.DyadicCompare.compareNonnegative128ToWord_eq]
  simp only [UInt64.toNat_one]
  change
    Dyadic.isLessNonnegativeFields significand.toNat exponent
        1 (-(4 * Int.ofNat (format.payloadBits - 1))) =
      Dyadic.isLess
        { negative := false
          significand := significand.toNat
          exponent }
        { negative := false
          significand := 1
          exponent := -(4 * Int.ofNat (format.payloadBits - 1)) }
  rw [Dyadic.isLessNonnegativeFields_eq]
  rw [Dyadic.isLessFields_eq]

/-! ## Complete carrier refinement -/

/--
The positive two-limb kernel is the shared arbitrary-width direct rounder.

Keeping this theorem beside the kernel avoids routing the Word/Limb interoperability proof through
the complete capacity-dispatch implementation.
-/
theorem roundPositiveCodeWord_toNat_eq_direct
    (format : Format) (heligible : NativeLimb.Eligible format)
    (significand : FloatLib.Numerics.FixedWord.UInt128)
    (exponent : Int) :
    (roundPositiveCodeWord format significand exponent).toNat =
      DirectDyadicPacking.roundPositiveCode format
        { negative := false
          significand := significand.toNat
          exponent } := by
  by_cases hzero : NativeLimb.isZero significand
  · have hzeroNat : significand.toNat = 0 :=
      (NativeLimb.isZero_eq_true_iff significand).1 hzero
    unfold roundPositiveCodeWord
    rw [ite_eq_left hzero]
    simp [DirectDyadicPacking.roundPositiveCode, hzeroNat]
    rfl
  · have hnonzero : significand.toNat ≠ 0 := by
      intro equality
      exact hzero ((NativeLimb.isZero_eq_true_iff significand).2 equality)
    unfold roundPositiveCodeWord
    rw [ite_eq_right hzero]
    by_cases hunderflow :
        isLessMinPositive format significand exponent = true
    · rw [ite_eq_left hunderflow]
      rw [isLessMinPositive_eq] at hunderflow
      rw [DirectDyadicPacking.roundPositiveCode_eq_dyadic]
      unfold DyadicRounding.roundPositiveCode
      have hspecial :
          ¬(significand.toNat == 0 || false) = true := by
        simp [hnonzero]
      rw [ite_eq_right hspecial, ite_eq_left hunderflow]
      simp only [FloatLib.Numerics.FixedWord.UInt128.toNat,
        UInt64.toNat_zero, UInt64.toNat_one, zero_mul, add_zero]
    · rw [ite_eq_right hunderflow]
      apply GuardStickyCarrier.roundNormalizedPositive_toNat_eq_direct candidateCarrierLawful
        format significand exponent (payloadBits_lt_of_eligible format heligible) hnonzero
      rw [← isLessMinPositive_eq]
      exact Bool.eq_false_of_not_eq_true hunderflow

private theorem roundPositiveCodeWord_lt_signMask_direct
    (format : Format) (heligible : NativeLimb.Eligible format)
    (significand : FloatLib.Numerics.FixedWord.UInt128)
    (exponent : Int) :
    (roundPositiveCodeWord format significand exponent).toNat <
      format.signMaskNat := by
  rw [roundPositiveCodeWord_toNat_eq_direct format heligible]
  exact DirectDyadicPacking.roundPositiveCode_lt_signMask format _

/--
Two-limb sign restoration is exact-width Posit sign restoration.

The positive code must lie below the sign mask; zero is unchanged under either sign.
-/
theorem restoreSignWord_toNat
    (format : Format) (heligible : NativeLimb.Eligible format)
    (negative : Bool)
    (positiveCode : FloatLib.Numerics.FixedWord.UInt128)
    (hpositive : positiveCode.toNat < format.signMaskNat) :
    (restoreSignWord format negative positiveCode).toNat =
      DyadicRounding.restoreSignCode
        format negative positiveCode.toNat := by
  cases negative with
  | false => rfl
  | true =>
      unfold restoreSignWord
      simp only [ite_true]
      by_cases hzero : NativeLimb.isZero positiveCode
      · have hzeroNat : positiveCode.toNat = 0 :=
          (NativeLimb.isZero_eq_true_iff positiveCode).1 hzero
        simp [hzero, hzeroNat, DyadicRounding.restoreSignCode]
        rfl
      · have hnonzero : positiveCode.toNat ≠ 0 := by
          intro equality
          exact hzero ((NativeLimb.isZero_eq_true_iff positiveCode).2 equality)
        rw [ite_eq_right hzero]
        rw [NativeLimb.lowBits_complement_increment_toNat
          format positiveCode heligible
          (hpositive.trans format.signMaskNat_lt_modulus) hnonzero]
        simp [DyadicRounding.restoreSignCode, hnonzero]

/-- Signed two-limb carrier rounding has the shared arbitrary-width direct semantics. -/
theorem roundCodeWord_toNat_eq_direct
    (format : Format) (heligible : NativeLimb.Eligible format)
    (negative : Bool)
    (significand : FloatLib.Numerics.FixedWord.UInt128)
    (exponent : Int) :
    (roundCodeWord format negative significand exponent).toNat =
      DirectDyadicPacking.roundCode format
        { negative
          significand := significand.toNat
          exponent } := by
  unfold roundCodeWord
  rw [restoreSignWord_toNat format heligible negative
    (roundPositiveCodeWord format significand exponent)
    (roundPositiveCodeWord_lt_signMask_direct
      format heligible significand exponent)]
  rw [roundPositiveCodeWord_toNat_eq_direct format heligible]
  unfold DirectDyadicPacking.roundCode
  by_cases hzero : significand.toNat = 0
  · simp [hzero, DirectDyadicPacking.roundPositiveCode,
      DyadicRounding.restoreSignCode]
  · simp [hzero, DyadicRounding.magnitude]

end FloatLib.Floats.Formats.Posit.Model.NativeLimbRounding.GuardSticky
