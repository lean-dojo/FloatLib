/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Decode.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.GuardSticky.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Proof

/-!
# Refinement of two-limb posit rounding

Significands that fit in 128 bits use two-limb guard/sticky rounding; larger significands use
the arbitrary-width direct rounder. Both branches agree with the shared exact-dyadic rounding
specification. The same refinement also proves that normalizing a four-limb product to a
two-limb window with a sticky bit preserves the rounded result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbRounding

open FloatLib.Numerics

/-- Capacity dispatch preserves the shared arbitrary-width direct positive rounder. -/
theorem roundPositiveCode_eq_direct
    (format : Format) (heligible : NativeLimb.Eligible format)
    (target : FloatLib.Numerics.Dyadic) :
    roundPositiveCode format heligible target =
      DirectDyadicPacking.roundPositiveCode format target := by
  unfold roundPositiveCode
  by_cases hspecial :
      target.significand == 0 || target.negative
  · rw [ite_eq_left hspecial]
    unfold DirectDyadicPacking.roundPositiveCode
    rw [ite_eq_left hspecial]
  · rw [ite_eq_right hspecial]
    by_cases hcapacity : target.significand < 2 ^ 128
    · rw [dite_eq_left hcapacity]
      have hsignificand : target.significand ≠ 0 := by
        intro hzero
        apply hspecial
        simp [hzero]
      have hnegative : target.negative = false := by
        cases hvalue : target.negative <;> simp_all
      have htarget :
          ({ negative := false
             significand := target.significand
             exponent := target.exponent } :
            FloatLib.Numerics.Dyadic) = target := by
        cases target
        simp_all
      let nativeSignificand :=
        FloatLib.Numerics.FixedWord.UInt128.ofNat
          target.significand
      have hnative :
          nativeSignificand.toNat = target.significand := by
        dsimp [nativeSignificand]
        exact FloatLib.Numerics.FixedWord.UInt128.toNat_ofNat
          target.significand hcapacity
      have hnativeNonzero : nativeSignificand.toNat ≠ 0 := by
        rw [hnative]
        exact hsignificand
      have hunderflowEq :
          GuardSticky.isLessMinPositive format
              nativeSignificand target.exponent =
            target.isLess (DyadicRounding.minPositive format) := by
        rw [GuardSticky.isLessMinPositive_eq, hnative, htarget]
      by_cases hunderflow :
          GuardSticky.isLessMinPositive format
              nativeSignificand target.exponent = true
      · rw [ite_eq_left hunderflow]
        have hunderflowTarget :
            target.isLess (DyadicRounding.minPositive format) = true := by
          rw [← hunderflowEq]
          exact hunderflow
        have hunderflowDirect :
            Dyadic.isLessPowerOfTwoAtLeading
                target.significand target.exponent
                (DirectDyadicPacking.leadingBit target.significand)
                (-(4 * Int.ofNat (format.payloadBits - 1))) = true := by
          rw [Dyadic.isLessPowerOfTwoAtLeading_eq
            target.significand target.exponent
            (DirectDyadicPacking.leadingBit target.significand)
            (-(4 * Int.ofNat (format.payloadBits - 1)))
            (DirectDyadicPacking.leadingBit_eq_log2 target.significand)]
          rw [Dyadic.isLessNonnegativeFields_eq, Dyadic.isLessFields_eq]
          simpa only [DyadicRounding.minPositive_eq_fields, htarget] using
            hunderflowTarget
        unfold DirectDyadicPacking.roundPositiveCode
        rw [ite_eq_right hspecial]
        rw [ite_eq_left hunderflowDirect]
      · rw [ite_eq_right hunderflow]
        have hnotUnderflow :
            ({ negative := false
               significand := nativeSignificand.toNat
               exponent := target.exponent } :
              FloatLib.Numerics.Dyadic).isLess
                (DyadicRounding.minPositive format) = false := by
          rw [hnative, htarget, ← hunderflowEq]
          exact Bool.eq_false_of_not_eq_true hunderflow
        have hresult :=
          GuardStickyCarrier.roundNormalizedPositive_toNat_eq_direct
            GuardSticky.candidateCarrierLawful format nativeSignificand target.exponent
            (GuardSticky.payloadBits_lt_of_eligible format heligible)
            hnativeNonzero hnotUnderflow
        rw [hnative, htarget] at hresult
        exact hresult
    · rw [dite_eq_right hcapacity]

/-- Complete two-limb rounding has the shared arbitrary-width direct semantics. -/
theorem roundCodeNat_eq_direct
    (format : Format) (heligible : NativeLimb.Eligible format)
    (value : FloatLib.Numerics.Dyadic) :
    roundCodeNat format heligible value =
      DirectDyadicPacking.roundCode format value := by
  unfold roundCodeNat DirectDyadicPacking.roundCode
  split
  · rfl
  · dsimp only
    rw [roundPositiveCode_eq_direct]

/-- Two-limb positive rounding is the shared exact-dyadic rounder. -/
theorem roundPositiveCode_eq_dyadic
    (format : Format) (heligible : NativeLimb.Eligible format)
    (target : FloatLib.Numerics.Dyadic) :
    roundPositiveCode format heligible target =
      DyadicRounding.roundPositiveCode format target := by
  rw [roundPositiveCode_eq_direct]
  exact DirectDyadicPacking.roundPositiveCode_eq_dyadic format target

/-- Positive two-limb rounding always selects a code below the sign bit. -/
theorem roundPositiveCode_lt_signMask
    (format : Format) (heligible : NativeLimb.Eligible format)
    (target : FloatLib.Numerics.Dyadic) :
    roundPositiveCode format heligible target <
      format.signMaskNat := by
  rw [roundPositiveCode_eq_direct]
  exact DirectDyadicPacking.roundPositiveCode_lt_signMask format target

/-- Packed positive rounding returns the exact-dyadic model value. -/
theorem roundPositive_eq_dyadic
    (format : Format) (heligible : NativeLimb.Eligible format)
    (target : FloatLib.Numerics.Dyadic) :
    roundPositive format heligible target =
      DyadicRounding.roundPositive format target := by
  unfold roundPositive DyadicRounding.roundPositive
  rw [roundPositiveCode_eq_dyadic]

/-- Every two-limb rounded result is a valid complete posit encoding. -/
theorem roundCodeNat_lt_modulus
    (format : Format) (heligible : NativeLimb.Eligible format)
    (value : FloatLib.Numerics.Dyadic) :
    roundCodeNat format heligible value < format.modulus := by
  unfold roundCodeNat
  split
  · exact Nat.two_pow_pos format.bits
  · dsimp only
    apply DyadicRounding.restoreSignCode_lt_modulus
    exact roundPositiveCode_lt_signMask format heligible _

/-- Re-encoding the code-only result gives the model-valued two-limb rounder. -/
theorem ofNatBits_roundCodeNat
    (format : Format) (heligible : NativeLimb.Eligible format)
    (value : FloatLib.Numerics.Dyadic) :
    Model.ofNatBits (roundCodeNat format heligible value) =
      round format heligible value := by
  unfold roundCodeNat round
  split
  · rfl
  · dsimp only
    have hpositive :=
      roundPositiveCode_lt_signMask format heligible
        (DyadicRounding.magnitude value)
    rw [DyadicRounding.ofNatBits_restoreSignCode
      format value.negative _ hpositive]
    rfl

/-- Two-limb rounding is exactly the shared exact-dyadic rounder. -/
theorem round_eq_dyadic
    (format : Format) (heligible : NativeLimb.Eligible format)
    (value : FloatLib.Numerics.Dyadic) :
    round format heligible value =
      DyadicRounding.round format value := by
  unfold round DyadicRounding.round
  simp only [roundPositive_eq_dyadic]

/-- Two-limb rounding therefore refines the exact rational Posit Standard semantics. -/
theorem round_eq_roundRat
    (format : Format) (heligible : NativeLimb.Eligible format)
    (value : FloatLib.Numerics.Dyadic) :
    round format heligible value =
      Model.roundRat format value.toRat := by
  rw [round_eq_dyadic, DyadicRounding.round_eq_roundRat]

/--
The carrier-returning positive rounder denotes the shared exact positive round code.

This theorem is the boundary used by packed arithmetic: execution retains `UInt128`, while
refinement proofs recover the same natural-number code as the general capacity-dispatched
rounder.
-/
theorem GuardSticky.roundPositiveCodeWord_toNat
    (format : Format) (heligible : NativeLimb.Eligible format)
    (significand : FloatLib.Numerics.FixedWord.UInt128)
    (exponent : Int) :
    (GuardSticky.roundPositiveCodeWord
        format significand exponent).toNat =
      roundPositiveCode format heligible
        { negative := false
          significand := significand.toNat
          exponent } := by
  have hcapacity : significand.toNat < 2 ^ 128 :=
    significand.toNat_lt
  have hroundtrip :
      FloatLib.Numerics.FixedWord.UInt128.ofNat significand.toNat =
        significand := by
    apply FloatLib.Numerics.FixedWord.UInt128.toNat_injective
    rw [FloatLib.Numerics.FixedWord.UInt128.toNat_ofNat
      significand.toNat hcapacity]
  by_cases hzero : NativeLimb.isZero significand
  · have hzeroNat : significand.toNat = 0 :=
      (NativeLimb.isZero_eq_true_iff significand).mp hzero
    have hzeroTest : (significand.toNat == 0 || false) = true := by
      simp [hzeroNat]
    calc
      (GuardSticky.roundPositiveCodeWord
          format significand exponent).toNat =
          ({ hi := 0, lo := 0 } :
            FloatLib.Numerics.FixedWord.UInt128).toNat := by
        rw [show GuardSticky.roundPositiveCodeWord
            format significand exponent = { hi := 0, lo := 0 } by
          unfold GuardSticky.roundPositiveCodeWord
          rw [ite_eq_left hzero]]
      _ = 0 := by
        simp only [FloatLib.Numerics.FixedWord.UInt128.toNat,
          UInt64.toNat_zero, zero_mul, add_zero]
      _ = roundPositiveCode format heligible
          { negative := false
            significand := significand.toNat
            exponent } := by
        unfold roundPositiveCode
        rw [ite_eq_left hzeroTest]
  · have hnonzeroNat : significand.toNat ≠ 0 := by
      intro equality
      exact hzero <|
        (NativeLimb.isZero_eq_true_iff significand).mpr equality
    have hnonzeroTest :
        ¬(significand.toNat == 0 || false) = true := by
      simpa using hnonzeroNat
    unfold GuardSticky.roundPositiveCodeWord roundPositiveCode
    rw [ite_eq_right hzero, ite_eq_right hnonzeroTest, dite_eq_left hcapacity, hroundtrip]
    by_cases hsmall :
        GuardSticky.isLessMinPositive format significand exponent = true
    · rw [ite_eq_left hsmall, ite_eq_left hsmall]
      simp only [FloatLib.Numerics.FixedWord.UInt128.toNat,
        UInt64.toNat_zero, UInt64.toNat_one, zero_mul, add_zero]
    · rw [ite_eq_right hsmall, ite_eq_right hsmall]

/-- Carrier-returning positive rounding always stays below the Posit sign bit. -/
theorem GuardSticky.roundPositiveCodeWord_lt_signMask
    (format : Format) (heligible : NativeLimb.Eligible format)
    (significand : FloatLib.Numerics.FixedWord.UInt128)
    (exponent : Int) :
    (GuardSticky.roundPositiveCodeWord
        format significand exponent).toNat <
      format.signMaskNat := by
  rw [GuardSticky.roundPositiveCodeWord_toNat format heligible]
  exact roundPositiveCode_lt_signMask format heligible _

/-- Signed carrier-returning rounding is the general two-limb exact round code. -/
theorem GuardSticky.roundCodeWord_toNat
    (format : Format) (heligible : NativeLimb.Eligible format)
    (negative : Bool)
    (significand : FloatLib.Numerics.FixedWord.UInt128)
    (exponent : Int) :
    (GuardSticky.roundCodeWord
        format negative significand exponent).toNat =
      roundCodeNat format heligible
        { negative
          significand := significand.toNat
          exponent } := by
  unfold GuardSticky.roundCodeWord
  rw [GuardSticky.restoreSignWord_toNat format heligible
    negative (GuardSticky.roundPositiveCodeWord
      format significand exponent)
    (GuardSticky.roundPositiveCodeWord_lt_signMask
      format heligible significand exponent)]
  rw [GuardSticky.roundPositiveCodeWord_toNat format heligible]
  unfold roundCodeNat
  by_cases hzero : significand.toNat = 0
  · simp [hzero, roundPositiveCode, DyadicRounding.restoreSignCode]
  · simp [hzero, DyadicRounding.magnitude]

/--
Normalizing a four-limb significand into its jammed two-limb leading window preserves direct
positive Posit rounding for every two-limb-eligible format.
-/
theorem GuardSticky.roundPositiveCode_normalizeJam128
    (format : Format) (heligible : NativeLimb.Eligible format)
    (significand : FloatLib.Numerics.FixedWord.UInt256)
    (exponent : Int) :
    DirectDyadicPacking.roundPositiveCode format
        { negative := false
          significand := significand.normalizeJam128.toNat
          exponent :=
            exponent + Int.ofNat significand.normalizationShift128 } =
      DirectDyadicPacking.roundPositiveCode format
        { negative := false
          significand := significand.toNat
          exponent } := by
  let shift := significand.normalizationShift128
  have hjammed :
      significand.normalizeJam128.toNat =
        FloatLib.Numerics.shiftRightJam significand.toNat shift := by
    simp [shift]
  rw [hjammed]
  by_cases hshift : shift = 0
  · have hjamZero :
        FloatLib.Numerics.shiftRightJam significand.toNat 0 =
          significand.toNat := by
      unfold FloatLib.Numerics.shiftRightJam
      simp only [pow_zero, Nat.mod_one, beq_self_eq_true,
        ite_true, Nat.div_one]
    have hnormalization :
        significand.normalizationShift128 = 0 := by
      simpa [shift] using hshift
    have hzeroExponent : Int.ofNat 0 = (0 : Int) := rfl
    rw [hshift, hjamZero, hnormalization, hzeroExponent, add_zero]
  · have hnonzero : significand.toNat ≠ 0 := by
      intro hzero
      apply hshift
      dsimp [shift]
      unfold FloatLib.Numerics.FixedWord.UInt256.normalizationShift128
      rw [FloatLib.Numerics.FixedWord.UInt256.log2_toNat, hzero]
      rfl
    have hlog :
        significand.toNat.log2 = shift + 127 := by
      dsimp [shift] at hshift ⊢
      unfold FloatLib.Numerics.FixedWord.UInt256.normalizationShift128 at hshift ⊢
      rw [FloatLib.Numerics.FixedWord.UInt256.log2_toNat] at hshift ⊢
      omega
    have hlower :
        2 ^ (shift + 127) ≤ significand.toNat := by
      rw [← hlog]
      exact Nat.log2_self_le hnonzero
    have hupper :
        significand.toNat < 2 ^ (shift + 128) := by
      have hbound : significand.toNat < 2 ^ (significand.toNat.log2 + 1) :=
        Nat.lt_log2_self
      rw [hlog] at hbound
      simpa [show shift + 127 + 1 = shift + 128 by omega] using hbound
    have hjammedUpper :
        FloatLib.Numerics.shiftRightJam significand.toNat shift <
          2 ^ 128 := by
      rw [← hjammed]
      exact significand.normalizeJam128.toNat_lt
    apply DirectDyadicPacking.roundPositiveCode_shiftRightJam
      format 127 (by omega) (by
        unfold NativeLimb.Eligible at heligible
        unfold Format.payloadBits
        omega)
      significand.toNat shift exponent hlower
    · simpa [show shift + 127 + 1 = shift + 128 by omega] using hupper
    · simpa [show 127 + 1 = 128 by omega] using hjammedUpper

/--
Signed two-limb rounding of a normalized jammed four-limb significand is exactly the shared
arbitrary-width result.
-/
theorem GuardSticky.roundCodeWord_normalizeJam128_toNat
    (format : Format) (heligible : NativeLimb.Eligible format)
    (negative : Bool)
    (significand : FloatLib.Numerics.FixedWord.UInt256)
    (exponent : Int) :
    (GuardSticky.roundCodeWord format negative
        significand.normalizeJam128
        (exponent + Int.ofNat significand.normalizationShift128)).toNat =
      roundCodeNat format heligible
        { negative
          significand := significand.toNat
          exponent } := by
  rw [GuardSticky.roundCodeWord_toNat format heligible]
  unfold roundCodeNat
  have hzero :=
    FloatLib.Numerics.FixedWord.UInt256.normalizeJam128_toNat_eq_zero_iff
      significand
  by_cases hsignificand : significand.toNat = 0
  · have hnormalized : significand.normalizeJam128.toNat = 0 :=
      hzero.2 hsignificand
    rw [ite_eq_left (by simpa only [beq_iff_eq] using hnormalized)]
    rw [ite_eq_left (by simpa only [beq_iff_eq] using hsignificand)]
  · have hnormalized : significand.normalizeJam128.toNat ≠ 0 := by
      exact fun equality => hsignificand (hzero.1 equality)
    rw [ite_eq_right (by simpa only [beq_iff_eq] using hnormalized)]
    rw [ite_eq_right (by simpa only [beq_iff_eq] using hsignificand)]
    unfold DyadicRounding.magnitude
    change
      DyadicRounding.restoreSignCode format negative
          (roundPositiveCode format heligible
            {
              negative := false
              significand := significand.normalizeJam128.toNat
              exponent :=
                exponent + Int.ofNat significand.normalizationShift128
            }) =
        DyadicRounding.restoreSignCode format negative
          (roundPositiveCode format heligible
            {
              negative := false
              significand := significand.toNat
              exponent
            })
    rw [roundPositiveCode_eq_direct format heligible,
      roundPositiveCode_eq_direct format heligible]
    rw [GuardSticky.roundPositiveCode_normalizeJam128
      format heligible significand exponent]

end FloatLib.Floats.Formats.Posit.Model.NativeLimbRounding
