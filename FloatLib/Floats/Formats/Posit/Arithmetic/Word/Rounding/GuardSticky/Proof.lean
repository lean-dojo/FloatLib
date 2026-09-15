/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Shared.GuardSticky.Proof
import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Fields.Proof
import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Word.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Proof
public import FloatLib.Kernels.FixedWord.DyadicCompare.Proof

/-!
# Correctness of direct one-word guard-and-sticky Posit rounding

`candidateCarrierLawful` proves that the `UInt64` candidate carrier satisfies the shared carrier
laws at capacity 64. The shared theorems then establish the packing and rounding refinement;
the remaining proofs connect the one-word entry points, which add the zero test, the exact
minimum-positive comparison, and sign restoration, to the arbitrary-width direct rounder. The
one-word kernel and the two-limb kernel are therefore execution refinements of one rounding rule,
selected only by exact intermediate capacity.

The separate `WordLimb` proof module establishes the cross-carrier projection theorem used by
operations with a genuine two-limb intermediate. Importing this scalar proof does not load the
complete two-limb rounding proof.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordRounding.GuardSticky

open FloatLib.Numerics

/-- A bounded scalar left shift has its exact natural-number value. -/
private theorem shiftLeft_toNat
    (value : UInt64) (shift : Nat)
    (hshift : shift < 64)
    (hfit : value.toNat <<< shift < 2 ^ 64) :
    (shiftLeft value shift).toNat = value.toNat <<< shift := by
  unfold shiftLeft
  rw [ite_eq_left hshift]
  exact FixedWord.shiftLeft_toNat value shift hshift hfit

/-- A single bit shifted below the word width has its exact power-of-two value. -/
private theorem shiftLeft_one_toNat (shift : Nat) (hshift : shift < 64) :
    (shiftLeft 1 shift).toNat = 2 ^ shift := by
  rw [shiftLeft_toNat (1 : UInt64) shift hshift, UInt64.toNat_one, Nat.shiftLeft_eq, one_mul]
  rw [UInt64.toNat_one, Nat.shiftLeft_eq, one_mul]
  exact Nat.pow_lt_pow_right (by decide) hshift

/--
Natural-number laws of the one-word candidate carrier at capacity 64.

Bit and suffix reads are exact at every width. The arithmetic laws hold under the bounds the
shared rounder establishes: shifts stay below 64 positions, sums and successors fit the word, and
masks are narrower than the word.
-/
theorem candidateCarrierLawful :
    GuardStickyCarrier.LawfulCandidateCarrier candidateCarrier UInt64.toNat 64 where
  bitAt_eq_testBit := NativeWord.bitAt_eq_testBit
  hasLowBits_eq value width := by
    have htoNat :
        (NativeWord.lowBits value width).toNat =
          value.toNat % 2 ^ width := by
      by_cases hwidth : width ≤ 64
      · exact NativeWord.lowBits_toNat_of_le value width hwidth
      · have hlarge : 64 < width := Nat.lt_of_not_ge hwidth
        have hvalue : value.toNat < 2 ^ width :=
          value.toNat_lt.trans_le <|
            Nat.pow_le_pow_right (by decide) hlarge.le
        unfold NativeWord.lowBits NativeWord.lowMask
        rw [ite_eq_right (Nat.not_lt.mpr hlarge.le), UInt64.toNat_and]
        change value.toNat &&& (2 ^ 64 - 1) =
          value.toNat % 2 ^ width
        rw [Nat.and_two_pow_sub_one_eq_mod,
          Nat.mod_eq_of_lt value.toNat_lt, Nat.mod_eq_of_lt hvalue]
    apply Bool.eq_iff_iff.mpr
    simp only [hasLowBits, bne_iff_ne]
    constructor
    · intro hword hremainder
      apply hword
      apply UInt64.toNat_inj.mp
      rw [htoNat]
      simpa using hremainder
    · intro hremainder hword
      apply hremainder
      have equality := congrArg UInt64.toNat hword
      rw [htoNat] at equality
      simpa using equality
  toNat_lt := UInt64.toNat_lt
  toNat_ofWord _ := rfl
  shiftLeft_toNat := shiftLeft_toNat
  shiftRight_toNat := NativeWord.shiftRight_toNat
  fractionBelow_toNat value leading hleading hlower _ := by
    have honeShift : (shiftLeft 1 leading).toNat = 2 ^ leading :=
      shiftLeft_one_toNat leading hleading
    have honeLe : shiftLeft 1 leading ≤ value := by
      rw [UInt64.le_iff_toNat_le, honeShift]
      exact hlower
    show (value - shiftLeft 1 leading).toNat = value.toNat - 2 ^ leading
    rw [UInt64.toNat_sub_of_le value (shiftLeft 1 leading) honeLe, honeShift]
  add_toNat left right hfit := by
    show (left + right).toNat = left.toNat + right.toNat
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hfit]
  lowOnes_toNat := NativeWord.lowMask_toNat
  increment_toNat value hfit := by
    show (value + 1).toNat = value.toNat + 1
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hfit]
  isOdd_eq := FixedWord.lowBitIsNonzero_eq_odd
  log2_eq := FixedWord.log2_toNat

/-- Under one-word eligibility the payload is shorter than the carrier. -/
theorem payloadBits_lt_of_eligible
    (format : Format) (heligible : NativeWord.Eligible format) :
    format.payloadBits < 64 := by
  unfold NativeWord.Eligible Format.payloadBits at *
  omega

/-- The scalar minimum-positive comparison is exact dyadic comparison. -/
private theorem isLessMinPositive_eq
    (format : Format) (significand : UInt64) (exponent : Int) :
    isLessMinPositive format significand exponent =
      ({ negative := false
         significand := significand.toNat
         exponent } : FloatLib.Numerics.Dyadic).isLess
        (DyadicRounding.minPositive format) := by
  rw [DyadicRounding.minPositive_eq_fields]
  unfold isLessMinPositive
  dsimp only
  rw [FixedWord.DyadicCompare.isLessNonnegative_eq]
  simp only [UInt64.toNat_one]
  rw [Dyadic.isLessNonnegativeFields_eq, Dyadic.isLessFields_eq]

/-! ## Positive rounding -/

/-- The positive one-word kernel is the shared arbitrary-width direct rounder. -/
theorem roundPositiveCodeWord_toNat_eq_direct
    (format : Format) (heligible : NativeWord.Eligible format)
    (significand : UInt64) (exponent : Int) :
    (roundPositiveCodeWord format heligible significand exponent).toNat =
      DirectDyadicPacking.roundPositiveCode format
        { negative := false
          significand := significand.toNat
          exponent } := by
  by_cases hzero : significand = 0
  · subst significand
    rfl
  have hnonzero : significand.toNat ≠ 0 := by
    intro hzeroNat
    apply hzero
    apply UInt64.toNat_inj.mp
    simpa using hzeroNat
  unfold roundPositiveCodeWord
  simp only [beq_iff_eq, hzero, ite_false]
  by_cases hunderflow :
      isLessMinPositive format significand exponent = true
  · rw [ite_eq_left hunderflow]
    rw [isLessMinPositive_eq] at hunderflow
    rw [DirectDyadicPacking.roundPositiveCode_eq_dyadic]
    unfold DyadicRounding.roundPositiveCode
    have hspecial :
        ¬(significand.toNat == 0 || false) = true := by
      simp [hnonzero]
    rw [ite_eq_right hspecial, ite_eq_left hunderflow, UInt64.toNat_one]
  · rw [ite_eq_right hunderflow]
    apply GuardStickyCarrier.roundNormalizedPositive_toNat_eq_direct candidateCarrierLawful
      format significand exponent (payloadBits_lt_of_eligible format heligible) hnonzero
    rw [← isLessMinPositive_eq]
    exact Bool.eq_false_of_not_eq_true hunderflow

/-- Natural-number positive rounding has the same direct semantics. -/
theorem roundPositiveCode_eq_direct
    (format : Format) (heligible : NativeWord.Eligible format)
    (significand : UInt64) (exponent : Int) :
    roundPositiveCode format heligible significand exponent =
      DirectDyadicPacking.roundPositiveCode format
        { negative := false
          significand := significand.toNat
          exponent } := by
  exact roundPositiveCodeWord_toNat_eq_direct
    format heligible significand exponent

/-- Positive scalar rounding always remains below the Posit sign bit. -/
private theorem roundPositiveCodeWord_lt_signMask
    (format : Format) (heligible : NativeWord.Eligible format)
    (significand : UInt64) (exponent : Int) :
    (roundPositiveCodeWord format heligible significand exponent).toNat <
      format.signMaskNat := by
  rw [roundPositiveCodeWord_toNat_eq_direct]
  exact DirectDyadicPacking.roundPositiveCode_lt_signMask format _

/-! ## Signed rounding -/

/-- The signed one-word kernel is the shared arbitrary-width direct rounder. -/
theorem roundCodeWord_toNat_eq_direct
    (format : Format) (heligible : NativeWord.Eligible format)
    (negative : Bool) (significand : UInt64) (exponent : Int) :
    (roundCodeWord format heligible negative significand exponent).toNat =
      DirectDyadicPacking.roundCode format
        { negative
          significand := significand.toNat
          exponent } := by
  unfold roundCodeWord
  rw [NativeWord.restoreSignWord_toNat format heligible negative
    (roundPositiveCodeWord format heligible significand exponent)
    (roundPositiveCodeWord_lt_signMask
      format heligible significand exponent)]
  rw [roundPositiveCodeWord_toNat_eq_direct]
  unfold DirectDyadicPacking.roundCode
  by_cases hzero : significand.toNat = 0
  · simp [hzero, DirectDyadicPacking.roundPositiveCode,
      DyadicRounding.restoreSignCode]
  · simp [hzero, DyadicRounding.magnitude]

/-- Complete natural-number native-field rounding has the shared direct semantics. -/
theorem roundCodeNat_eq_direct
    (format : Format) (heligible : NativeWord.Eligible format)
    (negative : Bool) (significand : UInt64) (exponent : Int) :
    roundCodeNat format heligible negative significand exponent =
      DirectDyadicPacking.roundCode format
        { negative
          significand := significand.toNat
          exponent } := by
  exact roundCodeWord_toNat_eq_direct
    format heligible negative significand exponent

/-- Direct one-word field rounding always returns a valid complete Posit code. -/
theorem roundCodeNat_lt_modulus
    (format : Format) (heligible : NativeWord.Eligible format)
    (negative : Bool) (significand : UInt64) (exponent : Int) :
    roundCodeNat format heligible negative significand exponent <
      format.modulus := by
  rw [roundCodeNat_eq_direct]
  exact DirectDyadicPacking.roundCode_lt_modulus format _

end FloatLib.Floats.Formats.Posit.Model.NativeWordRounding.GuardSticky
