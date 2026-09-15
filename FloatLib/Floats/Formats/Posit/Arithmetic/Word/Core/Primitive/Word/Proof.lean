/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Word.Runtime
public import FloatLib.Kernels.FixedWord.Core.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Proof

/-!
# Correctness of native-word posit primitives

The `UInt64` primitives agree with the exact-width posit model and their natural-number
specifications. Executable definitions live in
`FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Word.Runtime`.

The lemmas cover masking, sign manipulation, modular negation, and bounded word conversion.
Higher posit kernels use them to relate machine operations to exact-width words and natural
numbers.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWord

open FloatLib.Numerics

variable {format : Format}

/-- Every format eligible for native-word execution has at most `2^64` complete codes. -/
theorem modulus_le_two_pow_64 (format : Format) (heligible : Eligible format) :
    format.modulus ≤ 2 ^ 64 := by
  unfold Format.modulus Eligible at *
  exact Nat.pow_le_pow_right (by decide) heligible

/-- Every fully stored native posit also admits native nonnegative-candidate decoding. -/
theorem candidateEligible_of_eligible (format : Format)
    (heligible : Eligible format) :
    CandidateEligible format := by
  unfold Eligible at heligible
  unfold CandidateEligible
  omega

/-- The native sign mask is exact for every format stored in one machine word. -/
theorem signMaskWord_toNat (format : Format)
    (heligible : Eligible format) :
    (signMaskWord format).toNat = format.signMaskNat := by
  have hindex : format.signIndex < 64 := by
    unfold Format.signIndex
    unfold Eligible at heligible
    omega
  unfold signMaskWord
  rw [FloatLib.Numerics.FixedWord.shiftLeft_toNat
    (1 : UInt64) format.signIndex hindex]
  · simp [Format.signMaskNat, Nat.shiftLeft_eq]
  · simp [Nat.shiftLeft_eq]
    exact Nat.pow_lt_pow_right (by decide) hindex

/-- Native and natural comparisons with the positive-code endpoint are identical. -/
theorem lt_signMaskWord_iff (format : Format)
    (heligible : Eligible format) (code : UInt64) :
    code < signMaskWord format ↔ code.toNat < format.signMaskNat := by
  change code.toNat < (signMaskWord format).toNat ↔ _
  rw [signMaskWord_toNat format heligible]

/-- Incrementing a positive candidate below the sign mask cannot wrap a machine word. -/
theorem toNat_add_one_of_lt_signMask
    (format : Format) (heligible : Eligible format)
    (code : UInt64) (hcode : code.toNat < format.signMaskNat) :
    (code + 1).toNat = code.toNat + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt]
  rw [← signMaskWord_toNat format heligible] at hcode
  have hmaskBound := UInt64.toNat_lt (signMaskWord format)
  omega

/--
The native successor-range test is exactly the natural-code test used by the reference rounder.

This bridge belongs at the representation boundary because packed scalar and multi-limb target
rounders need the same fact. Keeping it here prevents each arithmetic backend from unfolding
machine-word addition and the format sign mask independently.
-/
theorem successor_lt_signMaskWord_iff
    (format : Format) (heligible : Eligible format)
    (code : UInt64) (hcode : code.toNat < format.signMaskNat) :
    code + 1 < signMaskWord format ↔
      code.toNat + 1 < format.signMaskNat := by
  change (code + 1).toNat < (signMaskWord format).toNat ↔ _
  rw [toNat_add_one_of_lt_signMask format heligible code hcode]
  rw [signMaskWord_toNat format heligible]

/-- Boolean form of `successor_lt_signMaskWord_iff` used by executable classifiers. -/
theorem successorInRange_eq
    (format : Format) (heligible : Eligible format)
    (code : UInt64) (hcode : code.toNat < format.signMaskNat) :
    decide (code + 1 < signMaskWord format) =
      decide (code.toNat + 1 < format.signMaskNat) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using
    successor_lt_signMaskWord_iff format heligible code hcode

/--
The appended-bit midpoint `2 * code + 1` fits in `UInt64` for every representable positive
candidate.
-/
theorem toNat_twice_add_one_of_lt_signMask
    (format : Format) (heligible : Eligible format)
    (code : UInt64) (hcode : code.toNat < format.signMaskNat) :
    (code + code + 1).toNat = 2 * code.toNat + 1 := by
  have hsignIndex : format.signIndex ≤ 63 := by
    unfold Eligible at heligible
    unfold Format.signIndex
    omega
  have hsignMask : format.signMaskNat ≤ 2 ^ 63 := by
    unfold Format.signMaskNat
    exact Nat.pow_le_pow_right (by decide) hsignIndex
  have hdouble : code.toNat + code.toNat < 2 ^ 64 := by
    omega
  have hfull : code.toNat + code.toNat + 1 < 2 ^ 64 := by
    omega
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_one,
    Nat.mod_eq_of_lt hdouble, Nat.mod_eq_of_lt hfull]
  omega

/-- The native wrapped modulus is the word conversion of the exact format modulus. -/
theorem modulusWord_eq_ofNat_modulus (format : Format)
    (heligible : Eligible format) :
    modulusWord format = UInt64.ofNat format.modulus := by
  apply UInt64.toNat_inj.mp
  rw [modulusWord, UInt64.toNat_add,
    signMaskWord_toNat format heligible, UInt64.toNat_ofNat']
  rw [Format.modulus_eq_two_mul_signMaskNat]
  omega

/-- Native sign restoration is the exact natural-code sign operation. -/
theorem restoreSignWord_toNat
    (format : Format) (heligible : Eligible format)
    (negative : Bool) (positiveCode : UInt64)
    (hpositive : positiveCode.toNat < format.signMaskNat) :
    (restoreSignWord format negative positiveCode).toNat =
      DyadicRounding.restoreSignCode format negative positiveCode.toNat := by
  cases negative with
  | false =>
      rfl
  | true =>
      by_cases hzero : positiveCode = 0
      · subst positiveCode
        simp [restoreSignWord, DyadicRounding.restoreSignCode]
      · have hpositiveNonzero : positiveCode.toNat ≠ 0 := by
          intro hzeroNat
          apply hzero
          apply UInt64.toNat_inj.mp
          simpa using hzeroNat
        have hpositiveLtModulus :
            positiveCode.toNat < format.modulus :=
          hpositive.trans format.signMaskNat_lt_modulus
        by_cases hwidth : format.bits < 64
        · have hmodulusLt : format.modulus < 2 ^ 64 := by
            unfold Format.modulus
            exact Nat.pow_lt_pow_right (by decide) hwidth
          have hmodulusWord :
              (modulusWord format).toNat = format.modulus := by
            rw [modulusWord_eq_ofNat_modulus format heligible,
              UInt64.toNat_ofNat', Nat.mod_eq_of_lt hmodulusLt]
          have hcodeLe :
              positiveCode ≤ modulusWord format := by
            rw [UInt64.le_iff_toNat_le, hmodulusWord]
            exact hpositiveLtModulus.le
          unfold restoreSignWord DyadicRounding.restoreSignCode
          simp only [ite_true, beq_iff_eq, hzero, ite_false]
          rw [UInt64.toNat_sub_of_le _ _ hcodeLe, hmodulusWord]
          simp [hpositiveNonzero]
        · have hwidthEq : format.bits = 64 := by
            unfold Eligible at heligible
            omega
          have hmodulus : format.modulus = 2 ^ 64 := by
            simp [Format.modulus, hwidthEq]
          have hmodulusWord :
              (modulusWord format).toNat = 0 := by
            rw [modulusWord_eq_ofNat_modulus format heligible,
              UInt64.toNat_ofNat', hmodulus, Nat.mod_self]
          unfold restoreSignWord DyadicRounding.restoreSignCode
          simp only [ite_true, beq_iff_eq, hzero, ite_false]
          rw [UInt64.toNat_sub, hmodulusWord, hmodulus]
          rw [Nat.add_zero, Nat.mod_eq_of_lt]
          · simp [hpositiveNonzero]
          · omega

/-- Native bit inspection agrees with natural-number bit inspection. -/
theorem bitAt_eq_testBit (value : UInt64) (index : Nat) :
    bitAt value index = value.toNat.testBit index := by
  unfold bitAt
  split
  next hindex =>
    rw [Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq]
    have hindexPow : index < 2 ^ 64 := by omega
    constructor
    · intro equality
      have naturalEquality := congrArg UInt64.toNat equality
      simpa only [UInt64.toNat_and, UInt64.toNat_shiftRight,
        UInt64.toNat_ofNat', UInt64.toNat_one,
        Nat.mod_eq_of_lt hindexPow, Nat.mod_eq_of_lt hindex,
        Nat.shiftRight_eq_div_pow, Nat.and_comm,
        Nat.one_and_eq_mod_two] using naturalEquality
    · intro equality
      apply UInt64.toNat_inj.mp
      simpa only [UInt64.toNat_and, UInt64.toNat_shiftRight,
        UInt64.toNat_ofNat', UInt64.toNat_one,
        Nat.mod_eq_of_lt hindexPow, Nat.mod_eq_of_lt hindex,
        Nat.shiftRight_eq_div_pow, Nat.and_comm,
        Nat.one_and_eq_mod_two] using equality
  next hindex =>
    symm
    apply Nat.testBit_lt_two_pow
    calc
      value.toNat < 2 ^ 64 := UInt64.toNat_lt value
      _ ≤ 2 ^ index := Nat.pow_le_pow_right (by omega) (by omega)

/-- Natural value of a native low-bit mask below the machine width. -/
theorem lowMask_toNat (width : Nat) (hwidth : width < 64) :
    (lowMask width).toNat = 2 ^ width - 1 := by
  unfold lowMask
  rw [ite_eq_left hwidth, UInt64.toNat_sub_of_le]
  · simp [Nat.mod_eq_of_lt hwidth, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hwidth)]
  · simp [UInt64.le_iff_toNat_le, Nat.mod_eq_of_lt hwidth,
      Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hwidth)]
    exact Nat.one_le_two_pow

/-- Native low-bit extraction agrees with reduction modulo the corresponding power of two. -/
theorem lowBits_toNat (value : UInt64) (width : Nat) (hwidth : width < 64) :
    (lowBits value width).toNat = value.toNat % 2 ^ width := by
  rw [lowBits, UInt64.toNat_and, lowMask_toNat width hwidth]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- Native low-bit extraction is exact through the complete machine width. -/
theorem lowBits_toNat_of_le (value : UInt64) (width : Nat)
    (hwidth : width ≤ 64) :
    (lowBits value width).toNat = value.toNat % 2 ^ width := by
  rcases hwidth.lt_or_eq with hwidth | rfl
  · exact lowBits_toNat value width hwidth
  · simp only [lowBits, lowMask, lt_self_iff_false, ite_false,
      UInt64.toNat_and]
    change value.toNat &&& 2 ^ 64 - 1 = value.toNat % 2 ^ 64
    exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- Whole-word complementation flips every native bit that can be inspected. -/
theorem bitAt_complement (value : UInt64) (index : Nat)
    (hindex : index < 64) :
    bitAt (~~~value) index = !bitAt value index := by
  rw [bitAt_eq_testBit, bitAt_eq_testBit]
  rw [← UInt64.toNat_toBitVec (~~~value),
    ← UInt64.toNat_toBitVec value]
  rw [BitVec.testBit_toNat (~~~value).toBitVec,
    BitVec.testBit_toNat value.toBitVec]
  rw [UInt64.toBitVec_not, BitVec.getLsbD_not]
  simp [hindex]

end FloatLib.Floats.Formats.Posit.Model.NativeWord
