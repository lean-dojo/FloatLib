/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.SquareRoot.Runtime
public import FloatLib.Kernels.FixedWord.RestoringSqrt.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Arithmetic.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Elimination.Proof

import FloatLib.Numerics.Exact.Dyadic.Order
import FloatLib.Floats.Formats.Posit.Arithmetic.WordLimb.Proof

/-!
# Correctness of packed native-word Posit square root

The storage adapter decodes once, scales the exact significand into four fixed words, and runs the
shared restoring square-root kernel. Its proved root and remainder are jammed into the common
guard/sticky rounder, giving the executable word path exactly the arbitrary-width direct
square-root semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedSquareRoot

open FloatLib.Numerics
open FloatLib.Numerics.FixedWord
open FloatLib.Numerics.FixedWord.RestoringSquareRoot

/-- The fixed-word scaling product is the exact mathematical left shift. -/
private theorem scaledRadicandWord_toNat
    (significand : UInt64) (shift : Nat) (hshift : shift < 128) :
    (scaledRadicandWord significand shift).toNat =
      significand.toNat <<< shift := by
  have hone :
      ({ hi := 0, lo := 1 } : UInt128).toNat = 1 := by
    simp [UInt128.toNat]
  have hfit :
      ({ hi := 0, lo := 1 } : UInt128).toNat <<< shift < 2 ^ 128 := by
    rw [hone, Nat.shiftLeft_eq, one_mul]
    exact Nat.pow_lt_pow_right (by decide) hshift
  unfold scaledRadicandWord
  rw [mul128_toNat, UInt128.shiftLeft_toNat _ shift hshift hfit]
  simp [UInt128.toNat, Nat.shiftLeft_eq]

/-- The native zero test and low-bit update implement representation-free sticky jamming. -/
private theorem jamRoot_toNat (root remainder : UInt128) :
    (if NativeLimb.isZero remainder then root else root.setLowBit).toNat =
      StickyPrefix.jamRemainder root.toNat remainder.toNat := by
  by_cases hzero : remainder.toNat = 0 <;>
    simp [NativeLimb.isZero_eq_true_iff, StickyPrefix.jamRemainder, hzero,
      UInt128.setLowBit_toNat]

/-- Direct signed packing reduces to direct positive packing when the sign is clear. -/
private theorem directRoundCode_eq_roundPositiveCode
    (format : Format) (significand : Nat) (exponent : Int) :
    DirectDyadicPacking.roundCode format
        { negative := false, significand, exponent } =
      DirectDyadicPacking.roundPositiveCode format
        { negative := false, significand, exponent } := by
  by_cases hzero : significand = 0
  · simp [DirectDyadicPacking.roundCode,
      DirectDyadicPacking.roundPositiveCode, hzero]
  · simp [DirectDyadicPacking.roundCode, DyadicRounding.magnitude,
      DyadicRounding.restoreSignCode, hzero]

/--
For a positive nonzero source, the native root prefix is exactly the direct mathematical prefix.
-/
private theorem roundFieldsWord_toNat_eq_direct_of_positive
    (format : Format) (heligible : NativeWord.Eligible format)
    (significand : UInt64) (exponent : Int)
    (hsignificand : significand ≠ 0) :
    (roundFieldsWord format heligible false significand exponent).toNat =
      DirectDyadicSquareRoot.roundCode format
        { negative := false
          significand := significand.toNat
          exponent } := by
  have hsignificandNat : significand.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hsignificand
  have hpayload : format.payloadBits < 64 := by
    unfold Format.payloadBits NativeWord.Eligible at *
    omega
  have hparity : (exponent.emod 2).toNat < 2 := by
    change (exponent % 2).toNat < 2
    omega
  unfold roundFieldsWord
  simp only [beq_iff_eq, hsignificand, Bool.false_eq_true, if_false]
  rw [NativeWordLimb.roundCodeWordLow_toNat_eq_direct
    format heligible, jamRoot_toNat]
  set shift := (exponent.emod 2).toNat + 2 * format.payloadBits with hshift
  have hscaled : (scaledRadicandWord significand shift).toNat = significand.toNat <<< shift :=
    scaledRadicandWord_toNat significand shift (by omega)
  have hfit : (scaledRadicandWord significand shift).toNat < 2 ^ 192 := by
    rw [hscaled, Nat.shiftLeft_eq]
    calc
      significand.toNat * 2 ^ shift < 2 ^ 64 * 2 ^ shift :=
        Nat.mul_lt_mul_of_pos_right significand.toNat_lt (Nat.two_pow_pos shift)
      _ = 2 ^ (64 + shift) := (Nat.pow_add 2 64 shift).symm
      _ ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨hroot, hremainder⟩ := rootAndRemainder_spec _ 96 (by decide) (by decide) hfit
  rw [hroot, hremainder, hscaled, directRoundCode_eq_roundPositiveCode]
  simp [DirectDyadicSquareRoot.roundCode, DirectDyadicSquareRoot.rootPrefix,
    DirectDyadicSquareRoot.prefixAtPrecision, DirectDyadicSquareRoot.prefixPrecision,
    DirectDyadicSquareRoot.truncatedRoot, DirectDyadicSquareRoot.squareRemainder,
    DirectDyadicSquareRoot.scaledRadicand, DirectDyadicSquareRoot.exponentParity,
    hsignificandNat, hshift]

/-- Native field rounding is exactly the common direct square-root domain rule. -/
theorem roundFieldsWord_toNat_eq_direct
    (format : Format) (heligible : NativeWord.Eligible format)
    (negative : Bool) (significand : UInt64) (exponent : Int) :
    (roundFieldsWord format heligible
        negative significand exponent).toNat =
      if ({
          negative
          significand := significand.toNat
          exponent
        } : FloatLib.Numerics.Dyadic).isLess
          FloatLib.Numerics.Dyadic.zero then
        format.signMaskNat
      else
        DirectDyadicSquareRoot.roundCode format
          { negative
            significand := significand.toNat
            exponent } := by
  by_cases hzero : significand = 0
  · subst significand
    simp [roundFieldsWord, FloatLib.Numerics.Dyadic.isLess_eq_decide,
      FloatLib.Numerics.Dyadic.toRat,
      FloatLib.Numerics.Dyadic.signedSignificand,
      DirectDyadicSquareRoot.roundCode]
  · cases negative with
    | false =>
        have hnonnegative :
            (({
                negative := false
                significand := significand.toNat
                exponent
              } : FloatLib.Numerics.Dyadic).isLess
                FloatLib.Numerics.Dyadic.zero) = false := by
          rw [FloatLib.Numerics.Dyadic.isLess_eq_decide,
            FloatLib.Numerics.Dyadic.zero_toRat]
          apply decide_eq_false
          unfold FloatLib.Numerics.Dyadic.toRat
            FloatLib.Numerics.Dyadic.signedSignificand
          apply not_lt_of_ge
          apply mul_nonneg
          · rw [Rat.ofInt_eq_cast]
            exact Int.cast_nonneg (Int.natCast_nonneg _)
          · exact (zpow_pos (by norm_num) _).le
        rw [roundFieldsWord_toNat_eq_direct_of_positive
          format heligible significand exponent hzero]
        simp [hnonnegative]
    | true =>
        have hsignificandPositive : 0 < significand.toNat := by
          exact Nat.pos_of_ne_zero (by
            simpa [← UInt64.toNat_inj] using hzero)
        have hnegativeValue :
            (({
                negative := true
                significand := significand.toNat
                exponent
              } : FloatLib.Numerics.Dyadic).isLess
                FloatLib.Numerics.Dyadic.zero) = true := by
          rw [FloatLib.Numerics.Dyadic.isLess_eq_decide,
            FloatLib.Numerics.Dyadic.zero_toRat]
          apply decide_eq_true
          unfold FloatLib.Numerics.Dyadic.toRat
            FloatLib.Numerics.Dyadic.signedSignificand
          simp only [if_true]
          apply mul_neg_of_neg_of_pos
          · rw [Rat.ofInt_eq_cast]
            have hintPositive :
                (0 : Int) < Int.ofNat significand.toNat :=
              Int.ofNat_lt.mpr hsignificandPositive
            exact_mod_cast neg_neg_of_pos hintPositive
          · exact zpow_pos (by norm_num) _
        rw [show
          roundFieldsWord format heligible true significand exponent =
            NativeWord.signMaskWord format by
          simp [roundFieldsWord, hzero]]
        rw [NativeWord.signMaskWord_toNat format heligible]
        simp [hnegativeValue]

/-- The packed scalar adapter is exactly the stored-word square-root kernel. -/
theorem sqrtWordCodeValid_eq
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (value : UInt64)
    (hvalue : value.toNat < format.modulus) :
    sqrtWordCodeValid heligible value hvalue =
      NativeWordArithmetic.sqrtWordCode heligible value := by
  unfold sqrtWordCodeValid sqrtWordCodeWordValid
    NativeWordArithmetic.sqrtWordCode
  rw [NativeWord.withDyadicWordFieldsValid_toNat,
    NativeWord.signMaskWord_toNat format heligible]
  simp only [roundFieldsWord_toNat_eq_direct]
  rw [← NativeWord.withDyadicFieldsValid_eq_word
    (format := format) (heligible := heligible)
    (code := value) (hcode := hvalue)
    (onNaR := format.signMaskNat)
    (continuation := fun negative significand exponent =>
      if ({
          negative
          significand
          exponent
        } : FloatLib.Numerics.Dyadic).isLess
          FloatLib.Numerics.Dyadic.zero then
        format.signMaskNat
      else
        DirectDyadicSquareRoot.roundCode format
          { negative, significand, exponent })]
  rw [NativeWord.withDyadicFieldsValid_eq,
    NativeWord.withDyadicFields_eq]
  cases NativeWord.toDyadic? format value <;> rfl

/-- Every packed scalar square root is a complete in-range Posit encoding. -/
theorem sqrtWordCodeValid_lt_modulus
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (value : UInt64)
    (hvalue : value.toNat < format.modulus) :
    sqrtWordCodeValid heligible value hvalue < format.modulus := by
  rw [sqrtWordCodeValid_eq]
  exact NativeWordArithmetic.sqrtWordCode_lt_modulus heligible value

/-- The word-valued and natural-number views of the complete root code are identical. -/
theorem sqrtWordCodeWordValid_toNat
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (value : UInt64)
    (hvalue : value.toNat < format.modulus) :
    (sqrtWordCodeWordValid heligible value hvalue).toNat =
      sqrtWordCodeValid heligible value hvalue :=
  rfl

end FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedSquareRoot
