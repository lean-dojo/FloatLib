/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.SignedSum.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Elimination.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Dyadic.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.SignedSum.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Proof
import FloatLib.Floats.Formats.Posit.Arithmetic.WordLimb.Proof
public import FloatLib.Kernels.FixedWord.DyadicCompare.Proof
public import FloatLib.Kernels.FixedWord.Product.Proof
public import FloatLib.Kernels.FixedWord.SignedMagnitude.Proof

/-!
# Correctness of packed one-word Posit signed sums

Scalar alignment and signed-magnitude arithmetic are used exactly when the intermediate fits one
word. Capacity failures continue in the common proved two-limb engine. These theorems establish
that every branch returns the same direct exact-dyadic code.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedSignedSum

open FloatLib.Numerics

/-- Continuing a one-word sum in the two-limb engine preserves the direct exact code. -/
theorem roundWideFieldsWord_toNat
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : UInt64) (rightExponent : Int) :
    (roundWideFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent).toNat =
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (Dyadic.addFields
          leftNegative leftSignificand.toNat leftExponent
          rightNegative rightSignificand.toNat rightExponent) := by
  let hlimb : NativeLimb.Eligible format :=
    NativeWordLimb.limbEligible format heligible
  let result :=
    NativeLimbPacked.SignedSum.roundFieldsWord format hlimb
      leftNegative (NativeWordLimb.widen leftSignificand) leftExponent
      rightNegative (NativeWordLimb.widen rightSignificand) rightExponent
  have hresult :
      result.toNat < format.modulus := by
    rw [NativeLimbPacked.SignedSum.roundFieldsWord_toNat format hlimb]
    exact NativeLimbRounding.roundCodeNat_lt_modulus format hlimb _
  change result.lo.toNat =
    NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
      (Dyadic.addFields
        leftNegative leftSignificand.toNat leftExponent
        rightNegative rightSignificand.toNat rightExponent)
  calc
    result.lo.toNat = result.toNat :=
      FixedWord.UInt128.lo_toNat_eq_toNat_of_lt_two_pow result <| by
        exact hresult.trans_le <|
          NativeWord.modulus_le_two_pow_64 format heligible
    _ = NativeLimbRounding.roundCodeNat format hlimb
          (Dyadic.addFields
            leftNegative
              (NativeWordLimb.widen leftSignificand).toNat
              leftExponent
            rightNegative
              (NativeWordLimb.widen rightSignificand).toNat
              rightExponent) :=
      NativeLimbPacked.SignedSum.roundFieldsWord_toNat
        format hlimb
        leftNegative (NativeWordLimb.widen leftSignificand) leftExponent
        rightNegative (NativeWordLimb.widen rightSignificand) rightExponent
    _ = DirectDyadicPacking.roundCode format
          (Dyadic.addFields
            leftNegative
              (NativeWordLimb.widen leftSignificand).toNat
              leftExponent
            rightNegative
              (NativeWordLimb.widen rightSignificand).toNat
              rightExponent) :=
      NativeLimbRounding.roundCodeNat_eq_direct format hlimb _
    _ = DirectDyadicPacking.roundCode format
          (Dyadic.addFields
            leftNegative leftSignificand.toNat leftExponent
            rightNegative rightSignificand.toNat rightExponent) := by
      rw [NativeWordLimb.widen_toNat, NativeWordLimb.widen_toNat]
    _ = NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
          (Dyadic.addFields
            leftNegative leftSignificand.toNat leftExponent
            rightNegative rightSignificand.toNat rightExponent) :=
      (NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct
        format heligible _).symm

/-- Scalar field rounding and exact-target rounding have the same direct semantics. -/
private theorem roundCodeWord_toNat_eq_dyadicTarget
    (format : Format) (heligible : NativeWord.Eligible format)
    (negative : Bool) (significand : UInt64) (exponent : Int) :
    (NativeWordRounding.GuardSticky.roundCodeWord
      format heligible negative significand exponent).toNat =
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        { negative, significand := significand.toNat, exponent } := by
  rw [NativeWordRounding.GuardSticky.roundCodeWord_toNat_eq_direct,
    NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct]

/-- Direct rounding ignores the unused sign and exponent attached to zero magnitude. -/
private theorem roundCode_eq_signedMagnitudeDyadic
    (format : Format)
    (negative : Bool) (magnitude : UInt64) (exponent : Int) :
    DirectDyadicPacking.roundCode format
        { negative, significand := magnitude.toNat, exponent } =
      DirectDyadicPacking.roundCode format
        (FixedWord.signedMagnitudeDyadic negative magnitude exponent) := by
  by_cases hzero : magnitude = 0
  · subst magnitude
    simp [FixedWord.signedMagnitudeDyadic, DirectDyadicPacking.roundCode]
  · simp [FixedWord.signedMagnitudeDyadic, hzero]

/-- Scalar signed-magnitude accumulation rounds the exact aligned dyadic sum. -/
theorem roundAlignedFieldsWord_toNat
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64)
    (rightNegative : Bool) (rightSignificand : UInt64)
    (exponent : Int)
    (hleft : leftSignificand ≠ 0)
    (hright : rightSignificand ≠ 0) :
    (roundAlignedFieldsWord format heligible
        leftNegative leftSignificand
        rightNegative rightSignificand exponent).toNat =
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (Dyadic.addFields
          leftNegative leftSignificand.toNat exponent
          rightNegative rightSignificand.toNat exponent) := by
  unfold roundAlignedFieldsWord
  by_cases hsame : leftNegative = rightNegative
  · subst rightNegative
    simp only [beq_self_eq_true, if_true]
    by_cases hcarry :
        (FixedWord.add64 leftSignificand rightSignificand).carry = 0
    · simp only [beq_iff_eq, hcarry, if_true]
      have hadd :=
        FixedWord.add64_toNat leftSignificand rightSignificand
      simp only [hcarry, UInt64.toNat_zero, zero_mul, add_zero] at hadd
      have hsum :
          leftSignificand.toNat + rightSignificand.toNat < 2 ^ 64 := by
        rw [← hadd]
        exact (FixedWord.add64 leftSignificand rightSignificand).value.toNat_lt
      have hexact :=
        FixedWord.signedMagnitudeDyadic_addSignedMagnitudes_eq_addFields
          leftNegative leftNegative leftSignificand rightSignificand exponent
          hleft hright (fun _ => hsum)
      rw [roundCodeWord_toNat_eq_dyadicTarget,
        NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct,
        NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct,
        roundCode_eq_signedMagnitudeDyadic]
      simpa [FixedWord.addSignedMagnitudes, FixedWord.add64] using
        congrArg (DirectDyadicPacking.roundCode format) hexact
    · simp only [beq_iff_eq, hcarry, if_false]
      exact roundWideFieldsWord_toNat format heligible
        leftNegative leftSignificand exponent
        leftNegative rightSignificand exponent
  · simp only [beq_iff_eq, hsame, if_false]
    have hexact :=
      FixedWord.signedMagnitudeDyadic_addSignedMagnitudes_eq_addFields
        leftNegative rightNegative leftSignificand rightSignificand exponent
        hleft hright (fun equality => (hsame equality).elim)
    rw [roundCodeWord_toNat_eq_dyadicTarget,
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct,
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct,
      roundCode_eq_signedMagnitudeDyadic]
    exact congrArg (DirectDyadicPacking.roundCode format) hexact

/-- Scalar alignment and the two-limb continuation round the same exact dyadic sum. -/
theorem roundFieldsWord_toNat
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : UInt64) (rightExponent : Int) :
    (roundFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent).toNat =
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (Dyadic.addFields
          leftNegative leftSignificand.toNat leftExponent
          rightNegative rightSignificand.toNat rightExponent) := by
  unfold roundFieldsWord
  simp only [beq_iff_eq]
  split_ifs with hleft hright hexponents hshift hfit hshift hfit
  · subst hleft
    rw [roundCodeWord_toNat_eq_dyadicTarget,
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct,
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct]
    by_cases hright : rightSignificand = 0
    · subst hright
      rfl
    · have hrightNat : rightSignificand.toNat ≠ 0 := by
        simpa [← UInt64.toNat_inj] using hright
      simp [Dyadic.addFields, hrightNat]
  · subst hright
    rw [roundCodeWord_toNat_eq_dyadicTarget,
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct,
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct]
    have hleftNat : leftSignificand.toNat ≠ 0 := by
      simpa [← UInt64.toNat_inj] using hleft
    simp [Dyadic.addFields, hleftNat]
  · have hleftNat : leftSignificand.toNat ≠ 0 := by
      simpa [← UInt64.toNat_inj] using hleft
    have hrightNat : rightSignificand.toNat ≠ 0 := by
      simpa [← UInt64.toNat_inj] using hright
    have hshifted :=
      FixedWord.DyadicCompare.shiftLeft_toNat rightSignificand _ hshift hfit
    have hshiftedNatNe :
        rightSignificand.toNat <<< (rightExponent - leftExponent).toNat ≠ 0 :=
      Nat.shiftLeft_eq_zero_iff.not.mpr hrightNat
    rw [roundAlignedFieldsWord_toNat format heligible _ _ _ _ _ hleft
      (fun hzero => hshiftedNatNe (by simpa [hshifted] using congrArg UInt64.toNat hzero))]
    congr 1
    simp [Dyadic.addFields, hleftNat, hrightNat, hshiftedNatNe, hexponents, hshifted]
  · exact roundWideFieldsWord_toNat format heligible _ _ _ _ _ _
  · exact roundWideFieldsWord_toNat format heligible _ _ _ _ _ _
  · have hleftNat : leftSignificand.toNat ≠ 0 := by
      simpa [← UInt64.toNat_inj] using hleft
    have hrightNat : rightSignificand.toNat ≠ 0 := by
      simpa [← UInt64.toNat_inj] using hright
    have hshifted :=
      FixedWord.DyadicCompare.shiftLeft_toNat leftSignificand _ hshift hfit
    have hshiftedNatNe :
        leftSignificand.toNat <<< (leftExponent - rightExponent).toNat ≠ 0 :=
      Nat.shiftLeft_eq_zero_iff.not.mpr hleftNat
    rw [roundAlignedFieldsWord_toNat format heligible _ _ _ _ _
      (fun hzero => hshiftedNatNe (by simpa [hshifted] using congrArg UInt64.toNat hzero)) hright]
    congr 1
    simp [Dyadic.addFields, hleftNat, hrightNat, hshiftedNatNe, hexponents, hshifted]
  · exact roundWideFieldsWord_toNat format heligible _ _ _ _ _ _
  · exact roundWideFieldsWord_toNat format heligible _ _ _ _ _ _

/-- Packed native addition returns the flattened exact addition code. -/
theorem addWordsCodeWordValid_toNat
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    (addWordsCodeWordValid heligible left right hleft hright).toNat =
      NativeWordArithmetic.addWordsCodeFlatValid
        heligible left right hleft hright := by
  unfold addWordsCodeWordValid NativeWordArithmetic.addWordsCodeFlatValid
  rw [NativeWord.withTwoDyadicWordFieldsValid_toNat,
    NativeWord.signMaskWord_toNat format
      heligible]
  simp only [roundFieldsWord_toNat]
  rfl

/-- Packed native subtraction returns the flattened exact subtraction code. -/
theorem subWordsCodeWordValid_toNat
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    (subWordsCodeWordValid heligible left right hleft hright).toNat =
      NativeWordArithmetic.subWordsCodeFlatValid
        heligible left right hleft hright := by
  unfold subWordsCodeWordValid NativeWordArithmetic.subWordsCodeFlatValid
  rw [NativeWord.withTwoDyadicWordFieldsValid_toNat,
    NativeWord.signMaskWord_toNat format
      heligible]
  simp only [roundFieldsWord_toNat]
  rfl

/-- Continuing a genuine two-limb product preserves the direct exact fused code. -/
theorem roundWideFmaFieldsWord_toNat
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : UInt64) (rightExponent : Int)
    (addendNegative : Bool) (addendSignificand : UInt64) (addendExponent : Int) :
    (roundWideFmaFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent
        addendNegative addendSignificand addendExponent).toNat =
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (Dyadic.fmaFields
          leftNegative leftSignificand.toNat leftExponent
          rightNegative rightSignificand.toNat rightExponent
          addendNegative addendSignificand.toNat addendExponent) := by
  let hlimb : NativeLimb.Eligible format :=
    NativeWordLimb.limbEligible format heligible
  let product := FixedWord.mul64 leftSignificand rightSignificand
  let result :=
    NativeLimbPacked.SignedSum.roundFieldsWord format hlimb
      (Bool.xor leftNegative rightNegative) product
      (leftExponent + rightExponent)
      addendNegative (NativeWordLimb.widen addendSignificand)
      addendExponent
  have hresult :
      result.toNat < format.modulus := by
    rw [NativeLimbPacked.SignedSum.roundFieldsWord_toNat format hlimb]
    exact NativeLimbRounding.roundCodeNat_lt_modulus format hlimb _
  change result.lo.toNat =
    NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
      (Dyadic.fmaFields
        leftNegative leftSignificand.toNat leftExponent
        rightNegative rightSignificand.toNat rightExponent
        addendNegative addendSignificand.toNat addendExponent)
  calc
    result.lo.toNat = result.toNat :=
      FixedWord.UInt128.lo_toNat_eq_toNat_of_lt_two_pow result <| by
        exact hresult.trans_le <|
          NativeWord.modulus_le_two_pow_64 format heligible
    _ = NativeLimbRounding.roundCodeNat format hlimb
          (Dyadic.addFields
            (Bool.xor leftNegative rightNegative) product.toNat
            (leftExponent + rightExponent)
            addendNegative
              (NativeWordLimb.widen addendSignificand).toNat
              addendExponent) :=
      NativeLimbPacked.SignedSum.roundFieldsWord_toNat
        format hlimb
        (Bool.xor leftNegative rightNegative) product
        (leftExponent + rightExponent)
        addendNegative (NativeWordLimb.widen addendSignificand)
        addendExponent
    _ = DirectDyadicPacking.roundCode format
          (Dyadic.addFields
            (Bool.xor leftNegative rightNegative) product.toNat
            (leftExponent + rightExponent)
            addendNegative
              (NativeWordLimb.widen addendSignificand).toNat
              addendExponent) :=
      NativeLimbRounding.roundCodeNat_eq_direct format hlimb _
    _ = DirectDyadicPacking.roundCode format
          (Dyadic.fmaFields
            leftNegative leftSignificand.toNat leftExponent
            rightNegative rightSignificand.toNat rightExponent
            addendNegative addendSignificand.toNat addendExponent) := by
      unfold Dyadic.fmaFields
      rw [FixedWord.mul64_toNat,
        NativeWordLimb.widen_toNat]
    _ = NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
          (Dyadic.fmaFields
            leftNegative leftSignificand.toNat leftExponent
            rightNegative rightSignificand.toNat rightExponent
            addendNegative addendSignificand.toNat addendExponent) :=
      (NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct
        format heligible _).symm

/-- Capacity-directed fused accumulation implements exact FMA. -/
theorem roundFmaFieldsWord_toNat
    (format : Format) (heligible : NativeWord.Eligible format)
    (leftNegative : Bool) (leftSignificand : UInt64) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : UInt64) (rightExponent : Int)
    (addendNegative : Bool) (addendSignificand : UInt64) (addendExponent : Int) :
    (roundFmaFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent
        addendNegative addendSignificand addendExponent).toNat =
      NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat format heligible
        (Dyadic.fmaFields
          leftNegative leftSignificand.toNat leftExponent
          rightNegative rightSignificand.toNat rightExponent
          addendNegative addendSignificand.toNat addendExponent) := by
  unfold roundFmaFieldsWord
  by_cases hhigh :
      (FixedWord.mul64 leftSignificand rightSignificand).hi = 0
  · simp only [beq_iff_eq, hhigh, if_true]
    rw [roundFieldsWord_toNat,
      FixedWord.mul64_lo_toNat_of_hi_eq_zero
        leftSignificand rightSignificand hhigh]
    rfl
  · simp only [beq_iff_eq, hhigh, if_false]
    exact roundWideFmaFieldsWord_toNat format heligible
      leftNegative leftSignificand leftExponent
      rightNegative rightSignificand rightExponent
      addendNegative addendSignificand addendExponent

/-- Packed native FMA returns the flattened exact fused code. -/
theorem fmaWordsCodeWordValid_toNat
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right addend : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus)
    (haddend : addend.toNat < format.modulus) :
    (fmaWordsCodeWordValid heligible
        left right addend hleft hright haddend).toNat =
      NativeWordArithmetic.fmaWordsCodeFlatValid
        heligible left right addend hleft hright haddend := by
  unfold fmaWordsCodeWordValid NativeWordArithmetic.fmaWordsCodeFlatValid
  rw [NativeWord.withThreeDyadicWordFieldsValid_toNat,
    NativeWord.signMaskWord_toNat format
      heligible]
  simp only [roundFmaFieldsWord_toNat]
  rfl

/-- Every packed native addition result is a complete in-range Posit encoding. -/
theorem addWordsCodeWordValid_lt_modulus
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    (addWordsCodeWordValid heligible left right hleft hright).toNat <
      format.modulus := by
  rw [addWordsCodeWordValid_toNat]
  exact NativeWordArithmetic.addWordsCodeFlatValid_lt_modulus
    heligible left right hleft hright

/-- Every packed native subtraction result is a complete in-range Posit encoding. -/
theorem subWordsCodeWordValid_lt_modulus
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    (subWordsCodeWordValid heligible left right hleft hright).toNat <
      format.modulus := by
  rw [subWordsCodeWordValid_toNat]
  exact NativeWordArithmetic.subWordsCodeFlatValid_lt_modulus
    heligible left right hleft hright

/-- Every packed native FMA result is a complete in-range Posit encoding. -/
theorem fmaWordsCodeWordValid_lt_modulus
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right addend : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus)
    (haddend : addend.toNat < format.modulus) :
    (fmaWordsCodeWordValid heligible
        left right addend hleft hright haddend).toNat <
      format.modulus := by
  rw [fmaWordsCodeWordValid_toNat]
  exact NativeWordArithmetic.fmaWordsCodeFlatValid_lt_modulus
    heligible left right addend hleft hright haddend

end FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedSignedSum
