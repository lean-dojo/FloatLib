/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.DyadicCompare.Proof
public import FloatLib.Kernels.FixedWord.SignedMagnitude.UInt128.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Decode.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Rounding.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Boundary.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.SignedSum.Runtime

/-!
# Correctness of packed two-limb Posit sums

Native decoding, alignment, signed-magnitude accumulation, and rounding implement exact dyadic
addition and subtraction. The capacity branch is used only when an aligned intermediate genuinely
exceeds two limbs; it shares the same exact semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked.SignedSum

open FloatLib.Numerics

/-- Converting an exact capacity result back to two limbs preserves its complete code. -/
theorem roundCapacityFieldsWord_toNat
    (format : Format) (heligible : NativeLimb.Eligible format)
    (leftNegative : Bool) (leftSignificand : FixedWord.UInt128)
    (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : FixedWord.UInt128)
    (rightExponent : Int) :
    (roundCapacityFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent).toNat =
      NativeLimbRounding.roundCodeNat format heligible
        (Dyadic.addFields
          leftNegative leftSignificand.toNat leftExponent
          rightNegative rightSignificand.toNat rightExponent) := by
  unfold roundCapacityFieldsWord
  apply FixedWord.UInt128.toNat_ofNat
  exact lt_of_lt_of_le
    (NativeLimbRounding.roundCodeNat_lt_modulus format heligible _)
    (by
      unfold Format.modulus NativeLimb.Eligible at *
      exact Nat.pow_le_pow_right (by decide) heligible)

/-- Exact Posit rounding ignores the unused sign and exponent attached to zero magnitude. -/
private theorem roundCodeNat_eq_signedMagnitudeDyadic128
    (format : Format) (heligible : NativeLimb.Eligible format)
    (negative : Bool) (magnitude : FixedWord.UInt128) (exponent : Int) :
    NativeLimbRounding.roundCodeNat format heligible
        { negative, significand := magnitude.toNat, exponent } =
      NativeLimbRounding.roundCodeNat format heligible
        (FixedWord.signedMagnitudeDyadic128 negative magnitude exponent) := by
  by_cases hzero : magnitude.toNat = 0
  · have hsigned :
        FixedWord.signedMagnitudeDyadic128
            negative magnitude exponent =
          FloatLib.Numerics.Dyadic.zero := by
      cases negative <;>
        simp [FixedWord.signedMagnitudeDyadic128, hzero]
    rw [hsigned]
    simp only [NativeLimbRounding.roundCodeNat, hzero,
      beq_self_eq_true, FloatLib.Numerics.Dyadic.zero_significand,
      ite_true]
  · rw [FixedWord.signedMagnitudeDyadic128_eq_of_toNat_ne_zero
      negative magnitude exponent hzero]

/--
The aligned two-limb signed-magnitude kernel rounds the exact common-exponent sum.

The caller handles zero operands before alignment. Same-sign overflow is the only branch whose
exact magnitude can require more than 128 bits.
-/
theorem roundAlignedFieldsWord_toNat
    (format : Format) (heligible : NativeLimb.Eligible format)
    (leftNegative : Bool) (leftSignificand : FixedWord.UInt128)
    (rightNegative : Bool) (rightSignificand : FixedWord.UInt128)
    (exponent : Int)
    (hleft : leftSignificand.toNat ≠ 0)
    (hright : rightSignificand.toNat ≠ 0) :
    (roundAlignedFieldsWord format heligible
        leftNegative leftSignificand
        rightNegative rightSignificand exponent).toNat =
      NativeLimbRounding.roundCodeNat format heligible
        (Dyadic.addFields
          leftNegative leftSignificand.toNat exponent
          rightNegative rightSignificand.toNat exponent) := by
  unfold roundAlignedFieldsWord
  by_cases hsame : leftNegative = rightNegative
  · subst rightNegative
    simp only [beq_self_eq_true, ite_true]
    by_cases hcarry :
        (FixedWord.add128 leftSignificand rightSignificand).carry = 0
    · simp only [beq_iff_eq, hcarry, ite_true]
      have hadd :=
        FixedWord.add128_toNat leftSignificand rightSignificand
      simp only [hcarry, UInt64.toNat_zero, zero_mul, add_zero] at hadd
      have hsum :
          leftSignificand.toNat + rightSignificand.toNat < 2 ^ 128 := by
        rw [← hadd]
        exact
          (FixedWord.add128 leftSignificand rightSignificand).value.toNat_lt
      have hexact :=
        FixedWord.signedMagnitudeDyadic128_addSignedMagnitudes128_eq_addFields
          leftNegative leftNegative leftSignificand rightSignificand exponent
          hleft hright (fun _ => hsum)
      rw [NativeLimbRounding.GuardSticky.roundCodeWord_toNat]
      rw [roundCodeNat_eq_signedMagnitudeDyadic128]
      simpa [FixedWord.addSignedMagnitudes128] using
        congrArg (NativeLimbRounding.roundCodeNat format heligible) hexact
    · simp only [beq_iff_eq, hcarry, ite_false]
      exact roundCapacityFieldsWord_toNat format heligible
        leftNegative leftSignificand exponent
        leftNegative rightSignificand exponent
  · simp only [beq_iff_eq, hsame, ite_false]
    have hexact :=
      FixedWord.signedMagnitudeDyadic128_addSignedMagnitudes128_eq_addFields
        leftNegative rightNegative leftSignificand rightSignificand exponent
        hleft hright (fun equality => (hsame equality).elim)
    rw [NativeLimbRounding.GuardSticky.roundCodeWord_toNat]
    rw [roundCodeNat_eq_signedMagnitudeDyadic128]
    exact congrArg (NativeLimbRounding.roundCodeNat format heligible) hexact

/-- Native exponent alignment and its exact capacity branch round the same dyadic sum. -/
theorem roundFieldsWord_toNat
    (format : Format) (heligible : NativeLimb.Eligible format)
    (leftNegative : Bool) (leftSignificand : FixedWord.UInt128)
    (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : FixedWord.UInt128)
    (rightExponent : Int) :
    (roundFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent).toNat =
      NativeLimbRounding.roundCodeNat format heligible
        (Dyadic.addFields
          leftNegative leftSignificand.toNat leftExponent
          rightNegative rightSignificand.toNat rightExponent) := by
  unfold roundFieldsWord
  simp only [NativeLimb.isZero_eq_true_iff]
  split_ifs with hleft hright hexponents hshift hfit hshift hfit
  · rw [NativeLimbRounding.GuardSticky.roundCodeWord_toNat format heligible]
    by_cases hrightNat : rightSignificand.toNat = 0
    · simp [Dyadic.addFields, hleft, hrightNat, NativeLimbRounding.roundCodeNat]
    · simp [Dyadic.addFields, hleft, hrightNat]
  · rw [NativeLimbRounding.GuardSticky.roundCodeWord_toNat format heligible]
    simp [Dyadic.addFields, hleft, hright]
  · have hshifted :=
      FixedWord.DyadicCompare.shiftLeft128_toNat rightSignificand _ hshift hfit
    have hshiftedNe :
        rightSignificand.toNat <<< (rightExponent - leftExponent).toNat ≠ 0 :=
      Nat.shiftLeft_eq_zero_iff.not.mpr hright
    rw [roundAlignedFieldsWord_toNat format heligible _ _ _ _ _ hleft
      (by rw [hshifted]; exact hshiftedNe)]
    congr 1
    simp [Dyadic.addFields, hleft, hright, hshiftedNe, hexponents, hshifted]
  · exact roundCapacityFieldsWord_toNat format heligible _ _ _ _ _ _
  · exact roundCapacityFieldsWord_toNat format heligible _ _ _ _ _ _
  · have hshifted :=
      FixedWord.DyadicCompare.shiftLeft128_toNat leftSignificand _ hshift hfit
    have hshiftedNe :
        leftSignificand.toNat <<< (leftExponent - rightExponent).toNat ≠ 0 :=
      Nat.shiftLeft_eq_zero_iff.not.mpr hleft
    rw [roundAlignedFieldsWord_toNat format heligible _ _ _ _ _
      (by rw [hshifted]; exact hshiftedNe) hright]
    congr 1
    simp [Dyadic.addFields, hleft, hright, hshiftedNe, hexponents, hshifted]
  · exact roundCapacityFieldsWord_toNat format heligible _ _ _ _ _ _
  · exact roundCapacityFieldsWord_toNat format heligible _ _ _ _ _ _

/-- Packed two-limb addition returns the exact complete Posit code. -/
theorem addWordsCodeWord_toNat
    {format : Format}
    (heligible : NativeLimb.Eligible format)
    (left right : FixedWord.UInt128) :
    (addWordsCodeWord heligible left right).toNat =
      Boundary.binaryCode format.signMaskNat
        (fun leftValue rightValue =>
          NativeLimbRounding.roundCodeNat format heligible
            (FloatLib.Numerics.Dyadic.add leftValue rightValue))
        (NativeLimb.toDyadic? format left)
        (NativeLimb.toDyadic? format right) := by
  unfold addWordsCodeWord
  rw [NativeLimb.map_withTwoDyadicFields_eq_match_toDyadic?
    FixedWord.UInt128.toNat format left right
    (NativeLimb.signMaskWord format)
    (fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      roundFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent)
    (fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      NativeLimbRounding.roundCodeNat format heligible
        (Dyadic.addFields
          leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent))
    (roundFieldsWord_toNat format heligible),
    NativeLimb.signMaskWord_toNat format heligible]
  unfold Boundary.binaryCode Boundary.binaryResult
  cases NativeLimb.toDyadic? format left with
  | none => rfl
  | some leftValue =>
      cases NativeLimb.toDyadic? format right with
      | none => rfl
      | some rightValue =>
          simp only
          rw [Dyadic.addFields_eq]

/-- Packed two-limb subtraction returns the exact complete Posit code. -/
theorem subWordsCodeWord_toNat
    {format : Format}
    (heligible : NativeLimb.Eligible format)
    (left right : FixedWord.UInt128) :
    (subWordsCodeWord heligible left right).toNat =
      Boundary.binaryCode format.signMaskNat
        (fun leftValue rightValue =>
          NativeLimbRounding.roundCodeNat format heligible
            (FloatLib.Numerics.Dyadic.sub leftValue rightValue))
        (NativeLimb.toDyadic? format left)
        (NativeLimb.toDyadic? format right) := by
  unfold subWordsCodeWord
  rw [NativeLimb.map_withTwoDyadicFields_eq_match_toDyadic?
    FixedWord.UInt128.toNat format left right
    (NativeLimb.signMaskWord format)
    (fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      roundFieldsWord format heligible
        leftNegative leftSignificand leftExponent
        (!rightNegative) rightSignificand rightExponent)
    (fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      NativeLimbRounding.roundCodeNat format heligible
        (Dyadic.addFields
          leftNegative leftSignificand leftExponent
          (!rightNegative) rightSignificand rightExponent))
    (fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      roundFieldsWord_toNat format heligible
        leftNegative leftSignificand leftExponent
        (!rightNegative) rightSignificand rightExponent),
    NativeLimb.signMaskWord_toNat format heligible]
  unfold Boundary.binaryCode Boundary.binaryResult
  cases NativeLimb.toDyadic? format left with
  | none => rfl
  | some leftValue =>
      cases NativeLimb.toDyadic? format right with
      | none => rfl
      | some rightValue =>
          simp only
          change
            NativeLimbRounding.roundCodeNat format heligible
                (FloatLib.Numerics.Dyadic.subFields
                  leftValue.negative leftValue.significand leftValue.exponent
                  rightValue.negative rightValue.significand
                    rightValue.exponent) =
              NativeLimbRounding.roundCodeNat format heligible
                (FloatLib.Numerics.Dyadic.sub leftValue rightValue)
          rw [FloatLib.Numerics.Dyadic.subFields_eq]

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked.SignedSum
