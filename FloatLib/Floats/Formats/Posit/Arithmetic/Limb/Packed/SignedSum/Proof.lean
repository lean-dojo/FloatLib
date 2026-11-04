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
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Boundary.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.SignedSum.Runtime

/-!
# Correctness of packed two-limb Posit sums

A packed two-limb sum decodes natively, aligns, accumulates signed magnitudes, and rounds. We
show here that this whole pipeline is exact dyadic addition and subtraction. The capacity
branch runs only when an aligned intermediate really is wider than two limbs. It has the same
exact semantics.
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
Two-limb signed-magnitude accumulation rounds like the exact common-exponent field sum. A zero
operand leaves the other one, and a zero sum rounds to zero whatever its sign.
-/
private theorem roundCodeNat_addSignedMagnitudes128
    (format : Format) (heligible : NativeLimb.Eligible format)
    (leftNegative rightNegative : Bool)
    (leftSignificand rightSignificand : FixedWord.UInt128) (exponent : Int)
    (hsum :
      leftNegative = rightNegative →
        leftSignificand.toNat + rightSignificand.toNat < 2 ^ 128) :
    NativeLimbRounding.roundCodeNat format heligible
        { negative :=
            (FixedWord.addSignedMagnitudes128
              leftNegative rightNegative leftSignificand rightSignificand).1
          significand :=
            (FixedWord.addSignedMagnitudes128
              leftNegative rightNegative leftSignificand rightSignificand).2.toNat
          exponent } =
      NativeLimbRounding.roundCodeNat format heligible
        (Dyadic.addFields
          leftNegative leftSignificand.toNat exponent
          rightNegative rightSignificand.toNat exponent) := by
  by_cases hnonzero : leftSignificand.toNat ≠ 0 ∧ rightSignificand.toNat ≠ 0
  · rw [roundCodeNat_eq_signedMagnitudeDyadic128,
      FixedWord.signedMagnitudeDyadic128_addSignedMagnitudes128_eq_addFields
        leftNegative rightNegative leftSignificand rightSignificand exponent
        hnonzero.1 hnonzero.2 hsum]
  -- One operand is zero: the kernel returns the other operand's sign and magnitude.
  have hzeroCode (value : FloatLib.Numerics.Dyadic) (hvalue : value.significand = 0) :
      NativeLimbRounding.roundCodeNat format heligible value = 0 := by
    simp [NativeLimbRounding.roundCodeNat, hvalue]
  by_cases hsame : leftNegative = rightNegative
  · subst rightNegative
    have hadd := FixedWord.add128_value_toNat_of_lt leftSignificand rightSignificand (hsum rfl)
    by_cases hleft : leftSignificand.toNat = 0
    · by_cases hright : rightSignificand.toNat = 0
      · rw [hzeroCode _ (by simp [FixedWord.addSignedMagnitudes128, hadd, hleft, hright]),
          hzeroCode _ (by simp [Dyadic.addFields, hleft, hright])]
      · simp [FixedWord.addSignedMagnitudes128, hadd, hleft, hright, Dyadic.addFields]
    · have hright : rightSignificand.toNat = 0 := by tauto
      simp [FixedWord.addSignedMagnitudes128, hadd, hleft, hright, Dyadic.addFields]
  · have hsameBool : (leftNegative == rightNegative) = false := by
      simpa using hsame
    by_cases hequal : leftSignificand = rightSignificand
    · subst rightSignificand
      have hleft : leftSignificand.toNat = 0 := by tauto
      rw [hzeroCode _
          (by simp [FixedWord.addSignedMagnitudes128, hsameBool, FixedWord.UInt128.toNat]),
        hzeroCode _ (by simp [Dyadic.addFields, hleft])]
    · by_cases hleft : leftSignificand.toNat = 0
      · have hright : rightSignificand.toNat ≠ 0 := fun hright =>
          hequal (FixedWord.UInt128.toNat_injective (hleft.trans hright.symm))
        have hless : FixedWord.UInt128.less leftSignificand rightSignificand = true := by
          rw [FixedWord.UInt128.less_eq_true_iff]
          omega
        have hsub := FixedWord.UInt128.sub_toNat rightSignificand leftSignificand (by omega)
        simp [FixedWord.addSignedMagnitudes128, hsameBool, hequal, hless, hsub, hleft, hright,
          Dyadic.addFields]
      · have hright : rightSignificand.toNat = 0 := by tauto
        have hless : FixedWord.UInt128.less leftSignificand rightSignificand = false := by
          rw [Bool.eq_false_iff, ne_eq, FixedWord.UInt128.less_eq_true_iff]
          omega
        have hsub := FixedWord.UInt128.sub_toNat leftSignificand rightSignificand (by omega)
        simp [FixedWord.addSignedMagnitudes128, hsameBool, hequal, hless, hsub, hleft, hright,
          Dyadic.addFields]

/--
The aligned two-limb signed-magnitude kernel rounds the exact common-exponent sum.

Same-sign overflow is the only branch whose exact magnitude can require more than 128 bits.
-/
theorem roundAlignedFieldsWord_toNat
    (format : Format) (heligible : NativeLimb.Eligible format)
    (leftNegative : Bool) (leftSignificand : FixedWord.UInt128)
    (rightNegative : Bool) (rightSignificand : FixedWord.UInt128)
    (exponent : Int) :
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
      rw [NativeLimbRounding.GuardSticky.roundCodeWord_toNat]
      simpa [FixedWord.addSignedMagnitudes128] using
        roundCodeNat_addSignedMagnitudes128 format heligible leftNegative leftNegative
          leftSignificand rightSignificand exponent (fun _ => hsum)
    · simp only [beq_iff_eq, hcarry, ite_false]
      exact roundCapacityFieldsWord_toNat format heligible
        leftNegative leftSignificand exponent
        leftNegative rightSignificand exponent
  · simp only [beq_iff_eq, hsame, ite_false]
    rw [NativeLimbRounding.GuardSticky.roundCodeWord_toNat]
    exact roundCodeNat_addSignedMagnitudes128 format heligible leftNegative rightNegative
      leftSignificand rightSignificand exponent (fun equality => (hsame equality).elim)

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
  · rw [roundAlignedFieldsWord_toNat format heligible,
      FixedWord.DyadicCompare.shiftLeft128_toNat rightSignificand _ hfit,
      Dyadic.addFields_eq, Dyadic.addFields_eq,
      Dyadic.add_align_right_to_left_exponent _ _ _ _ _ _ hleft hexponents]
    rfl
  · exact roundCapacityFieldsWord_toNat format heligible _ _ _ _ _ _
  · exact roundCapacityFieldsWord_toNat format heligible _ _ _ _ _ _
  · rw [roundAlignedFieldsWord_toNat format heligible,
      FixedWord.DyadicCompare.shiftLeft128_toNat leftSignificand _ hfit,
      Dyadic.addFields_eq, Dyadic.addFields_eq,
      Dyadic.add_align_left_to_right_exponent _ _ _ _ _ _ hright (lt_of_not_ge hexponents)]
    rfl
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
  refine Boundary.withTwoDyadicFields_toNat_eq_binaryCode heligible left right _ _ ?_
  intro leftNegative leftSignificand leftExponent rightNegative rightSignificand rightExponent
  rw [roundFieldsWord_toNat, Dyadic.addFields_eq]

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
  refine Boundary.withTwoDyadicFields_toNat_eq_binaryCode heligible left right _ _ ?_
  intro leftNegative leftSignificand leftExponent rightNegative rightSignificand rightExponent
  rw [roundFieldsWord_toNat, ← Dyadic.subFields_eq]
  rfl

end FloatLib.Floats.Formats.Posit.Model.NativeLimbPacked.SignedSum
