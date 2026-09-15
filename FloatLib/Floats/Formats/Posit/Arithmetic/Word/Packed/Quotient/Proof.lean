/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Quotient.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Elimination.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Direct.Proof
public import FloatLib.Kernels.FixedWord.Quotient.Restoring128Proof
import FloatLib.Floats.Formats.Posit.Arithmetic.WordLimb.Proof

/-!
# Correctness of packed native-word Posit division

The packed divider is a storage adapter over the width-generic quotient-prefix kernel. These
theorems connect its decoded field boundary to the model-valued quotient semantics and prove that
both natural and `UInt64` results are complete in-range Posit encodings.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedQuotient

open FloatLib.Numerics
open FloatLib.Numerics.FixedWord
open FloatLib.Floats.Formats.Posit.Model.StickyPrefix
open FloatLib.Numerics.FixedWord.RestoringQuotient

/-! ## Mathematical views and common-leading normalization -/

/-- Exact mathematical view of positive decoded native fields. -/
def positiveDyadic
    (significand : UInt64) (exponent : Int) : FloatLib.Numerics.Dyadic :=
  { negative := false
    significand := significand.toNat
    exponent }

/-- Agreement between the one-word normalizer and the arbitrary-width normalizer. -/
private structure NormalizationAgreement
    (native : NormalizedWords)
    (exact : DirectDyadicQuotient.NormalizedSignificands) : Prop where
  numerator_eq : native.numerator.toNat = exact.numerator
  denominator_eq : native.denominator.toNat = exact.denominator
  numeratorLeading_eq :
    native.numeratorLeading = exact.numeratorLeading
  denominatorLeading_eq :
    native.denominatorLeading = exact.denominatorLeading

/--
Shifting a nonzero word up to a common leading position below the word width agrees with the
natural-number shift.
-/
private theorem shiftLeft_toCommon_toNat
    (value : UInt64) (common : Nat)
    (hvalue : value ≠ 0)
    (hleading : value.toNat.log2 ≤ common)
    (hcommon : common < 64) :
    (value <<< UInt64.ofNat (common - value.toNat.log2)).toNat =
      value.toNat <<< (common - value.toNat.log2) := by
  have hvalueNat : value.toNat ≠ 0 :=
    (FixedWord.uint64_toNat_eq_zero value).not.mpr hvalue
  have hbounds :=
    DirectDyadicQuotient.shiftToCommon_bounds value.toNat common hvalueNat hleading
  exact FixedWord.shiftLeft_toNat value _ (by omega)
    (hbounds.2.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))

/-- Native common-leading normalization is exactly the arbitrary-width normalization. -/
private theorem normalizeWords_toNat
    (numerator denominator : UInt64)
    (hnumerator : numerator ≠ 0)
    (hdenominator : denominator ≠ 0) :
    let native := normalizeWords numerator denominator
    let exact :=
      DirectDyadicQuotient.normalizeSignificands
        numerator.toNat denominator.toNat
    NormalizationAgreement native exact := by
  have hnumeratorLt : numerator.toNat.log2 < 64 :=
    (Nat.log2_lt ((FixedWord.uint64_toNat_eq_zero numerator).not.mpr hnumerator)).2
      numerator.toNat_lt
  have hdenominatorLt : denominator.toNat.log2 < 64 :=
    (Nat.log2_lt ((FixedWord.uint64_toNat_eq_zero denominator).not.mpr hdenominator)).2
      denominator.toNat_lt
  have hnumeratorShift :=
    shiftLeft_toCommon_toNat numerator (max numerator.toNat.log2 denominator.toNat.log2)
      hnumerator (Nat.le_max_left _ _) (by omega)
  have hdenominatorShift :=
    shiftLeft_toCommon_toNat denominator (max numerator.toNat.log2 denominator.toNat.log2)
      hdenominator (Nat.le_max_right _ _) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [normalizeWords, DirectDyadicQuotient.normalizeSignificands, FixedWord.log2_toNat,
      hnumeratorShift, hdenominatorShift]

/-! ## Quotient-prefix refinement -/

/-- Native remainder jamming is exactly the representation-independent sticky operation. -/
private theorem jamState_toNat
    (state : QuotientState UInt128) :
    (jamState state).toNat =
      jamRemainder state.quotient.toNat state.remainder.toNat := by
  unfold jamState jamRemainder
  by_cases hhi : state.remainder.hi = 0
  · by_cases hlo : state.remainder.lo = 0
    · simp [hhi, hlo, UInt128.toNat]
    · have hnonzero : state.remainder.toNat ≠ 0 := by
        unfold UInt128.toNat
        have hloNat : state.remainder.lo.toNat ≠ 0 := by
          simpa [← UInt64.toNat_inj] using hlo
        omega
      simp only [hhi, beq_self_eq_true, Bool.true_and, hlo,
        beq_iff_eq, ite_false, hnonzero]
      rw [UInt128.setLowBit_toNat]
  · have hnonzero : state.remainder.toNat ≠ 0 := by
      unfold UInt128.toNat
      have hhiPositive : 0 < state.remainder.hi.toNat := by
        have : state.remainder.hi.toNat ≠ 0 := by
          simpa [← UInt64.toNat_inj] using hhi
        omega
      omega
    simp [hhi, hnonzero, UInt128.setLowBit_toNat]

/-- A quotient prefix generated from nonzero magnitudes has a nonzero leading bit. -/
private theorem quotientPrefix_significand_ne_zero
    (format : Format)
    (numerator denominator : FloatLib.Numerics.Dyadic)
    (hnumerator : numerator.significand ≠ 0)
    (hdenominator : denominator.significand ≠ 0) :
    (DirectDyadicQuotient.quotientPrefix format numerator denominator).significand ≠
      0 := by
  have hbounds :=
    DirectDyadicQuotient.prefixAtLeading_significand_bounds
      (DirectDyadicQuotient.prefixLeading format)
      numerator denominator hnumerator hdenominator
  unfold DirectDyadicQuotient.quotientPrefix
  exact ne_of_gt
    ((Nat.two_pow_pos (DirectDyadicQuotient.prefixLeading format)).trans_le
      hbounds.1)

/-- Rebuilding a quotient prefix from its positive fields preserves the prefix. -/
private theorem quotientPrefix_eq_positiveFields
    (format : Format)
    (numerator denominator : FloatLib.Numerics.Dyadic) :
    {
      negative := false
      significand :=
        (DirectDyadicQuotient.quotientPrefix format
          numerator denominator).significand
      exponent :=
        (DirectDyadicQuotient.quotientPrefix format
          numerator denominator).exponent
    } =
      DirectDyadicQuotient.quotientPrefix format numerator denominator := by
  unfold DirectDyadicQuotient.quotientPrefix
    DirectDyadicQuotient.prefixAtLeading
  rfl

/--
The two-limb restoring loop on a normalized one-word ratio computes the Euclidean quotient and
remainder of the scaled numerator.
-/
private theorem quotientSteps128_normalized_toNat
    (numerator denominator : UInt64) (steps : Nat)
    (hdenominator : denominator ≠ 0) (hsteps : steps ≤ 64) :
    let state :=
      quotientSteps128 (NativeWordLimb.widen denominator) steps
        { quotient := NativeWordLimb.widen (numerator / denominator)
          remainder := NativeWordLimb.widen (numerator % denominator) }
    state.quotient.toNat = numerator.toNat * 2 ^ steps / denominator.toNat ∧
      state.remainder.toNat = numerator.toNat * 2 ^ steps % denominator.toNat := by
  have hdenominatorPos : 0 < denominator.toNat :=
    Nat.pos_of_ne_zero ((FixedWord.uint64_toNat_eq_zero denominator).not.mpr hdenominator)
  have hdivision :=
    quotientSteps128_div_mod (NativeWordLimb.widen denominator) steps
      { quotient := NativeWordLimb.widen (numerator / denominator)
        remainder := NativeWordLimb.widen (numerator % denominator) }
      (by
        simp only [NativeWordLimb.widen_toNat]
        exact denominator.toNat_lt.trans (Nat.pow_lt_pow_right (by decide) (by decide)))
      (by
        simp only [NativeWordLimb.widen_toNat, UInt64.toNat_mod]
        exact Nat.mod_lt _ hdenominatorPos)
      (by
        simp only [NativeWordLimb.widen_toNat, UInt64.toNat_div]
        calc (numerator.toNat / denominator.toNat + 1) * 2 ^ steps ≤ 2 ^ 64 * 2 ^ 64 :=
              Nat.mul_le_mul
                (by have := Nat.div_le_self numerator.toNat denominator.toNat
                    have := numerator.toNat_lt
                    omega)
                (Nat.pow_le_pow_right (by decide) hsteps)
          _ = 2 ^ 128 := by rw [← pow_add])
  simpa only [NativeWordLimb.widen_toNat, UInt64.toNat_div, UInt64.toNat_mod,
    Nat.div_add_mod'] using hdivision

/--
The native restoring loop generates exactly the arbitrary-width quotient prefix.
-/
private theorem quotientPrefixWord_toNat
    (format : Format) (heligible : NativeWord.Eligible format)
    (numeratorSignificand : UInt64) (numeratorExponent : Int)
    (denominatorSignificand : UInt64) (denominatorExponent : Int)
    (hnumerator : numeratorSignificand ≠ 0)
    (hdenominator : denominatorSignificand ≠ 0) :
    let native :=
      quotientPrefixWord format
        numeratorSignificand numeratorExponent
        denominatorSignificand denominatorExponent
    let exact :=
      DirectDyadicQuotient.quotientPrefix format
        (positiveDyadic numeratorSignificand numeratorExponent)
        (positiveDyadic denominatorSignificand denominatorExponent)
    native.significand.toNat = exact.significand ∧
      native.exponent = exact.exponent := by
  obtain ⟨hnumeratorEq, hdenominatorEq, hnumeratorLeading, hdenominatorLeading⟩ :=
    normalizeWords_toNat numeratorSignificand denominatorSignificand hnumerator hdenominator
  have hspec :=
    DirectDyadicQuotient.normalizeSignificands_spec
      numeratorSignificand.toNat denominatorSignificand.toNat
      ((FixedWord.uint64_toNat_eq_zero _).not.mpr hnumerator)
      ((FixedWord.uint64_toNat_eq_zero _).not.mpr hdenominator)
  have hdenominatorWord :
      (normalizeWords numeratorSignificand denominatorSignificand).denominator ≠ 0 := by
    intro hzero
    rw [← FixedWord.uint64_toNat_eq_zero, hdenominatorEq] at hzero
    exact Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hspec.denominator_lower) hzero
  have hcomparison :
      ((normalizeWords numeratorSignificand denominatorSignificand).numerator <
          (normalizeWords numeratorSignificand denominatorSignificand).denominator) =
        ((DirectDyadicQuotient.normalizeSignificands
            numeratorSignificand.toNat denominatorSignificand.toNat).numerator <
          (DirectDyadicQuotient.normalizeSignificands
            numeratorSignificand.toNat denominatorSignificand.toNat).denominator) :=
    propext (by rw [UInt64.lt_iff_toNat_lt, hnumeratorEq, hdenominatorEq])
  have hstepsLe :
      (if (normalizeWords numeratorSignificand denominatorSignificand).numerator <
          (normalizeWords numeratorSignificand denominatorSignificand).denominator then
        format.payloadBits + 1
      else
        format.payloadBits) ≤ 64 := by
    unfold Format.payloadBits NativeWord.Eligible at *
    split <;> omega
  have hloop :=
    quotientSteps128_normalized_toNat
      (normalizeWords numeratorSignificand denominatorSignificand).numerator
      (normalizeWords numeratorSignificand denominatorSignificand).denominator _
      hdenominatorWord hstepsLe
  simp only [quotientPrefixWord, DirectDyadicQuotient.quotientPrefix,
    DirectDyadicQuotient.prefixAtLeading, DirectDyadicQuotient.prefixLeading, positiveDyadic]
  rw [jamState_toNat, hloop.1, hloop.2, hnumeratorEq, hdenominatorEq, hnumeratorLeading,
    hdenominatorLeading]
  simp only [hcomparison, Nat.shiftLeft_eq]
  exact ⟨rfl, rfl⟩

/-! ## Positive and signed field rounding -/

/--
The native guard/sticky packer applied to the native quotient prefix of nonzero fields is the
sign-restored arbitrary-width positive quotient code.
-/
private theorem roundCodeWord_quotientPrefixWord_toNat
    (format : Format) (heligible : NativeWord.Eligible format) (negative : Bool)
    (numeratorSignificand : UInt64) (numeratorExponent : Int)
    (denominatorSignificand : UInt64) (denominatorExponent : Int)
    (hnumerator : numeratorSignificand ≠ 0)
    (hdenominator : denominatorSignificand ≠ 0) :
    (NativeLimbRounding.GuardSticky.roundCodeWord format negative
        (quotientPrefixWord format
          numeratorSignificand numeratorExponent
          denominatorSignificand denominatorExponent).significand
        (quotientPrefixWord format
          numeratorSignificand numeratorExponent
          denominatorSignificand denominatorExponent).exponent).lo.toNat =
      DyadicRounding.restoreSignCode format negative
        (DirectDyadicQuotient.roundPositiveCode format
          (positiveDyadic numeratorSignificand numeratorExponent)
          (positiveDyadic denominatorSignificand denominatorExponent)) := by
  have hnumeratorNat : numeratorSignificand.toNat ≠ 0 :=
    (FixedWord.uint64_toNat_eq_zero numeratorSignificand).not.mpr hnumerator
  have hdenominatorNat : denominatorSignificand.toNat ≠ 0 :=
    (FixedWord.uint64_toNat_eq_zero denominatorSignificand).not.mpr hdenominator
  have hprefix :=
    quotientPrefixWord_toNat format heligible
      numeratorSignificand numeratorExponent
      denominatorSignificand denominatorExponent
      hnumerator hdenominator
  have hexactNonzero :=
    quotientPrefix_significand_ne_zero format
      (positiveDyadic numeratorSignificand numeratorExponent)
      (positiveDyadic denominatorSignificand denominatorExponent)
      hnumeratorNat hdenominatorNat
  rw [NativeWordLimb.roundCodeWordLow_toNat_eq_direct format heligible,
    DirectDyadicPacking.roundCode, DirectDyadicQuotient.roundPositiveCode, hprefix.1, hprefix.2,
    ite_eq_right, ite_eq_right]
  · simp only [DyadicRounding.magnitude]
    rw [quotientPrefix_eq_positiveFields]
  · simp [positiveDyadic, hnumeratorNat, hdenominatorNat]
  · simpa using hexactNonzero

/-- The positive native kernel is the shared arbitrary-width quotient rounder. -/
theorem roundPositiveCode_eq
    (format : Format) (heligible : NativeWord.Eligible format)
    (numeratorSignificand : UInt64) (numeratorExponent : Int)
    (denominatorSignificand : UInt64) (denominatorExponent : Int) :
    roundPositiveCode format
        numeratorSignificand numeratorExponent
        denominatorSignificand denominatorExponent =
      DirectDyadicQuotient.roundPositiveCode format
        (positiveDyadic numeratorSignificand numeratorExponent)
        (positiveDyadic denominatorSignificand denominatorExponent) := by
  unfold roundPositiveCode roundPositiveCodeWord
  by_cases hnumerator : numeratorSignificand = 0
  · simp [hnumerator, DirectDyadicQuotient.roundPositiveCode, positiveDyadic]
  by_cases hdenominator : denominatorSignificand = 0
  · simp [hdenominator, DirectDyadicQuotient.roundPositiveCode, positiveDyadic]
  rw [ite_eq_right (by simp [hnumerator, hdenominator]),
    roundCodeWord_quotientPrefixWord_toNat format heligible false
      numeratorSignificand numeratorExponent denominatorSignificand denominatorExponent
      hnumerator hdenominator]
  rfl

/-- The word-valued positive result is definitionally the natural API's code. -/
theorem roundPositiveCodeWord_toNat
    (format : Format) (_heligible : NativeWord.Eligible format)
    (numeratorSignificand : UInt64) (numeratorExponent : Int)
    (denominatorSignificand : UInt64) (denominatorExponent : Int) :
    (roundPositiveCodeWord format
        numeratorSignificand numeratorExponent
        denominatorSignificand denominatorExponent).toNat =
      roundPositiveCode format
        numeratorSignificand numeratorExponent
        denominatorSignificand denominatorExponent :=
  rfl

/-- Signed decoded-field rounding is the complete native-word quotient code. -/
theorem roundFields_eq
    (format : Format) (heligible : NativeWord.Eligible format)
    (numeratorNegative : Bool)
    (numeratorSignificand : UInt64) (numeratorExponent : Int)
    (denominatorNegative : Bool)
    (denominatorSignificand : UInt64) (denominatorExponent : Int) :
    roundFields format
        numeratorNegative numeratorSignificand numeratorExponent
        denominatorNegative denominatorSignificand denominatorExponent =
      DirectDyadicQuotient.roundCode format
        {
          negative := numeratorNegative
          significand := numeratorSignificand.toNat
          exponent := numeratorExponent
        }
        {
          negative := denominatorNegative
          significand := denominatorSignificand.toNat
          exponent := denominatorExponent
        } := by
  unfold roundFields roundFieldsWord DirectDyadicQuotient.roundCode
  by_cases hdenominator : denominatorSignificand = 0
  · simp [hdenominator, NativeWord.signMaskWord_toNat format heligible]
  have hdenominatorNat : denominatorSignificand.toNat ≠ 0 :=
    (FixedWord.uint64_toNat_eq_zero denominatorSignificand).not.mpr hdenominator
  by_cases hnumerator : numeratorSignificand = 0
  · simp [hdenominator, hnumerator, hdenominatorNat]
  have hnumeratorNat : numeratorSignificand.toNat ≠ 0 :=
    (FixedWord.uint64_toNat_eq_zero numeratorSignificand).not.mpr hnumerator
  simp only [hdenominator, hnumerator, hdenominatorNat, hnumeratorNat, beq_iff_eq, ite_false]
  rw [roundCodeWord_quotientPrefixWord_toNat format heligible _
    numeratorSignificand numeratorExponent denominatorSignificand denominatorExponent
    hnumerator hdenominator]
  rfl

/-- The word-valued signed result contains the complete scalar code. -/
theorem roundFieldsWord_toNat
    (format : Format) (_heligible : NativeWord.Eligible format)
    (numeratorNegative : Bool)
    (numeratorSignificand : UInt64) (numeratorExponent : Int)
    (denominatorNegative : Bool)
    (denominatorSignificand : UInt64) (denominatorExponent : Int) :
    (roundFieldsWord format
        numeratorNegative numeratorSignificand numeratorExponent
        denominatorNegative denominatorSignificand denominatorExponent).toNat =
      roundFields format
        numeratorNegative numeratorSignificand numeratorExponent
        denominatorNegative denominatorSignificand denominatorExponent :=
  rfl

/-! ## Packed carrier boundary -/

/-- The packed scalar quotient is the native-word quotient of the decoded operands. -/
theorem divWordsCodeValid_eq
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    divWordsCodeValid heligible left right hleft hright =
      match NativeWord.toDyadic? format left,
          NativeWord.toDyadic? format right with
      | some numerator, some denominator =>
          DirectDyadicQuotient.roundCode format
            numerator denominator
      | _, _ =>
          format.signMaskNat := by
  unfold divWordsCodeValid
  simp only [roundFields_eq format heligible]
  change
    NativeWord.withTwoDyadicFieldsValid format
        heligible
        left hleft right hright format.signMaskNat
        (fun leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent =>
          DirectDyadicQuotient.roundCode format
            {
              negative := leftNegative
              significand := leftSignificand
              exponent := leftExponent
            }
            {
              negative := rightNegative
              significand := rightSignificand
              exponent := rightExponent
            }) =
      _
  rw [NativeWord.withTwoDyadicFieldsValid_eq]
  rw [NativeWord.withTwoDyadicFields_eq]
  cases NativeWord.toDyadic? format left <;>
      cases NativeWord.toDyadic? format right <;>
    rfl

/-- The carrier-facing quotient word contains the exact scalar packed quotient code. -/
theorem divWordsCodeWordValid_toNat
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    (divWordsCodeWordValid heligible left right hleft hright).toNat =
      divWordsCodeValid heligible left right hleft hright := by
  unfold divWordsCodeWordValid divWordsCodeValid
  rw [NativeWord.withTwoDyadicWordFieldsValid_toNat,
    NativeWord.signMaskWord_toNat format
      heligible]
  simp only [roundFieldsWord_toNat format heligible]

/-- Every packed quotient is a complete in-range Posit encoding. -/
theorem divWordsCodeValid_lt_modulus
    {format : Format}
    (heligible : NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    divWordsCodeValid heligible left right hleft hright <
      format.modulus := by
  rw [divWordsCodeValid_eq]
  cases NativeWord.toDyadic? format left <;>
      cases NativeWord.toDyadic? format right <;>
    first
    | exact format.signMaskNat_lt_modulus
    | exact DirectDyadicQuotient.roundCode_lt_modulus format _ _

end FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic.PackedQuotient
