/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Decode.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Fields.Proof

/-!
# Correctness of native-word posit decoding

Candidate, finite, and total native-word decoders agree with the reference exact-width posit
model under their explicit storage and range contracts. Executable definitions live in
`FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Decode.Runtime`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWord

open FloatLib.Numerics

variable {format : Format}

/--
Native candidate decoding agrees with the exact posit field decoder.

The hypotheses are precisely the rounding-search invariant: the candidate is nonzero, lies below
the sign code, and the format plus its one-bit-wider threshold fit in a machine word.
-/
theorem nonnegativeDyadicAt_eq_decodeFields
    (format : Format) (code : UInt64)
    (heligible : CandidateEligible format)
    (hcode : code.toNat < format.signMaskNat)
    (hnonzero : code ≠ 0) :
    nonnegativeDyadicAt format code =
      (Model.ofNatBits (format := format) code.toNat).decodeFields.toDyadic := by
  let value := Model.ofNatBits (format := format) code.toNat
  have hsign : value.signBit = false :=
    Model.signBit_ofNatBits_eq_false format code.toNat hcode
  have hmagnitude : value.magnitudeBits = code.toNat :=
    Model.magnitudeBits_ofNatBits_of_lt_signMask format code.toNat hcode
  have hpayload : format.payloadBits ≤ 64 := by
    unfold CandidateEligible at heligible
    unfold Format.payloadBits
    omega
  have hrun :
      countLeadingRun code format.payloadBits
          (bitAt code (format.payloadBits - 1)) =
        value.regimeRunLength := by
    unfold Model.regimeRunLength Model.regimeBit
    rw [hmagnitude, ← bitAt_eq_testBit,
      countLeadingRun_eq_model]
  have htrailing : value.trailingBits ≤ format.payloadBits := by
    unfold Model.trailingBits
    omega
  have hfractionBits : value.fractionBits < 64 := by
    have hrun := Model.regimeRunLength_pos value
    have hfraction :=
      Model.regimeRunLength_add_fractionBits_le_payload value
    omega
  have husedExponentBits : value.usedExponentBits < 64 := by
    have hused : value.usedExponentBits ≤ format.exponentBits :=
      Model.usedExponentBits_le_exponentBits value
    simp only [Format.exponentBits] at hused
    omega
  have hcodeBool : (code == 0) = false :=
    beq_eq_false_iff_ne.mpr hnonzero
  unfold nonnegativeDyadicAt
  simp only [hcodeBool, Bool.false_eq_true, ite_false]
  rw [show bitAt code (format.payloadBits - 1) = value.regimeBit by
    unfold Model.regimeBit
    rw [hmagnitude, bitAt_eq_testBit]]
  rw [show
      countLeadingRun code format.payloadBits value.regimeBit =
        value.regimeRunLength by
    rw [countLeadingRun_eq_model]
    unfold Model.regimeRunLength
    rw [hmagnitude]]
  dsimp only [Model.DecodedFields.toDyadic, Model.decodeFields]
  change
    FloatLib.Numerics.Dyadic.mk false
        (lowBits code value.fractionBits |||
          (1 <<< UInt64.ofNat value.fractionBits)).toNat
        (value.regimeValue * 4 +
          Int.ofNat
            (Nat.shiftLeft
              (lowBits (shiftRight code value.fractionBits)
                value.usedExponentBits).toNat
              (2 - value.usedExponentBits)) -
          Int.ofNat value.fractionBits) =
      FloatLib.Numerics.Dyadic.mk value.signBit
        (2 ^ value.fractionBits + value.fractionField)
        value.scale
  rw [hsign, significand_toNat code value.fractionBits hfractionBits,
    shiftedLowBits_toNat code value.fractionBits value.usedExponentBits
      hfractionBits husedExponentBits]
  simp only [Model.fractionField, Model.storedExponentField,
    Model.exponentField, Model.scale, Format.exponentBits,
    Format.regimeExponentStep]
  rw [hmagnitude]
  simp [Nat.shiftLeft_eq]

/-- Native decoding agrees with the totalized exact-dyadic candidate decoder. -/
theorem nonnegativeDyadicAt_eq_model
    (format : Format) (code : UInt64)
    (heligible : CandidateEligible format)
    (hcode : code.toNat < format.signMaskNat) :
    nonnegativeDyadicAt format code =
      Model.DyadicRounding.nonnegativeDyadicAt format code.toNat := by
  by_cases hzero : code = 0
  · subst code
    change FloatLib.Numerics.Dyadic.zero =
      match (Model.zero format).decodeExact with
      | .zero => FloatLib.Numerics.Dyadic.zero
      | .finite fields => fields.toDyadic
      | .nar => FloatLib.Numerics.Dyadic.zero
    rw [Model.decodeExact_zero]
  · let value := Model.ofNatBits (format := format) code.toNat
    have hvalueBits : value.toNatBits = code.toNat :=
      Model.toNatBits_ofNatBits_of_lt code.toNat
        (hcode.trans format.signMaskNat_lt_modulus)
    have hvalueZero : value ≠ Model.zero format := by
      intro equality
      have bitsEquality := congrArg Model.toNatBits equality
      rw [hvalueBits, Model.zero_toNatBits] at bitsEquality
      exact hzero (UInt64.toNat_inj.mp (by simpa using bitsEquality))
    have hvalueNaR : value ≠ Model.nar format := by
      intro equality
      have bitsEquality := congrArg Model.toNatBits equality
      rw [hvalueBits, Model.nar_toNatBits] at bitsEquality
      omega
    rw [nonnegativeDyadicAt_eq_decodeFields format code heligible hcode hzero]
    unfold Model.DyadicRounding.nonnegativeDyadicAt
    have hnar : value.isNaR = false := by
      exact beq_eq_false_iff_ne.mpr hvalueNaR
    have hzeroValue : value.isZero = false := by
      exact beq_eq_false_iff_ne.mpr hvalueZero
    change value.decodeFields.toDyadic =
      match value.decodeExact with
      | .zero => FloatLib.Numerics.Dyadic.zero
      | .finite fields => fields.toDyadic
      | .nar => FloatLib.Numerics.Dyadic.zero
    have hdecode :
        value.decodeExact = .finite value.decodeFields := by
      simp [Model.decodeExact, hnar, hzeroValue]
    rw [hdecode]

/-- Direct native finite decoding agrees with the exact model. -/
theorem decodeFinite_eq_decodeFields
    (format : Format) (code : UInt64)
    (heligible : Eligible format)
    (hcode : code.toNat < format.modulus)
    (hnar :
      Model.ofNatBits (format := format) code.toNat ≠ Model.nar format)
    (hzero :
      Model.ofNatBits (format := format) code.toNat ≠ Model.zero format) :
    decodeFinite format code =
      (Model.ofNatBits (format := format) code.toNat).decodeFields.toDyadic := by
  let value := Model.ofNatBits (format := format) code.toNat
  let magnitude := UInt64.ofNat (magnitudeNat format code)
  have hmagnitudeNat :
      magnitudeNat format code = value.magnitudeBits :=
    magnitudeNat_eq_model format code hcode
  have hmagnitudeLt :
      value.magnitudeBits < format.signMaskNat :=
    Model.magnitudeBits_lt_signMask_of_ne_nar value hnar
  have hmagnitudeFit : value.magnitudeBits < 2 ^ 64 :=
    lt_of_lt_of_le
      (hmagnitudeLt.trans format.signMaskNat_lt_modulus)
      (by
        unfold Eligible at heligible
        unfold Format.modulus
        exact Nat.pow_le_pow_right (by decide) heligible)
  have hmagnitudeToNat : magnitude.toNat = value.magnitudeBits := by
    dsimp [magnitude]
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    · exact hmagnitudeNat
    · simpa only [hmagnitudeNat] using hmagnitudeFit
  have hmagnitudeNonzero :
      magnitude ≠ 0 := by
    intro equality
    have equalityNat := congrArg UInt64.toNat equality
    rw [hmagnitudeToNat] at equalityNat
    exact
      (Model.magnitudeBits_ne_zero_of_ne_zero value hzero)
        (by simpa using equalityNat)
  have hsign :
      value.signBit =
        decide (format.signMaskNat ≤ code.toNat) :=
    Model.signBit_ofNatBits_eq_decide format code.toNat hcode
  have hnative :
      nonnegativeDyadicAt format magnitude =
        (Model.ofNatBits
          (format := format) magnitude.toNat).decodeFields.toDyadic :=
    nonnegativeDyadicAt_eq_decodeFields format magnitude
      (candidateEligible_of_eligible format heligible)
      (by simpa [hmagnitudeToNat] using hmagnitudeLt)
      hmagnitudeNonzero
  have hmagnitudeModel :
      (Model.ofNatBits
        (format := format) magnitude.toNat).magnitudeBits =
          value.magnitudeBits := by
    rw [Model.magnitudeBits_ofNatBits_of_lt_signMask format magnitude.toNat
      (by simpa [hmagnitudeToNat] using hmagnitudeLt)]
    exact hmagnitudeToNat
  unfold decodeFinite
  change
    { nonnegativeDyadicAt format magnitude with
        negative := decide (format.signMaskNat ≤ code.toNat) } =
      value.decodeFields.toDyadic
  rw [hnative, ← hsign]
  exact decodeFields_toDyadic_eq_of_magnitudeBits_eq
    (Model.ofNatBits (format := format) magnitude.toNat)
    value hmagnitudeModel

/-- The total direct decoder agrees with `Model.toDyadic?` on every in-range native word. -/
theorem toDyadic?_eq_model
    (format : Format) (code : UInt64)
    (heligible : Eligible format)
    (hcode : code.toNat < format.modulus) :
    toDyadic? format code =
      (Model.ofNatBits (format := format) code.toNat).toDyadic? := by
  let value := Model.ofNatBits (format := format) code.toNat
  by_cases hnarCode : code.toNat = format.signMaskNat
  · unfold toDyadic?
    simp only [hnarCode, beq_self_eq_true, ite_true]
    change none = (Model.nar format).toDyadic?
    exact (Model.toDyadic?_nar format).symm
  · by_cases hzeroCode : code = 0
    · subst code
      have hsignMaskNonzero : format.signMaskNat ≠ 0 :=
        Nat.ne_of_gt (Nat.two_pow_pos format.signIndex)
      change toDyadic? format 0 = (Model.zero format).toDyadic?
      rw [Model.toDyadic?_zero]
      unfold toDyadic?
      have hmaskBool : ((0 : Nat) == format.signMaskNat) = false :=
        beq_eq_false_iff_ne.mpr (Ne.symm hsignMaskNonzero)
      simp only [UInt64.toNat_zero, hmaskBool, Bool.false_eq_true,
        ite_false, beq_self_eq_true, ite_true]
    · have hvalueBits : value.toNatBits = code.toNat :=
        Model.toNatBits_ofNatBits_of_lt code.toNat hcode
      have hvalueNaR : value ≠ Model.nar format := by
        intro equality
        have bitsEquality := congrArg Model.toNatBits equality
        rw [hvalueBits, Model.nar_toNatBits] at bitsEquality
        exact hnarCode bitsEquality
      have hvalueZero : value ≠ Model.zero format := by
        intro equality
        have bitsEquality := congrArg Model.toNatBits equality
        rw [hvalueBits, Model.zero_toNatBits] at bitsEquality
        exact hzeroCode (UInt64.toNat_inj.mp (by simpa using bitsEquality))
      have hnarBool : (code.toNat == format.signMaskNat) = false :=
        beq_eq_false_iff_ne.mpr hnarCode
      have hzeroBool : (code == 0) = false :=
        beq_eq_false_iff_ne.mpr hzeroCode
      have hvalueNaRBool : value.isNaR = false :=
        beq_eq_false_iff_ne.mpr hvalueNaR
      have hvalueZeroBool : value.isZero = false :=
        beq_eq_false_iff_ne.mpr hvalueZero
      unfold toDyadic?
      simp only [hnarBool, hzeroBool, Bool.false_eq_true, ite_false]
      change some (decodeFinite format code) = value.toDyadic?
      rw [decodeFinite_eq_decodeFields format code heligible hcode
        hvalueNaR hvalueZero]
      change some value.decodeFields.toDyadic = value.toDyadic?
      unfold Model.toDyadic? Model.decodeExact
      simp [hvalueNaRBool, hvalueZeroBool]


end FloatLib.Floats.Formats.Posit.Model.NativeWord
