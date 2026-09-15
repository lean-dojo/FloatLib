/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Core.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Decode.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Fields.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Proof
public import FloatLib.Kernels.FixedWord.Difference.Proof
public import FloatLib.Kernels.FixedWord.LimbRound.Proof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Refinement of direct two-limb posit decoding

The two-limb backend inspects a packed 128-bit code without first rebuilding an arbitrary-precision
natural. This module proves each primitive observation (zero detection, individual bits, regime
length, fields, and the resulting dyadic value) equal to the exact-width posit model.

The proofs are separate from `Decode.Runtime`, so importing the decoder does not import these
dependencies. Arithmetic refinements use `toDyadic?_eq_model` for stored words and the
continuation laws for kernels that consume native significands directly.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimb

open FloatLib.Numerics

section PackedBitPrimitives

/-- The fixed-limb zero test is exactly mathematical equality with zero. -/
theorem isZero_eq_true_iff (value : FloatLib.Numerics.FixedWord.UInt128) :
    isZero value = true ↔ value.toNat = 0 := by
  constructor
  · intro hzero
    have hparts : value.hi = 0 ∧ value.lo = 0 := by
      simpa [isZero] using hzero
    unfold FloatLib.Numerics.FixedWord.UInt128.toNat
    simp [hparts.1, hparts.2]
  · intro hzero
    have hzeroEncoding :
        value = FloatLib.Numerics.FixedWord.UInt128.ofNat 0 := by
      apply FloatLib.Numerics.FixedWord.UInt128.toNat_injective
      rw [hzero, FloatLib.Numerics.FixedWord.UInt128.toNat_ofNat 0 (by norm_num)]
    subst value
    decide

/-- Native two-limb bit inspection agrees with natural-number bit inspection. -/
theorem bitAt_eq_testBit (value : FloatLib.Numerics.FixedWord.UInt128) (index : Nat) :
    bitAt value index = value.toNat.testBit index := by
  unfold bitAt FloatLib.Numerics.FixedWord.UInt128.toNat
  rw [Nat.add_comm, Nat.mul_comm value.hi.toNat,
    Nat.testBit_two_pow_mul_add value.hi.toNat value.lo.toNat_lt index]
  by_cases hindex : index < 64
  · rw [ite_eq_left hindex, ite_eq_left hindex]
    exact NativeWord.bitAt_eq_testBit value.lo index
  · rw [ite_eq_right hindex, ite_eq_right hindex]
    exact NativeWord.bitAt_eq_testBit value.hi (index - 64)

/-- Two-limb low-bit extraction is exact at every zero-extended width. -/
theorem lowBits_toNat
    (value : FloatLib.Numerics.FixedWord.UInt128) (width : Nat) :
    (lowBits value width).toNat = value.toNat % 2 ^ width := by
  by_cases hwidth : width ≤ 128
  · by_cases hsmall : width < 64
    · have hpow :
          2 ^ 64 = 2 ^ width * 2 ^ (64 - width) := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hsmall)]
      unfold lowBits FloatLib.Numerics.FixedWord.UInt128.toNat
      simp only [hsmall, ite_true, UInt64.reduceToNat, zero_mul, add_zero,
        NativeWord.lowBits_toNat _ width hsmall]
      rw [hpow]
      rw [show
        value.hi.toNat * (2 ^ width * 2 ^ (64 - width)) =
          2 ^ width * (value.hi.toNat * 2 ^ (64 - width)) by
        ac_rfl]
      exact (Nat.add_mul_mod_self_left _ _ _).symm
    · have hlarge : 64 ≤ width := Nat.le_of_not_gt hsmall
      let highWidth := width - 64
      have hhighWidth : highWidth ≤ 64 := by
        unfold highWidth
        omega
      have hwidthEq : width = highWidth + 64 := by
        unfold highWidth
        omega
      have hmodulus :
          2 ^ width = 2 ^ highWidth * 2 ^ 64 := by
        rw [hwidthEq, pow_add]
      have hhighRemainder :
          (NativeWord.lowBits value.hi highWidth).toNat =
            value.hi.toNat % 2 ^ highWidth :=
        NativeWord.lowBits_toNat_of_le value.hi highWidth hhighWidth
      have hhighBound :
          value.hi.toNat % 2 ^ highWidth < 2 ^ highWidth :=
        Nat.mod_lt _ (Nat.two_pow_pos highWidth)
      have hresultBound :
          value.lo.toNat +
              (value.hi.toNat % 2 ^ highWidth) * 2 ^ 64 <
            2 ^ highWidth * 2 ^ 64 := by
        have hlow := value.lo.toNat_lt
        nlinarith
      unfold lowBits FloatLib.Numerics.FixedWord.UInt128.toNat
      simp only [hsmall, ite_false, hwidth, ite_true]
      rw [hhighRemainder]
      rw [hmodulus, Nat.add_mod,
        Nat.mod_eq_of_lt (lt_of_lt_of_le value.lo.toNat_lt
          (Nat.le_mul_of_pos_left (2 ^ 64) (Nat.two_pow_pos highWidth))),
        Nat.mul_mod_mul_right, Nat.mod_eq_of_lt hresultBound]
  · have hsmall : ¬width < 64 := by omega
    have hvalue :
        value.toNat < 2 ^ width := by
      exact value.toNat_lt.trans_le <|
        Nat.pow_le_pow_right (by decide) (by omega)
    unfold lowBits
    simp only [hsmall, ite_false, hwidth, Nat.mod_eq_of_lt hvalue]

/--
For a standardized posit exponent field, the low limb already contains the complete extraction.

The exponent field has at most two bits, so optimized decoding need not construct a two-limb
natural number merely to read it.
-/
private theorem lowBits_lo_toNat_of_le_two
    (value : FloatLib.Numerics.FixedWord.UInt128)
    (width : Nat) (hwidth : width ≤ 2) :
    (lowBits value width).lo.toNat = value.toNat % 2 ^ width := by
  have hsmall : width < 64 := by omega
  rw [← lowBits_toNat value width]
  unfold lowBits FloatLib.Numerics.FixedWord.UInt128.toNat
  simp only [hsmall, ite_true, UInt64.toNat_zero, zero_mul, add_zero]

/--
Native hidden-bit insertion produces the exact posit significand throughout the two-limb range.
-/
private theorem significand_toNat_of_lt
    (value : FloatLib.Numerics.FixedWord.UInt128)
    (width : Nat) (hwidth : width < 128) :
    (FloatLib.Numerics.FixedWord.add128
      (lowBits value width)
      (FloatLib.Numerics.FixedWord.UInt128.singleBit width)).value.toNat =
      2 ^ width + value.toNat % 2 ^ width := by
  have hlow :
      (lowBits value width).toNat = value.toNat % 2 ^ width :=
    lowBits_toNat value width
  have hbit :
      (FloatLib.Numerics.FixedWord.UInt128.singleBit width).toNat =
        2 ^ width :=
    FloatLib.Numerics.FixedWord.UInt128.singleBit_toNat_of_lt width hwidth
  rw [FloatLib.Numerics.FixedWord.add128_value_toNat_of_lt, hlow, hbit]
  · omega
  · have hremainder : value.toNat % 2 ^ width < 2 ^ width :=
      Nat.mod_lt _ (Nat.two_pow_pos width)
    calc
      (lowBits value width).toNat +
          (FloatLib.Numerics.FixedWord.UInt128.singleBit width).toNat =
        value.toNat % 2 ^ width + 2 ^ width := by rw [hlow, hbit]
      _ < 2 ^ width + 2 ^ width := Nat.add_lt_add_right hremainder _
      _ = 2 ^ (width + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ 128 :=
        Nat.pow_le_pow_right (by decide) (by omega)

/-- Native two-limb logarithmic zero counting agrees with the exact model scan. -/
theorem countLeadingZeros_eq_model
    (value : FloatLib.Numerics.FixedWord.UInt128) (width : Nat) :
    countLeadingZeros value width =
      Model.countLeadingRun value.toNat width false := by
  let truncated := lowBits value width
  have htruncated :
      truncated.toNat = value.toNat % 2 ^ width :=
    lowBits_toNat value width
  have htruncatedLt : truncated.toNat < 2 ^ width := by
    rw [htruncated]
    exact Nat.mod_lt _ (Nat.two_pow_pos width)
  unfold countLeadingZeros
  change
    (if isZero truncated then
      width
    else
      width -
        (FloatLib.Numerics.FixedWord.UInt128.log2 truncated + 1)) =
      Model.countLeadingRun value.toNat width false
  rw [Model.countLeadingRun_mod_twoPow value.toNat width false,
    ← htruncated]
  split
  next hzero =>
    have hzero' : truncated.toNat = 0 :=
      (isZero_eq_true_iff truncated).mp hzero
    simp [hzero', Model.countLeadingRun_zero_false]
  next hnonzero =>
    have hnonzero' : truncated.toNat ≠ 0 := by
      intro equality
      apply hnonzero
      exact (isZero_eq_true_iff truncated).mpr equality
    rw [Model.countLeadingRun_false_eq_log2 truncated.toNat width
      (Nat.pos_of_ne_zero hnonzero') htruncatedLt]
    rw [← FloatLib.Numerics.FixedWord.UInt128.log2_toNat]

/-- Two-limb and reference-model regime scans return the same run length. -/
theorem countLeadingRun_eq_model
    (value : FloatLib.Numerics.FixedWord.UInt128) (width : Nat) (bit : Bool) :
    countLeadingRun value width bit =
      Model.countLeadingRun value.toNat width bit := by
  unfold countLeadingRun
  cases bit with
  | false =>
      exact countLeadingZeros_eq_model value width
  | true =>
      simp only [ite_true]
      by_cases hwidth : width ≤ 128
      · rw [ite_eq_left hwidth, countLeadingZeros_eq_model]
        exact
          (Model.countLeadingRun_true_eq_false_of_testBit_flip
            value.toNat (complement value).toNat width (by
              intro index hindex
              rw [← bitAt_eq_testBit value index,
                ← bitAt_eq_testBit (complement value) index]
              unfold bitAt complement
              by_cases hlow : index < 64
              · simp only [hlow, ite_true]
                exact NativeWord.bitAt_complement value.lo index hlow
              · have hhigh : index - 64 < 64 := by omega
                simp only [hlow, ite_false]
                exact NativeWord.bitAt_complement
                  value.hi (index - 64) hhigh)).symm
      · rw [ite_eq_right hwidth]
        cases width with
        | zero =>
            contradiction
        | succ index =>
            have hindex : 128 ≤ index := by omega
            have hvalue :
                value.toNat < 2 ^ index := by
              exact value.toNat_lt.trans_le <|
                Nat.pow_le_pow_right (by decide) hindex
            rw [Model.countLeadingRun, Nat.testBit_lt_two_pow hvalue]
            rfl

end PackedBitPrimitives

section NonnegativeFieldDecoding

/--
Running a continuation directly over native nonnegative fields agrees with constructing the
proof-facing dyadic and projecting those same fields.
-/
private theorem withNonnegativeFields_eq_nonnegativeDyadicAt
    {α : Type}
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (continuation : Nat → Int → α) :
    withNonnegativeFields format code
        (fun significand exponent =>
          continuation significand.toNat exponent) =
      continuation
        (nonnegativeDyadicAt format code).significand
        (nonnegativeDyadicAt format code).exponent := by
  unfold nonnegativeDyadicAt withNonnegativeFields
  split <;>
    simp only [FloatLib.Numerics.FixedWord.UInt128.toNat,
      UInt64.toNat_zero, zero_mul, add_zero]

/-- The direct candidate decoder always clears the sign field. -/
@[simp] theorem nonnegativeDyadicAt_negative
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128) :
    (nonnegativeDyadicAt format code).negative = false := by
  unfold nonnegativeDyadicAt withNonnegativeFields
  split <;> rfl

/--
Direct two-limb candidate decoding agrees with the exact posit field decoder.

The hypotheses are exactly the rounding-search invariant: the candidate is nonzero, lies below
the sign code, and the descriptor's positive candidate range fits in two limbs.
-/
private theorem nonnegativeDyadicAt_eq_decodeFields
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (heligible : CandidateEligible format)
    (hcode : code.toNat < format.signMaskNat)
    (hnonzero : code.toNat ≠ 0) :
    nonnegativeDyadicAt format code =
      (Model.ofNatBits (format := format) code.toNat).decodeFields.toDyadic := by
  let value := Model.ofNatBits (format := format) code.toNat
  have hsign : value.signBit = false :=
    Model.signBit_ofNatBits_eq_false format code.toNat hcode
  have hmagnitude : value.magnitudeBits = code.toNat :=
    Model.magnitudeBits_ofNatBits_of_lt_signMask format code.toNat hcode
  have hbit : bitAt code (format.payloadBits - 1) = value.regimeBit := by
    unfold Model.regimeBit
    rw [hmagnitude, bitAt_eq_testBit]
  have hrun :
      countLeadingRun code format.payloadBits value.regimeBit =
        value.regimeRunLength := by
    rw [countLeadingRun_eq_model]
    unfold Model.regimeRunLength
    rw [hmagnitude]
  have hcodeBool : isZero code = false := by
    apply Bool.eq_false_iff.mpr
    intro hzero
    exact hnonzero ((isZero_eq_true_iff code).mp hzero)
  have hfractionBits : value.fractionBits < 128 := by
    have hrunPos := Model.regimeRunLength_pos value
    have hfields := Model.regimeRunLength_add_fractionBits_le_payload value
    unfold CandidateEligible Format.payloadBits at *
    omega
  unfold nonnegativeDyadicAt withNonnegativeFields
  simp only [hcodeBool, Bool.false_eq_true, ite_false]
  rw [hbit, hrun]
  change
    FloatLib.Numerics.Dyadic.mk false
        ((FloatLib.Numerics.FixedWord.add128
          (lowBits code value.fractionBits)
          (FloatLib.Numerics.FixedWord.UInt128.singleBit
            value.fractionBits)).value.toNat)
        (value.regimeValue * Int.ofNat format.regimeExponentStep +
          Int.ofNat
            ((lowBits
                (FloatLib.Numerics.FixedWord.UInt128.shiftRight
                  code value.fractionBits)
                value.usedExponentBits).lo.toNat *
              2 ^ (format.exponentBits - value.usedExponentBits)) -
          Int.ofNat value.fractionBits) =
      FloatLib.Numerics.Dyadic.mk value.signBit
        (2 ^ value.fractionBits + value.fractionField) value.scale
  rw [significand_toNat_of_lt code value.fractionBits hfractionBits,
    lowBits_lo_toNat_of_le_two
      (FloatLib.Numerics.FixedWord.UInt128.shiftRight code value.fractionBits)
      value.usedExponentBits (Nat.min_le_left _ _),
    FloatLib.Numerics.FixedWord.UInt128.shiftRight_toNat, hsign]
  simp only [Model.fractionField, Model.storedExponentField,
    Model.exponentField, Model.scale, hmagnitude]

end NonnegativeFieldDecoding

section SignedMagnitudeRecovery

/-- Whole-carrier complementation has the expected unsigned mathematical value. -/
private theorem complement_toNat
    (code : FloatLib.Numerics.FixedWord.UInt128) :
    (complement code).toNat = 2 ^ 128 - 1 - code.toNat := by
  unfold complement FloatLib.Numerics.FixedWord.UInt128.toNat
  simp only [UInt64.toNat_not, UInt64.size]
  change
    (2 ^ 64 - 1 - code.lo.toNat) +
        (2 ^ 64 - 1 - code.hi.toNat) * 2 ^ 64 =
      2 ^ 128 - 1 - (code.lo.toNat + code.hi.toNat * 2 ^ 64)
  have hlow : code.lo.toNat ≤ 2 ^ 64 - 1 := by
    have := code.lo.toNat_lt
    norm_num at this ⊢
    omega
  have hhigh : code.hi.toNat ≤ 2 ^ 64 - 1 := by
    have := code.hi.toNat_lt
    norm_num at this ⊢
    omega
  have hlowSum := Nat.sub_add_cancel hlow
  have hhighSum := Nat.sub_add_cancel hhigh
  apply Nat.eq_sub_of_add_eq
  calc
    ((2 ^ 64 - 1 - code.lo.toNat) +
          (2 ^ 64 - 1 - code.hi.toNat) * 2 ^ 64) +
        (code.lo.toNat + code.hi.toNat * 2 ^ 64) =
      ((2 ^ 64 - 1 - code.lo.toNat) + code.lo.toNat) +
        ((2 ^ 64 - 1 - code.hi.toNat) + code.hi.toNat) * 2 ^ 64 := by
      ring
    _ = 2 ^ 128 - 1 := by
      rw [hlowSum, hhighSum]
      norm_num

/-- Incrementing the complement of a nonzero word computes its 128-bit two's complement. -/
private theorem complement_increment_toNat
    (code : FloatLib.Numerics.FixedWord.UInt128)
    (hnonzero : code.toNat ≠ 0) :
    (complement code).increment.toNat = 2 ^ 128 - code.toNat := by
  have hbound := FloatLib.Numerics.FixedWord.UInt128.toNat_lt code
  have hpositive := Nat.pos_of_ne_zero hnonzero
  have hincrement :
      2 ^ 128 - 1 - code.toNat + 1 =
        2 ^ 128 - code.toNat := by
    rw [Nat.sub_sub, Nat.add_comm 1 code.toNat, ← Nat.sub_sub]
    exact Nat.sub_add_cancel
      ((Nat.one_le_iff_ne_zero).mpr (Nat.sub_ne_zero_of_lt hbound))
  rw [FloatLib.Numerics.FixedWord.UInt128.increment_toNat]
  · rw [complement_toNat, hincrement]
  · rw [complement_toNat, hincrement]
    exact Nat.sub_lt (Nat.two_pow_pos 128) hpositive

/--
Reducing a full-carrier two's complement to the format width yields exact-width subtraction.

Both magnitude extraction and sign restoration use this identity.
-/
theorem lowBits_complement_increment_toNat
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (heligible : Eligible format)
    (hcode : code.toNat < format.modulus)
    (hnonzero : code.toNat ≠ 0) :
    (lowBits (complement code).increment format.bits).toNat =
      format.modulus - code.toNat := by
  rw [lowBits_toNat]
  have hwidth : format.bits ≤ 128 := heligible
  have hpositive := Nat.pos_of_ne_zero hnonzero
  have hcodeLe : code.toNat ≤ 2 ^ format.bits := by
    simpa [Format.modulus] using hcode.le
  let factor := 2 ^ (128 - format.bits)
  have hfactorPositive : 0 < factor := Nat.two_pow_pos _
  have hfactor :
      2 ^ 128 = 2 ^ format.bits * factor := by
    unfold factor
    rw [← pow_add]
    congr 1
    omega
  have hfactorDecompose : factor = 1 + (factor - 1) := by
    omega
  have hfactorProduct :
      2 ^ format.bits * factor =
        2 ^ format.bits + (factor - 1) * 2 ^ format.bits := by
    calc
      2 ^ format.bits * factor =
          2 ^ format.bits * (1 + (factor - 1)) :=
        congrArg (2 ^ format.bits * ·) hfactorDecompose
      _ = 2 ^ format.bits + (factor - 1) * 2 ^ format.bits := by
        ring
  have hdecompose :
      2 ^ 128 - code.toNat =
        (2 ^ format.bits - code.toNat) +
          (factor - 1) * 2 ^ format.bits := by
    calc
      2 ^ 128 - code.toNat =
          (2 ^ format.bits +
            (factor - 1) * 2 ^ format.bits) - code.toNat := by
        rw [hfactor, hfactorProduct]
      _ = (2 ^ format.bits - code.toNat) +
          (factor - 1) * 2 ^ format.bits :=
        Nat.sub_add_comm hcodeLe
  rw [complement_increment_toNat code hnonzero, hdecompose,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
  · rfl
  · exact Nat.sub_lt (Nat.two_pow_pos format.bits) hpositive

/-- Native sign inspection agrees with exact-width posit sign decoding. -/
private theorem isNegative_eq_model_signBit
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (hcode : code.toNat < format.modulus) :
    isNegative format code =
      (Model.ofNatBits (format := format) code.toNat).signBit := by
  unfold isNegative
  rw [bitAt_eq_testBit,
    Model.signBit_ofNatBits_eq_decide format code.toNat hcode,
    Nat.testBit_eq_decide_div_mod_eq]
  by_cases hnegative : format.signMaskNat ≤ code.toNat
  · have hquotient : code.toNat / format.signMaskNat = 1 := by
      apply Nat.div_eq_of_lt_le
      · simpa using hnegative
      · simpa [Format.modulus_eq_two_mul_signMaskNat] using hcode
    have hquotient' : code.toNat / 2 ^ format.signIndex = 1 := by
      simpa [Format.signMaskNat] using hquotient
    simp [hquotient', hnegative]
  · have hquotient : code.toNat / format.signMaskNat = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_not_ge hnegative)
    have hquotient' : code.toNat / 2 ^ format.signIndex = 0 := by
      simpa [Format.signMaskNat] using hquotient
    simp [hquotient', hnegative]

/-- Two-limb magnitude calculation agrees with the exact-width model. -/
private theorem magnitudeWord_toNat_eq_model
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (heligible : Eligible format)
    (hcode : code.toNat < format.modulus) :
    (magnitudeWord format code).toNat =
      (Model.ofNatBits (format := format) code.toNat).magnitudeBits := by
  let value := Model.ofNatBits (format := format) code.toNat
  have hbits : value.toNatBits = code.toNat :=
    Model.toNatBits_ofNatBits_of_lt code.toNat hcode
  have hsign :
      isNegative format code = value.signBit := by
    exact isNegative_eq_model_signBit format code hcode
  cases hnegative : isNegative format code with
  | false =>
      unfold magnitudeWord Model.magnitudeBits
      simp only [hnegative, Bool.false_eq_true, ite_false]
      rw [← hsign, hnegative, hbits]
      simp
  | true =>
      have hnonzero : code.toNat ≠ 0 := by
        intro hzero
        have : isNegative format code = false := by
          unfold isNegative
          rw [bitAt_eq_testBit, hzero]
          simp
        rw [hnegative] at this
        contradiction
      unfold magnitudeWord Model.magnitudeBits
      simp only [hnegative, ite_true]
      rw [lowBits_complement_increment_toNat
        format code heligible hcode hnonzero,
        ← hsign, hnegative, hbits]
      simp

end SignedMagnitudeRecovery

section TotalDecoderRefinement

/-- Direct two-limb finite decoding agrees with the exact field decoder. -/
private theorem decodeFinite_eq_decodeFields
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (heligible : Eligible format)
    (hcode : code.toNat < format.modulus)
    (hnar :
      Model.ofNatBits (format := format) code.toNat ≠ Model.nar format)
    (hzero :
      Model.ofNatBits (format := format) code.toNat ≠ Model.zero format) :
    decodeFinite format code =
      (Model.ofNatBits (format := format) code.toNat).decodeFields.toDyadic := by
  let value := Model.ofNatBits (format := format) code.toNat
  let magnitude := magnitudeWord format code
  have hmagnitudeNat : magnitude.toNat = value.magnitudeBits :=
    magnitudeWord_toNat_eq_model format code heligible hcode
  have hmagnitudeLt :
      value.magnitudeBits < format.signMaskNat :=
    Model.magnitudeBits_lt_signMask_of_ne_nar value hnar
  have hmagnitudeNonzero : magnitude.toNat ≠ 0 := by
    rw [hmagnitudeNat]
    exact Model.magnitudeBits_ne_zero_of_ne_zero value hzero
  have hsign :
      isNegative format code = value.signBit := by
    exact isNegative_eq_model_signBit format code hcode
  have hnative :
      nonnegativeDyadicAt format magnitude =
        (Model.ofNatBits
          (format := format) magnitude.toNat).decodeFields.toDyadic :=
    nonnegativeDyadicAt_eq_decodeFields format magnitude
      (candidateEligible_of_eligible format heligible)
      (by simpa [hmagnitudeNat] using hmagnitudeLt)
      hmagnitudeNonzero
  have hmagnitudeModel :
      (Model.ofNatBits
        (format := format) magnitude.toNat).magnitudeBits =
          value.magnitudeBits := by
    rw [Model.magnitudeBits_ofNatBits_of_lt_signMask
      format magnitude.toNat
      (by simpa [hmagnitudeNat] using hmagnitudeLt)]
    exact hmagnitudeNat
  unfold decodeFinite
  change
    { nonnegativeDyadicAt format magnitude with
        negative := isNegative format code } =
      value.decodeFields.toDyadic
  rw [hnative, hsign]
  exact NativeWord.decodeFields_toDyadic_eq_of_magnitudeBits_eq
    (Model.ofNatBits (format := format) magnitude.toNat)
    value hmagnitudeModel

/-- The direct decoder recognizes the unique NaR encoding exactly. -/
private theorem toDyadic?_eq_model_of_nar
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (heligible : Eligible format)
    (hnarCode : code.toNat = format.signMaskNat) :
    toDyadic? format code =
      (Model.ofNatBits (format := format) code.toNat).toDyadic? := by
  have hword : code = signMaskWord format := by
    apply FloatLib.Numerics.FixedWord.UInt128.toNat_injective
    rw [hnarCode, signMaskWord_toNat format heligible]
  unfold toDyadic?
  simp only [hword, beq_self_eq_true, ite_true]
  rw [signMaskWord_toNat format heligible]
  change none = (Model.nar format).toDyadic?
  exact (Model.toDyadic?_nar format).symm

/-- The direct decoder recognizes the unique zero encoding exactly. -/
private theorem toDyadic?_eq_model_of_zero
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (heligible : Eligible format)
    (hzeroCode : code.toNat = 0) :
    toDyadic? format code =
      (Model.ofNatBits (format := format) code.toNat).toDyadic? := by
  have hcodeZero :
      code = FloatLib.Numerics.FixedWord.UInt128.ofNat 0 := by
    apply FloatLib.Numerics.FixedWord.UInt128.toNat_injective
    rw [hzeroCode, FloatLib.Numerics.FixedWord.UInt128.toNat_ofNat 0 (by norm_num)]
  subst code
  have htoNat :
      (FloatLib.Numerics.FixedWord.UInt128.ofNat 0).toNat = 0 :=
    FloatLib.Numerics.FixedWord.UInt128.toNat_ofNat 0 (by norm_num)
  change
    toDyadic? format (FloatLib.Numerics.FixedWord.UInt128.ofNat 0) =
      (Model.ofNatBits
        (format := format) (FloatLib.Numerics.FixedWord.UInt128.ofNat 0).toNat).toDyadic?
  rw [htoNat]
  change toDyadic? format (FloatLib.Numerics.FixedWord.UInt128.ofNat 0) =
    (Model.zero format).toDyadic?
  rw [Model.toDyadic?_zero]
  unfold toDyadic?
  have hmaskBool :
      (FloatLib.Numerics.FixedWord.UInt128.ofNat 0 == signMaskWord format) =
        false := by
    apply beq_eq_false_iff_ne.mpr
    intro equality
    have equalityNat := congrArg
      FloatLib.Numerics.FixedWord.UInt128.toNat equality
    rw [htoNat] at equalityNat
    have hmaskPositive :
        0 < (signMaskWord format).toNat := by
      rw [signMaskWord_toNat format heligible]
      exact format.signMaskNat_pos
    omega
  have hzeroBool :
      isZero (FloatLib.Numerics.FixedWord.UInt128.ofNat 0) = true :=
    (isZero_eq_true_iff _).mpr htoNat
  simp only [hmaskBool, hzeroBool, Bool.false_eq_true,
    ite_false, ite_true]

-- Every ordinary in-range word takes the finite two-limb decoding branch.
private theorem toDyadic?_eq_model_of_ordinary
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (heligible : Eligible format)
    (hcode : code.toNat < format.modulus)
    (hnarCode : code.toNat ≠ format.signMaskNat)
    (hzeroCode : code.toNat ≠ 0) :
    toDyadic? format code =
      (Model.ofNatBits (format := format) code.toNat).toDyadic? := by
  let value := Model.ofNatBits (format := format) code.toNat
  have hvalueBits : value.toNatBits = code.toNat :=
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
    exact hzeroCode bitsEquality
  have hzeroBool : isZero code = false := by
    apply Bool.eq_false_iff.mpr
    intro equality
    exact hzeroCode ((isZero_eq_true_iff code).mp equality)
  have hvalueNaRBool : value.isNaR = false :=
    beq_eq_false_iff_ne.mpr hvalueNaR
  have hvalueZeroBool : value.isZero = false :=
    beq_eq_false_iff_ne.mpr hvalueZero
  have hnarWordBool : (code == signMaskWord format) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro equality
    apply hnarCode
    have equalityNat := congrArg
      FloatLib.Numerics.FixedWord.UInt128.toNat equality
    simpa [signMaskWord_toNat format heligible] using equalityNat
  unfold toDyadic?
  simp only [hnarWordBool, hzeroBool, Bool.false_eq_true, ite_false]
  change some (decodeFinite format code) = value.toDyadic?
  rw [decodeFinite_eq_decodeFields format code heligible hcode
    hvalueNaR hvalueZero]
  exact
    (Model.toDyadic?_eq_some_decodeFields
      value hvalueNaRBool hvalueZeroBool).symm

/-- The total two-limb decoder agrees with `Model.toDyadic?` on every in-range word. -/
theorem toDyadic?_eq_model
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (heligible : Eligible format)
    (hcode : code.toNat < format.modulus) :
    toDyadic? format code =
      (Model.ofNatBits (format := format) code.toNat).toDyadic? := by
  by_cases hnarCode : code.toNat = format.signMaskNat
  · exact toDyadic?_eq_model_of_nar format code heligible hnarCode
  · by_cases hzeroCode : code.toNat = 0
    · exact toDyadic?_eq_model_of_zero format code heligible hzeroCode
    · exact toDyadic?_eq_model_of_ordinary
        format code heligible hcode hnarCode hzeroCode

end TotalDecoderRefinement

section ContinuationLaws

/-- Mapping a native nonnegative-field eliminator distributes over its terminal continuation. -/
private theorem withNonnegativeFields_map
    {α β : Type}
    (projection : α → β)
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (continuation :
      FloatLib.Numerics.FixedWord.UInt128 → Int → α) :
    projection (withNonnegativeFields format code continuation) =
      withNonnegativeFields format code
        (fun significand exponent =>
          projection (continuation significand exponent)) := by
  unfold withNonnegativeFields
  split <;> rfl

/--
Native field elimination agrees with decoding to an exact dyadic and projecting its fields.

The theorem exposes the mathematical `Nat` value of the significand, allowing
operation proofs to reuse `Dyadic.addFields` while executable kernels retain `UInt128`.
-/
private theorem withDyadicFields_eq_match_toDyadic?
    {α : Type}
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (onNaR : α)
    (continuation : Bool → Nat → Int → α) :
    withDyadicFields format code onNaR
        (fun negative significand exponent =>
          continuation negative significand.toNat exponent) =
      match toDyadic? format code with
      | none => onNaR
      | some value =>
          continuation value.negative value.significand value.exponent := by
  unfold withDyadicFields toDyadic? decodeFinite magnitudeWord
  by_cases hnar : code == signMaskWord format
  · simp [hnar]
  · by_cases hzero : isZero code
    · simp [hnar, hzero, FloatLib.Numerics.FixedWord.UInt128.toNat]
    · simp only [hnar, hzero, Bool.false_eq_true, ite_false]
      exact withNonnegativeFields_eq_nonnegativeDyadicAt
        format
        (if isNegative format code then
          lowBits (complement code).increment format.bits
        else
          code)
        (continuation (isNegative format code))

/--
Mapping the result of native field elimination is equivalent to mapping each terminal branch.

This structural law lets operation proofs project a carrier-valued continuation to its exact
mathematical view without reopening the decoder implementation.
-/
private theorem map_withDyadicFields
    {α β : Type}
    (projection : α → β)
    (format : Format) (code : FloatLib.Numerics.FixedWord.UInt128)
    (onNaR : α)
    (continuation :
      Bool → FloatLib.Numerics.FixedWord.UInt128 → Int → α) :
    projection (withDyadicFields format code onNaR continuation) =
      withDyadicFields format code (projection onNaR)
        (fun negative significand exponent =>
          projection (continuation negative significand exponent)) := by
  unfold withDyadicFields
  split
  · rfl
  · split
    · rfl
    · exact withNonnegativeFields_map
        projection format
        (if isNegative format code then
          lowBits (complement code).increment format.bits
        else
          code)
        (fun significand exponent =>
          continuation (isNegative format code) significand exponent)

/-- Mapping a two-input native decoder distributes over both nested eliminators. -/
private theorem map_withTwoDyadicFields
    {α β : Type}
    (projection : α → β)
    (format : Format)
    (left right : FloatLib.Numerics.FixedWord.UInt128)
    (onNaR : α)
    (continuation :
      Bool → FloatLib.Numerics.FixedWord.UInt128 → Int →
      Bool → FloatLib.Numerics.FixedWord.UInt128 → Int → α) :
    projection
        (withTwoDyadicFields format left right onNaR continuation) =
      withTwoDyadicFields format left right (projection onNaR)
        (fun leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent =>
          projection
            (continuation
              leftNegative leftSignificand leftExponent
              rightNegative rightSignificand rightExponent)) := by
  unfold withTwoDyadicFields
  rw [map_withDyadicFields
    projection format left onNaR
    (fun leftNegative leftSignificand leftExponent =>
      withDyadicFields format right onNaR
        (continuation leftNegative leftSignificand leftExponent))]
  apply congrArg
    (withDyadicFields format left (projection onNaR))
  funext leftNegative leftSignificand leftExponent
  exact map_withDyadicFields
    projection format right onNaR
    (continuation leftNegative leftSignificand leftExponent)

/--
Eliminating two native words is the nested exact-dyadic decoder.

The theorem keeps operation proofs over mathematical significands while the runtime continuation
receives `UInt128` fields directly.
-/
private theorem withTwoDyadicFields_eq_match_toDyadic?
    {α : Type}
    (format : Format)
    (left right : FloatLib.Numerics.FixedWord.UInt128)
    (onNaR : α)
    (continuation :
      Bool → Nat → Int → Bool → Nat → Int → α) :
    withTwoDyadicFields format left right onNaR
        (fun leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent =>
          continuation
            leftNegative leftSignificand.toNat leftExponent
            rightNegative rightSignificand.toNat rightExponent) =
      match toDyadic? format left with
      | none => onNaR
      | some leftValue =>
          match toDyadic? format right with
          | none => onNaR
          | some rightValue =>
              continuation
                leftValue.negative leftValue.significand leftValue.exponent
                rightValue.negative rightValue.significand rightValue.exponent := by
  unfold withTwoDyadicFields
  calc
    _ =
        match toDyadic? format left with
        | none => onNaR
        | some leftValue =>
            withDyadicFields format right onNaR
              (fun rightNegative rightSignificand rightExponent =>
                continuation
                  leftValue.negative leftValue.significand leftValue.exponent
                  rightNegative rightSignificand.toNat rightExponent) :=
      withDyadicFields_eq_match_toDyadic?
        format left onNaR
        (fun leftNegative leftSignificand leftExponent =>
          withDyadicFields format right onNaR
            (fun rightNegative rightSignificand rightExponent =>
              continuation
                leftNegative leftSignificand leftExponent
                rightNegative rightSignificand.toNat rightExponent))
    _ = _ := by
      cases hleft : toDyadic? format left with
      | none => rfl
      | some leftValue =>
        exact withDyadicFields_eq_match_toDyadic?
          format right onNaR
          (continuation
            leftValue.negative leftValue.significand leftValue.exponent)

/--
Projecting a carrier-valued two-input decoder agrees with an exact mathematical continuation
whenever the carrier continuation satisfies the supplied pointwise refinement law.

Native binary kernels retain `UInt128` significands; their refinements use the corresponding
`Nat` values.
-/
theorem map_withTwoDyadicFields_eq_match_toDyadic?
    {α β : Type}
    (projection : α → β)
    (format : Format)
    (left right : FloatLib.Numerics.FixedWord.UInt128)
    (onNaR : α)
    (nativeContinuation :
      Bool → FloatLib.Numerics.FixedWord.UInt128 → Int →
      Bool → FloatLib.Numerics.FixedWord.UInt128 → Int → α)
    (exactContinuation :
      Bool → Nat → Int → Bool → Nat → Int → β)
    (hrefine :
      ∀ leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent,
        projection
            (nativeContinuation
              leftNegative leftSignificand leftExponent
              rightNegative rightSignificand rightExponent) =
          exactContinuation
            leftNegative leftSignificand.toNat leftExponent
            rightNegative rightSignificand.toNat rightExponent) :
    projection
        (withTwoDyadicFields
          format left right onNaR nativeContinuation) =
      match toDyadic? format left with
      | none => projection onNaR
      | some leftValue =>
          match toDyadic? format right with
          | none => projection onNaR
          | some rightValue =>
              exactContinuation
                leftValue.negative leftValue.significand leftValue.exponent
                rightValue.negative rightValue.significand rightValue.exponent := by
  rw [map_withTwoDyadicFields
    projection format left right onNaR nativeContinuation]
  have hcontinuation :
      (fun leftNegative leftSignificand leftExponent
          rightNegative rightSignificand rightExponent =>
        projection
          (nativeContinuation
            leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent)) =
        (fun leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent =>
          exactContinuation
            leftNegative leftSignificand.toNat leftExponent
            rightNegative rightSignificand.toNat rightExponent) := by
    funext leftNegative leftSignificand leftExponent
      rightNegative rightSignificand rightExponent
    exact hrefine
      leftNegative leftSignificand leftExponent
      rightNegative rightSignificand rightExponent
  rw [hcontinuation]
  exact withTwoDyadicFields_eq_match_toDyadic?
    format left right (projection onNaR) exactContinuation

/--
Eliminating three native words is the nested exact-dyadic decoder.

The runtime continuation receives fixed-width significands while the theorem exposes their
mathematical values to proof-facing clients.
-/
theorem withThreeDyadicFields_eq_match_toDyadic?
    {α : Type}
    (format : Format)
    (left right addend : FloatLib.Numerics.FixedWord.UInt128)
    (onNaR : α)
    (continuation :
      Bool → Nat → Int →
      Bool → Nat → Int →
      Bool → Nat → Int → α) :
    withThreeDyadicFields format left right addend onNaR
        (fun leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent
            addendNegative addendSignificand addendExponent =>
          continuation
            leftNegative leftSignificand.toNat leftExponent
            rightNegative rightSignificand.toNat rightExponent
            addendNegative addendSignificand.toNat addendExponent) =
      match toDyadic? format left with
      | none => onNaR
      | some leftValue =>
          match toDyadic? format right with
          | none => onNaR
          | some rightValue =>
              match toDyadic? format addend with
              | none => onNaR
              | some addendValue =>
                  continuation
                    leftValue.negative leftValue.significand leftValue.exponent
                    rightValue.negative rightValue.significand rightValue.exponent
                    addendValue.negative addendValue.significand addendValue.exponent := by
  unfold withThreeDyadicFields
  calc
    _ =
        match toDyadic? format left with
        | none => onNaR
        | some leftValue =>
            match toDyadic? format right with
            | none => onNaR
            | some rightValue =>
                withDyadicFields format addend onNaR
                  (fun addendNegative addendSignificand addendExponent =>
                    continuation
                      leftValue.negative leftValue.significand leftValue.exponent
                      rightValue.negative rightValue.significand rightValue.exponent
                      addendNegative addendSignificand.toNat addendExponent) :=
      withTwoDyadicFields_eq_match_toDyadic?
        format left right onNaR
        (fun leftNegative leftSignificand leftExponent =>
          fun rightNegative rightSignificand rightExponent =>
            withDyadicFields format addend onNaR
              (fun addendNegative addendSignificand addendExponent =>
                continuation
                  leftNegative leftSignificand leftExponent
                  rightNegative rightSignificand rightExponent
                  addendNegative addendSignificand.toNat addendExponent))
    _ = _ := by
      cases hleft : toDyadic? format left with
      | none => rfl
      | some leftValue =>
          cases hright : toDyadic? format right with
          | none => rfl
          | some rightValue =>
              exact withDyadicFields_eq_match_toDyadic?
                format addend onNaR
                (continuation
                  leftValue.negative leftValue.significand leftValue.exponent
                  rightValue.negative rightValue.significand rightValue.exponent)

end ContinuationLaws

end FloatLib.Floats.Formats.Posit.Model.NativeLimb
