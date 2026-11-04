/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Fields.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Word.Proof

/-!
# Correctness of native-word posit field decoding

Extracting the leading run, sign, magnitude, exponent, and significand from a `UInt64` refines the
exact-width posit model, and this module proves it one field at a time. Executable primitives
are in `FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Fields.Runtime`.

Posit fields have variable length. The regime run decides where the exponent and the fraction
begin, so the proof first records how the regime consumes the rest of the word, and only then
relates native shifts and masks to semantic fields. The addition, multiplication, division, and
quire kernels built on top all reuse this decoding boundary and keep no parsers of their own.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWord

open FloatLib.Numerics

variable {format : Format}

/-- Native `log2` leading-zero counting agrees with the exact natural-number scan. -/
theorem countLeadingZeros_eq_model
    (value : UInt64) (width : Nat) :
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
  simp only [FixedWord.log2Word_eq_log2]
  change
    (if truncated == 0 then
      width
    else
      width - (truncated.log2.toNat + 1)) =
        Model.countLeadingRun value.toNat width false
  rw [Model.countLeadingRun_mod_twoPow value.toNat width false,
    ← htruncated]
  split
  next hzero =>
    have hzero' : truncated.toNat = 0 := by
      exact congrArg UInt64.toNat (beq_iff_eq.mp hzero)
    simp [hzero', Model.countLeadingRun_zero_false]
  next hnonzero =>
    have hnonzero' : truncated.toNat ≠ 0 := by
      intro equality
      apply hnonzero
      apply beq_iff_eq.mpr
      apply UInt64.toNat_inj.mp
      simpa using equality
    rw [Model.countLeadingRun_false_eq_log2 truncated.toNat width
      (Nat.pos_of_ne_zero hnonzero') htruncatedLt]
    rw [← FloatLib.Numerics.FixedWord.log2_toNat]

/-- Native and model regime-run scans return the same length. -/
theorem countLeadingRun_eq_model (value : UInt64) (width : Nat) (bit : Bool) :
    countLeadingRun value width bit =
      Model.countLeadingRun value.toNat width bit := by
  unfold countLeadingRun
  split
  next hwidth =>
    cases bit with
    | false =>
        exact countLeadingZeros_eq_model value width
    | true =>
        simp only [ite_true]
        rw [countLeadingZeros_eq_model (~~~value) width]
        exact
          (Model.countLeadingRun_true_eq_false_of_testBit_flip
            value.toNat (~~~value).toNat width (by
              intro index hindex
              rw [← bitAt_eq_testBit value index,
                ← bitAt_eq_testBit (~~~value) index,
                bitAt_complement value index (by omega)])).symm
  next =>
    rfl

/--
Native right shift agrees with natural-number right shift. Shifts past the machine width give
zero on both sides.
-/
theorem shiftRight_toNat (value : UInt64) (shift : Nat) :
    (shiftRight value shift).toNat = value.toNat >>> shift := by
  unfold shiftRight
  by_cases hshift : shift < 64
  · rw [ite_eq_left hshift, UInt64.toNat_shiftRight]
    simp [Nat.mod_eq_of_lt hshift]
  · rw [ite_eq_right hshift, UInt64.toNat_zero, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (value.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]

/-- Extracting a shifted field in one word agrees with natural-number division and remainder. -/
theorem shiftedLowBits_toNat (value : UInt64) (shift width : Nat) :
    (lowBits (shiftRight value shift) width).toNat =
      value.toNat / 2 ^ shift % 2 ^ width := by
  rw [lowBits_toNat _ width, shiftRight_toNat value shift, Nat.shiftRight_eq_div_pow]

/-- Adding the implicit bit to a native fraction has the expected natural value. -/
theorem significand_toNat (value : UInt64) (fractionBits : Nat)
    (hfractionBits : fractionBits < 64) :
    (lowBits value fractionBits |||
        ((1 : UInt64) <<< UInt64.ofNat fractionBits)).toNat =
      2 ^ fractionBits + value.toNat % 2 ^ fractionBits := by
  rw [UInt64.toNat_or, lowBits_toNat value fractionBits,
    FloatLib.Numerics.FixedWord.uint64_powTwo_toNat fractionBits hfractionBits]
  have hfraction :
      value.toNat % 2 ^ fractionBits < 2 ^ fractionBits :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [Nat.or_two_pow_eq_add_of_lt hfraction, Nat.add_comm]

/-- Native whole-word magnitude agrees with the reference natural-number magnitude. -/
theorem magnitudeWord_eq_ofNat_magnitudeNat
    (format : Format) (code : UInt64)
    (heligible : Eligible format)
    (hcode : code.toNat < format.modulus) :
    magnitudeWord format code =
      UInt64.ofNat (magnitudeNat format code) := by
  have hmask :
      (signMaskWord format).toNat = format.signMaskNat :=
    signMaskWord_toNat format heligible
  by_cases hnegative : format.signMaskNat ≤ code.toNat
  · have hnegativeWord : signMaskWord format ≤ code := by
      rw [UInt64.le_iff_toNat_le, hmask]
      exact hnegative
    unfold magnitudeWord magnitudeWordAt magnitudeNat
    rw [ite_eq_left hnegativeWord, ite_eq_left (decide_eq_true hnegative)]
    rw [modulusWord_eq_ofNat_modulus format heligible]
    rw [UInt64.ofNat_sub (Nat.le_of_lt hcode)]
    simp
  · have hnegativeWord : ¬signMaskWord format ≤ code := by
      rw [UInt64.le_iff_toNat_le, hmask]
      exact hnegative
    unfold magnitudeWord magnitudeWordAt magnitudeNat
    simp only [hnegativeWord, ite_false, decide_eq_false hnegative,
      Bool.false_eq_true]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt code.toNat_lt]

/-- Native magnitude calculation agrees with the exact-width model. -/
theorem magnitudeNat_eq_model (format : Format) (code : UInt64)
    (hcode : code.toNat < format.modulus) :
    magnitudeNat format code =
      (Model.ofNatBits (format := format) code.toNat).magnitudeBits := by
  let value := Model.ofNatBits (format := format) code.toNat
  have hbits : value.toNatBits = code.toNat :=
    Model.toNatBits_ofNatBits_of_lt code.toNat hcode
  unfold magnitudeNat Model.magnitudeBits
  rw [Model.signBit_ofNatBits_eq_decide format code.toNat hcode, hbits]

/--
Decoded dyadic magnitude fields depend only on the unsigned posit magnitude.

The sign is overwritten on purpose, since it is the one decoded dyadic field that depends on the
original complete word and not on its two's-complement magnitude.
-/
theorem decodeFields_toDyadic_eq_of_magnitudeBits_eq
    (left right : Model format)
    (hmagnitude : left.magnitudeBits = right.magnitudeBits) :
    { left.decodeFields.toDyadic with negative := right.signBit } =
      right.decodeFields.toDyadic := by
  have hregimeBit : left.regimeBit = right.regimeBit := by
    unfold Model.regimeBit
    rw [hmagnitude]
  have hrun : left.regimeRunLength = right.regimeRunLength := by
    unfold Model.regimeRunLength
    rw [hmagnitude, hregimeBit]
  have hterminator :
      left.hasRegimeTerminator = right.hasRegimeTerminator := by
    unfold Model.hasRegimeTerminator
    rw [hrun]
  have htrailing : left.trailingBits = right.trailingBits := by
    unfold Model.trailingBits
    rw [hrun, hterminator]
  have hused : left.usedExponentBits = right.usedExponentBits := by
    unfold Model.usedExponentBits
    rw [htrailing]
  have hfractionBits : left.fractionBits = right.fractionBits := by
    unfold Model.fractionBits
    rw [htrailing, hused]
  have hfractionField : left.fractionField = right.fractionField := by
    unfold Model.fractionField
    rw [hmagnitude, hfractionBits]
  have hstored :
      left.storedExponentField = right.storedExponentField := by
    unfold Model.storedExponentField
    rw [hmagnitude, hfractionBits, hused]
  have hexponent : left.exponentField = right.exponentField := by
    unfold Model.exponentField
    rw [hstored, hused]
  have hregimeValue : left.regimeValue = right.regimeValue := by
    unfold Model.regimeValue
    rw [hregimeBit, hrun]
  have hscale : left.scale = right.scale := by
    unfold Model.scale
    rw [hregimeValue, hexponent, hfractionBits]
  simp only [Model.DecodedFields.toDyadic, Model.decodeFields]
  rw [hfractionBits, hfractionField, hscale]

/-- Native nonnegative-candidate decoding always clears the exact-dyadic sign field. -/
@[simp] theorem nonnegativeDyadicAt_negative (format : Format) (code : UInt64) :
    (nonnegativeDyadicAt format code).negative = false := by
  unfold nonnegativeDyadicAt
  split <;> rfl

end FloatLib.Floats.Formats.Posit.Model.NativeWord
