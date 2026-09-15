/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Model.SignedMagnitude
public import FloatLib.Numerics.Exact.Dyadic.Basic

/-!
# Tapered posit field decoding

Posit field decoding recovers the variable-length regime, tapered exponent, fraction,
significand, and binary scale from a model word. The resulting `DecodedFields` structure is the
common proof-facing boundary for exact semantics and optimized arithmetic.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit

open FloatLib.Numerics

namespace Model

variable {format : Format}

/--
Count a leading run in exactly `width` low bits of `value`, starting at bit `width - 1`.
-/
@[inline] def countLeadingRun (value : Nat) : (width : Nat) → Bool → Nat
  | 0, _ => 0
  | width + 1, bit =>
      if value.testBit width == bit then
        1 + countLeadingRun value width bit
      else
        0

/-- A leading run cannot consume more bits than the width being inspected. -/
theorem countLeadingRun_le (value width : Nat) (bit : Bool) :
    countLeadingRun value width bit ≤ width := by
  induction width with
  | zero =>
      simp [countLeadingRun]
  | succ width inductionHypothesis =>
      simp only [countLeadingRun]
      split
      · omega
      · omega

/-- Inspecting a nonempty word from its actual first bit finds a nonempty run. -/
theorem countLeadingRun_self_pos
    (value width : Nat) (hwidth : 0 < width) :
    0 <
      countLeadingRun value width
        (value.testBit (width - 1)) := by
  cases width with
  | zero =>
      contradiction
  | succ width =>
      simp [countLeadingRun]

/-- First regime bit in the magnitude payload. -/
@[inline] def regimeBit (value : Model format) : Bool :=
  value.magnitudeBits.testBit (format.payloadBits - 1)

/-- Number of equal leading regime bits. -/
@[inline] def regimeRunLength (value : Model format) : Nat :=
  countLeadingRun value.magnitudeBits format.payloadBits value.regimeBit

/-- The tapered regime consumes at most the complete payload. -/
theorem regimeRunLength_le_payload (value : Model format) :
    value.regimeRunLength ≤ format.payloadBits :=
  countLeadingRun_le _ _ _

/-- Every posit word has a nonempty leading regime run. -/
theorem regimeRunLength_pos (value : Model format) :
    0 < value.regimeRunLength := by
  unfold regimeRunLength regimeBit
  exact countLeadingRun_self_pos _ _
    (Format.payloadBits_pos format)

/-- Whether an opposite regime-terminator bit is present. -/
@[inline] def hasRegimeTerminator (value : Model format) : Bool :=
  value.regimeRunLength < format.payloadBits

/-- Bits available after the regime and its optional terminator. -/
@[inline] def trailingBits (value : Model format) : Nat :=
  format.payloadBits - value.regimeRunLength -
    (if value.hasRegimeTerminator then 1 else 0)

/-- Regime and trailing fields together fit inside the payload. -/
theorem regimeRunLength_add_trailingBits_le_payload
    (value : Model format) :
    value.regimeRunLength + value.trailingBits ≤ format.payloadBits := by
  unfold trailingBits
  have hrun := regimeRunLength_le_payload value
  split <;> omega

/-- Number of exponent bits actually present in this tapered encoding. -/
@[inline] def usedExponentBits (value : Model format) : Nat :=
  min format.exponentBits value.trailingBits

/-- Number of explicit fraction bits present in this tapered encoding. -/
@[inline] def fractionBits (value : Model format) : Nat :=
  value.trailingBits - value.usedExponentBits

/-- The explicit fraction is a subfield of the trailing payload. -/
theorem fractionBits_le_trailingBits (value : Model format) :
    value.fractionBits ≤ value.trailingBits := by
  simp [fractionBits]

/-- Regime and explicit fraction together never exceed the payload. -/
theorem regimeRunLength_add_fractionBits_le_payload
    (value : Model format) :
    value.regimeRunLength + value.fractionBits ≤ format.payloadBits := by
  calc
    value.regimeRunLength + value.fractionBits ≤
        value.regimeRunLength + value.trailingBits :=
      Nat.add_le_add_left
        (fractionBits_le_trailingBits value) _
    _ ≤ format.payloadBits :=
      regimeRunLength_add_trailingBits_le_payload value

/-- Low explicit fraction field. -/
@[inline] def fractionField (value : Model format) : Nat :=
  value.magnitudeBits % 2 ^ value.fractionBits

/-- Exponent bits physically present between the regime and fraction. -/
@[inline] def storedExponentField (value : Model format) : Nat :=
  value.magnitudeBits / 2 ^ value.fractionBits % 2 ^ value.usedExponentBits

/--
Full exponent value after restoring unavailable low bits as zeros.

Exponent bits are consumed most-significant first. Tapering therefore removes low exponent bits,
which is represented by this left shift.
-/
@[inline] def exponentField (value : Model format) : Nat :=
  value.storedExponentField * 2 ^ (format.exponentBits - value.usedExponentBits)

/-- At most the descriptor's two standard exponent bits are physically present. -/
theorem usedExponentBits_le_exponentBits (value : Model format) :
    value.usedExponentBits ≤ format.exponentBits := by
  simp [usedExponentBits]

/-- The restored standard exponent field is always below four. -/
theorem exponentField_lt_four (value : Model format) :
    value.exponentField < 4 := by
  have hstored :
      value.storedExponentField < 2 ^ value.usedExponentBits := by
    unfold storedExponentField
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hused : value.usedExponentBits ≤ format.exponentBits :=
    usedExponentBits_le_exponentBits value
  have hmul :
      value.storedExponentField *
          2 ^ (format.exponentBits - value.usedExponentBits) <
        2 ^ value.usedExponentBits *
          2 ^ (format.exponentBits - value.usedExponentBits) :=
    (Nat.mul_lt_mul_right
      (Nat.two_pow_pos
        (format.exponentBits - value.usedExponentBits))).mpr hstored
  rw [← Nat.pow_add, Nat.add_sub_of_le hused] at hmul
  simpa [exponentField, Format.exponentBits] using hmul

/-- Signed regime value `k`. -/
@[inline] def regimeValue (value : Model format) : Int :=
  if value.regimeBit then
    Int.ofNat value.regimeRunLength - 1
  else
    -Int.ofNat value.regimeRunLength

/-- Exact binary scale after accounting for the explicit fraction denominator. -/
@[inline] def scale (value : Model format) : Int :=
  value.regimeValue * Int.ofNat format.regimeExponentStep +
    Int.ofNat value.exponentField - Int.ofNat value.fractionBits

/-- Every decoded posit scale is no smaller than `-4` times its payload width. -/
theorem neg_four_payloadBits_le_scale (value : Model format) :
    -(4 * Int.ofNat format.payloadBits) ≤ value.scale := by
  have hrunPositive : 0 < value.regimeRunLength :=
    regimeRunLength_pos value
  have hfields :
      value.regimeRunLength + value.fractionBits ≤ format.payloadBits :=
    regimeRunLength_add_fractionBits_le_payload value
  have hrunPositiveInt : (0 : Int) < value.regimeRunLength := by
    exact_mod_cast hrunPositive
  have hfieldsInt :
      (value.regimeRunLength : Int) + value.fractionBits ≤
        format.payloadBits := by
    exact_mod_cast hfields
  have hstep :
      Int.ofNat format.regimeExponentStep = (4 : Int) :=
    rfl
  cases hbit : value.regimeBit with
  | false =>
      simp only [scale, regimeValue, hbit, Bool.false_eq_true, ite_false,
        hstep, Int.ofNat_eq_natCast]
      omega
  | true =>
      simp only [scale, regimeValue, hbit, ite_true,
        hstep, Int.ofNat_eq_natCast]
      omega

/-- Every decoded posit scale is strictly below four times its total encoded width. -/
theorem scale_lt_four_bits (value : Model format) :
    value.scale < 4 * Int.ofNat format.bits := by
  have hrun := regimeRunLength_le_payload value
  have hexponent := exponentField_lt_four value
  have hpayload : format.payloadBits + 1 = format.bits := by
    simpa only [Format.payloadBits] using
      Nat.sub_add_cancel
        (Nat.le_trans (by decide : 1 ≤ 2) format.bits_ge_two)
  have hrunInt :
      (value.regimeRunLength : Int) ≤ format.payloadBits := by
    exact_mod_cast hrun
  have hexponentInt : (value.exponentField : Int) < 4 := by
    exact_mod_cast hexponent
  have hpayloadInt : (format.payloadBits : Int) + 1 = format.bits := by
    exact_mod_cast hpayload
  have hstep :
      Int.ofNat format.regimeExponentStep = (4 : Int) :=
    rfl
  cases hbit : value.regimeBit with
  | false =>
      simp only [scale, regimeValue, hbit, Bool.false_eq_true, ite_false,
        hstep, Int.ofNat_eq_natCast]
      omega
  | true =>
      simp only [scale, regimeValue, hbit, ite_true,
        hstep, Int.ofNat_eq_natCast]
      omega

/--
At the minimum standard width, every word is zero, NaR, or one of the two encodings of unit
magnitude. The latter therefore has dyadic scale zero.

This boundary case complements the uniform payload bound used in quire proofs for widths
of at least three.
-/
theorem zero_or_nar_or_scale_eq_zero_of_bits_eq_two
    (value : Model format) (hbits : format.bits = 2) :
    value = zero format ∨ value = nar format ∨ value.scale = 0 := by
  have hcode := toNatBits_lt_modulus value
  simp only [Format.modulus, hbits] at hcode
  have hcases :
      value.toNatBits = 0 ∨ value.toNatBits = 1 ∨
        value.toNatBits = 2 ∨ value.toNatBits = 3 := by
    omega
  rcases hcases with hvalue | hvalue | hvalue | hvalue
  · left
    rw [← ofNatBits_toNatBits value, hvalue]
    rfl
  · right
    right
    have hencoded :
        (ofNatBits (format := format) 1).toNatBits = 1 := by
      apply toNatBits_ofNatBits_of_lt
      simp [Format.modulus, hbits]
    have hencodedBits :
        (ofNatBits (format := format) 1).bits.toNat = 1 :=
      hencoded
    rw [← ofNatBits_toNatBits value, hvalue]
    simp [scale, regimeValue, regimeRunLength, regimeBit, magnitudeBits,
      signBit, BitVec.msb_eq_decide, trailingBits, hasRegimeTerminator,
      fractionBits, usedExponentBits, exponentField, storedExponentField,
      Format.payloadBits, Format.exponentBits, Format.regimeExponentStep,
      hbits, hencoded, hencodedBits, countLeadingRun]
  · right
    left
    rw [← ofNatBits_toNatBits value, hvalue]
    apply congrArg ofBits
    apply BitVec.eq_of_toNat_eq
    simp [Format.signMaskNat, Format.signIndex, hbits]
  · right
    right
    have hencoded :
        (ofNatBits (format := format) 3).toNatBits = 3 := by
      apply toNatBits_ofNatBits_of_lt
      simp [Format.modulus, hbits]
    have hencodedBits :
        (ofNatBits (format := format) 3).bits.toNat = 3 :=
      hencoded
    rw [← ofNatBits_toNatBits value, hvalue]
    simp [scale, regimeValue, regimeRunLength, regimeBit, magnitudeBits,
      signBit, BitVec.msb_eq_decide, trailingBits, hasRegimeTerminator,
      fractionBits, usedExponentBits, exponentField, storedExponentField,
      Format.payloadBits, Format.exponentBits, Format.regimeExponentStep,
      Format.modulus, hbits, hencoded, hencodedBits, countLeadingRun]

/-- Complete decoded fields of a nonzero finite posit. -/
structure DecodedFields (format : Format) where
  /-- Sign of the represented finite value. -/
  negative : Bool
  /-- First bit of the variable-length regime. -/
  regimeBit : Bool
  /-- Number of repeated regime bits. -/
  regimeRunLength : Nat
  /-- Signed regime value. -/
  regimeValue : Int
  /-- Number of exponent bits physically present. -/
  usedExponentBits : Nat
  /-- Exponent after omitted low bits are restored as zero. -/
  exponentField : Nat
  /-- Number of explicit fraction bits. -/
  fractionBits : Nat
  /-- Explicit fraction field. -/
  fractionField : Nat
  /-- Positive integer significand, including its implicit leading bit. -/
  significand : Nat
  /-- Binary exponent applied to `significand`. -/
  scale : Int
  deriving DecidableEq, Repr

/-- Decode all fields of a nonzero finite posit word. -/
@[inline] def decodeFields (value : Model format) : DecodedFields format where
  negative := value.signBit
  regimeBit := value.regimeBit
  regimeRunLength := value.regimeRunLength
  regimeValue := value.regimeValue
  usedExponentBits := value.usedExponentBits
  exponentField := value.exponentField
  fractionBits := value.fractionBits
  fractionField := value.fractionField
  significand := 2 ^ value.fractionBits + value.fractionField
  scale := value.scale

/-- A decoded posit significand fits within the complete posit word's width. -/
theorem decodeFields_significand_lt_modulus (value : Model format) :
    value.decodeFields.significand < format.modulus := by
  have hfraction :
      value.fractionField < 2 ^ value.fractionBits := by
    unfold fractionField
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hsignificand :
      2 ^ value.fractionBits + value.fractionField <
        2 ^ (value.fractionBits + 1) := by
    calc
      2 ^ value.fractionBits + value.fractionField <
          2 ^ value.fractionBits + 2 ^ value.fractionBits :=
        Nat.add_lt_add_left hfraction _
      _ = 2 ^ (value.fractionBits + 1) := by
        rw [Nat.pow_succ]
        omega
  have hpayload : format.payloadBits + 1 = format.bits := by
    simpa only [Format.payloadBits] using
      Nat.sub_add_cancel
        (Nat.le_trans (by decide : 1 ≤ 2) format.bits_ge_two)
  have hfractionBits : value.fractionBits + 1 ≤ format.bits := by
    have hfields :=
      regimeRunLength_add_fractionBits_le_payload value
    have hrun := regimeRunLength_pos value
    omega
  apply lt_of_lt_of_le hsignificand
  unfold Format.modulus
  exact Nat.pow_le_pow_right (by decide) hfractionBits

/--
A decoded posit significand fits in the format payload.

The regime always consumes at least one payload bit, so the implicit leading significand bit
together with every explicit fraction bit occupies at most `payloadBits` positions.
-/
theorem decodeFields_significand_lt_two_pow_payloadBits
    (value : Model format) :
    value.decodeFields.significand < 2 ^ format.payloadBits := by
  have hfraction :
      value.fractionField < 2 ^ value.fractionBits := by
    unfold fractionField
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hsignificand :
      value.decodeFields.significand <
        2 ^ (value.fractionBits + 1) := by
    change
      2 ^ value.fractionBits + value.fractionField <
        2 ^ (value.fractionBits + 1)
    rw [Nat.pow_succ]
    omega
  have hfields :=
    regimeRunLength_add_fractionBits_le_payload value
  have hrun := regimeRunLength_pos value
  exact hsignificand.trans_le <|
    Nat.pow_le_pow_right (by decide) (by omega)

namespace DecodedFields

/-- Signed integer significand before applying the binary scale. -/
@[inline] def signedSignificand (fields : DecodedFields format) : Int :=
  if fields.negative then
    -Int.ofNat fields.significand
  else
    Int.ofNat fields.significand

/--
Format-independent exact dyadic value represented by these decoded fields.

Integer kernels use this value after the posit decoder recovers the tapered fields.
Other radix-two families use the same exact-number representation.
-/
@[inline] def toDyadic (fields : DecodedFields format) : FloatLib.Numerics.Dyadic :=
  { negative := fields.negative
    significand := fields.significand
    exponent := fields.scale }

/-- Exact dyadic rational represented by these decoded fields. -/
@[inline] def toRat (fields : DecodedFields format) : Rat :=
  fields.toDyadic.toRat

/-- Expanding `toDyadic` exposes the decoded sign, significand, and binary scale unchanged. -/
@[simp] theorem toDyadic_fields (fields : DecodedFields format) :
    fields.toDyadic =
      { negative := fields.negative
        significand := fields.significand
        exponent := fields.scale } :=
  rfl

end DecodedFields
end Model
end FloatLib.Floats.Formats.Posit
