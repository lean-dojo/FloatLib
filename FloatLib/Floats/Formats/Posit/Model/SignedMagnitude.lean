/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Model.Basic

/-!
# Posit sign and unsigned magnitude

Posit negation is two's complement over the complete encoded word. Field decoding works on the
corresponding unsigned magnitude, so this module isolates the representation laws connecting the
two views.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit

namespace Model

variable {format : Format}

/--
Negate a posit by taking the two's complement of its entire encoded word.

This operation fixes both zero and NaR and exchanges every positive finite code with its negative
counterpart, exactly as specified by the posit encoding.
-/
@[inline] def neg (value : Model format) : Model format :=
  ofNatBits (format.modulus - value.toNatBits)

/-- Posit negation fixes the unique zero encoding. -/
@[simp] theorem neg_zero (format : Format) :
    neg (zero format) = zero format := by
  change
    ofBits (BitVec.ofNat format.bits
      (format.modulus - (BitVec.ofNat format.bits 0).toNat)) =
      ofBits (BitVec.ofNat format.bits 0)
  apply congrArg ofBits
  apply BitVec.eq_of_toNat_eq
  simp [Format.modulus]

/-- Posit two's-complement negation fixes the unique NaR encoding. -/
@[simp] theorem neg_nar (format : Format) :
    neg (nar format) = nar format := by
  simp only [neg, nar_toNatBits, Format.modulus_eq_two_mul_signMaskNat,
    Nat.two_mul, Nat.add_sub_cancel_left]
  rfl

/-- Whether the encoded sign bit is set. -/
@[inline] def signBit (value : Model format) : Bool :=
  value.bits.msb

/-- Sign-bit inspection is unsigned comparison with the descriptor's sign mask. -/
theorem signBit_eq_decide (value : Model format) :
    value.signBit =
      decide (format.signMaskNat ≤ value.toNatBits) := by
  unfold signBit
  rw [BitVec.msb_eq_decide]
  rfl

/-- Exact-width encoding exposes the expected sign for every in-range natural word. -/
theorem signBit_ofNatBits_eq_decide (format : Format) (code : Nat)
    (hcode : code < format.modulus) :
    (ofNatBits (format := format) code).signBit =
      decide (format.signMaskNat ≤ code) := by
  rw [signBit_eq_decide, toNatBits_ofNatBits_of_lt code hcode]

/-- An in-range word below the sign mask has a clear sign bit. -/
theorem signBit_ofNatBits_eq_false (format : Format) (code : Nat)
    (hcode : code < format.signMaskNat) :
    (ofNatBits (format := format) code).signBit = false := by
  rw [signBit_ofNatBits_eq_decide format code
    (lt_trans hcode format.signMaskNat_lt_modulus)]
  exact decide_eq_false (Nat.not_le.mpr hcode)

/--
Unsigned magnitude word used to decode the regime and trailing fields.

Negative posit encodings are the two's complement of the corresponding positive word.
-/
@[inline] def magnitudeBits (value : Model format) : Nat :=
  if value.signBit then
    format.modulus - value.toNatBits
  else
    value.toNatBits

/-- A nonnegative in-range encoding is its own unsigned decoding magnitude. -/
theorem magnitudeBits_ofNatBits_of_lt_signMask
    (format : Format) (code : Nat)
    (hcode : code < format.signMaskNat) :
    (ofNatBits (format := format) code).magnitudeBits = code := by
  unfold magnitudeBits
  rw [signBit_ofNatBits_eq_false format code hcode]
  exact toNatBits_ofNatBits_of_lt code
    (lt_trans hcode format.signMaskNat_lt_modulus)

/-- Every posit other than NaR has unsigned magnitude strictly below the sign mask. -/
theorem magnitudeBits_lt_signMask_of_ne_nar
    (value : Model format)
    (hnar : value ≠ nar format) :
    value.magnitudeBits < format.signMaskNat := by
  have hcode := toNatBits_lt_modulus value
  have htwice := Format.modulus_eq_two_mul_signMaskNat format
  have hnotSignMask : value.toNatBits ≠ format.signMaskNat := by
    intro equality
    apply hnar
    rw [← ofNatBits_toNatBits value, equality]
    rfl
  unfold magnitudeBits
  rw [signBit_eq_decide]
  by_cases hnegative : format.signMaskNat ≤ value.toNatBits
  · simp only [decide_eq_true hnegative, if_true]
    omega
  · simp only [decide_eq_false hnegative, Bool.false_eq_true, if_false]
    omega

/-- Every nonzero posit has nonzero unsigned magnitude. -/
theorem magnitudeBits_ne_zero_of_ne_zero
    (value : Model format)
    (hzero : value ≠ zero format) :
    value.magnitudeBits ≠ 0 := by
  have hcode := toNatBits_lt_modulus value
  have hcodeNonzero : value.toNatBits ≠ 0 := by
    intro equality
    apply hzero
    rw [← ofNatBits_toNatBits value, equality]
    rfl
  unfold magnitudeBits
  rw [signBit_eq_decide]
  by_cases hnegative : format.signMaskNat ≤ value.toNatBits
  · simp only [decide_eq_true hnegative, if_true]
    omega
  · simp only [decide_eq_false hnegative, Bool.false_eq_true, if_false]
    exact hcodeNonzero

end Model
end FloatLib.Floats.Formats.Posit
