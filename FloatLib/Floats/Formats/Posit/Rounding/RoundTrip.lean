/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Proof
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof
import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Fields.Proof

/-!
# Exact posit decoding and rounding round trips

Rounding an exactly decoded finite posit recovers its original word at every descriptor width.
The sign/magnitude lemmas isolate whole-word two's-complement symmetry so character conversion,
integer functions, and changes of precision can reuse the same decoding argument.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/-- Restore the complete word from its sign and unsigned magnitude. -/
theorem ofNatBits_magnitudeBits (value : Model format) :
    (if value.signBit then neg (ofNatBits value.magnitudeBits)
      else ofNatBits value.magnitudeBits) = value := by
  cases hsign : value.signBit with
  | false => simp [magnitudeBits, hsign]
  | true =>
      have hcode := value.toNatBits_lt_modulus
      have hsignCode : format.signMaskNat ≤ value.toNatBits := by
        simpa [signBit_eq_decide] using hsign
      have hpositive : 0 < value.toNatBits := lt_of_lt_of_le format.signMaskNat_pos hsignCode
      simp only [hsign, ite_true, magnitudeBits, neg]
      rw [toNatBits_ofNatBits_of_lt _ (by omega),
        Nat.sub_sub_self hcode.le, ofNatBits_toNatBits]

/-- Decoded fields factor as their sign times the exact value of the unsigned magnitude word. -/
theorem decodeFields_toRat_eq_signed_magnitude (value : Model format)
    (hnar : value ≠ nar format) (hzero : value ≠ zero format) :
    value.decodeFields.toRat =
      if value.signBit then -nonnegativeRatAt format value.magnitudeBits
      else nonnegativeRatAt format value.magnitudeBits := by
  have hbound := magnitudeBits_lt_signMask_of_ne_nar value hnar
  have hpositive := Nat.pos_of_ne_zero (magnitudeBits_ne_zero_of_ne_zero value hzero)
  rw [nonnegativeRatAt_of_pos_lt_signMask format hpositive hbound]
  have hmag := magnitudeBits_ofNatBits_of_lt_signMask format value.magnitudeBits hbound
  have hsign := signBit_ofNatBits_eq_false format value.magnitudeBits hbound
  have hfields := NativeWord.decodeFields_toDyadic_eq_of_magnitudeBits_eq
    (ofNatBits value.magnitudeBits) value hmag
  simp only [DecodedFields.toRat]
  rw [← hfields]
  let magnitude := (ofNatBits (format := format) value.magnitudeBits).decodeFields.toDyadic
  have hnegative : magnitude.negative = false := hsign
  change ({ magnitude with negative := value.signBit } : FloatLib.Numerics.Dyadic).toRat =
    if value.signBit then -magnitude.toRat else magnitude.toRat
  rcases Bool.eq_false_or_eq_true value.signBit with hsignValue | hsignValue <;>
    simp [FloatLib.Numerics.Dyadic.toRat, FloatLib.Numerics.Dyadic.signedSignificand,
      hnegative, hsignValue]

/-- Every finite word, including zero, decodes as its signed unsigned-magnitude value. -/
theorem toRat?_eq_signed_magnitude (value : Model format) (hnar : value ≠ nar format) :
    value.toRat? = some (if value.signBit then -nonnegativeRatAt format value.magnitudeBits
      else nonnegativeRatAt format value.magnitudeBits) := by
  by_cases hzero : value = zero format
  · subst value
    have hmag : (zero format).magnitudeBits = 0 :=
      magnitudeBits_ofNatBits_of_lt_signMask format 0 format.signMaskNat_pos
    simp [hmag]
  · have hn : value.isNaR = false := beq_eq_false_iff_ne.mpr hnar
    have hz : value.isZero = false := beq_eq_false_iff_ne.mpr hzero
    simp only [toRat?, decodeExact, hn, hz, Bool.false_eq_true, ite_false,
      ExactValue.toRat?]
    rw [decodeFields_toRat_eq_signed_magnitude value hnar hzero]

/-- Standard posit rounding is a left inverse of exact rational decoding at every width. -/
theorem roundRat_toRat? (value : Model format) (exact : Rat)
    (hexact : value.toRat? = some exact) :
    roundRat format exact = value := by
  by_cases hnar : value = nar format
  · subst value
    simp at hexact
  by_cases hzero : value = zero format
  · subst value
    simp only [toRat?_zero, Option.some.injEq] at hexact
    subst exact
    exact roundRat_zero format
  have hnarBool : value.isNaR = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hnar ((isNaR_eq_true_iff value).mp h)
  have hzeroBool : value.isZero = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hzero ((isZero_eq_true_iff value).mp h)
  have hfields : value.decodeFields.toRat = exact := by
    simpa [toRat?, decodeExact, hnarBool, hzeroBool, ExactValue.toRat?] using hexact
  rw [← hfields, decodeFields_toRat_eq_signed_magnitude value hnar hzero]
  have hbound := magnitudeBits_lt_signMask_of_ne_nar value hnar
  have hpositive := nonnegativeRatAt_pos format
    (Nat.pos_of_ne_zero (magnitudeBits_ne_zero_of_ne_zero value hzero)) hbound
  cases hsign : value.signBit with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [roundRat_nonnegativeRatAt format hbound]
      simpa [hsign] using ofNatBits_magnitudeBits value
  | true =>
      simp only [ite_true]
      rw [roundRat_of_neg (neg_lt_zero.mpr hpositive), neg_neg,
        roundPositiveRat_nonnegativeRatAt format hbound]
      simpa [hsign] using ofNatBits_magnitudeBits value

end FloatLib.Floats.Formats.Posit.Model
