/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Model.Fields

/-!
# Exact posit decoding

Every posit word is classified, and ordinary values decode into the shared exact dyadic carrier.
The one-pass compiled decoder is proved equal to the transparent field-based definition.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit

open FloatLib.Numerics

namespace Model

variable {format : Format}

/--
Decode a nonzero finite posit code directly into the shared dyadic execution carrier.

The sign and complete encoded word are supplied separately so callers that already classified the
word can reuse the same extraction. `decodeFiniteDyadic` below remains the model-facing boundary.
-/
@[noinline] def decodeFiniteDyadicCode
    (format : Format) (negative : Bool) (code : Nat) :
    FloatLib.Numerics.Dyadic :=
  let magnitude :=
    if negative then
      format.modulus - code
    else
      code
  let regimeBit := magnitude.testBit (format.payloadBits - 1)
  let regimeRunLength :=
    countLeadingRun magnitude format.payloadBits regimeBit
  let hasRegimeTerminator : Bool :=
    regimeRunLength < format.payloadBits
  let trailingBits :=
    format.payloadBits - regimeRunLength -
      (if hasRegimeTerminator then 1 else 0)
  let usedExponentBits :=
    min format.exponentBits trailingBits
  let fractionBits :=
    trailingBits - usedExponentBits
  let fractionModulus :=
    2 ^ fractionBits
  let fractionField :=
    magnitude % fractionModulus
  let storedExponentField :=
    magnitude / fractionModulus % 2 ^ usedExponentBits
  let exponentField :=
    storedExponentField * 2 ^ (format.exponentBits - usedExponentBits)
  let regimeValue : Int :=
    if regimeBit then
      Int.ofNat regimeRunLength - 1
    else
      -Int.ofNat regimeRunLength
  let scale :=
    regimeValue * Int.ofNat format.regimeExponentStep +
      Int.ofNat exponentField - Int.ofNat fractionBits
  {
    negative
    significand := fractionModulus + fractionField
    exponent := scale
  }

/--
Decode a nonzero finite posit directly into the shared dyadic execution carrier.

This decoder computes sign restoration, regime scanning, and trailing-field powers once.
`decodeFields` exposes the same quantities as independent projections for proofs; the theorem
below establishes their equality.
-/
@[inline] def decodeFiniteDyadic
    (value : Model format) : FloatLib.Numerics.Dyadic :=
  decodeFiniteDyadicCode format value.signBit value.toNatBits

/-- The one-pass execution decoder agrees exactly with the proof-facing field decoder. -/
theorem decodeFiniteDyadic_eq_decodeFields_toDyadic
    (value : Model format) :
    value.decodeFiniteDyadic = value.decodeFields.toDyadic := by
  rfl

/-- Complete exact interpretation of a posit word. -/
inductive ExactValue (format : Format) where
  /-- The unique zero word. -/
  | zero
  /-- A nonzero finite dyadic rational together with its tapered fields. -/
  | finite (fields : DecodedFields format)
  /-- The unique Not-a-Real word. -/
  | nar
  deriving DecidableEq, Repr

/-- Decode every posit word, retaining its exact tapered fields. -/
@[inline] def decodeExact (value : Model format) : ExactValue format :=
  if value.isNaR then
    .nar
  else if value.isZero then
    .zero
  else
    .finite value.decodeFields

/--
One-pass compiled implementation of the optional exact-dyadic decoder.

Zero and NaR are handled before calling `decodeFiniteDyadic`, which decodes the nonzero finite
branch.
-/
@[inline] private def toDyadicImpl?
    (value : Model format) : Option FloatLib.Numerics.Dyadic :=
  let code := value.toNatBits
  if code == format.signMaskNat then
    none
  else if code == 0 then
    some FloatLib.Numerics.Dyadic.zero
  else
    some (decodeFiniteDyadicCode format value.signBit code)

/-- Characterize the nonzero finite branch of exact posit decoding. -/
theorem decodeExact_eq_finite_iff
    (value : Model format) (fields : DecodedFields format) :
    value.decodeExact = .finite fields ↔
      value.isNaR = false ∧ value.isZero = false ∧
        value.decodeFields = fields := by
  by_cases hnar : value.isNaR = true
  · simp [decodeExact, hnar]
  · have hnarFalse := Bool.eq_false_of_not_eq_true hnar
    by_cases hzero : value.isZero = true
    · simp [decodeExact, hnarFalse, hzero]
    · have hzeroFalse := Bool.eq_false_of_not_eq_true hzero
      simp [decodeExact, hnarFalse, hzeroFalse]

/--
Decode the ordinary value directly into the shared exact dyadic carrier.

`none` identifies NaR exactly. The unique posit zero maps to the canonical dyadic zero; all other
words retain their exact sign, integer significand, and binary scale.
-/
@[implemented_by toDyadicImpl?, inline] def toDyadic?
    (value : Model format) : Option FloatLib.Numerics.Dyadic :=
  match value.decodeExact with
  | .zero => some FloatLib.Numerics.Dyadic.zero
  | .finite fields => some fields.toDyadic
  | .nar => none

/--
The one-pass compiled decoder is extensionally equal to the transparent logical decoder.

This proves equality of the Lean definitions used by `toDyadic?`'s `implemented_by` refinement.
-/
private theorem toDyadicImpl?_eq_toDyadic?
    (value : Model format) :
    value.toDyadicImpl? = value.toDyadic? := by
  by_cases hnar : value = nar format
  · subst value
    simp [toDyadicImpl?, toDyadic?, decodeExact]
  · have hnarCode : value.toNatBits ≠ format.signMaskNat := by
      intro equality
      apply hnar
      rw [← ofNatBits_toNatBits value, equality]
      rfl
    by_cases hzero : value = zero format
    · subst value
      have hsignMask : (0 : Nat) ≠ format.signMaskNat := by
        simpa [Format.signMaskNat] using
          (Nat.ne_of_lt (Nat.two_pow_pos format.signIndex))
      simp [toDyadicImpl?, toDyadic?, decodeExact, hsignMask]
    · have hzeroCode : value.toNatBits ≠ 0 := by
        intro equality
        apply hzero
        rw [← ofNatBits_toNatBits value, equality]
        rfl
      have hnarFalse : value.isNaR = false :=
        beq_eq_false_iff_ne.mpr hnar
      have hzeroFalse : value.isZero = false :=
        beq_eq_false_iff_ne.mpr hzero
      have hdecode :
          decodeFiniteDyadicCode format value.signBit value.toNatBits =
            value.decodeFields.toDyadic := by
        simpa only [decodeFiniteDyadic] using
          decodeFiniteDyadic_eq_decodeFields_toDyadic value
      simp [toDyadicImpl?, toDyadic?, decodeExact, hnarCode, hzeroCode,
        hnarFalse, hzeroFalse, hdecode]

/-- Exact decoding recognizes the unique posit zero word. -/
@[simp] theorem decodeExact_zero (format : Format) :
    decodeExact (zero format) = .zero := by
  simp [decodeExact]

/-- Exact decoding recognizes the unique posit NaR word. -/
@[simp] theorem decodeExact_nar (format : Format) :
    decodeExact (nar format) = .nar := by
  simp [decodeExact]

/-- The unique posit zero maps to the canonical shared dyadic zero. -/
@[simp] theorem toDyadic?_zero (format : Format) :
    toDyadic? (zero format) = some FloatLib.Numerics.Dyadic.zero := by
  simp [toDyadic?]

/-- NaR has no ordinary dyadic interpretation. -/
@[simp] theorem toDyadic?_nar (format : Format) :
    toDyadic? (nar format) = none := by
  simp [toDyadic?]

/-- An ordinary posit decodes to the dyadic value of its exact tapered fields. -/
theorem toDyadic?_eq_some_decodeFields
    (value : Model format)
    (hnar : value.isNaR = false)
    (hzero : value.isZero = false) :
    value.toDyadic? = some value.decodeFields.toDyadic := by
  unfold toDyadic?
  have hdecode :
      value.decodeExact = .finite value.decodeFields :=
    (decodeExact_eq_finite_iff value value.decodeFields).2
      ⟨hnar, hzero, rfl⟩
  rw [hdecode]

end Model
end FloatLib.Floats.Formats.Posit
