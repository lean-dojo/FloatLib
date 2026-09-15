/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Product.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Quotient.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.SignedSum.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.SquareRoot.Proof

/-!
# Shared proofs for fixed-word posit backends

The executable boundaries for `UInt8`, `UInt16`, `UInt32`, and `UInt64` remain separate so Lean
can compile each one with its native calling convention. Their range arguments, however, are
mathematical facts about the posit format rather than the carrier. This module holds those shared
facts and keeps them out of the specialized runtime files.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords

variable {format : Format} {capacity observed exactResult : Nat}

/--
A result below the exact format modulus also fits any carrier at least as wide as the format.
-/
theorem result_lt_capacity
    (width_le : format.bits ≤ capacity)
    (result_lt : exactResult < format.modulus) :
    exactResult < 2 ^ capacity :=
  lt_of_lt_of_le result_lt <| by
    unfold Format.modulus
    exact Nat.pow_le_pow_right (by decide) width_le

/--
Reducing an exact format result modulo a sufficiently wide carrier does not change the result.
-/
theorem result_mod_capacity
    (width_le : format.bits ≤ capacity)
    (result_lt : exactResult < format.modulus) :
    exactResult % 2 ^ capacity = exactResult :=
  Nat.mod_eq_of_lt (result_lt_capacity width_le result_lt)

/--
An observed result remains below the format modulus when narrowing to the carrier preserves
the exact result.
-/
theorem observed_lt_modulus
    (width_le : format.bits ≤ capacity)
    (observed_eq : observed = exactResult % 2 ^ capacity)
    (result_lt : exactResult < format.modulus) :
    observed < format.modulus := by
  rw [observed_eq, result_mod_capacity width_le result_lt]
  exact result_lt

/-! ## Packed-word range invariants -/

/-- Packed native-word addition returns a valid posit code. -/
theorem packedAdd_lt_modulus
    (eligible : Model.NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    (Model.NativeWordArithmetic.PackedSignedSum.addWordsCodeWordValid
      eligible left right hleft hright).toNat < format.modulus := by
  rw [Model.NativeWordArithmetic.PackedSignedSum.addWordsCodeWordValid_toNat]
  exact Model.NativeWordArithmetic.addWordsCodeFlatValid_lt_modulus
    eligible left right hleft hright

/-- Packed native-word subtraction returns a valid posit code. -/
theorem packedSub_lt_modulus
    (eligible : Model.NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    (Model.NativeWordArithmetic.PackedSignedSum.subWordsCodeWordValid
      eligible left right hleft hright).toNat < format.modulus := by
  rw [Model.NativeWordArithmetic.PackedSignedSum.subWordsCodeWordValid_toNat]
  exact Model.NativeWordArithmetic.subWordsCodeFlatValid_lt_modulus
    eligible left right hleft hright

/-- Packed native-word multiplication returns a valid posit code. -/
theorem packedMul_lt_modulus
    (eligible : Model.NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    (Model.NativeWordArithmetic.PackedProduct.mulWordsCodeWordValid
      eligible left right hleft hright).toNat < format.modulus := by
  rw [Model.NativeWordArithmetic.PackedProduct.mulWordsCodeWordValid_toNat]
  exact Model.NativeWordArithmetic.PackedProduct.mulWordsCodeValid_lt_modulus
    eligible left right hleft hright

/-- Packed native-word division returns a valid posit code. -/
theorem packedDiv_lt_modulus
    (eligible : Model.NativeWord.Eligible format)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) :
    (Model.NativeWordArithmetic.PackedQuotient.divWordsCodeWordValid
      eligible left right hleft hright).toNat < format.modulus := by
  rw [Model.NativeWordArithmetic.PackedQuotient.divWordsCodeWordValid_toNat]
  exact Model.NativeWordArithmetic.PackedQuotient.divWordsCodeValid_lt_modulus
    eligible left right hleft hright

/-- Packed native-word square root returns a valid posit code. -/
theorem packedSqrt_lt_modulus
    (eligible : Model.NativeWord.Eligible format)
    (value : UInt64)
    (hvalue : value.toNat < format.modulus) :
    (Model.NativeWordArithmetic.PackedSquareRoot.sqrtWordCodeWordValid
      eligible value hvalue).toNat < format.modulus := by
  rw [Model.NativeWordArithmetic.PackedSquareRoot.sqrtWordCodeWordValid_toNat]
  exact Model.NativeWordArithmetic.PackedSquareRoot.sqrtWordCodeValid_lt_modulus
    eligible value hvalue

/-- Packed native-word fused multiply-add returns a valid posit code. -/
theorem packedFma_lt_modulus
    (eligible : Model.NativeWord.Eligible format)
    (left right addend : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus)
    (haddend : addend.toNat < format.modulus) :
    (Model.NativeWordArithmetic.PackedSignedSum.fmaWordsCodeWordValid
      eligible left right addend hleft hright haddend).toNat <
        format.modulus := by
  rw [Model.NativeWordArithmetic.PackedSignedSum.fmaWordsCodeWordValid_toNat]
  exact Model.NativeWordArithmetic.fmaWordsCodeFlatValid_lt_modulus
    eligible left right addend hleft hright haddend

end FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords
