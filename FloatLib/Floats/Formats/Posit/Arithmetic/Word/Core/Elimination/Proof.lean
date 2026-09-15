/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Elimination.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Fields.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Decode.Runtime

/-!
# Correctness of posit scalar-field elimination

The one-, two-, and three-operand continuation interfaces agree with the total posit decoder.
Executable eliminators live in
`FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Elimination.Runtime`.

The continuation shape lets hot kernels consume decoded fields without allocating intermediate
records. These theorems show that the optimization only changes data flow: zero, NaR, sign, scale,
and significand branches are exactly those of the ordinary decoder for every supported word-sized
posit descriptor.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWord

open FloatLib.Numerics

/--
Scalar-field elimination agrees with case analysis on the total dyadic decoder.

This theorem is the refinement boundary used by flattened packed-word kernels. It allows compiler
optimizations to remove intermediate records while all arithmetic proofs continue to target
`toDyadic?`.
-/
theorem withDyadicFields_eq {α : Type}
    (format : Format) (code : UInt64) (onNaR : α)
    (continuation : Bool → Nat → Int → α) :
    withDyadicFields format code onNaR continuation =
      match toDyadic? format code with
      | none => onNaR
      | some value =>
          continuation value.negative value.significand value.exponent := by
  unfold withDyadicFields toDyadic?
  split
  next =>
    rfl
  next =>
    split
    next =>
      rfl
    next =>
      rw [withNonnegativeFields_eq]
      rfl

/-- The exact valid-word decoder is definitionally the `Nat` view of the word decoder. -/
theorem withDyadicFieldsValid_eq_word {α : Type}
    (format : Format) (heligible : Eligible format)
    (code : UInt64) (hcode : code.toNat < format.modulus)
    (onNaR : α) (continuation : Bool → Nat → Int → α) :
    withDyadicFieldsValid format heligible code hcode onNaR continuation =
      withDyadicWordFieldsValid format heligible code hcode onNaR
        fun negative significand exponent =>
          continuation negative significand.toNat exponent :=
  rfl

/--
Taking the natural value of a valid native-word decode commutes with field elimination.

Fixed carriers use this theorem to relate a native-word result to a mathematical
`Nat` specification without exposing the decoder's exceptional, zero, or sign cases.
-/
theorem withDyadicWordFieldsValid_toNat
    (format : Format) (heligible : Eligible format)
    (code : UInt64) (hcode : code.toNat < format.modulus)
    (onNaR : UInt64)
    (continuation : Bool → UInt64 → Int → UInt64) :
    (withDyadicWordFieldsValid format heligible
        code hcode onNaR continuation).toNat =
      withDyadicWordFieldsValid format heligible
        code hcode onNaR.toNat
        fun negative significand exponent =>
          (continuation negative significand exponent).toNat := by
  unfold withDyadicWordFieldsValid withDyadicWordFieldsAt
  by_cases hnar : code == signMaskWord format
  · simp only [hnar, if_true]
  · simp only [hnar, Bool.false_eq_true, if_false]
    by_cases hzero : code == 0
    · simp only [hzero, if_true]
    · simp only [hzero, Bool.false_eq_true, if_false,
        withNonnegativeWordFieldsAtPayload_toNat]

/-- Valid-word scalar elimination is exactly the total scalar decoder. -/
theorem withDyadicFieldsValid_eq {α : Type}
    (format : Format) (heligible : Eligible format)
    (code : UInt64) (hcode : code.toNat < format.modulus)
    (onNaR : α) (continuation : Bool → Nat → Int → α) :
    withDyadicFieldsValid format heligible code hcode onNaR continuation =
      withDyadicFields format code onNaR continuation := by
  have hnar :
      (code == signMaskWord format) =
        (code.toNat == format.signMaskNat) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro equality
      have equalityNat := congrArg UInt64.toNat equality
      simpa [signMaskWord_toNat format heligible] using equalityNat
    · intro equality
      apply UInt64.toNat_inj.mp
      simpa [signMaskWord_toNat format heligible] using equality
  have hnegative :
      decide (signMaskWord format ≤ code) =
        decide (format.signMaskNat ≤ code.toNat) := by
    simp only [UInt64.le_iff_toNat_le,
      signMaskWord_toNat format heligible]
  have hmagnitude :
      magnitudeWordAt (signMaskWord format) (modulusWord format) code =
        UInt64.ofNat (magnitudeNat format code) := by
    simpa [magnitudeWord] using
      magnitudeWord_eq_ofNat_magnitudeNat format code heligible hcode
  unfold withDyadicFieldsValid withDyadicWordFieldsValid
    withDyadicWordFieldsAt withDyadicFields
  rw [hnar]
  split
  · rfl
  · split
    · rfl
    · rw [hnegative, hmagnitude]
      rfl

/-- Two-word scalar elimination agrees with case analysis on the exact dyadic decoder. -/
theorem withTwoDyadicFields_eq {α : Type}
    (format : Format) (left right : UInt64) (onNaR : α)
    (continuation :
      Bool → Nat → Int → Bool → Nat → Int → α) :
    withTwoDyadicFields format left right onNaR continuation =
      match toDyadic? format left, toDyadic? format right with
      | some leftValue, some rightValue =>
          continuation leftValue.negative leftValue.significand leftValue.exponent
            rightValue.negative rightValue.significand rightValue.exponent
      | _, _ =>
          onNaR := by
  unfold withTwoDyadicFields
  rw [withDyadicFields_eq]
  cases hleft : toDyadic? format left with
  | none =>
      rfl
  | some leftValue =>
      simp only
      rw [withDyadicFields_eq]
      cases hright : toDyadic? format right <;> rfl

/--
Preparing a descriptor once is semantically identical to nesting the scalar valid-word decoder.

The two-operand interface shares the descriptor constants while preserving each operand's
decoding result.
-/
theorem withTwoDyadicWordFieldsValid_eq_nested {α : Type}
    (format : Format) (heligible : Eligible format)
    (left : UInt64) (hleft : left.toNat < format.modulus)
    (right : UInt64) (hright : right.toNat < format.modulus)
    (onNaR : α)
    (continuation :
      Bool → UInt64 → Int → Bool → UInt64 → Int → α) :
    withTwoDyadicWordFieldsValid format heligible
        left hleft right hright onNaR continuation =
      withDyadicWordFieldsValid format heligible left hleft onNaR
        fun leftNegative leftSignificand leftExponent =>
          withDyadicWordFieldsValid format heligible right hright onNaR
            fun rightNegative rightSignificand rightExponent =>
              continuation leftNegative leftSignificand leftExponent
                rightNegative rightSignificand rightExponent :=
  rfl

/--
Taking the natural value of a two-operand native decode commutes with both continuations.

Arithmetic modules use this shared theorem when a fixed carrier retains the result as `UInt64`
but the reference kernel exposes its complete code as `Nat`.
-/
theorem withTwoDyadicWordFieldsValid_toNat
    (format : Format) (heligible : Eligible format)
    (left : UInt64) (hleft : left.toNat < format.modulus)
    (right : UInt64) (hright : right.toNat < format.modulus)
    (onNaR : UInt64)
    (continuation :
      Bool → UInt64 → Int → Bool → UInt64 → Int → UInt64) :
    (withTwoDyadicWordFieldsValid format heligible
        left hleft right hright onNaR continuation).toNat =
      withTwoDyadicWordFieldsValid format heligible
        left hleft right hright onNaR.toNat
        fun leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent =>
          (continuation leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent).toNat := by
  rw [withTwoDyadicWordFieldsValid_eq_nested,
    withTwoDyadicWordFieldsValid_eq_nested]
  simp only [withDyadicWordFieldsValid_toNat]

/--
The exact two-word eliminator is definitionally the `Nat` view of native-word
elimination.

This bridge lets packed arithmetic execute on machine scalars while its proof reuses the existing
exact dyadic-field path without a second decoder theorem.
-/
theorem withTwoDyadicFieldsValid_eq_word {α : Type}
    (format : Format) (heligible : Eligible format)
    (left : UInt64) (hleft : left.toNat < format.modulus)
    (right : UInt64) (hright : right.toNat < format.modulus)
    (onNaR : α)
    (continuation :
      Bool → Nat → Int → Bool → Nat → Int → α) :
    withTwoDyadicFieldsValid format heligible
        left hleft right hright onNaR continuation =
      withTwoDyadicWordFieldsValid format heligible
        left hleft right hright onNaR
        fun leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent =>
          continuation leftNegative leftSignificand.toNat leftExponent
            rightNegative rightSignificand.toNat rightExponent :=
  rfl

/-- Valid two-word elimination is exactly the total two-word scalar decoder. -/
theorem withTwoDyadicFieldsValid_eq {α : Type}
    (format : Format) (heligible : Eligible format)
    (left : UInt64) (hleft : left.toNat < format.modulus)
    (right : UInt64) (hright : right.toNat < format.modulus)
    (onNaR : α)
    (continuation :
      Bool → Nat → Int → Bool → Nat → Int → α) :
    withTwoDyadicFieldsValid format heligible
        left hleft right hright onNaR continuation =
      withTwoDyadicFields format left right onNaR continuation := by
  change
    withDyadicFieldsValid format heligible left hleft onNaR
      (fun leftNegative leftSignificand leftExponent =>
        withDyadicFieldsValid format heligible right hright onNaR
          fun rightNegative rightSignificand rightExponent =>
            continuation leftNegative leftSignificand leftExponent
              rightNegative rightSignificand rightExponent) =
      withTwoDyadicFields format left right onNaR continuation
  unfold withTwoDyadicFields
  simp_rw [withDyadicFieldsValid_eq]

/-- Three-word scalar elimination agrees with exact dyadic decoding. -/
theorem withThreeDyadicFields_eq {α : Type}
    (format : Format) (left right addend : UInt64) (onNaR : α)
    (continuation :
      Bool → Nat → Int →
      Bool → Nat → Int →
      Bool → Nat → Int → α) :
    withThreeDyadicFields format left right addend onNaR continuation =
      match toDyadic? format left, toDyadic? format right,
          toDyadic? format addend with
      | some leftValue, some rightValue, some addendValue =>
          continuation leftValue.negative leftValue.significand leftValue.exponent
            rightValue.negative rightValue.significand rightValue.exponent
            addendValue.negative addendValue.significand addendValue.exponent
      | _, _, _ =>
          onNaR := by
  unfold withThreeDyadicFields
  rw [withDyadicFields_eq]
  cases hleft : toDyadic? format left with
  | none =>
      rfl
  | some leftValue =>
      simp only
      rw [withDyadicFields_eq]
      cases hright : toDyadic? format right with
      | none =>
          rfl
      | some rightValue =>
          simp only
          rw [withDyadicFields_eq]
          cases haddend : toDyadic? format addend <;> rfl

/--
Preparing a descriptor once is semantically identical to three nested valid-word decoders.

The three-operand interface shares the descriptor constants while preserving each operand's
decoding result.
-/
theorem withThreeDyadicWordFieldsValid_eq_nested {α : Type}
    (format : Format) (heligible : Eligible format)
    (left : UInt64) (hleft : left.toNat < format.modulus)
    (right : UInt64) (hright : right.toNat < format.modulus)
    (addend : UInt64) (haddend : addend.toNat < format.modulus)
    (onNaR : α)
    (continuation :
      Bool → UInt64 → Int →
      Bool → UInt64 → Int →
      Bool → UInt64 → Int → α) :
    withThreeDyadicWordFieldsValid format heligible
        left hleft right hright addend haddend onNaR continuation =
      withDyadicWordFieldsValid format heligible left hleft onNaR
        fun leftNegative leftSignificand leftExponent =>
          withDyadicWordFieldsValid format heligible right hright onNaR
            fun rightNegative rightSignificand rightExponent =>
              withDyadicWordFieldsValid format heligible addend haddend onNaR
                fun addendNegative addendSignificand addendExponent =>
                  continuation leftNegative leftSignificand leftExponent
                    rightNegative rightSignificand rightExponent
                    addendNegative addendSignificand addendExponent :=
  rfl

/--
Taking the natural value of a three-operand native decode commutes with every continuation.

Fused fixed-carrier kernels use this bridge to retain a word-valued result while refining the
existing exact field implementation.
-/
theorem withThreeDyadicWordFieldsValid_toNat
    (format : Format) (heligible : Eligible format)
    (left : UInt64) (hleft : left.toNat < format.modulus)
    (right : UInt64) (hright : right.toNat < format.modulus)
    (addend : UInt64) (haddend : addend.toNat < format.modulus)
    (onNaR : UInt64)
    (continuation :
      Bool → UInt64 → Int →
      Bool → UInt64 → Int →
      Bool → UInt64 → Int → UInt64) :
    (withThreeDyadicWordFieldsValid format heligible
        left hleft right hright addend haddend onNaR continuation).toNat =
      withThreeDyadicWordFieldsValid format heligible
        left hleft right hright addend haddend onNaR.toNat
        fun leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent
            addendNegative addendSignificand addendExponent =>
          (continuation
            leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent
            addendNegative addendSignificand addendExponent).toNat := by
  rw [withThreeDyadicWordFieldsValid_eq_nested,
    withThreeDyadicWordFieldsValid_eq_nested]
  simp only [withDyadicWordFieldsValid_toNat]

/-- Valid three-word elimination is exactly the total three-word scalar decoder. -/
theorem withThreeDyadicFieldsValid_eq {α : Type}
    (format : Format) (heligible : Eligible format)
    (left : UInt64) (hleft : left.toNat < format.modulus)
    (right : UInt64) (hright : right.toNat < format.modulus)
    (addend : UInt64) (haddend : addend.toNat < format.modulus)
    (onNaR : α)
    (continuation :
      Bool → Nat → Int →
      Bool → Nat → Int →
      Bool → Nat → Int → α) :
    withThreeDyadicFieldsValid format heligible
        left hleft right hright addend haddend onNaR continuation =
      withThreeDyadicFields format left right addend onNaR continuation := by
  change
    withDyadicFieldsValid format heligible left hleft onNaR
      (fun leftNegative leftSignificand leftExponent =>
        withDyadicFieldsValid format heligible right hright onNaR
          fun rightNegative rightSignificand rightExponent =>
            withDyadicFieldsValid format heligible addend haddend onNaR
              fun addendNegative addendSignificand addendExponent =>
                continuation leftNegative leftSignificand leftExponent
                  rightNegative rightSignificand rightExponent
                  addendNegative addendSignificand addendExponent) =
      withThreeDyadicFields format left right addend onNaR continuation
  unfold withThreeDyadicFields
  simp_rw [withDyadicFieldsValid_eq]

end FloatLib.Floats.Formats.Posit.Model.NativeWord
