/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Decode.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Word.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Direct.Runtime

/-!
# Native-word posit arithmetic runtime

The stored-word entry points decode `UInt64` operands without constructing exact-width `BitVec`
values and return complete result encodings directly. The model-valued kernels they refine are the
width-generic direct kernels in `DirectDyadicArithmetic`; `addWords_eq_add` and its siblings in
`Word.Arithmetic.Proof` state that refinement, so no second model-valued copy of the arithmetic is
maintained here. The kernels that the configured backend executes are the packed variants
`addWordsCodeFlatValid`, `subWordsCodeFlatValid`, `fmaWordsCodeFlatValid`,
`PackedProduct.mulWordsCodeValid`, `PackedQuotient.divWordsCodeValid`, and
`PackedSquareRoot.sqrtWordCodeValid`, together with the `PackedSignedSum.*WordValid` family.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic

open FloatLib.Numerics

variable {format : Format}

/-! ## Direct stored-word entry points -/

/--
Decode two packed words, add their exact dyadic values, and return the complete result encoding.

NaR propagation is represented directly by the unique sign-mask code. Ordinary results use the
encoded-word rounder, so callers that already own packed storage need not construct an
intermediate exact-width model.
-/
@[inline] def addWordsCode
    (_heligible : NativeWord.Eligible format)
    (left right : UInt64) : Nat :=
  match NativeWord.toDyadic? format left, NativeWord.toDyadic? format right with
  | some leftValue, some rightValue =>
      DirectDyadicPacking.roundCode format
        (FloatLib.Numerics.Dyadic.add leftValue rightValue)
  | _, _ =>
      format.signMaskNat

/-- Direct stored-word subtraction result encoding. -/
@[inline] def subWordsCode
    (_heligible : NativeWord.Eligible format)
    (left right : UInt64) : Nat :=
  match NativeWord.toDyadic? format left, NativeWord.toDyadic? format right with
  | some leftValue, some rightValue =>
      DirectDyadicPacking.roundCode format
        (FloatLib.Numerics.Dyadic.sub leftValue rightValue)
  | _, _ =>
      format.signMaskNat

/-- Direct stored-word multiplication result encoding. -/
@[inline] def mulWordsCode
    (_heligible : NativeWord.Eligible format)
    (left right : UInt64) : Nat :=
  match NativeWord.toDyadic? format left, NativeWord.toDyadic? format right with
  | some leftValue, some rightValue =>
      DirectDyadicPacking.roundCode format
        (FloatLib.Numerics.Dyadic.mul leftValue rightValue)
  | _, _ =>
      format.signMaskNat

/-- Direct stored-word division result encoding. -/
@[inline] def divWordsCode
    (_heligible : NativeWord.Eligible format)
    (left right : UInt64) : Nat :=
  match NativeWord.toDyadic? format left, NativeWord.toDyadic? format right with
  | some numerator, some denominator =>
      DirectDyadicQuotient.roundCode format numerator denominator
  | _, _ =>
      format.signMaskNat

/-- Direct stored-word square-root result encoding. -/
@[inline] def sqrtWordCode
    (_heligible : NativeWord.Eligible format)
    (value : UInt64) : Nat :=
  match NativeWord.toDyadic? format value with
  | none =>
      format.signMaskNat
  | some radicand =>
      if radicand.isLess FloatLib.Numerics.Dyadic.zero then
        format.signMaskNat
      else
        DirectDyadicSquareRoot.roundCode format radicand

/-- Direct stored-word fused multiply-add result encoding. -/
@[inline] def fmaWordsCode
    (_heligible : NativeWord.Eligible format)
    (left right addend : UInt64) : Nat :=
  match NativeWord.toDyadic? format left, NativeWord.toDyadic? format right,
      NativeWord.toDyadic? format addend with
  | some leftValue, some rightValue, some addendValue =>
      DirectDyadicPacking.roundCode format
        (FloatLib.Numerics.Dyadic.add
          (FloatLib.Numerics.Dyadic.mul leftValue rightValue)
          addendValue)
  | _, _, _ =>
      format.signMaskNat

/--
Decode two packed words directly, add their exact dyadic values, and round once.

This wraps `addWordsCode` in the model carrier. Its refinement theorem requires each stored
operand to fit the format width.
-/
@[inline] def addWords
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) : Model format :=
  Model.ofNatBits (addWordsCode heligible left right)

/-- Direct stored-word subtraction. -/
@[inline] def subWords
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) : Model format :=
  Model.ofNatBits (subWordsCode heligible left right)

/-- Direct stored-word multiplication. -/
@[inline] def mulWords
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) : Model format :=
  Model.ofNatBits (mulWordsCode heligible left right)

/-- Direct stored-word division. -/
@[inline] def divWords
    (heligible : NativeWord.Eligible format)
    (left right : UInt64) : Model format :=
  Model.ofNatBits (divWordsCode heligible left right)

/-- Direct stored-word square root. -/
@[inline] def sqrtWord
    (heligible : NativeWord.Eligible format)
    (value : UInt64) : Model format :=
  Model.ofNatBits (sqrtWordCode heligible value)

/-- Direct stored-word fused multiply-add with one final rounding step. -/
@[inline] def fmaWords
    (heligible : NativeWord.Eligible format)
    (left right addend : UInt64) : Model format :=
  Model.ofNatBits (fmaWordsCode heligible left right addend)

end FloatLib.Floats.Formats.Posit.Model.NativeWordArithmetic
