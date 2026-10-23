/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.LimbRound.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.ProductRound.Runtime

/-!
# Native two-word finite multiplication

This is the executable `64 x 64 -> 128` normal-product tier for one-word IEEE formats whose
significand product needs two words. Refinement proofs are in `TwoWordMul.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeTwoWordMul

open NativeSmallWord

/-- Capacity contract for a one-storage-word format whose product needs two native words. -/
def Eligible (fmt : FloatFormat) : Prop :=
  fmt.isIEEE = true ∧
    fmt.bitWidth ≤ 64 ∧
    32 ≤ fmt.fracWidth ∧
    fmt.fracWidth ≤ 62

/--
Two-word eligibility is decided from the descriptor fields. As for
`NativeSmallWord.StorageEligible`, the conditional form is inlined and simplifies for a closed
format.
-/
@[inline] instance (fmt : FloatFormat) : Decidable (Eligible fmt) :=
  if h : fmt.isIEEE = true ∧ fmt.bitWidth ≤ 64 ∧ 32 ≤ fmt.fracWidth ∧ fmt.fracWidth ≤ 62 then
    isTrue h
  else
    isFalse h

/-- Leading-bit position `2 * fracWidth` or `2 * fracWidth + 1` of a normalized two-word product. -/
@[inline] def productLeading (fmt : FloatFormat)
    (product : FloatLib.Numerics.FixedWord.UInt128) : UInt64 :=
  let lower := UInt64.ofNat (2 * fmt.fracWidth)
  let threshold :=
    (1 : UInt64) <<<
      UInt64.ofNat (2 * fmt.fracWidth + 1 - 64)
  if product.hi < threshold then lower else lower + 1

/--
Round an exact two-word product of two normal finite significands, returning the packed storage
word.
-/
@[inline] def roundNormalProductWord? (fmt : FloatFormat) (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : UInt64) : Option UInt64 :=
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let leading := productLeading fmt product
  let scale := (xExponent - 1) + (yExponent - 1)
  let position := leading + scale
  let normalThreshold :=
    UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 1)
  if position < normalThreshold then
    none
  else
    let rounded :=
      product.roundShiftRightEven
        (leading - UInt64.ofNat fmt.fracWidth).toNat
    NativeWordProduct.finishWord? fmt sign position rounded

/-- `roundNormalProductWord?` as a model value. -/
@[inline] def roundNormalProduct? (fmt : FloatFormat) (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : UInt64) :
    Option (Model fmt) :=
  (roundNormalProductWord? fmt sign xExponent yExponent xMantissa yMantissa).map ofWord

/--
Decode two normal finite storage words and try the reusable two-word product path, returning the
packed storage word of an accepted product. Carriers that store the encoding as a `UInt64` call it
on their words, so the product never becomes an exact-width model value.
-/
@[inline] def mulNormalWord? (fmt : FloatFormat) (xBits yBits : UInt64) : Option UInt64 :=
  NativeSmallWord.withNormalPairWord? fmt xBits yBits (roundNormalProductWord? fmt)

/-- `mulNormalWord?` as a model value, on the operands' storage words. -/
@[inline] def mulNormal? {fmt : FloatFormat}
    (x y : Model fmt) : Option (Model fmt) :=
  (mulNormalWord? fmt (toWord x) (toWord y)).map ofWord

end Model.NativeTwoWordMul
end FloatLib.Floats.Formats.BinaryInterchange
