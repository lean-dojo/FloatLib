/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Add.Runtime

/-!
# Native one-word finite fused multiply-add

The native FMA path serves conventional IEEE formats with at most 29 fraction bits (`Eligible`),
which include binary16, bfloat16, and the eight-bit formats. It is the word-tier counterpart of the
IEEE branch of `FiniteKernel.Internal.fmaComponents`. The exact product of the two significands and
the addend significand are placed at unsigned scales in the product rounder's coordinate and passed
to the same signed-magnitude helpers as one-word addition, with scale offset `0`. With at most
`2 * fracWidth + 2 ≤ 60` bits in the product, every aligned sum and every sticky magnitude fits in
`UInt64`. Refinement proofs are in `Fma.Proof`.

It returns `none` for exceptional operands, a zero product, a wide alignment that the sticky path
declines, results below the normal threshold before rounding, and overflow after rounding. The
dispatcher then tries the native-storage component kernel, which returns the addend of a zero
product as it is.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordFma

open NativeSmallWord NativeSmallWordAdd

/--
Capacity contract of the one-word FMA kernel.

A significand has at most `fracWidth + 1` bits, so the exact product of two significands is
below `2 ^ 60`, and the exponent bound keeps every product-coordinate scale below `2 ^ 33`.
-/
def Eligible (fmt : FloatFormat) : Prop :=
  fmt.isIEEE = true ∧
    fmt.bitWidth ≤ 64 ∧
    fmt.expWidth ≤ 30 ∧
    fmt.fracWidth ≤ 29

/--
FMA eligibility is decided from the descriptor fields. As for `NativeSmallWord.StorageEligible`,
the conditional form is inlined and simplifies for a closed format.
-/
@[inline] instance (fmt : FloatFormat) : Decidable (Eligible fmt) :=
  if h : fmt.isIEEE = true ∧ fmt.bitWidth ≤ 64 ∧ fmt.expWidth ≤ 30 ∧ fmt.fracWidth ≤ 29 then
    isTrue h
  else
    isFalse h

/--
Largest shift of the exact product above the addend that stays exact: the product has at most
`2 * fracWidth + 2` bits, so shifting it left by `61 - 2 * fracWidth` keeps it below `2 ^ 63`.
-/
@[inline] def productShiftLimit (fmt : FloatFormat) : UInt64 :=
  61 - 2 * UInt64.ofNat fmt.fracWidth

/--
Round `product * 2 ^ productScale + addend * 2 ^ addendScale` once, in product coordinates.

The signs belong to the product and the addend. A zero addend rounds the product alone. Otherwise
the operand at the larger scale is shifted left onto the smaller one when the shift is exact
(`shiftLimit` for the addend, `productShiftLimit` for the product), and larger gaps go through the
sticky alignment of `roundJammed?`. A zero product returns `none`.
-/
@[inline] def fmaFields? (fmt : FloatFormat)
    (productSign : Bool) (product productScale : UInt64)
    (addendSign : Bool) (addend addendScale : UInt64) : Option (Model fmt) :=
  if product == 0 then
    none
  else if addend == 0 then
    roundMagnitude? fmt 0 productSign product productScale
  else if productScale ≤ addendScale then
    let shift := addendScale - productScale
    if shift ≤ shiftLimit fmt then
      roundAligned? fmt 0 productSign addendSign product (addend <<< shift) productScale
    else
      roundJammed? fmt 0 addendSign productSign addend product shift productScale
  else
    let shift := productScale - addendScale
    if shift ≤ productShiftLimit fmt then
      roundAligned? fmt 0 productSign addendSign (product <<< shift) addend addendScale
    else
      roundJammed? fmt 0 productSign addendSign product addend shift addendScale

/--
One-word finite fused multiply-add on the operands' storage words.

The three operands are decoded with the shared one-word field extractors, and an exceptional
operand returns `none`. The product scale is the sum of the compact finite scales of `x` and `y`,
and `alignOffset fmt` moves the addend's compact scale into product coordinates. `Fma.Proof`
proves every accepted result equal to `FiniteKernel.fma? x y z`.
-/
@[inline] def fmaFinite? {fmt : FloatFormat} (x y z : Model fmt) : Option (Model fmt) :=
  let xBits := toWord x
  let yBits := toWord y
  let zBits := toWord z
  let xExponent := exponentField fmt xBits
  let yExponent := exponentField fmt yBits
  let zExponent := exponentField fmt zBits
  let allOnes := exponentMask fmt
  if xExponent == allOnes || yExponent == allOnes || zExponent == allOnes then
    none
  else
    fmaFields? fmt
      (Bool.xor (signField fmt xBits) (signField fmt yBits))
      (NativeSmallWordFinite.finiteMantissa fmt xExponent (fractionField fmt xBits) *
        NativeSmallWordFinite.finiteMantissa fmt yExponent (fractionField fmt yBits))
      (FloatLib.Numerics.FixedWord.finiteScale xExponent +
        FloatLib.Numerics.FixedWord.finiteScale yExponent)
      (signField fmt zBits)
      (NativeSmallWordFinite.finiteMantissa fmt zExponent (fractionField fmt zBits))
      (FloatLib.Numerics.FixedWord.finiteScale zExponent + alignOffset fmt)

end Model.NativeSmallWordFma
end FloatLib.Floats.Formats.BinaryInterchange
