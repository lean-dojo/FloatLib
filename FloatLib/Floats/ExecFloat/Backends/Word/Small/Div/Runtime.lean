/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Quotient.Runtime
import FloatLib.Kernels.FixedWord.Quotient.Compiler
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Core.Runtime
public import Mathlib.Data.Rat.Cast.Order

/-!
# Native one-word finite division

The native normal-division path serves conventional IEEE formats whose storage and quotient
intermediates fit in `UInt64`. Refinement proofs and the exact-rational specification live in
`Div.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordDiv

open FloatLib.Numerics.FixedWord.RestoringQuotient

/--
Round and pack a normal quotient with `UInt64` significands and an `Int` exponent.

For nonzero significands within the eligible format's width, the function declines if the
leading exponent is outside the normal range before rounding or exceeds its upper bound after
rounding. The public dispatcher handles these cases. The normal exponent bounds
`1 - bias` and `bias` and the encoding offset come from `NativeSmallWord.biasInt`, so the
descriptor contributes no `Nat` power or shift per call.
-/
@[inline] def roundNormalNative? (fmt : FloatFormat) (sign : Bool)
    (num den : UInt64) (exponent : Int) : Option (Model fmt) :=
  let bias := NativeSmallWord.biasInt fmt
  let rationalExponent :=
    floorLog2RatWord num den
  let totalExponent := rationalExponent + exponent
  if totalExponent < (1 : Int) - bias || bias < totalExponent then
    none
  else
    let shift :=
      Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
    let roundedMantissa :=
      roundScaledQuotient num den shift
    let carry :=
      roundedMantissa == NativeSmallWord.carryBit fmt
    let normalizedExponent :=
      if carry then totalExponent + 1 else totalExponent
    if bias < normalizedExponent then
      none
    else
      let normalizedMantissa :=
        if carry then NativeSmallWord.hiddenBit fmt else roundedMantissa
      let encodedExponent :=
        UInt64.ofNat (Int.toNat (normalizedExponent + bias))
      let fraction :=
        normalizedMantissa - NativeSmallWord.hiddenBit fmt
      some <| NativeSmallWord.ofWord <|
        NativeSmallWord.packFields fmt sign encodedExponent fraction

/--
Decode two normal finite operands and try the one-word quotient path.

The function deliberately declines for zero, subnormal, and exceptional operands. The public
dispatcher retains the exact arbitrary-precision implementation for every declined case.
-/
@[inline] def divNormal? {fmt : FloatFormat}
    (x y : Model fmt) : Option (Model fmt) :=
  NativeSmallWord.withNormalPair? x y fun sign xExponent yExponent
      xMantissa yMantissa =>
    roundNormalNative? fmt sign xMantissa yMantissa
      (Int.ofNat (xExponent - 1).toNat -
        Int.ofNat (yExponent - 1).toNat)

end Model.NativeSmallWordDiv
end FloatLib.Floats.Formats.BinaryInterchange
