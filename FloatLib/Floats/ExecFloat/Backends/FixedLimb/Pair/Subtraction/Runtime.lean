/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Difference.Runtime
public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime

/-!
# Two-word subtraction runtime

The two-word subtraction runtime combines the equal-exponent kernel with a complete finite
candidate chain for every eligible layout. It reuses the pair-kernel storage layer; correctness
proofs are isolated in `Subtraction.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

/--
Try exact native subtraction of same-sign normal operands with the same exponent.

An accepted nonzero result remains normal. Exact cancellation returns positive zero; a nonzero
subnormal difference is left to the generic implementation.
-/
@[inline] def subNormalSameExponent? {fmt : FloatFormat} (x y : Model fmt) : Option (Model fmt) :=
  let xWords := toWords x
  let yWords := toWords y
  let xExponent := expField fmt xWords.hi
  let yExponent := expField fmt yWords.hi
  let xSign := signBit fmt xWords.hi
  let ySign := signBit fmt yWords.hi
  if xSign != ySign || xExponent == 0 || xExponent == expAllOnes fmt ||
      yExponent != xExponent then
    none
  else
    let xMantissa := normalMantissa fmt (fracHigh fmt xWords.hi) xWords.lo
    let yMantissa := normalMantissa fmt (fracHigh fmt yWords.hi) yWords.lo
    if xMantissa == yMantissa then
      some (Model.posZero fmt)
    else
      let xLess := FloatLib.Numerics.FixedWord.UInt128.less xMantissa yMantissa
      let difference :=
        if xLess then
          FloatLib.Numerics.FixedWord.UInt128.sub yMantissa xMantissa
        else
          FloatLib.Numerics.FixedWord.UInt128.sub xMantissa yMantissa
      let leading := FloatLib.Numerics.FixedWord.UInt128.log2 difference
      if xExponent.toNat + leading ≤ fmt.fracWidth then
        none
      else
        let normalized :=
          FloatLib.Numerics.FixedWord.UInt128.shiftLeft difference (fmt.fracWidth - leading)
        let resultExponent :=
          UInt64.ofNat (xExponent.toNat + leading - fmt.fracWidth)
        some <| packNormal fmt (if xLess then !xSign else xSign)
          resultExponent normalized

/--
Evaluate finite two-word subtraction.

The fixed-limb equal-exponent kernel is attempted first. Every remaining finite case uses generic
exact addition with a negated right operand; exceptional inputs remain visible to the dispatcher.
Descriptor specialization follows the pattern described in `Dispatch.Add.Runtime`.
-/
@[specialize fmt] def subFinite? {fmt : FloatFormat} (x y : Model fmt) : Option (Model fmt) :=
  match subNormalSameExponent? x y with
  | some difference => some difference
  | none => FiniteKernel.addRuntime? x (neg y)

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
