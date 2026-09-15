/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import FloatLib.Kernels.FixedWord.LimbRound.Runtime

/-!
# Two-word addition runtime

The two-word addition runtime combines the same-exponent kernel with a complete finite candidate
chain for every eligible layout. Correctness theorems are isolated in `Addition.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

/--
Try native same-sign addition of normal operands with the same exponent.

The two largest exponent fields are rejected so incrementing the accepted exponent always remains
finite. The sum of two `fracWidth + 1`-bit significands fits in the two-word accumulator.
-/
@[inline] def addNormalSameExponent? {fmt : FloatFormat} (x y : Model fmt) : Option (Model fmt) :=
  let xWords := toWords x
  let yWords := toWords y
  let xExponent := expField fmt xWords.hi
  let yExponent := expField fmt yWords.hi
  let xSign := signBit fmt xWords.hi
  let ySign := signBit fmt yWords.hi
  if xSign != ySign || xExponent == 0 || expAllOnes fmt - 1 ≤ xExponent ||
      yExponent != xExponent then
    none
  else
    let xMantissa := normalMantissa fmt (fracHigh fmt xWords.hi) xWords.lo
    let yMantissa := normalMantissa fmt (fracHigh fmt yWords.hi) yWords.lo
    let exact := FloatLib.Numerics.FixedWord.add128 xMantissa yMantissa
    let rounded := exact.value.roundShiftRightOneEven
    some <| packNormal fmt xSign (xExponent + 1) rounded

/--
Evaluate finite two-word addition.

The fixed-limb same-exponent kernel is attempted first. Every remaining finite case uses the
width-generic exact kernel; exceptional inputs are reported as `none` to the operation dispatcher.
The `@[specialize fmt]` annotation enables descriptor-dependent constants to be simplified at
closed-format call sites without requesting that callers inline this candidate chain.
-/
@[specialize fmt] def addFinite? {fmt : FloatFormat} (x y : Model fmt) : Option (Model fmt) :=
  match addNormalSameExponent? x y with
  | some sum => some sum
  | none => FiniteKernel.addRuntime? x y

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
