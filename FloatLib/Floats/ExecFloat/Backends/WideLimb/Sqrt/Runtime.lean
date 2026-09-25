/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Core.Runtime
public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.SquareRoot

/-!
# Wide-limb square-root runtime

Positive normal inputs are decoded directly from their stored limbs. Their significands are
scaled by `fracWidth` or `fracWidth + 1` bits and passed to a checked increasing-precision integer
square root. The exact remainder determines rounding, including carry into the exponent.

The normal path has no fraction-width bound and does not require the bias to exceed the
precision. Zero, subnormal, negative, and exceptional inputs use the reference operation.
`Sqrt.Proof` establishes equality with that operation on every eligible stored value.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

/-- Read the normal significand without allocating a separate array of fraction limbs. -/
@[inline] def sqrtMantissa {fmt : FloatFormat} (x : Value fmt) : Nat :=
  let implicitBit := 1 <<< fmt.fracWidth
  implicitBit + (x.1.toNatImpl &&& (implicitBit - 1))

/--
Square root of normal scalar fields, with remainder rounding and a possible exponent carry.

For the normal-input contract, the scaled radicand has either `2 * fracWidth + 1` or
`2 * fracWidth + 2` bits. Its square root therefore needs no discarded integer bits: the exact
remainder is below the rounding midpoint precisely when it is at most the integer root.
-/
def sqrtNormalValue (fmt : FloatFormat) (exponent mantissa : Nat) : Value fmt :=
  let shift := fmt.fracWidth + (exponent + fmt.bias) % 2
  let (root, remainder) := FixedWord.IntegerSquareRoot.sqrtRem (mantissa <<< shift)
  let rounded := if remainder ≤ root then root else root + 1
  let implicitBit := 1 <<< fmt.fracWidth
  let carry := rounded == implicitBit <<< 1
  let resultExponent := (exponent + fmt.bias) / 2 + if carry then 1 else 0
  let fraction := if carry then 0 else rounded - implicitBit
  pack fmt false (UInt32.ofNat resultExponent) (LimbArray.ofNat fraction (limbCount fmt))

/-- Try the checked square-root candidate on a positive normal stored value. -/
def sqrtNormal? (fmt : FloatFormat) (x : Value fmt) : Option (Value fmt) :=
  if signBit x then
    none
  else
    let exponent := expWord x
    if exponent == 0 || exponent == expAllOnes fmt then
      none
    else
      some (sqrtNormalValue fmt exponent.toNat (sqrtMantissa x))

/-- Wide-limb square root, with the exact reference operation for declined inputs. -/
def sqrt (fmt : FloatFormat) (x : Value fmt) : Value fmt :=
  match sqrtNormal? fmt x with
  | some result => result
  | none => ofModel (Spec.sqrt (toModel x))

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
