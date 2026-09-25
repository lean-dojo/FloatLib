/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Finite.Runtime
public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Base.Runtime

/-!
# Native binary32 square root

Positive finite inputs are scaled to a 47- or 48-bit radicand, so the exact floor square root and
nearest-even decision fit entirely in `UInt64`. The complete operation retains IEEE NaN,
infinity, negative-input, and signed-zero behavior. Correctness lives in `Sqrt.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/--
Round the square root of a positive finite binary32 mantissa and scale.

For `0 < mantissa < 2^24` and `scale ≤ 253`, the input value is
`mantissa * 2^(scale - 149)`, with subtraction in `Int`. The selected shift places its square root
in the 24-bit binary32 significand range before the final nearest-even decision.
-/
@[inline] def sqrtPositiveFiniteCore (mantissa scale : UInt64) : UInt32 :=
  let leading := FloatLib.Numerics.FixedWord.log2Word mantissa
  let position := leading + scale
  let shift := if position % 2 == 0 then 47 - leading else 46 - leading
  let scaledMantissa := mantissa <<< shift
  let root := FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrt scaledMantissa
  let remainder := scaledMantissa - root * root
  let roundedRoot := if remainder ≤ root then root else root + 1
  let carry := roundedRoot == 0x1000000
  let encodedExponent := (position + 105) / 2 + if carry then 1 else 0
  let roundedMantissa := if carry then 0x800000 else roundedRoot
  mkBits false encodedExponent.toNat (roundedMantissa - 0x800000).toNat

/-- Decode binary32 fields and run the bounded positive-finite square-root kernel. -/
@[inline] def sqrtPositiveFinite (exponent fraction : UInt32) : UInt32 :=
  sqrtPositiveFiniteCore
    (finiteMantissa exponent fraction)
    (finiteScale exponent)

/-- Native binary32 square root, including IEEE exceptional-value behavior. -/
@[inline] def sqrt (x : Value) : Value :=
  let bits := toUInt32 x
  let exponent := expField bits
  let fraction := fracField bits
  if exponent == 0xff then
    if fraction == 0 then
      if signBit bits then ofUInt32 0x7fc00000 else x
    else
      ofUInt32 (bits ||| 0x00400000)
  else if exponent == 0 && fraction == 0 then
    x
  else if signBit bits then
    ofUInt32 0x7fc00000
  else
    ofUInt32 (sqrtPositiveFinite exponent fraction)

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
