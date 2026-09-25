/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Core.Runtime

/-!
# Native binary64 subtraction runtime

The signed Sterbenz kernels live here; their refinement proofs are isolated in
`Subtraction.Proof`.

The routines accept normal operands of the same sign whose magnitudes lie within a factor of
two. Their exact difference fits in one native word, including when the result is subnormal.
Other inputs are left to the arithmetic dispatcher.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

/--
Pack an exact significand difference below `2^53` at an encoded exponent in `1..2046`.

The represented magnitude is `difference * 2^(exponent - 1075)`, with the exponent subtraction
in `Int`. Zero becomes positive zero. Nonzero results below the minimum normal value are packed
as subnormals; all other results are normalized without rounding.
-/
@[inline] def packExactDifference
    (sign : Bool) (difference exponent : UInt64) : Value :=
  if difference == 0 then
    ofUInt64 0
  else
    let leading := FloatLib.Numerics.FixedWord.log2Word difference
    if leading + exponent < 53 then
      let fraction := difference <<< (exponent - 1)
      ofUInt64 (packFieldsWord sign 0 fraction)
    else
      let shift := 52 - leading
      let mantissa := difference <<< shift
      let encodedExponent := exponent + leading - 52
      let fraction := mantissa - 0x0010000000000000
      ofUInt64 (packFieldsWord sign encodedExponent fraction)

/--
Try exact subtraction of positive normal binary64 values in Sterbenz's factor-two region.

The same-exponent case aligns immediately. Adjacent exponents are accepted precisely when the
significand of the larger operand is no greater than that of the smaller operand, which is the
native field form of the
factor-two condition.
-/
@[inline] def subSterbenz? (x y : Value) : Option Value :=
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  if signBit xBits || signBit yBits ||
      xExponent == 0 || yExponent == 0 ||
      xExponent == 0x7ff || yExponent == 0x7ff then
    none
  else
    let xMantissa := finiteMantissa xExponent (fracField xBits)
    let yMantissa := finiteMantissa yExponent (fracField yBits)
    if xExponent == yExponent then
      if yMantissa ≤ xMantissa then
        some <| packExactDifference false
          (xMantissa - yMantissa) xExponent
      else
        some <| packExactDifference true
          (yMantissa - xMantissa) xExponent
    else if xExponent == yExponent + 1 && xMantissa ≤ yMantissa then
      some <| packExactDifference false
        ((xMantissa <<< 1) - yMantissa) yExponent
    else if yExponent == xExponent + 1 && yMantissa ≤ xMantissa then
      some <| packExactDifference true
        ((yMantissa <<< 1) - xMantissa) xExponent
    else
      none

/--
Try exact Sterbenz subtraction for same-sign normal binary64 inputs.

Positive operands use `subSterbenz?` directly. Negative operands are negated and swapped so the
same proved positive kernel computes `x - y` with the correct result sign.
-/
@[inline] def subSignedSterbenz? (x y : Value) : Option Value :=
  let xSign := signBit (toUInt64 x)
  let ySign := signBit (toUInt64 y)
  if xSign != ySign then
    none
  else if xSign then
    subSterbenz? (negate y) (negate x)
  else
    subSterbenz? x y

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
