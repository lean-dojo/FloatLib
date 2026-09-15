/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Subtraction.Runtime

/-!
# Native binary64 addition and subtraction runtime

The executable binary64 dispatchers combine equal-exponent addition with signed Sterbenz
subtraction. Their refinement proofs are isolated in `Addition.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

/--
Try native same-sign addition of normal binary64 operands with the same exponent.

The sum of two 53-bit significands is rounded once to nearest-even and packed directly.
-/
@[inline] def addNormalSameExponent? (x y : Value) : Option Value :=
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  let xSign := signBit xBits
  let ySign := signBit yBits
  if xSign != ySign || xExponent == 0 || xExponent == 0x7ff ||
      yExponent != xExponent then
    none
  else
    let xMantissa := finiteMantissa xExponent (fracField xBits)
    let yMantissa := finiteMantissa yExponent (fracField yBits)
    let rounded :=
      FloatLib.Numerics.FixedWord.roundShiftRightEven (xMantissa + yMantissa) 1
    let resultExponent := xExponent + 1
    if 0x7ff ≤ resultExponent then
      none
    else
      some <| ofUInt64 <|
        packFieldsWord xSign resultExponent
          (rounded - 0x0010000000000000)

/-- Try native equal-exponent addition before the exact finite binary64 implementation. -/
@[inline] def addFiniteFastImpl? (x y : Value) : Option Value :=
  match addNormalSameExponent? x y with
  | some sum => some sum
  | none => addFiniteImpl? x y

/--
Try signed Sterbenz subtraction first, then reuse native same-exponent addition for opposite-sign
subtraction. Every declined case retains the exact finite component kernel.
-/
@[inline] def subFiniteFastImpl? (x y : Value) : Option Value :=
  match subSignedSterbenz? x y with
  | some difference => some difference
  | none => addFiniteFastImpl? x (negate y)

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
