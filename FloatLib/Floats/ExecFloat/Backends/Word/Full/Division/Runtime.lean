/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Core.Runtime
public import FloatLib.Kernels.FixedWord.Quotient.Runtime

/-!
# Native binary64 division runtime

The normal-result binary64 path performs restoring division on `UInt64`. Inputs outside the
normal-result kernel fall back to the exact generic finite implementation. Correctness proofs are
isolated in `Division.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord.RestoringQuotient
open FloatLib.Numerics.FixedWord

/--
Try the common finite division path whose rounded result is normal.

Returning `none` delegates zeros, subnormals, overflow boundaries, and exceptional encodings to
the generic exact-rational implementation.
-/
@[inline] def divNormal? (x y : Value) : Option Value :=
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  if xExponent == 0x7ff || yExponent == 0x7ff then
    none
  else
    let xMantissa := finiteMantissa xExponent (fracField xBits)
    let yMantissa := finiteMantissa yExponent (fracField yBits)
    if xMantissa == 0 || yMantissa == 0 then
      none
    else
      let exponent :=
        Int.ofNat (finiteScale xExponent).toNat -
          Int.ofNat (finiteScale yExponent).toNat
      let rationalExponent :=
        floorLog2RatWord xMantissa yMantissa
      let totalExponent := rationalExponent + exponent
      if totalExponent < -1022 || 1023 < totalExponent then
        none
      else
        let shift := Int.toNat (52 - rationalExponent)
        let roundedMantissa :=
          roundScaledQuotient xMantissa yMantissa shift
        let carry := roundedMantissa == 0x0020000000000000
        let normalizedExponent :=
          if carry then totalExponent + 1 else totalExponent
        if 1023 < normalizedExponent then
          none
        else
          let normalizedMantissa :=
            if carry then 0x0010000000000000 else roundedMantissa
          let encodedExponent :=
            UInt64.ofNat (Int.toNat (normalizedExponent + 1023))
          let fraction := normalizedMantissa - 0x0010000000000000
          some <| ofUInt64 <|
            packFieldsWord
              (Bool.xor (signBit xBits) (signBit yBits))
              encodedExponent fraction

/--
Use the native normal-result divider when it accepts the operands, otherwise retain the exact
generic finite binary64 implementation.
-/
@[inline] def divFiniteFastImpl? (x y : Value) : Option Value :=
  match divNormal? x y with
  | some quotient => some quotient
  | none => NativeBinary64.divFiniteImpl? x y

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
