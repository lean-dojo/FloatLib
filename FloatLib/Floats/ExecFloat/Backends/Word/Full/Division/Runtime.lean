/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Kernels.FixedWord.Quotient.Compiler

public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Core.Runtime
public import FloatLib.Kernels.FixedWord.Quotient.Runtime

/-!
# Native binary64 division runtime

The normal-result binary64 path performs restoring division on `UInt64`. Inputs outside that
kernel fall back to the exact generic finite implementation. `Division.Proof` has the proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord.RestoringQuotient
open FloatLib.Numerics.FixedWord

/--
Divide two binary64 storage words on the common path whose rounded result is normal, returning the
packed result word. Carriers that store binary64 as a `UInt64` call it on their words, so a normal
quotient never becomes an exact-width model value.

It returns `none` for zeros, subnormal or overflowing results, and exceptional encodings. Declined
finite cases go to the generic finite kernel, and the dispatcher sends exceptional operands to
`Spec.divSpecial`.
-/
@[inline] def divNormalWord? (xBits yBits : UInt64) : Option UInt64 :=
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
          some <|
            packFieldsWord
              (Bool.xor (signBit xBits) (signBit yBits))
              encodedExponent fraction

/-- `divNormalWord?` as a model value. -/
@[inline] def divNormal? (x y : Value) : Option Value :=
  (divNormalWord? (toUInt64 x) (toUInt64 y)).map ofUInt64

/--
Finite binary64 division through the native normal-result divider, falling back to the generic
component kernel `divFiniteComponents?`.
-/
@[inline] def divFinite? (x y : Value) : Option Value :=
  match divNormal? x y with
  | some quotient => some quotient
  | none => NativeBinary64.divFiniteComponents? x y

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
