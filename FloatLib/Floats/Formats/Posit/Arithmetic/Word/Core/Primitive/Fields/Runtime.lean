/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Word.Runtime

/-!
# Native-word posit field decoding

These primitives extract posit sign, magnitude, regime, exponent, and
significand data directly from `UInt64`. Their exact-width model refinements live in
`FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Fields.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWord

open FloatLib.Numerics

/-- Unsigned magnitude used by a direct native-word posit decoder. -/
@[inline] def magnitudeNat (format : Format) (code : UInt64) : Nat :=
  if decide (format.signMaskNat ≤ code.toNat) then
    format.modulus - code.toNat
  else
    code.toNat

/--
Unsigned posit magnitude from prepared native layout constants.

Separating this first-order kernel from the format wrapper lets multi-operand arithmetic prepare
the sign mask and modulus once and reuse them for every decoded operand.
-/
@[inline] def magnitudeWordAt
    (signMask modulus code : UInt64) : UInt64 :=
  if signMask ≤ code then
    modulus - code
  else
    code

/-- Unsigned posit magnitude computed without leaving the native word. -/
@[inline] def magnitudeWord (format : Format) (code : UInt64) : UInt64 :=
  magnitudeWordAt (signMaskWord format) (modulusWord format) code

/--
Decode exact dyadic fields for a nonnegative finite candidate word.

Masks, shifts, and the significand use `UInt64`. Field widths and the extracted exponent use
`Nat`; the final exponent uses `Int`.
-/
@[inline] def nonnegativeDyadicAt (format : Format) (code : UInt64) :
    FloatLib.Numerics.Dyadic :=
  if code == 0 then
    FloatLib.Numerics.Dyadic.zero
  else
    let regimeBit := bitAt code (format.payloadBits - 1)
    let regimeRunLength :=
      countLeadingRun code format.payloadBits regimeBit
    let hasRegimeTerminator : Bool :=
      regimeRunLength < format.payloadBits
    let trailingBits :=
      format.payloadBits - regimeRunLength -
        (if hasRegimeTerminator then 1 else 0)
    let usedExponentBits := min format.exponentBits trailingBits
    let fractionBits := trailingBits - usedExponentBits
    let storedExponent :=
      lowBits (shiftRight code fractionBits) usedExponentBits
    let exponentField :=
      Nat.shiftLeft storedExponent.toNat (2 - usedExponentBits)
    let regimeValue : Int :=
      if regimeBit then
        Int.ofNat regimeRunLength - 1
      else
        -Int.ofNat regimeRunLength
    let significand :=
      lowBits code fractionBits |||
        ((1 : UInt64) <<< UInt64.ofNat fractionBits)
    {
      negative := false
      significand := significand.toNat
      exponent :=
        regimeValue * 4 +
          Int.ofNat exponentField - Int.ofNat fractionBits
    }

end FloatLib.Floats.Formats.Posit.Model.NativeWord
