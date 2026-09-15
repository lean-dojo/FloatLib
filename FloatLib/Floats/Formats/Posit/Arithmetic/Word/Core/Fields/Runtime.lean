/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Word.Runtime
public import FloatLib.Kernels.FixedWord.Core.Runtime

/-!
# Scalar-field posit decoding

Compiled native-word kernels consume decoded posit fields through scalar continuations. The
machine-scalar path keeps layout arithmetic in `UInt64` and `Int64`; total wrappers retain a
natural-number reference path outside the native backend contract. Refinement proofs live in
`FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Fields.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWord

open FloatLib.Numerics

/-- Run a continuation on machine-scalar nonnegative dyadic fields. -/
@[inline] def withNonnegativeMachineFieldsAtPayload {α : Type}
    (payloadBits : UInt64) (code : UInt64)
    (continuation : UInt64 → Int64 → α) : α :=
  if code == 0 then
    continuation 0 0
  else
    let regimeBit :=
      FixedWord.bitAtWord code (payloadBits - 1)
    let regimeRunLength :=
      FixedWord.countLeadingRunWord code payloadBits regimeBit
    let hasRegimeTerminator : Bool :=
      regimeRunLength < payloadBits
    let trailingBits :=
      payloadBits - regimeRunLength -
        (if hasRegimeTerminator then 1 else 0)
    let usedExponentBits := min 2 trailingBits
    let fractionBits := trailingBits - usedExponentBits
    let storedExponent :=
      FixedWord.lowBitsWord
        (FixedWord.shiftRightWord code fractionBits)
        usedExponentBits
    let exponentField :=
      storedExponent <<< (2 - usedExponentBits)
    let regimeValue : Int64 :=
      if regimeBit then
        regimeRunLength.toInt64 - 1
      else
        -regimeRunLength.toInt64
    let significand :=
      FixedWord.lowBitsWord code fractionBits |||
        ((1 : UInt64) <<< fractionBits)
    continuation significand
      (regimeValue * 4 +
        exponentField.toInt64 - fractionBits.toInt64)

/-- Natural-number reference decoder for nonnegative native-word dyadic fields. -/
@[inline] def withNonnegativeReferenceFieldsAtPayload {α : Type}
    (payloadBits : Nat) (code : UInt64)
    (continuation : UInt64 → Int → α) : α :=
  if code == 0 then
    continuation 0 0
  else
    let regimeBit := bitAt code (payloadBits - 1)
    let regimeRunLength :=
      countLeadingRun code payloadBits regimeBit
    let hasRegimeTerminator : Bool :=
      regimeRunLength < payloadBits
    let trailingBits :=
      payloadBits - regimeRunLength -
        (if hasRegimeTerminator then 1 else 0)
    let usedExponentBits := min 2 trailingBits
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
    continuation significand
      (regimeValue * 4 +
        Int.ofNat exponentField - Int.ofNat fractionBits)

/-- Use machine-scalar decoding for payload widths from one through 64, and reference decoding
otherwise. -/
@[inline] def withNonnegativeWordFieldsAtPayload {α : Type}
    (payloadBits : Nat) (code : UInt64)
    (continuation : UInt64 → Int → α) : α :=
  if _hpayloadPositive : 0 < payloadBits then
    if _hpayload : payloadBits ≤ 64 then
      withNonnegativeMachineFieldsAtPayload
        (UInt64.ofNat payloadBits) code fun significand exponent =>
          continuation significand exponent.toInt
    else
      withNonnegativeReferenceFieldsAtPayload
        payloadBits code continuation
  else
    withNonnegativeReferenceFieldsAtPayload
      payloadBits code continuation

/-- Format-facing wrapper around the prepared-payload native-word decoder. -/
@[inline] def withNonnegativeWordFields {α : Type}
    (format : Format) (code : UInt64)
    (continuation : UInt64 → Int → α) : α :=
  withNonnegativeWordFieldsAtPayload format.payloadBits code continuation

/-- Natural-number view of the prepared-payload native-word decoder. -/
@[inline] def withNonnegativeFieldsAtPayload {α : Type}
    (payloadBits : Nat) (code : UInt64)
    (continuation : Nat → Int → α) : α :=
  withNonnegativeWordFieldsAtPayload payloadBits code fun significand exponent =>
    continuation significand.toNat exponent

/-- Format-facing natural-number view of the native-word field decoder. -/
@[inline] def withNonnegativeFields {α : Type}
    (format : Format) (code : UInt64)
    (continuation : Nat → Int → α) : α :=
  withNonnegativeFieldsAtPayload format.payloadBits code continuation

end FloatLib.Floats.Formats.Posit.Model.NativeWord
