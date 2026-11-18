/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.FP8.Conversion
public import FloatLib.Floats.Formats.OCP.FP8.E4M3
public import FloatLib.Floats.Formats.OCP.FP8.E5M2

/-! OFP8 revision 1.0, §§5.1–5.2.1: generic contracts and Table 3 boundaries. -/

@[expose] public section

namespace FloatLibTests.Conformance.OCP.OFP8

open FloatLib.Floats
open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.OCP.FP8

private def word {format : FloatFormat}
    (outcome : ExecFloat.ConversionOutcome (Model format)) : Nat :=
  match outcome with
  | .success value _ => Model.toNatBits value
  | .failure _ => 256

private def fromBinary32 (format : FloatFormat) (overflow : OverflowMode) (bits : Nat) : Nat :=
  word (convert format overflow (Model.ofNatBits (fmt := FloatFormat.binary32) bits))

example : Model.toRat? (Model.maxFinite FloatFormat.e4m3 false) = some 448 := by decide +kernel
example : Model.toRat? (Model.maxFinite FloatFormat.e5m2 false) = some 57344 := by decide +kernel

-- Infinity, NaN and signed zero in Table 3.
example : fromBinary32 FloatFormat.e4m3 .saturate 0x7f800000 = 126 := by decide +kernel
example : fromBinary32 FloatFormat.e4m3 .native 0x7f800000 = 127 := by decide +kernel
example : fromBinary32 FloatFormat.e5m2 .saturate 0xff800000 = 251 := by decide +kernel
example : fromBinary32 FloatFormat.e5m2 .native 0xff800000 = 252 := by decide +kernel
example : fromBinary32 FloatFormat.e4m3 .saturate 0x7fc00000 = 127 := by decide +kernel
example : fromBinary32 FloatFormat.e4m3 .native 0x80000000 = 128 := by decide +kernel
example : fromBinary32 FloatFormat.e5m2 .saturate 0x80000000 = 128 := by decide +kernel

-- Round before overflow: 464 ties to 448, but its binary32 successor overflows.
example : fromBinary32 FloatFormat.e4m3 .native 0x43e80000 = 126 := by decide +kernel
example : fromBinary32 FloatFormat.e4m3 .native 0x43e80001 = 127 := by decide +kernel
example : fromBinary32 FloatFormat.e4m3 .saturate 0x43e80001 = 126 := by decide +kernel
-- The E5M2 upper tie, 61440, rounds to infinity under NONSAT.
example : fromBinary32 FloatFormat.e5m2 .native 0x47700000 = 124 := by decide +kernel
example : fromBinary32 FloatFormat.e5m2 .saturate 0x47700000 = 123 := by decide +kernel
-- Half the least subnormal ties to zero; the successor rounds to the least subnormal.
example : fromBinary32 FloatFormat.e4m3 .native 0x3a800000 = 0 := by decide +kernel
example : fromBinary32 FloatFormat.e4m3 .native 0x3a800001 = 1 := by decide +kernel
example : fromBinary32 FloatFormat.e5m2 .native 0x37000000 = 0 := by decide +kernel
example : fromBinary32 FloatFormat.e5m2 .native 0x37000001 = 1 := by decide +kernel

section Contracts

variable {Source : Type} [ExecFloat.ExactDecoder Source SignedRat]
variable (destination : FloatFormat) (overflow : OverflowMode) (value : Source)

example : ExecFloat.Binary.Conversion.specWith id ((policy overflow).withRounding .nearest)
    (ExecFloat.ExactDecoder.run value) (convert destination overflow value) :=
  convert_spec destination overflow value

example (exact : SignedRat) (h : ExecFloat.ExactDecoder.run value = .finite exact) :
    convert destination overflow value = ExecFloat.Binary.Conversion.quantizeFiniteWith id
      ((policy overflow).withRounding .nearest) exact :=
  convert_finite destination overflow value exact h

example (exact : SignedRat) (rounded : Model destination) (status : ExecFloat.ConversionStatus)
    (hsource : ExecFloat.ExactDecoder.run value = .finite exact)
    (hout : convert destination overflow value = .success rounded status)
    (hfinite : Model.isFinite rounded = true) :
    Model.toReal rounded =
      if overflow = .saturate ∨ destination.encoding = .finite then
        Model.clampAt destination (Model.roundAt destination (exact.value : ℝ))
      else Model.roundAt destination (exact.value : ℝ) :=
  toReal_convert_finite destination overflow value exact rounded status hsource hout hfinite

example (negative : Bool) (h : ExecFloat.ExactDecoder.run value = .infinity negative) :
    convert destination .saturate value =
      .success (Model.maxFinite destination negative)
        { inexact := true, overflow := true, saturated := true, mappedSpecial := true } :=
  convert_infinity_sat destination value negative h

example (negative : Bool) (h : ExecFloat.ExactDecoder.run value = .infinity negative) :
    convert destination .native value =
      let rounded := Model.nativeOverflow destination negative
      let mapped := !Model.isInfinite rounded
      .success rounded { inexact := mapped, overflow := mapped, mappedSpecial := mapped } :=
  convert_infinity_nonsat destination value negative h

example (payload : Option Nat) (negative signaling : Bool) (nan : Model destination)
    (hnan : Model.canonicalNaN? destination = some nan)
    (h : ExecFloat.ExactDecoder.run value = .exceptional (.nan payload negative signaling)) :
    convert destination overflow value =
      .success (Model.propagatedNaN destination negative (payload.getD 0))
        { invalid := signaling } :=
  convert_nan destination overflow value payload negative signaling nan hnan h

end Contracts

-- The same policy works through the public nominal conversion interface.
example : (ExecFloat.convert (target := E4M3)
    (Model.ofNatBits (fmt := FloatFormat.binary32) 0x7f800000)
      (context := policy .native)).map (fun value => value.toUInt8.toNat) =
    .success 127 { inexact := true, overflow := true, mappedSpecial := true } := by
  decide +kernel

end FloatLibTests.Conformance.OCP.OFP8
