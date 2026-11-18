/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# NaN payload operations

IEEE 754-2019 §9.7 recommends three operations on the payload of a NaN: `getPayload`,
`setPayload` and `setPayloadSignaling`. The clause number is the one in the 754 working group's
list of changes from 754-2008, and its note `payload-functions.txt`
(<https://grouper.ieee.org/groups/msc/ANSI_IEEE-Std-754-2019/background/>) states their purpose:
homogeneous operations that raise no exception and treat a payload as a nonnegative
floating-point integer. The semantics below are those of the C23 binding (ISO/IEC 9899:2024
working draft N3220, Table F.2 and F.10.13.2 to F.10.13.4):

* `getPayload x` is the payload of a quiet or signaling NaN as a positive-signed floating-point
  integer, and `-1` when `x` is not a NaN.
* `setPayload x` is the quiet NaN with a clear sign bit and the payload `x`, and `+0` when `x`
  is not a floating-point integer that represents an admissible payload.
* `setPayloadSignaling x` is the signaling NaN with that payload, and `+0` likewise.

Which payloads are admissible is the implementation's choice (N3220 F.10.13.1). Here a value is
admissible when it is the encoding of a natural number below `payloadBound fmt` with a clear
sign bit, so `-0`, negative integers, fractions, infinities and NaNs are not. For a signaling NaN
the payload zero is not admissible either, because a NaN with a clear quiet bit and a zero
payload would be the word of an infinity. The GNU C library makes the same choices.

The payload of a NaN is `nanPayload`: the fraction field without its quiet bit in the IEEE
encoding, and zero in the encodings that have a single NaN per sign.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Exclusive bound on the payloads that a NaN of `fmt` can carry: `2 ^ (fracWidth - 1)` in the IEEE
encoding, whose quiet bit takes the top fraction bit, one in the encodings with a single NaN per
sign, and zero when the format has no NaN.
-/
def payloadBound (fmt : FloatFormat) : Nat :=
  match fmt.encoding with
  | .ieee => 2 ^ (fmt.fracWidth - 1)
  | .finiteMaxNaN | .finiteUnsignedZero => 1
  | .finite => 0

/--
The payload that `x` names: `some n` exactly when `x` is the encoding of the natural number `n`
with `n < payloadBound fmt`, so the sign bit is clear and `-0` names no payload.

The exponent test rejects a value of `2 ^ (fracWidth + 1)` or more before any shift is formed,
so a format with a wide exponent field costs no more than a narrow one.
-/
def admissiblePayload? {fmt : FloatFormat} (x : Model fmt) : Option Nat :=
  match exactValue x with
  | .finite value =>
      if value.negative || (fmt.fracWidth : Int) < value.exponent then
        none
      else
        let payload := (roundDyadicToInt .towardZero value).toNat
        if payload < payloadBound fmt ∧ ((payload : Nat) : Model fmt) = x then
          some payload
        else
          none
  | .infinity _ | .nan _ _ _ => none

/--
IEEE 754-2019 §9.7 `getPayload` (C23 `getpayload`, N3220 F.10.13.2): the payload of a quiet or
signaling NaN as a positive-signed floating-point integer, and `-1` for an operand that is not a
NaN. It raises no exception, also for a signaling NaN. The integer is exact whenever the format
can hold `2 ^ fracWidth` (`toReal_getPayload`).
-/
def getPayload {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  if isNaN x then ((nanPayload x : Nat) : Model fmt) else negOne fmt

/--
IEEE 754-2019 §9.7 `setPayload` (C23 `setpayload`, N3220 F.10.13.3): the quiet NaN with a clear
sign bit whose payload is the admissible payload that `x` names, and `+0` when `x` names none.
It raises no exception.
-/
def setPayload {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  match admissiblePayload? x with
  | some payload => propagatedNaN fmt false payload
  | none => posZero fmt

/--
IEEE 754-2019 §9.7 `setPayloadSignaling` (C23 `setpayloadsig`, N3220 F.10.13.4): the signaling
NaN with a clear sign bit whose payload is the nonzero admissible payload that `x` names, and
`+0` otherwise. Only the IEEE encoding has signaling NaNs, so every other encoding returns `+0`.
It raises no exception.
-/
def setPayloadSignaling {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  match fmt.encoding, admissiblePayload? x with
  | .ieee, some payload =>
      if payload = 0 then posZero fmt else ofFields fmt false fmt.expAllOnesNat payload
  | _, _ => posZero fmt

end Model
end FloatLib.Floats.Formats.BinaryInterchange
