/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Core.Runtime

/-!
# Shared native-word product finishing

The one-word and two-word multiplication kernels use different representations for the exact
product. After rounding that product to a `UInt64` significand, both kernels perform the same
carry adjustment, overflow test, and field packing. Keeping that final stage here gives the two
backends one executable definition as well as one proof.

`finishWord` returns a word rather than an `Option`; its caller chooses a decline marker outside
the valid packed range. Both definitions request inlining. The overflow threshold and exponent
offset are formed from `NativeSmallWord.biasWord` using machine-word arithmetic.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeWordProduct

open NativeSmallWord

/-- Finish a rounded native-word product already in the normal range, declining on overflow. -/
@[always_inline, inline] def finish? (fmt : FloatFormat) (sign : Bool)
    (position rounded : UInt64) : Option (Model fmt) :=
  let carry := rounded == carryBit fmt
  let normalizedPosition := if carry then position + 1 else position
  let overflowThreshold :=
    3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2
  if overflowThreshold < normalizedPosition then
    none
  else
    let normalizedMantissa :=
      if carry then hiddenBit fmt else rounded
    let exponentOffset :=
      biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2
    let exponent := normalizedPosition - exponentOffset
    let fraction := normalizedMantissa - hiddenBit fmt
    some <| NativeSmallWord.ofWord <|
      NativeSmallWord.packFields fmt sign exponent fraction

/--
Finish a rounded native-word product without constructing an `Option`.

On overflow the function returns `decline`; otherwise it returns the packed storage word.
-/
@[always_inline, inline] def finishWord (fmt : FloatFormat) (decline : UInt64)
    (sign : Bool) (position rounded : UInt64) : UInt64 :=
  let carry := rounded == carryBit fmt
  let normalizedPosition := if carry then position + 1 else position
  let overflowThreshold :=
    3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2
  if overflowThreshold < normalizedPosition then
    decline
  else
    let normalizedMantissa :=
      if carry then hiddenBit fmt else rounded
    let exponentOffset :=
      biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2
    let exponent := normalizedPosition - exponentOffset
    let fraction := normalizedMantissa - hiddenBit fmt
    NativeSmallWord.packFields fmt sign exponent fraction

end Model.NativeWordProduct
end FloatLib.Floats.Formats.BinaryInterchange
