/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Core.Runtime

/-!
# Shared native-word product finishing

The one-word and two-word multiplication kernels represent the exact product differently. After
rounding it to a `UInt64` significand, both do the same carry adjustment, overflow test and field
packing, so that final stage lives here with one executable definition and one proof.

`finish?` is `finishWord?` mapped to model values. `finishWord` returns a word in place of an
`Option`, and its caller picks a decline marker outside the valid packed range. The overflow
threshold and exponent offset are computed from `NativeSmallWord.biasWord` in machine-word
arithmetic.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeWordProduct

open NativeSmallWord

/--
Finish a rounded native-word product in the normal range as a packed storage word, declining on
overflow.

Carriers that store the encoding as a `UInt64` use this form so an accepted result never becomes
an exact-width model value.
-/
@[always_inline, inline] def finishWord? (fmt : FloatFormat) (sign : Bool)
    (position rounded : UInt64) : Option UInt64 :=
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
    some <| NativeSmallWord.packFields fmt sign exponent fraction

/-- `finishWord?` as a model value. -/
@[always_inline, inline] def finish? (fmt : FloatFormat) (sign : Bool)
    (position rounded : UInt64) : Option (Model fmt) :=
  (finishWord? fmt sign position rounded).map NativeSmallWord.ofWord

/--
Finish a rounded native-word product without building an `Option`.

It returns `decline` on overflow and the packed storage word otherwise.
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
