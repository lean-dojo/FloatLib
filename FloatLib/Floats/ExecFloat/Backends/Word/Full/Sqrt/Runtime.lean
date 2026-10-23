/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Core.Runtime
public import FloatLib.Kernels.FixedWord.CheckedSqrt.Runtime

/-!
# Native binary64 square-root runtime

Positive finite inputs are scaled to a 105- or 106-bit radicand held in two `UInt64` limbs. A
checked Newton candidate, or a 53-step restoring loop when the check fails, gives the floor root
and remainder in native words. The remainder decides the nearest-even result, and the binary64
exponent and fraction are packed without building a generic unpacked-float model.

`Sqrt.Proof` has the proofs and the `Nat.sqrt` model.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord
open FloatLib.Numerics.FixedWord

/-- Shift a binary64 significand into two limbs. Callers supply a positive shift below 128
and a result that fits in 128 bits. -/
@[inline] def shiftedRadicand
    (mantissa : UInt64) (shift : Nat) : FloatLib.Numerics.FixedWord.UInt128 :=
  if shift < 64 then
    { hi := mantissa >>> UInt64.ofNat (64 - shift)
      lo := mantissa <<< UInt64.ofNat shift }
  else
    { hi := mantissa <<< UInt64.ofNat (shift - 64)
      lo := 0 }

/-- Read a base-four digit of a two-limb radicand, for an index below 64. -/
@[inline] def digitAt (radicand : FloatLib.Numerics.FixedWord.UInt128) (index : Nat) : UInt64 :=
  if index < 32 then
    (radicand.lo >>> UInt64.ofNat (2 * index)) &&& 3
  else
    (radicand.hi >>> UInt64.ofNat (2 * (index - 32))) &&& 3

/--
Consume one base-four digit in the restoring square-root recurrence.

For the binary64 radicands built above, 53 iterations produce a 53-bit floor root, and the
remainder and trial divisor fit in one native word.
-/
@[inline] def rootStep (digit : UInt64)
    (state : RestoringRootState UInt64) : RestoringRootState UInt64 :=
  let expanded := state.remainder * 4 + digit
  let trial := state.root * 4 + 1
  if trial ≤ expanded then
    { root := state.root * 2 + 1
      remainder := expanded - trial }
  else
    { root := state.root * 2
      remainder := expanded }

/-- Consume the given number of radicand digits, most significant first. -/
@[inline] def rootLoop
    (radicand : FloatLib.Numerics.FixedWord.UInt128) :
    Nat → RestoringRootState UInt64 → RestoringRootState UInt64
  | 0, state => state
  | steps + 1, state =>
      let digit := digitAt radicand steps
      rootLoop radicand steps (rootStep digit state)

/-- Compute the floor root and exact remainder of a binary64-sized scaled radicand. -/
@[inline] def rootAndRemainder
    (mantissa : UInt64) (shift : Nat) : RestoringRootState UInt64 :=
  rootLoop (shiftedRadicand mantissa shift) 53 { root := 0, remainder := 0 }

/-! ## Checked Newton root

The restoring loop takes 53 serial steps. `rootAndRemainderChecked` takes the candidate and exact
square check of `CheckedSquareRoot` instead. Inputs outside the loop's verified range and rejected
candidates still run the loop, so the result is `rootAndRemainder` on every input
(`rootAndRemainderChecked_eq` in `Sqrt.Proof`).
-/

/-- `rootAndRemainder` through a checked Newton candidate where the loop's range conditions hold. -/
@[inline] def rootAndRemainderChecked (mantissa : UInt64) (shift : Nat) :
    RestoringRootState UInt64 :=
  if 0 < shift && shift < 128 &&
      (mantissa == 0 || (FloatLib.Numerics.FixedWord.log2Word mantissa).toNat + shift < 106) then
    let radicand := shiftedRadicand mantissa shift
    match CheckedSquareRoot.checkRoot? radicand (CheckedSquareRoot.approxRoot radicand) with
    | some state => state
    | none => rootAndRemainder mantissa shift
  else
    rootAndRemainder mantissa shift

/--
Positive finite binary64 square root of a decoded significand and scale, as a packed word.

For a nonzero significand below `2^53` and a scale at most 2045, the input value is
`mantissa * 2^(scale - 1074)`, with the exponent subtraction in `Int`. Parity chooses a 105- or
106-bit integer radicand. Its square root cannot be a half-integer, so the result rounds down
exactly when `remainder ≤ root`.
-/
@[inline] def sqrtPositiveFiniteCore
    (mantissa scale : UInt64) : UInt64 :=
  let leading := FloatLib.Numerics.FixedWord.log2Word mantissa
  let position := leading + scale
  let shift :=
    if position % 2 == 0 then
      104 - leading.toNat
    else
      105 - leading.toNat
  let state := rootAndRemainderChecked mantissa shift
  let roundedRoot :=
    if state.remainder ≤ state.root then state.root else state.root + 1
  let carry := roundedRoot == 0x0020000000000000
  let encodedExponent :=
    (position + 972) / 2 + if carry then 1 else 0
  let roundedMantissa :=
    if carry then 0x0010000000000000 else roundedRoot
  let fraction := roundedMantissa - 0x0010000000000000
  packFieldsWord false encodedExponent fraction

/-- Decode binary64 fields and run the bounded positive-finite square-root kernel. -/
@[inline] def sqrtPositiveFinite (exponent fraction : UInt64) : UInt64 :=
  sqrtPositiveFiniteCore
    (finiteMantissa exponent fraction)
    (finiteScale exponent)

/-- Native binary64 square root, including IEEE exceptional-value behavior. -/
@[inline] def sqrt (x : Value) : Value :=
  match Model.chooseNaN1 x with
  | some nan => nan
  | none =>
      if Model.isInf x then
        if Model.signBit x then
          Model.canonicalNaN FloatFormat.binary64
        else
          Model.posInf FloatFormat.binary64
      else if Model.isZero x then
        x
      else if Model.signBit x then
        Model.canonicalNaN FloatFormat.binary64
      else
        let bits := toUInt64 x
        ofUInt64 (sqrtPositiveFinite (expField bits) (fracField bits))

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
