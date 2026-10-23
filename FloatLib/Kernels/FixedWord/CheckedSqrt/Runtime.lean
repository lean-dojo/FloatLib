/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Difference.Runtime
public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Runtime
import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Compiler
public import FloatLib.Kernels.FixedWord.RestoringSqrt.Runtime
public import FloatLib.Kernels.FixedWord.LimbRound.Runtime
import FloatLib.Kernels.FixedWord.RestoringSqrt.Compiler

/-!
# Checked square roots of two-word radicands

`approxRoot` proposes the floor root of a two-word radicand from a native-word root of its leading
bits and one Newton step, the refinement of `IntegerSquareRoot.approxRoot`. `checkRoot?` accepts the
candidate, or its predecessor, only after an exact two-word square check, so no correctness argument
depends on the candidate. `rootAndRemainder` replaces the restoring loop for radicands below
`2 ^ 128` and keeps the loop otherwise. `CheckedSqrt.Proof` shows it equals the loop on every input.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.CheckedSquareRoot

open FloatLib.Numerics.FixedWord

/-- Quotient of a two-word value by a native divisor, from two native divisions. It is the exact
quotient for a value below `2 ^ 96` and a nonzero divisor below `2 ^ 32`. -/
@[inline] def Internal.divTwoStep (value : FloatLib.Numerics.FixedWord.UInt128) (divisor : UInt64) :
    UInt64 :=
  let high := (value.hi <<< 32) ||| (value.lo >>> 32)
  let low := ((high % divisor) <<< 32) ||| (value.lo &&& 0xffffffff)
  ((high / divisor) <<< 32) + low / divisor

/-- Candidate floor root: a native root of the leading 62 or 63 bits and one Newton step, or the
native root alone for a one-word radicand. -/
@[inline] def approxRoot (radicand : FloatLib.Numerics.FixedWord.UInt128) : UInt64 :=
  if radicand.hi == 0 then
    IntegerSquareRoot.sqrt radicand.lo
  else
    let shift := (UInt128.log2 radicand - 61) / 2
    let seed := IntegerSquareRoot.sqrt (UInt128.shiftRight radicand (2 * shift)).lo
    (seed <<< UInt64.ofNat (shift - 1)) +
      Internal.divTwoStep (UInt128.shiftRight radicand (shift + 1)) seed

/-- Accept `guess`, or `guess - 1` when `guess` is one too large, exactly when it is the floor root
of `radicand`, together with the remainder. -/
@[inline] def checkRoot? (radicand : FloatLib.Numerics.FixedWord.UInt128) (guess : UInt64) :
    Option (RestoringRootState UInt64) :=
  if guess < 0x4000000000000000 then
    let square := mul64 guess guess
    if UInt128.less radicand square then
      if guess == 0 then
        none
      else
        let previous := guess - 1
        let previousSquare := mul64 previous previous
        if UInt128.less radicand previousSquare then
          none
        else
          let remainder := UInt128.sub radicand previousSquare
          if remainder.hi == 0 && remainder.lo ≤ previous + previous then
            some { root := previous, remainder := remainder.lo }
          else
            none
    else
      let remainder := UInt128.sub radicand square
      if remainder.hi == 0 && remainder.lo ≤ guess + guess then
        some { root := guess, remainder := remainder.lo }
      else
        none
  else
    none

/--
`RestoringSquareRoot.rootAndRemainder` with the checked candidate for radicands below `2 ^ 128`.
The loop runs for larger radicands, digit counts outside its verified range, and rejected
candidates.
-/
@[inline] def rootAndRemainder (radicand : UInt256) (steps : Nat) :
    RestoringRootState UInt128 :=
  if 64 ≤ steps && steps ≤ 125 && radicand.limb3 == 0 && radicand.limb2 == 0 then
    let value := radicand.low128
    match checkRoot? value (approxRoot value) with
    | some state => { root := ⟨0, state.root⟩, remainder := ⟨0, state.remainder⟩ }
    | none => RestoringSquareRoot.rootAndRemainder radicand steps
  else
    RestoringSquareRoot.rootAndRemainder radicand steps

/-! ## Four-word radicands -/

/-- A floating-point approximation of a four-word value from its leading 64 bits. -/
@[inline] def Internal.approxFloat (value : UInt256) : Float :=
  let leading := value.log2
  if leading < 64 then
    value.limb0.toFloat
  else
    let shift := leading - 63
    (value.shiftRight128 shift).lo.toFloat.scaleB (Int.ofNat shift)

/-- One Newton correction `r ± |radicand - r^2| / (2 r)` with a floating-point quotient. -/
@[inline] def Internal.newtonStepWide (radicand : UInt256) (root : UInt128) : UInt128 :=
  let square := mul128 root root
  let denominator := Internal.approxFloat (UInt256.ofUInt128 root) * 2
  if UInt256.less radicand square then
    let quotient := (Internal.approxFloat (UInt256.sub square radicand) / denominator).toUInt64
    UInt128.sub root ⟨0, quotient⟩
  else
    let quotient := (Internal.approxFloat (UInt256.sub radicand square) / denominator).toUInt64
    (add128 root ⟨0, quotient⟩).value

/--
Candidate floor root of a four-word radicand of at least `2 ^ 128`: the floating-point root of
the leading 54 or 55 bits, two Newton corrections, and a final unit adjustment with exact squares.
The candidate is only a proposal, which `acceptRootWide?` checks.
-/
@[inline] def approxRootWide (radicand : UInt256) : UInt128 :=
  let leading := radicand.log2
  let shift := (leading - 53) - (leading - 53) % 2
  let top := (radicand.shiftRight128 shift).lo
  let base := (Float.sqrt top.toFloat).scaleB 26 |>.toUInt64
  let seed := UInt128.shiftLeft ⟨0, base⟩ (shift / 2 - 26)
  let second := Internal.newtonStepWide radicand (Internal.newtonStepWide radicand seed)
  let lowered :=
    if UInt256.less radicand (mul128 second second) then UInt128.sub second ⟨0, 1⟩ else second
  let remainder := UInt256.sub radicand (mul128 lowered lowered)
  if UInt256.less (UInt256.ofUInt128 (add128 lowered lowered).value) remainder then
    (add128 lowered ⟨0, 1⟩).value
  else
    lowered

/--
Accept `guess` exactly when it is the floor root of `radicand`, together with the remainder: the
square is at most the radicand and the remainder is at most twice the root.
-/
@[inline] def acceptRootWide? (radicand : UInt256) (guess : UInt128) :
    Option (RestoringRootState UInt128) :=
  if guess.hi < 0x2000000000000000 then
    let square := mul128 guess guess
    if UInt256.less radicand square then
      none
    else
      let remainder := UInt256.sub radicand square
      if remainder.limb3 == 0 && remainder.limb2 == 0 &&
          !UInt128.less (add128 guess guess).value remainder.low128 then
        some { root := guess, remainder := remainder.low128 }
      else
        none
  else
    none

/--
`rootAndRemainder` with the checked candidate also for radicands of at least `2 ^ 128`. It
equals `rootAndRemainder` on every input (`Internal.rootAndRemainder_eq`), and
`CheckedSqrt.Compiler` installs it in compiled code.
-/
@[inline] def Internal.rootAndRemainder (radicand : UInt256) (steps : Nat) :
    RestoringRootState UInt128 :=
  if 64 ≤ steps && steps ≤ 125 && (radicand.limb3 != 0 || radicand.limb2 != 0) &&
      radicand.log2 < 2 * steps then
    match acceptRootWide? radicand (approxRootWide radicand) with
    | some state => state
    | none => CheckedSquareRoot.rootAndRemainder radicand steps
  else
    CheckedSquareRoot.rootAndRemainder radicand steps

end FloatLib.Numerics.FixedWord.CheckedSquareRoot
