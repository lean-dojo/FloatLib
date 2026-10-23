/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Difference.Runtime
public import FloatLib.Kernels.FixedWord.LimbRound.Runtime

/-!
# Fixed-word restoring quotient generation

One- and two-limb unsigned restoring-division state machines share a quotient/remainder
recurrence, alongside a one-word rational-logarithm kernel.
`Quotient.Proof` proves the one-word loop and the two-limb step, and
`Quotient.Restoring128Proof` proves the two-limb loop.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.RestoringQuotient

universe u

/-- Quotient and remainder state shared by the native loop and its natural-number proof model. -/
structure QuotientState (α : Type u) where
  /-- Binary quotient prefix generated so far. -/
  quotient : α
  /-- Remainder after the generated quotient prefix. -/
  remainder : α
  deriving DecidableEq, Repr

/--
Generate one additional binary quotient digit.

Callers keep `den < 2^63` and `remainder < den`, so the doubled remainder fits one word, and keep
the generated quotient prefix below `2^63` so that its doubling fits as well.
-/
@[inline] def quotientStep (den : UInt64) (state : QuotientState UInt64) :
    QuotientState UInt64 :=
  let doubledQuotient := state.quotient + state.quotient
  let doubledRemainder := state.remainder + state.remainder
  if doubledRemainder < den then
    { quotient := doubledQuotient
      remainder := doubledRemainder }
  else
    { quotient := doubledQuotient + 1
      remainder := doubledRemainder - den }

/-- Generate `n` binary quotient digits, under the same capacity contract as `quotientStep`. -/
@[inline] def quotientSteps (den : UInt64) :
    Nat → QuotientState UInt64 → QuotientState UInt64
  | 0, state => state
  | n + 1, state => quotientSteps den n (quotientStep den state)

/--
Generate quotient digits with unboxed quotient and remainder accumulators.

Only the final result constructs a `QuotientState`. The arithmetic is that of `quotientSteps`,
including word wraparound outside its capacity bounds.
-/
def quotientStepsWords (den : UInt64) :
    Nat → UInt64 → UInt64 → QuotientState UInt64
  | 0, quotient, remainder => { quotient, remainder }
  | n + 1, quotient, remainder =>
      let doubledQuotient := quotient + quotient
      let doubledRemainder := remainder + remainder
      if doubledRemainder < den then
        quotientStepsWords den n doubledQuotient doubledRemainder
      else
        quotientStepsWords den n (doubledQuotient + 1) (doubledRemainder - den)

/-- Run the one-word restoring loop without allocating a state for each quotient bit. -/
@[inline] def Internal.quotientSteps (den : UInt64) (n : Nat) (state : QuotientState UInt64) :
    QuotientState UInt64 :=
  quotientStepsWords den n state.quotient state.remainder

/--
Generate one binary quotient digit in a two-limb carrier.

Callers maintain `remainder < den < 2^127` and `quotient < 2^127`. These bounds keep the doubled
remainder and the next quotient prefix in `UInt128`, so the step agrees with the natural-number
restoring recurrence.
-/
@[inline] def quotientStep128
    (den : FloatLib.Numerics.FixedWord.UInt128)
    (state : QuotientState FloatLib.Numerics.FixedWord.UInt128) :
    QuotientState FloatLib.Numerics.FixedWord.UInt128 :=
  let doubledQuotient :=
    FloatLib.Numerics.FixedWord.UInt128.shiftLeft state.quotient 1
  let doubledRemainder :=
    FloatLib.Numerics.FixedWord.UInt128.shiftLeft state.remainder 1
  if FloatLib.Numerics.FixedWord.UInt128.less doubledRemainder den then
    { quotient := doubledQuotient
      remainder := doubledRemainder }
  else
    { quotient := doubledQuotient.setLowBit
      remainder :=
        FloatLib.Numerics.FixedWord.UInt128.sub doubledRemainder den }

/--
Generate two-limb quotient digits using four primitive machine-word accumulators.

The preconditions are the same as `quotientStep128`: callers keep the denominator below `2^127`,
the remainder below the denominator, and the generated quotient in range.
-/
@[inline] def quotientSteps128Words
    (denHi denLo : UInt64) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 →
      QuotientState FloatLib.Numerics.FixedWord.UInt128
  | 0, quotientHi, quotientLo, remainderHi, remainderLo =>
      { quotient := ⟨quotientHi, quotientLo⟩
        remainder := ⟨remainderHi, remainderLo⟩ }
  | n + 1, quotientHi, quotientLo, remainderHi, remainderLo =>
      let doubledQuotientHi :=
        (quotientHi <<< 1) ||| (quotientLo >>> 63)
      let doubledQuotientLo := quotientLo <<< 1
      let doubledRemainderHi :=
        (remainderHi <<< 1) ||| (remainderLo >>> 63)
      let doubledRemainderLo := remainderLo <<< 1
      let below :=
        doubledRemainderHi < denHi ||
          (doubledRemainderHi == denHi && doubledRemainderLo < denLo)
      if below then
        quotientSteps128Words denHi denLo n
          doubledQuotientHi doubledQuotientLo
          doubledRemainderHi doubledRemainderLo
      else
        let borrow : UInt64 := if doubledRemainderLo < denLo then 1 else 0
        quotientSteps128Words denHi denLo n
          doubledQuotientHi (doubledQuotientLo ||| 1)
          (doubledRemainderHi - denHi - borrow)
          (doubledRemainderLo - denLo)

/--
Compiled two-limb quotient loop, on the accumulators of `quotientSteps128Words`.

It constructs the public state once, after the final digit, so no step allocates a structure or
an addition result.
-/
@[inline] def Internal.quotientSteps128
    (den : FloatLib.Numerics.FixedWord.UInt128) (n : Nat)
    (state : QuotientState FloatLib.Numerics.FixedWord.UInt128) :
    QuotientState FloatLib.Numerics.FixedWord.UInt128 :=
  quotientSteps128Words den.hi den.lo n
    state.quotient.hi state.quotient.lo
    state.remainder.hi state.remainder.lo

/--
Generate `n` binary quotient digits in a two-limb carrier.

The logical body is the shared restoring recurrence, and it is the only definition the kernel
sees. With `Quotient.Compiler` imported, compiled code runs `Internal.quotientSteps128` instead.
That module proves the two equal and registers the equation with `@[csimp]`, so the substitution
carries a proof, which `implemented_by` would not. Modules that import only this runtime compile
the logical recursion.
-/
def quotientSteps128
    (den : FloatLib.Numerics.FixedWord.UInt128) :
    Nat → QuotientState FloatLib.Numerics.FixedWord.UInt128 →
      QuotientState FloatLib.Numerics.FixedWord.UInt128
  | 0, state => state
  | n + 1, state =>
      quotientSteps128 den n (quotientStep128 den state)

/--
Round a restoring-division state to nearest, with ties to even.

Callers keep `0 < den < 2^63`, `remainder < den`, and the quotient below `2^63`, so the doubled
remainder and the incremented quotient fit one word.
-/
@[inline] def roundQuotientState
    (den : UInt64) (state : QuotientState UInt64) : UInt64 :=
  let doubledRemainder := state.remainder + state.remainder
  if doubledRemainder < den then
    state.quotient
  else if den < doubledRemainder then
    state.quotient + 1
  else if state.quotient % 2 == 0 then
    state.quotient
  else
    state.quotient + 1

/--
Floating-point candidate for `(num <<< shift) / den` when `shift < 64`. Its accuracy is never
assumed, because `isFloorQuotient` checks every candidate.
-/
@[inline] def Internal.approxQuotient (num den : UInt64) (shift : Nat) : UInt64 :=
  (num.toFloat / den.toFloat * ((1 : UInt64) <<< UInt64.ofNat shift).toFloat).toUInt64

/-- Remainder of `scaled` after subtracting `guess * den`, as a two-word value. -/
@[inline] def quotientRemainder (scaled : UInt128) (den guess : UInt64) : UInt128 :=
  UInt128.sub scaled (mul64 guess den)

/--
Whether `guess` is the floor quotient of `scaled` by `den` with room to round up, decided from
the two-word product and remainder.
-/
@[inline] def isFloorQuotient (scaled : UInt128) (den guess : UInt64) : Bool :=
  guess < 0x7fffffffffffffff && !UInt128.less scaled (mul64 guess den) &&
    (quotientRemainder scaled den guess).hi == 0 &&
    (quotientRemainder scaled den guess).lo < den

/--
Round `(num / den) * 2^shift` to nearest even using native restoring division.

`roundScaledQuotient_toNat` requires `0 < den < 2^63` and `(num <<< shift) / den + 1 < 2^63`,
which keep every intermediate of the restoring loop inside one word.
-/
@[inline] def roundScaledQuotient
    (num den : UInt64) (shift : Nat) : UInt64 :=
  let initial : QuotientState UInt64 :=
    { quotient := num / den
      remainder := num % den }
  roundQuotientState den (quotientSteps den shift initial)

/--
Compiled `roundScaledQuotient`. When `shift < 64` and `0 < den < 2^63`, the floating-point
candidate or a neighbour that passes `isFloorQuotient` replaces the restoring loop. Otherwise the
loop runs on primitive-word accumulators. The checked state is never materialized, so the fast path
allocates nothing. `Quotient.Compiler` proves it equal to `roundScaledQuotient`.
-/
@[inline] def Internal.roundScaledQuotient
    (num den : UInt64) (shift : Nat) : UInt64 :=
  if den != 0 && den < 0x8000000000000000 && shift < 64 then
    let scaled := UInt128.shiftLeft { hi := 0, lo := num } shift
    let guess := Internal.approxQuotient num den shift
    if isFloorQuotient scaled den guess then
      roundQuotientState den
        { quotient := guess, remainder := (quotientRemainder scaled den guess).lo }
    else if isFloorQuotient scaled den (guess - 1) then
      roundQuotientState den
        { quotient := guess - 1, remainder := (quotientRemainder scaled den (guess - 1)).lo }
    else if isFloorQuotient scaled den (guess + 1) then
      roundQuotientState den
        { quotient := guess + 1, remainder := (quotientRemainder scaled den (guess + 1)).lo }
    else
      roundQuotientState den (quotientStepsWords den shift (num / den) (num % den))
  else
    roundQuotientState den (quotientStepsWords den shift (num / den) (num % den))

/--
Compute `floor (log2 (num / den))` for nonzero operands, using native-word alignment.
-/
@[inline] def floorLog2RatWord (num den : UInt64) : Int :=
  let numLog := (log2Word num).toNat
  let denLog := (log2Word den).toNat
  if denLog ≤ numLog then
    let shift := numLog - denLog
    let initial := Int.ofNat shift
    if num < den <<< UInt64.ofNat shift then initial - 1 else initial
  else
    let shift := denLog - numLog
    let initial := -Int.ofNat shift
    if num <<< UInt64.ofNat shift < den then initial - 1 else initial

end FloatLib.Numerics.FixedWord.RestoringQuotient
