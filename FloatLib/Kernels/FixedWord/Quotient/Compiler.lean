/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Quotient.Runtime

/-!
# Compiler certificate for the two-limb quotient loop

The logical restoring loop is convenient for proofs, while the primitive-word accumulator avoids
allocating a two-limb state at every generated quotient bit. This small module proves those loops
extensionally equal and registers the optimized direction with `@[csimp]`.

Keeping this certificate separate from `Quotient.Proof` matters for executable clients: they can
enable the verified compiler rewrite without importing the much larger rational-arithmetic proof
development.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.RestoringQuotient

/-- Reassemble one primitive-word accumulator step as a two-limb quotient state. -/
private def quotientStep128WordsState
    (den quotient remainder : FloatLib.Numerics.FixedWord.UInt128) :
    QuotientState FloatLib.Numerics.FixedWord.UInt128 :=
  let doubledQuotientHi :=
    (quotient.hi <<< 1) ||| (quotient.lo >>> 63)
  let doubledQuotientLo := quotient.lo <<< 1
  let doubledRemainderHi :=
    (remainder.hi <<< 1) ||| (remainder.lo >>> 63)
  let doubledRemainderLo := remainder.lo <<< 1
  let below :=
    doubledRemainderHi < den.hi ||
      (doubledRemainderHi == den.hi && doubledRemainderLo < den.lo)
  if below then
    { quotient := ⟨doubledQuotientHi, doubledQuotientLo⟩
      remainder := ⟨doubledRemainderHi, doubledRemainderLo⟩ }
  else
    let borrow : UInt64 := if doubledRemainderLo < den.lo then 1 else 0
    { quotient := ⟨doubledQuotientHi, doubledQuotientLo ||| 1⟩
      remainder :=
        ⟨doubledRemainderHi - den.hi - borrow,
          doubledRemainderLo - den.lo⟩ }

/-- The reassembled primitive-word step is the logical two-limb restoring step. -/
private theorem quotientStep128WordsState_eq
    (den quotient remainder : FloatLib.Numerics.FixedWord.UInt128) :
    quotientStep128WordsState den quotient remainder =
      quotientStep128 den
        { quotient := quotient, remainder := remainder } := by
  unfold quotientStep128WordsState quotientStep128
  rfl

/-- The primitive-word accumulator unfolds by one reassembled restoring step. -/
private theorem quotientSteps128Words_succ
    (den : FloatLib.Numerics.FixedWord.UInt128) (n : Nat)
    (quotient remainder : FloatLib.Numerics.FixedWord.UInt128) :
    quotientSteps128Words den.hi den.lo (n + 1)
        quotient.hi quotient.lo remainder.hi remainder.lo =
      let next := quotientStep128WordsState den quotient remainder
      quotientSteps128Words den.hi den.lo n
        next.quotient.hi next.quotient.lo
        next.remainder.hi next.remainder.lo := by
  unfold quotientStep128WordsState
  simp only [quotientSteps128Words]
  split <;> rfl

/-- Every primitive-word accumulator iteration agrees with the logical two-limb loop. -/
private theorem quotientSteps128Words_eq
    (den : FloatLib.Numerics.FixedWord.UInt128) (n : Nat)
    (quotient remainder : FloatLib.Numerics.FixedWord.UInt128) :
    quotientSteps128Words den.hi den.lo n
        quotient.hi quotient.lo remainder.hi remainder.lo =
      quotientSteps128 den n
        { quotient := quotient, remainder := remainder } := by
  induction n generalizing quotient remainder with
  | zero =>
      rfl
  | succ n ih =>
      rw [quotientSteps128Words_succ, quotientSteps128]
      rw [quotientStep128WordsState_eq]
      simpa using
        ih (quotientStep128 den
              { quotient := quotient, remainder := remainder }).quotient
          (quotientStep128 den
              { quotient := quotient, remainder := remainder }).remainder

/-- The primitive-word accumulator implements the logical two-limb restoring recurrence. -/
theorem quotientSteps128Impl_eq_quotientSteps128
    (den : FloatLib.Numerics.FixedWord.UInt128) (n : Nat)
    (state : QuotientState FloatLib.Numerics.FixedWord.UInt128) :
    quotientSteps128Impl den n state =
      quotientSteps128 den n state := by
  unfold quotientSteps128Impl
  simpa using
    quotientSteps128Words_eq den n state.quotient state.remainder

/-- Compile the logical two-limb quotient loop through its verified word accumulator. -/
-- grind: no rule; this compiler substitution exposes an implementation accumulator.
@[csimp] theorem quotientSteps128_eq_quotientSteps128Impl :
    quotientSteps128 = quotientSteps128Impl := by
  funext den n state
  exact (quotientSteps128Impl_eq_quotientSteps128 den n state).symm

end FloatLib.Numerics.FixedWord.RestoringQuotient
