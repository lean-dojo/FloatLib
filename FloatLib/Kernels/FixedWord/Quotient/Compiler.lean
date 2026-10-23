/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Quotient.Runtime
import FloatLib.Kernels.FixedWord.Quotient.Proof

/-!
# Compiler certificates for restoring quotient loops

The logical restoring loop is convenient for proofs, while the primitive-word accumulator avoids
allocating a state at every generated quotient bit. This module proves the logical and accumulator
forms of the one- and two-limb loops equal and registers the accumulator direction with `@[csimp]`.

The compiled scaled quotient also tries a floating-point candidate, checked in exact integer
arithmetic, before the loop. Its certificate uses the loop's arithmetic specification from
`Quotient.Proof`, imported here privately so executable clients get the rewrite without
re-exporting that development.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.RestoringQuotient

/-- The unboxed one-word accumulators preserve every step of the restoring recurrence. -/
theorem quotientStepsWords_eq (den : UInt64) (n : Nat) (quotient remainder : UInt64) :
    quotientStepsWords den n quotient remainder =
      quotientSteps den n { quotient, remainder } := by
  induction n generalizing quotient remainder with
  | zero => rfl
  | succ n ih =>
      simp only [quotientStepsWords, quotientSteps, quotientStep]
      split <;> exact ih _ _

/-- The one-word accumulator agrees with the logical loop for every state and iteration count. -/
theorem Internal.quotientSteps_eq
    (den : UInt64) (n : Nat) (state : QuotientState UInt64) :
    Internal.quotientSteps den n state = RestoringQuotient.quotientSteps den n state := by
  exact quotientStepsWords_eq den n state.quotient state.remainder

/-- Compile one-word restoring division through primitive accumulators. -/
-- grind: no rule; this equation selects a compiler implementation.
@[csimp] theorem quotientSteps_eq_internal :
    quotientSteps = Internal.quotientSteps := by
  funext den n state
  exact (Internal.quotientSteps_eq den n state).symm

/--
Compile scaled quotient rounding through the same accumulator.

This equation also replaces calls whose original body was compiled before the loop certificate
was imported.
-/
-- grind: no rule; this equation selects a compiler implementation.
@[csimp] theorem roundScaledQuotient_eq_internal :
    roundScaledQuotient = Internal.roundScaledQuotient := by
  funext num den shift
  have hloop : roundQuotientState den
      (quotientStepsWords den shift (num / den) (num % den)) = roundScaledQuotient num den shift := by
    simp only [roundScaledQuotient, quotientStepsWords_eq]
  unfold Internal.roundScaledQuotient
  split
  · rename_i hguard
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hguard
    obtain ⟨⟨hden, hdenSmall⟩, hshift⟩ := hguard
    have hdenFit : den.toNat < 2 ^ 63 := UInt64.lt_iff_toNat_lt.mp hdenSmall
    have hnum : ({ hi := 0, lo := num } : UInt128).toNat = num.toNat := by
      simp [UInt128.toNat]
    have hscaled :
        (UInt128.shiftLeft { hi := 0, lo := num } shift).toNat = num.toNat <<< shift := by
      rw [UInt128.shiftLeft_toNat _ _ (by omega) (by
        rw [hnum, Nat.shiftLeft_eq]
        calc num.toNat * 2 ^ shift < 2 ^ 64 * 2 ^ 64 :=
              Nat.mul_lt_mul'' num.toNat_lt (Nat.pow_lt_pow_right (by decide) hshift)
          _ = 2 ^ 128 := by norm_num), hnum]
    have hchecked (guess : UInt64)
        (hguess :
          isFloorQuotient (UInt128.shiftLeft { hi := 0, lo := num } shift) den guess = true) :
        roundScaledQuotient num den shift =
          roundQuotientState den
            { quotient := guess,
              remainder :=
                (quotientRemainder (UInt128.shiftLeft { hi := 0, lo := num } shift) den guess).lo
            } := by
      obtain ⟨hq, hr, hfit⟩ := isFloorQuotient_spec hguess
      rw [hscaled] at hq hr
      apply UInt64.toNat_inj.mp
      rw [roundScaledQuotient_toNat num den shift hden hdenFit (by omega),
        roundQuotientState_toNat den _ _ hden hdenFit hq hr (by omega)]
    dsimp only
    split
    · exact hchecked _ ‹_›
    · split
      · exact hchecked _ ‹_›
      · split
        · exact hchecked _ ‹_›
        · exact hloop.symm
  · exact hloop.symm

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
theorem Internal.quotientSteps128_eq
    (den : FloatLib.Numerics.FixedWord.UInt128) (n : Nat)
    (state : QuotientState FloatLib.Numerics.FixedWord.UInt128) :
    Internal.quotientSteps128 den n state =
      RestoringQuotient.quotientSteps128 den n state := by
  unfold Internal.quotientSteps128
  simpa using
    quotientSteps128Words_eq den n state.quotient state.remainder

/-- Compile the logical two-limb quotient loop through its verified word accumulator. -/
-- grind: no rule; this compiler substitution exposes an implementation accumulator.
@[csimp] theorem quotientSteps128_eq_internal :
    quotientSteps128 = Internal.quotientSteps128 := by
  funext den n state
  exact (Internal.quotientSteps128_eq den n state).symm

end FloatLib.Numerics.FixedWord.RestoringQuotient
