/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import FloatLib.Kernels.FixedWord.Quotient.Proof

/-!
# Two-limb restoring quotient refinement

Each step doubles `quotient * denominator + remainder` while keeping the remainder below the
denominator. Iterating the step theorem from `Quotient.Proof` gives the scaled quotient and
remainder, provided the denominator and quotient prefixes fit in two limbs.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.RestoringQuotient

/--
One two-limb restoring step preserves the exact scaled numerator and keeps the quotient within the
capacity required by the remaining loop.
-/
theorem quotientStep128_spec
    (den : FloatLib.Numerics.FixedWord.UInt128)
    (state : QuotientState FloatLib.Numerics.FixedWord.UInt128)
    (hdenFit : den.toNat < 2 ^ 127)
    (hremainder : state.remainder.toNat < den.toNat)
    (hquotientFit : 2 * state.quotient.toNat + 1 < 2 ^ 128) :
    let result := quotientStep128 den state
    result.quotient.toNat * den.toNat + result.remainder.toNat =
        2 * (state.quotient.toNat * den.toNat +
          state.remainder.toNat) ∧
      result.remainder.toNat < den.toNat ∧
      state.quotient.toNat ≤ result.quotient.toNat ∧
      result.quotient.toNat + 1 ≤
        2 * (state.quotient.toNat + 1) := by
  have hnextFit :
      (natQuotientStep den.toNat state.toNat128).quotient <
        2 ^ 128 := by
    simp only [natQuotientStep, QuotientState.toNat128]
    by_cases hbelow :
        2 * state.remainder.toNat < den.toNat
    · simp [hbelow]
      omega
    · simp [hbelow]
      exact hquotientFit
  have hrefine :=
    quotientStep128_toNat den state hdenFit hremainder hnextFit
  have hquotient :
      (quotientStep128 den state).quotient.toNat =
        (natQuotientStep den.toNat state.toNat128).quotient := by
    simpa only [QuotientState.toNat128] using
      congrArg QuotientState.quotient hrefine
  have hremainderNat :
      (quotientStep128 den state).remainder.toNat =
        (natQuotientStep den.toNat state.toNat128).remainder := by
    simpa only [QuotientState.toNat128] using
      congrArg QuotientState.remainder hrefine
  have hmodel :=
    natQuotientStep_spec den.toNat state.toNat128 hremainder
  dsimp only
  rw [hquotient, hremainderNat]
  refine ⟨hmodel.1, hmodel.2.1, hmodel.2.2, ?_⟩
  simp only [natQuotientStep, QuotientState.toNat128]
  by_cases hbelow :
      2 * state.remainder.toNat < den.toNat
  · simp [hbelow]
    omega
  · simp [hbelow]
    omega

/--
The two-limb restoring loop preserves the exact scaled numerator without ever overflowing the
quotient carrier.
-/
theorem quotientSteps128_spec
    (den : FloatLib.Numerics.FixedWord.UInt128) (n : Nat)
    (state : QuotientState FloatLib.Numerics.FixedWord.UInt128)
    (hdenFit : den.toNat < 2 ^ 127)
    (hremainder : state.remainder.toNat < den.toNat)
    (hcapacity :
      (state.quotient.toNat + 1) * 2 ^ n ≤ 2 ^ 128) :
    let result := quotientSteps128 den n state
    result.quotient.toNat * den.toNat + result.remainder.toNat =
        (state.quotient.toNat * den.toNat +
          state.remainder.toNat) * 2 ^ n ∧
      result.remainder.toNat < den.toNat ∧
      state.quotient.toNat ≤ result.quotient.toNat := by
  induction n generalizing state with
  | zero =>
      simp [quotientSteps128, hremainder]
  | succ n ih =>
      let nextState := quotientStep128 den state
      have hstepFit :
          2 * state.quotient.toNat + 1 < 2 ^ 128 := by
        rw [pow_succ] at hcapacity
        nlinarith [Nat.two_pow_pos n]
      have hstep :
          nextState.quotient.toNat * den.toNat +
                nextState.remainder.toNat =
              2 * (state.quotient.toNat * den.toNat +
                state.remainder.toNat) ∧
            nextState.remainder.toNat < den.toNat ∧
            state.quotient.toNat ≤ nextState.quotient.toNat ∧
            nextState.quotient.toNat + 1 ≤
              2 * (state.quotient.toNat + 1) := by
        simpa only [nextState] using
          quotientStep128_spec den state hdenFit hremainder hstepFit
      have hnextCapacity :
          (nextState.quotient.toNat + 1) * 2 ^ n ≤ 2 ^ 128 := by
        calc
          (nextState.quotient.toNat + 1) * 2 ^ n ≤
              (2 * (state.quotient.toNat + 1)) * 2 ^ n :=
            Nat.mul_le_mul_right _ hstep.2.2.2
          _ = (state.quotient.toNat + 1) * 2 ^ (n + 1) := by
            rw [pow_succ]
            ring
          _ ≤ 2 ^ 128 := hcapacity
      have hrest :=
        ih nextState hstep.2.1 hnextCapacity
      let result := quotientSteps128 den n nextState
      change
        result.quotient.toNat * den.toNat + result.remainder.toNat =
            (state.quotient.toNat * den.toNat +
              state.remainder.toNat) * 2 ^ (n + 1) ∧
          result.remainder.toNat < den.toNat ∧
          state.quotient.toNat ≤ result.quotient.toNat
      change
        result.quotient.toNat * den.toNat + result.remainder.toNat =
            (nextState.quotient.toNat * den.toNat +
              nextState.remainder.toNat) * 2 ^ n ∧
          result.remainder.toNat < den.toNat ∧
          nextState.quotient.toNat ≤ result.quotient.toNat at hrest
      refine ⟨?_, hrest.2.1, le_trans hstep.2.2.1 hrest.2.2⟩
      rw [hrest.1, hstep.1, pow_succ]
      ring

/--
The final two-limb restoring state is the exact quotient and remainder of its scaled numerator.
-/
theorem quotientSteps128_div_mod
    (den : FloatLib.Numerics.FixedWord.UInt128) (n : Nat)
    (state : QuotientState FloatLib.Numerics.FixedWord.UInt128)
    (hdenFit : den.toNat < 2 ^ 127)
    (hremainder : state.remainder.toNat < den.toNat)
    (hcapacity :
      (state.quotient.toNat + 1) * 2 ^ n ≤ 2 ^ 128) :
    let numerator :=
      (state.quotient.toNat * den.toNat +
        state.remainder.toNat) * 2 ^ n
    let result := quotientSteps128 den n state
    result.quotient.toNat = numerator / den.toNat ∧
      result.remainder.toNat = numerator % den.toNat := by
  let numerator :=
    (state.quotient.toNat * den.toNat +
      state.remainder.toNat) * 2 ^ n
  let result := quotientSteps128 den n state
  change result.quotient.toNat = numerator / den.toNat ∧
    result.remainder.toNat = numerator % den.toNat
  have hspec :=
    quotientSteps128_spec den n state hdenFit hremainder hcapacity
  have hdenPositive : 0 < den.toNat := by omega
  have hunique :
      numerator / den.toNat = result.quotient.toNat ∧
        numerator % den.toNat = result.remainder.toNat :=
    (Nat.div_mod_unique hdenPositive).2 <| by
      refine ⟨?_, hspec.2.1⟩
      simpa only [result, numerator, Nat.add_comm, Nat.mul_comm] using
        hspec.1
  exact ⟨hunique.1.symm, hunique.2.symm⟩

end FloatLib.Numerics.FixedWord.RestoringQuotient
