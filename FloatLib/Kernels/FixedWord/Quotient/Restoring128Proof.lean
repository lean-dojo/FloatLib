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
  have hstep := natQuotientStep_quotient_le den.toNat state.toNat128
  have hnextFit :
      (natQuotientStep den.toNat state.toNat128).quotient < 2 ^ 128 :=
    lt_of_le_of_lt hstep hquotientFit
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
  change _ ≤ 2 * state.quotient.toNat + 1 at hstep
  omega

/--
Within its quotient capacity, the two-limb restoring loop agrees with the natural-number loop
step for step.
-/
private theorem quotientSteps128_toNat128
    (den : FloatLib.Numerics.FixedWord.UInt128) (n : Nat)
    (state : QuotientState FloatLib.Numerics.FixedWord.UInt128)
    (hdenFit : den.toNat < 2 ^ 127)
    (hremainder : state.remainder.toNat < den.toNat)
    (hcapacity :
      (state.quotient.toNat + 1) * 2 ^ n ≤ 2 ^ 128) :
    (quotientSteps128 den n state).toNat128 =
      natQuotientSteps den.toNat n state.toNat128 := by
  induction n generalizing state with
  | zero => rw [quotientSteps128.eq_1, natQuotientSteps.eq_1]
  | succ n ih =>
      have hstepFit :
          2 * state.quotient.toNat + 1 < 2 ^ 128 := by
        rw [pow_succ] at hcapacity
        nlinarith [Nat.two_pow_pos n]
      have hstep :=
        quotientStep128_spec den state hdenFit hremainder hstepFit
      have hnextCapacity :
          ((quotientStep128 den state).quotient.toNat + 1) * 2 ^ n ≤
            2 ^ 128 := by
        calc
          ((quotientStep128 den state).quotient.toNat + 1) * 2 ^ n ≤
              (2 * (state.quotient.toNat + 1)) * 2 ^ n :=
            Nat.mul_le_mul_right _ hstep.2.2.2
          _ = (state.quotient.toNat + 1) * 2 ^ (n + 1) := by
            rw [pow_succ]
            ring
          _ ≤ 2 ^ 128 := hcapacity
      have hnextFit :
          (natQuotientStep den.toNat state.toNat128).quotient < 2 ^ 128 :=
        lt_of_le_of_lt (natQuotientStep_quotient_le _ _) hstepFit
      rw [quotientSteps128.eq_2, natQuotientSteps.eq_2,
        ← quotientStep128_toNat den state hdenFit hremainder hnextFit]
      exact ih _ hstep.2.1 hnextCapacity

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
  have hmodel :=
    natQuotientSteps_spec den.toNat n state.toNat128 hremainder
  rw [← quotientSteps128_toNat128 den n state hdenFit hremainder hcapacity] at hmodel
  exact hmodel

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
  have hmodel :=
    natQuotientSteps_div_mod den.toNat n state.toNat128 hremainder
  rw [← quotientSteps128_toNat128 den n state hdenFit hremainder hcapacity] at hmodel
  exact hmodel

end FloatLib.Numerics.FixedWord.RestoringQuotient
