/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Core.Proof
public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Runtime
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Verified native and arbitrary-precision integer square root

`sqrtIter_toNat` identifies the native Newton iteration with `Nat.sqrt.iter`, and `sqrt_toNat`
proves that its initialization computes the floor square root. The native average cannot overflow.
The runtime module proves termination by a strictly decreasing guess.

`checkRoot?_eq` certifies the increasing-precision candidate by the defining square inequalities.
`sqrtRem_eq` also establishes the exact remainder, with explicit full-precision iteration as
fallback. `natSqrt_eq_sqrtNat` installs both implementations as a compiler substitution for
`Nat.sqrt`, preserving the direct native-word branch below `2^64`.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.IntegerSquareRoot

/-- The overflow-free native average has its ordinary natural-number value. -/
@[simp, grind =] theorem average_toNat (left right : UInt64) :
    (average left right).toNat = (left.toNat + right.toNat) / 2 := by
  have hleftHalf :
      (left >>> 1).toNat = left.toNat / 2 := by
    simp [Nat.shiftRight_eq_div_pow]
  have hrightHalf :
      (right >>> 1).toNat = right.toNat / 2 := by
    simp [Nat.shiftRight_eq_div_pow]
  have hcarry :
      (left &&& right &&& 1).toNat =
        if 2 ≤ left.toNat % 2 + right.toNat % 2 then 1 else 0 := by
    simp only [UInt64.toNat_and, UInt64.reduceToNat, Nat.and_one_is_mod]
    rw [show (2 : Nat) = 2 ^ 1 by decide, Nat.and_mod_two_pow]
    rcases Nat.mod_two_eq_zero_or_one left.toNat with hleft | hleft <;>
      rcases Nat.mod_two_eq_zero_or_one right.toNat with hright | hright <;>
      simp_all
  have hleft := left.toNat_lt
  have hright := right.toNat_lt
  have hfirstFit :
      left.toNat / 2 + right.toNat / 2 < 2 ^ 64 := by
    omega
  have hfullFit :
      left.toNat / 2 + right.toNat / 2 +
        (if 2 ≤ left.toNat % 2 + right.toNat % 2 then 1 else 0) < 2 ^ 64 := by
    split <;> omega
  unfold average
  rw [UInt64.toNat_add, UInt64.toNat_add, hleftHalf, hrightHalf, hcarry,
    Nat.mod_eq_of_lt hfirstFit, Nat.mod_eq_of_lt hfullFit, Nat.add_div (by decide)]

/-- The native Newton iteration is exactly Lean's natural-number iteration. -/
@[simp, grind =] theorem sqrtIter_toNat (value guess : UInt64) :
    (sqrtIter value guess).toNat =
      Nat.sqrt.iter value.toNat guess.toNat := by
  rw [sqrtIter.eq_1, Nat.sqrt.iter.eq_1]
  let next := average guess (value / guess)
  have hnext :
      next.toNat =
        (guess.toNat + value.toNat / guess.toNat) / 2 := by
    simp only [next, average_toNat, UInt64.toNat_div]
  by_cases hdecrease : next < guess
  · have hdecreaseNat :
        (guess.toNat + value.toNat / guess.toNat) / 2 < guess.toNat := by
      rw [← hnext]
      exact UInt64.lt_iff_toNat_lt.mp hdecrease
    rw [dite_eq_left hdecrease, dite_eq_left hdecreaseNat]
    simpa only [next, hnext] using sqrtIter_toNat value next
  · have hnotDecreaseNat :
        ¬(guess.toNat + value.toNat / guess.toNat) / 2 < guess.toNat := by
      rw [← hnext]
      exact fun h ↦ hdecrease (UInt64.lt_iff_toNat_lt.mpr h)
    rw [dite_eq_right hdecrease, dite_eq_right hnotDecreaseNat]
termination_by guess.toNat
decreasing_by
  exact UInt64.lt_iff_toNat_lt.mp hdecrease

/-- Native-word integer square root agrees exactly with `Nat.sqrt`. -/
@[simp, grind =] theorem sqrt_toNat (value : UInt64) :
    (sqrt value).toNat = Nat.sqrt value.toNat := by
  rw [Nat.sqrt.eq_1]
  by_cases hsmall : value ≤ 1
  · have hsmallNat : value.toNat ≤ 1 := by
      simpa [UInt64.le_iff_toNat_le] using hsmall
    simp [sqrt, hsmall, hsmallNat]
  · have hlargeNat : ¬value.toNat ≤ 1 := by
      simpa [UInt64.le_iff_toNat_le] using hsmall
    simp only [sqrt, log2Word_eq_log2, hsmall, hlargeNat, ite_false]
    rw [sqrtIter_toNat]
    apply congrArg (Nat.sqrt.iter value.toNat)
    let shift := value.log2.toNat / 2 + 1
    have hnonzero : value.toNat ≠ 0 := by
      omega
    have hlog :
        value.log2.toNat = value.toNat.log2 :=
      FloatLib.Numerics.FixedWord.log2_toNat value
    have hlogLt : value.toNat.log2 < 64 := by
      rw [Nat.log2_lt hnonzero]
      simpa [UInt64.size] using value.toNat_lt
    have hshift : shift < 64 := by
      simp only [shift, hlog]
      omega
    have hfit : (1 : UInt64).toNat <<< shift < 2 ^ 64 := by
      simp only [UInt64.reduceToNat, Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.pow_lt_pow_right (by decide) hshift
    simpa only [shift, hlog, UInt64.reduceToNat] using
      FloatLib.Numerics.FixedWord.shiftLeft_toNat (1 : UInt64) shift hshift hfit

private theorem predecessor_square (guess : Nat) :
    guess * guess - (guess + guess - 1) = (guess - 1) * (guess - 1) := by
  cases guess with
  | zero => decide
  | succ guess =>
      have hgap : guess + 1 + (guess + 1) - 1 = guess + guess + 1 := by omega
      have hsquare :
          (guess + 1) * (guess + 1) = guess * guess + (guess + guess + 1) := by ring
      simp only [Nat.add_sub_cancel, hgap, hsquare]

/-- Every accepted candidate gives the exact floor square root and remainder. -/
theorem checkRoot?_eq (value guess : Nat) (result : Nat × Nat)
    (h : checkRoot? value guess = some result) :
    result = (Nat.sqrt value, value - Nat.sqrt value * Nat.sqrt value) := by
  unfold checkRoot? at h
  dsimp only at h
  by_cases hlower : guess * guess ≤ value
  · rw [ite_eq_left hlower] at h
    split at h
    next hremainder =>
      have hroot : guess = Nat.sqrt value := Nat.eq_sqrt.mpr ⟨hlower, by
        have hdecompose := Nat.sub_add_cancel hlower
        nlinarith⟩
      rw [← hroot]
      exact (Option.some.inj h).symm
    next _ => simp at h
  · rw [ite_eq_right hlower, predecessor_square] at h
    split at h
    next hpredecessor =>
      have hpositive : 0 < guess := by
        by_contra hzero
        have : guess = 0 := by omega
        simp [this] at hlower
      have hroot : guess - 1 = Nat.sqrt value := Nat.eq_sqrt.mpr ⟨hpredecessor, by
        rw [Nat.sub_add_cancel hpositive]
        omega⟩
      rw [← hroot]
      exact (Option.some.inj h).symm
    next _ => simp at h

/-- Checked increasing-precision Newton preserves the floor square root and exact remainder. -/
theorem sqrtRem_eq (value : Nat) :
    sqrtRem value = (Nat.sqrt value, value - Nat.sqrt value * Nat.sqrt value) := by
  unfold sqrtRem
  cases h : checkRoot? value (approxRoot value (value.log2 / 2)) with
  | none => simp only [← Nat.sqrt.eq_1 value]
  | some result => exact checkRoot?_eq value _ result h

/--
The native and checked arbitrary-precision implementations preserve natural-number square root.
-/
theorem sqrtNat_eq_sqrt (value : Nat) :
    sqrtNat value = Nat.sqrt value := by
  unfold sqrtNat
  split
  next hfit =>
    rw [sqrt_toNat, UInt64.toNat_ofNat_of_lt' hfit]
  next _ =>
    exact congrArg Prod.fst (sqrtRem_eq value)

/--
The compiler uses native-word square root for one-word inputs and checked Newton for larger inputs.

This `@[csimp]` theorem is global: every module that imports it, in particular everything that
imports `FloatLib.Kernels`, compiles `Nat.sqrt` to `sqrtNat`, including uses unrelated to
FloatLib. The substitution is sound by `sqrtNat_eq_sqrt`. The checked candidate's fallback calls
`Nat.sqrt.iter` explicitly, so compiling the replacement cannot recurse through this substitution.
-/
-- grind: no rule; this is a compiler implementation substitution, not a search rewrite.
@[csimp] theorem natSqrt_eq_sqrtNat :
    Nat.sqrt = sqrtNat := by
  funext value
  exact (sqrtNat_eq_sqrt value).symm

end FloatLib.Numerics.FixedWord.IntegerSquareRoot
