/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.IntegerRoot.Runtime
public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Proof
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Nat.Log

/-!
# Exactness of seeded integer roots

An upper bound on the floor root is preserved by integer Newton iteration. Once the guesses
stop decreasing, the defining adjacent-power inequalities identify the floor root. The
radicand's binary logarithm provides the initial bound for every positive degree.
-/

@[expose] public section

namespace FloatLib.Numerics.IntegerRoot

/-- Integer Newton iteration returns the floor root from any upper bound with enough fuel. -/
theorem go_eq_nthRoot (n value fuel guess : Nat) (hguess : guess ≤ fuel)
    (hupper : value < (guess + 1) ^ (n + 2)) :
    Nat.nthRoot.go n value fuel guess = Nat.nthRoot (n + 2) value := by
  induction fuel generalizing guess with
  | zero =>
    have hg : guess = 0 := by omega
    subst guess
    exact (Nat.nthRoot_eq_of_le_of_lt (by simp) hupper).symm
  | succ fuel ih =>
    rw [Nat.nthRoot.go]
    split
    · rename_i hnext
      apply ih _ (by omega)
      have hg : guess ≠ 0 := by
        intro h
        simp [h] at hnext
      exact Nat.nthRoot.lt_pow_go_succ_aux hg
    · rename_i hnext
      apply (Nat.nthRoot_eq_of_le_of_lt ?_ hupper).symm
      have hmul := Nat.mul_le_of_le_div _ _ _ (Nat.le_of_not_lt hnext)
      have hdiv : guess ≤ value / guess ^ (n + 1) := by nlinarith
      have h := Nat.mul_le_of_le_div _ _ _ hdiv
      simpa [pow_succ, Nat.mul_comm] using h

private theorem initial_upper (value degree : Nat) (hd : 0 < degree) :
    value < (2 ^ ((value.log2 + degree) / degree) + 1) ^ degree := by
  have hvalue : value < 2 ^ (value.log2 + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by decide) value
  have hbits : value.log2 + 1 ≤ ((value.log2 + degree) / degree) * degree := by
    rw [Nat.add_div_right _ hd]
    have h := Nat.lt_mul_div_succ value.log2 hd
    exact Nat.succ_le_of_lt (by simpa [Nat.mul_comm] using h)
  calc
    value < 2 ^ (value.log2 + 1) := hvalue
    _ ≤ 2 ^ (((value.log2 + degree) / degree) * degree) :=
      Nat.pow_le_pow_right (by decide) hbits
    _ = (2 ^ ((value.log2 + degree) / degree)) ^ degree := pow_mul _ _ _
    _ ≤ (2 ^ ((value.log2 + degree) / degree) + 1) ^ degree :=
      Nat.pow_le_pow_left (by omega) degree

/-- The seeded implementation preserves the exact integer root for every input and degree. -/
theorem root_eq_nthRoot (degree value : Nat) :
    root degree value = Nat.nthRoot degree value := by
  match degree with
  | 0 => rfl
  | 1 => rfl
  | 2 =>
    rw [root, FixedWord.IntegerSquareRoot.sqrtNat_eq_sqrt]
    exact (Nat.nthRoot_eq_of_le_of_lt (Nat.sqrt_le' value)
      (Nat.lt_succ_sqrt' value)).symm
  | degree + 3 =>
    apply go_eq_nthRoot _ _ _ _ (by rfl)
    simpa [Nat.add_assoc] using initial_upper value (degree + 3) (by omega)

end FloatLib.Numerics.IntegerRoot
