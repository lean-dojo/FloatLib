/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.IntegerRoot.Runtime
public import FloatLib.Numerics.Kernel.RootProof

import Mathlib.Data.Nat.Log

/-!
# Exactness of seeded integer roots

Integer Newton iteration keeps an upper bound on the floor root. Once the guesses stop decreasing,
the defining adjacent-power inequalities identify the floor root, and the radicand's binary
logarithm gives the initial bound for every positive degree.
-/

@[expose] public section

namespace FloatLib.Numerics.IntegerRoot

/-- Integer Newton iteration returns the floor root from any upper bound with enough fuel. -/
private theorem go_eq_nthRoot (n value fuel guess : Nat) (hguess : guess ≤ fuel)
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
      have hdiv : guess ≤ value / guess ^ (n + 1) := by linarith
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

/-- The seeded Newton root is the floor root for every input and degree. -/
theorem Seeded.newton_eq_nthRoot (degree value : Nat) :
    Seeded.newton degree value = Nat.nthRoot degree value := by
  match degree with
  | 0 => rfl
  | 1 => rfl
  | degree + 2 =>
    dsimp only [Seeded.newton]
    split
    · rename_i hvalue
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hvalue with rfl | rfl <;> simp
    · apply go_eq_nthRoot _ _ _ _ (by rfl)
      simpa [Nat.add_assoc] using initial_upper value (degree + 2) (by omega)

/-- The checked Newton root is the floor root for every input and degree. -/
theorem newton_eq_nthRoot (degree value : Nat) :
    newton degree value = Nat.nthRoot degree value := by
  change Bool.casesOn (motive := fun _ => Nat) (Nat.ble value 1)
    (Bool.casesOn (motive := fun _ => Nat)
      (Kernel.isRoot degree (Kernel.rootGuess degree value) value) (Seeded.newton degree value)
      (Kernel.rootGuess degree value))
    (Seeded.newton degree value) = _
  cases Nat.ble value 1
  · change Bool.casesOn (motive := fun _ => Nat)
      (Kernel.isRoot degree (Kernel.rootGuess degree value) value) (Seeded.newton degree value)
      (Kernel.rootGuess degree value) = _
    cases h : Kernel.isRoot degree (Kernel.rootGuess degree value) value
    · exact Seeded.newton_eq_nthRoot degree value
    · have hk : degree ≠ 0 := by
        rintro rfl
        rw [Kernel.isRoot_zero] at h
        cases h
      exact (Kernel.isRoot_iff hk _ value).1 h
  · exact Seeded.newton_eq_nthRoot degree value

/-- The checked root and the seeded root agree. -/
theorem newton_eq_seeded (degree value : Nat) :
    newton degree value = Seeded.newton degree value := by
  rw [newton_eq_nthRoot, Seeded.newton_eq_nthRoot]

/--
Compiled code runs the seeded loop. The kernel body of `newton` builds its count of steps and its
bit length from operations that are cheap for the kernel and slow as compiled code (five to eight
times slower than the seeded loop), so a compiled caller imports this module.
-/
compiled_as newton := Seeded.newton by newton_eq_seeded

end FloatLib.Numerics.IntegerRoot
