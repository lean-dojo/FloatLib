/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits.Proof.Arithmetic
public import FloatLib.Numerics.Kernel.Bits.Proof.PopCount
public import FloatLib.Numerics.Kernel.Root

public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
/-!
# The kernel root check characterizes the floor root

* `isRoot_iff`: for a degree `k ≠ 0`, `isRoot k r n = true` exactly when `r` is `Nat.nthRoot k n`.
* `isRoot_two_iff`: `isRoot 2 r n = true` exactly when `r = Nat.sqrt n`.
* `isqrt_eq`: `isqrt n = Nat.sqrt n` for every `n`.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/-- `isRoot k r n` states the two inequalities that pin down the floor root. -/
theorem isRoot_eq_true (k r n : Nat) : isRoot k r n = true ↔ r ^ k ≤ n ∧ n < (r + 1) ^ k := by
  change Bool.and (Nat.ble (r ^ k) n) (Nat.ble (n + 1) ((r + 1) ^ k)) = true ↔ _
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]
  rfl

/-- For a nonzero degree, the check passes exactly on the floor of the root. -/
theorem isRoot_iff {k : Nat} (hk : k ≠ 0) (r n : Nat) :
    isRoot k r n = true ↔ r = Nat.nthRoot k n := by
  rw [isRoot_eq_true]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact (Nat.nthRoot_eq_of_le_of_lt h₁ h₂).symm
  · rintro rfl
    exact ⟨Nat.pow_nthRoot_le (.inl hk), Nat.lt_pow_nthRoot_add_one hk n⟩

/-- No number passes the check for degree zero. -/
theorem isRoot_zero (r n : Nat) : isRoot 0 r n = false := by
  cases h : isRoot 0 r n
  · rfl
  · rw [isRoot_eq_true] at h
    simp only [Nat.pow_zero] at h
    omega

/-- The check of degree two passes exactly on `Nat.sqrt n`. -/
theorem isRoot_two_iff (r n : Nat) : isRoot 2 r n = true ↔ r = Nat.sqrt n := by
  rw [isRoot_eq_true, Nat.eq_sqrt']

/-- `isqrt n` is the floor of the square root of `n`, for every `n`. -/
theorem isqrt_eq (n : Nat) : isqrt n = Nat.sqrt n := by
  have hgeneral : Bool.casesOn (motive := fun _ => Nat) (isRoot 2 (rootGuess 2 n) n)
      (Nat.sqrt n) (rootGuess 2 n) = Nat.sqrt n := by
    cases h : isRoot 2 (rootGuess 2 n) n
    · rfl
    · exact (isRoot_two_iff _ n).1 h
  change Bool.casesOn (motive := fun _ => Nat) (Nat.ble (size n) 384)
    (Bool.casesOn (motive := fun _ => Nat) (isRoot 2 (rootGuess 2 n) n) (Nat.sqrt n)
      (rootGuess 2 n))
    (Bool.casesOn (motive := fun _ => Nat) (isRoot 2 (sqrtGuess n (size n)) n)
      (Bool.casesOn (motive := fun _ => Nat) (isRoot 2 (rootGuess 2 n) n) (Nat.sqrt n)
        (rootGuess 2 n))
      (sqrtGuess n (size n))) = _
  rw [hgeneral]
  cases Nat.ble (size n) 384
  · rfl
  · cases hfast : isRoot 2 (sqrtGuess n (size n)) n
    · rfl
    · exact (isRoot_two_iff _ n).1 hfast

/-- Compiled code runs core's `Nat.sqrt`. -/
compiled_as isqrt := Nat.sqrt by isqrt_eq

end FloatLib.Numerics.Kernel
