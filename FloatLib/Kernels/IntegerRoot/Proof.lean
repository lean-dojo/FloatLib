/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.IntegerRoot.Runtime
public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Proof
public import FloatLib.Numerics.Exact.IntegerRoot.Proof

/-!
# Exactness of seeded integer roots

The square-root kernel and the seeded Newton iteration both return the floor root, so the
dispatcher agrees with `Nat.nthRoot` in every degree.
-/

@[expose] public section

namespace FloatLib.Numerics.IntegerRoot

/-- The seeded implementation computes `Nat.nthRoot` for every input and degree. -/
theorem root_eq_nthRoot (degree value : Nat) :
    root degree value = Nat.nthRoot degree value := by
  match degree with
  | 0 => rfl
  | 1 => rfl
  | 2 =>
    rw [root, FixedWord.IntegerSquareRoot.sqrtNat_eq_sqrt]
    exact (Nat.nthRoot_eq_of_le_of_lt (Nat.sqrt_le' value)
      (Nat.lt_succ_sqrt' value)).symm
  | degree + 3 => exact newton_eq_nthRoot (degree + 3) value

end FloatLib.Numerics.IntegerRoot
