/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits.Proof.Length

/-!
# The binary logarithm for Lean's kernel

Lean's kernel evaluates `Nat.log2` by its recursion, one step for each bit of the number: about
half a millisecond for a significand of binary64 and fifty milliseconds for a number of 4,000
bits. `log2 n` is the same number (`log2_eq`) read off the bit length `size n`, which the
kernel computes in a few native operations for a number of any size. A kernel form uses it
wherever its reference uses `Nat.log2`, and so does a definition of the reference that Lean's
kernel evaluates on long numbers, such as `RationalBinary.floorLog2`. Compiled code runs core's
`Nat.log2` in its place (`log2_eq_compiled`).
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/--
The position of the leading bit of `n`, and zero for zero (`log2_eq`): the bit length `size n`
less one.
-/
def log2 (n : Nat) : Nat :=
  Nat.pred (size n)

/-- `log2` is core's `Nat.log2`. -/
theorem log2_eq (n : Nat) : log2 n = Nat.log2 n := by
  unfold log2
  rw [size_eq_log2]
  by_cases hn : n = 0
  · subst hn
    rfl
  · rw [ite_eq_right hn]
    rfl

compiled_as log2 := Nat.log2 by log2_eq

end FloatLib.Numerics.Kernel
