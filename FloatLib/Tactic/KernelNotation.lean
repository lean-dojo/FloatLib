/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits.Proof.Arithmetic
public import FloatLib.Numerics.Kernel.ZProof

/-!
# From the kernel's function forms to the notation of the library

A definition written for Lean's kernel applies the fast operations as functions (`Nat.add a b`,
`Nat.shiftLeft a b`, `Nat.ble a b`) and branches with `Bool.casesOn`. `kernel_notation` rewrites
a goal about such a definition into the notation that `omega` and the arithmetic lemmas work
on: `a + b`, `a * 2 ^ b`, `a ≤ b`, `if … then … else …`. `Z.casesOn_eq_ite` and `fast_eq` are the
equations it rewrites with, next to `lowBits_eq`, `minNat_eq` and `maxNat_eq`.
-/

public meta section

namespace FloatLib.Numerics.Kernel

/--
`kernel_notation` rewrites the goal from the kernel's function forms (`Nat.add a b`,
`Nat.shiftLeft a b`, `Bool.casesOn`, `Nat.ble`, …) into the notation of the library (`a + b`,
`a * 2 ^ b`, `if … then … else …`, `a ≤ b`, …), on which `omega` and the arithmetic lemmas work.
-/
macro (name := kernelNotation) "kernel_notation" : tactic =>
  `(tactic| simp only [(FloatLib.Numerics.Kernel.Z.casesOn_eq_ite Iff.rfl),
    fun a b => (FloatLib.Numerics.Kernel.fast_eq a b).1,
    fun a b => (FloatLib.Numerics.Kernel.fast_eq a b).2.1,
    fun a b => (FloatLib.Numerics.Kernel.fast_eq a b).2.2.1,
    fun a b => (FloatLib.Numerics.Kernel.fast_eq a b).2.2.2.1,
    fun a b => (FloatLib.Numerics.Kernel.fast_eq a b).2.2.2.2.1,
    fun a b => (FloatLib.Numerics.Kernel.fast_eq a b).2.2.2.2.2.1,
    fun a b => (FloatLib.Numerics.Kernel.fast_eq a b).2.2.2.2.2.2.1,
    fun a => (FloatLib.Numerics.Kernel.fast_eq a 0).2.2.2.2.2.2.2.1,
    fun a b => (FloatLib.Numerics.Kernel.fast_eq a b).2.2.2.2.2.2.2.2.1,
    fun a b => (FloatLib.Numerics.Kernel.fast_eq a b).2.2.2.2.2.2.2.2.2.1,
    fun a b => (FloatLib.Numerics.Kernel.fast_eq a b).2.2.2.2.2.2.2.2.2.2.1,
    fun a b => (FloatLib.Numerics.Kernel.fast_eq a b).2.2.2.2.2.2.2.2.2.2.2.1,
    fun a b => (FloatLib.Numerics.Kernel.fast_eq a b).2.2.2.2.2.2.2.2.2.2.2.2,
    FloatLib.Numerics.Kernel.lowBits_eq, FloatLib.Numerics.Kernel.minNat_eq,
    FloatLib.Numerics.Kernel.maxNat_eq, Nat.one_mul])

end FloatLib.Numerics.Kernel
