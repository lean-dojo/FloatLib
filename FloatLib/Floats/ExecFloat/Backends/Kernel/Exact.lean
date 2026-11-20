/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.SignedRat
public import FloatLib.Numerics.Kernel.QProof
public import FloatLib.Tactic.KernelOptimize

/-!
# Kernel rules for integers, rationals and bit operations

`FloatLib.Numerics.Kernel` proves each of its kernel functions equal to the operation of core
Lean on `Int`, `Rat` or `Nat` that it computes (`Z.add_eq : Z.add a b = a + b`). This module tags
those equations `@[kernel_optimize ←]`, each with its measured kernel cost in microseconds
(64-bit operands, Lean v4.36.0), so that the rewrite set turns the core operation into the kernel
function. `simp only [kernel_optimize]` rewrites a statement with them, and `decide +kernel`
then lets the kernel evaluate it:

```lean
example : (123456789 : Int) * 987654321 - 5 ≤ 121932631112635270 := by
  simp only [kernel_optimize]
  decide +kernel
```

The kernel then runs `Int.ble' (Z.sub (Z.mul 123456789 987654321) 5) 121932631112635270`, at
about 17 µs per operation, where the statement as written costs it 40 to 90 µs per operation.

* Arithmetic on `Int`: `Z.add_eq`, `Z.sub_eq`, `Z.mul_eq`, `Z.neg_eq`, `Z.pow_eq`, `Z.ediv_eq`,
  `Z.emod_eq`, `Z.fdiv_eq`, `Z.shiftLeft_eq`, `Z.shiftRight_eq`, `Z.natAbs_eq`, `Z.toNat_eq`,
  `Z.min_eq`, `Z.max_eq`, and the equations of the functions (`Z.add_eq_compiled : @Z.add =
  @Int.add` and its siblings, with `Int.subNatNat` and `Int.negOfNat`) for a definition that
  calls `Int.add` and not `+`.
* Order on `Int`: `Z.ble'_iff`, `Z.blt'_iff`, `Z.beq'_iff`, on core's `Int.ble'`, `Int.blt'` and
  `Int.beq'`.
* Bits of naturals: `testBit_eq`, `size_eq`, `log2_eq_size_sub_one`, `popCount_eq` (the
  population count `(Nat.digits 2 n).sum`).
* Rationals: `Q.add_eq`, `Q.sub_eq`, `Q.mul_eq`, `Q.neg_eq`, `Q.inv_eq`, `Q.div_eq`, `Q.pow_eq`,
  `Q.abs_eq`, `Q.min_eq`, `Q.max_eq`, `Q.floor_eq`, `Q.ceil_eq`, `Q.mk_eq`, and the order
  `Q.le_iff`, `Q.lt_iff`, `Q.beq_iff`. A comparison of rationals costs the kernel about 50 µs
  with them and about 0.5 ms as written.
* Signed rationals: `SignedRat.ofRat_eq_ofNum`, which reads the sign bit of `SignedRat.ofRat q`
  from the case of the numerator of `q` where `ofRat` decides `q < 0`.
-/

open FloatLib.Numerics.Kernel

attribute [kernel_optimize ← (cost := 17)] Z.add_eq Z.sub_eq
attribute [kernel_optimize ← (cost := 18)] Z.mul_eq
attribute [kernel_optimize ← (cost := 5)] Z.neg_eq
attribute [kernel_optimize ← (cost := 12)] Z.pow_eq
attribute [kernel_optimize ← (cost := 27)] Z.ediv_eq Z.emod_eq Z.fdiv_eq
attribute [kernel_optimize ← (cost := 6)] Z.shiftLeft_eq Z.shiftRight_eq
attribute [kernel_optimize ← (cost := 4)] Z.natAbs_eq Z.toNat_eq
attribute [kernel_optimize ← (cost := 10)] Z.min_eq Z.max_eq
attribute [kernel_optimize ← (cost := 8)] Z.ble'_iff Z.blt'_iff Z.beq'_iff
-- The functions themselves, where a definition calls `Int.add` and not `+`.
attribute [kernel_optimize ←] Z.subNat_eq_compiled Z.negOfNat_eq_compiled Z.neg_eq_compiled
  Z.add_eq_compiled Z.sub_eq_compiled Z.mul_eq_compiled Z.natAbs_eq_compiled Z.toNat_eq_compiled

attribute [kernel_optimize ← (cost := 5)] testBit_eq
attribute [kernel_optimize ← (cost := 17)] size_eq
attribute [kernel_optimize (cost := 18)] log2_eq_size_sub_one
attribute [kernel_optimize ← (cost := 30)] popCount_eq

attribute [kernel_optimize ← (cost := 70)] Q.add_eq Q.sub_eq
attribute [kernel_optimize ← (cost := 45)] Q.mul_eq
attribute [kernel_optimize ← (cost := 7)] Q.neg_eq
attribute [kernel_optimize ← (cost := 40)] Q.inv_eq
attribute [kernel_optimize ← (cost := 85)] Q.div_eq
attribute [kernel_optimize ← (cost := 20)] Q.pow_eq
attribute [kernel_optimize ← (cost := 5)] Q.abs_eq
attribute [kernel_optimize ← (cost := 65)] Q.min_eq Q.max_eq
attribute [kernel_optimize ← (cost := 30)] Q.floor_eq Q.ceil_eq
attribute [kernel_optimize ← (cost := 17)] Q.mk_eq
attribute [kernel_optimize ← (cost := 50)] Q.le_iff Q.lt_iff
attribute [kernel_optimize ← (cost := 10)] Q.beq_iff

attribute [kernel_optimize (cost := 2)] FloatLib.Numerics.SignedRat.ofRat_eq_ofNum
