/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value
public import FloatLib.Tactic.LaneTable

/-!
# Kernel operations on all lanes of a row, and packed tables of small formats

The kernel operations of a binary format are made of the natural-number operations that Lean's
kernel computes natively, so `lane_decide` reads the staged operations (`KernelPath.add`,
`KernelPath.sub`, `KernelPath.mul`, `KernelPath.neg`, the comparison code) as lane programs and
evaluates one operation on every pair of encodings of a small format at once
(`Packed.Program`). The operations with their stages unfolded (`Flat.add` and its siblings) are
for single evaluations and are not read. Division, square root and fused multiply-add use
`Nat.div` and loops, which have no lane step.

One function of the kernel path does not run on lanes of 64 bits: `bitLength` compares its
argument with every power of two at once, on a number of `B * (B + 1)` bits. `bitLength_lane`
replaces it, lane by lane, by the binary search `searchLength` with six steps, which is the bit
length of every number below `2 ^ 64`. The replacement is registered with `@[lane_call]`, so the
lanes whose argument is not below `2 ^ min B 64` are marked as errors and no bound is assumed.

## Tables

`kernel_tables name (size := n) for F := format` declares, for a family `F` whose format has
`n = 2 ^ bitWidth ≤ 256` encodings, the packed tables `name.kernelAdd`, `name.kernelSub` and
`name.kernelMul` of the nearest-even kernel operations on all pairs of encodings (`lane_table`:
each is proved by one run of the staged operation on all lanes), and the rules
`name.toNat_add_nearest`, `name.toNat_sub_nearest` and `name.toNat_mul_nearest`, tagged
`@[kernel_optimize (cost := 4)]`: the encoding of a sum, difference or product of two stored
values is one lane of the table. `float_decide` then uses a lookup, of one shift and one mask,
in place of the operation, in every module that imports the tables.
`Value.toNat_of_table` is the general statement behind the three rules.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics
open FloatLib.Numerics.Kernel (bitLength bitLength_eq searchLength searchLength_eq)

/--
The bit length on lanes: below `2 ^ B` and below `2 ^ 64`, `bitLength B` is the binary search
with six steps.
-/
@[lane_call]
theorem bitLength_lane (B v : Nat) (h : v < 2 ^ min B 64) :
    searchLength 6 v 0 = bitLength B v := by
  have hB : v < 2 ^ B :=
    lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _))
  have hsearch : v < 2 ^ 2 ^ 6 :=
    lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _))
  rw [searchLength_eq 6 v 0 hsearch, bitLength_eq hB, Nat.zero_add]

namespace Flat

/-- On encodings, the flat addition is the staged addition. -/
theorem add_eq_add {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    Flat.add fmt mode x.toNatBits y.toNatBits = KernelPath.add fmt mode x.toNatBits
      y.toNatBits := by
  rw [Flat.add_eq, addShort_eq_spec, add_eq_spec]

/-- On encodings, the flat subtraction is the staged subtraction. -/
theorem sub_eq_sub {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    Flat.sub fmt mode x.toNatBits y.toNatBits = KernelPath.sub fmt mode x.toNatBits
      y.toNatBits := by
  rw [Flat.sub_eq, subShort_eq_spec, sub_eq_spec]

/-- On encodings, the flat multiplication is the staged multiplication. -/
theorem mul_eq_mul {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    Flat.mul fmt mode x.toNatBits y.toNatBits = KernelPath.mul fmt mode x.toNatBits
      y.toNatBits := by
  rw [Flat.mul_eq, mulFast_eq_spec, mul_eq_spec]

end Flat

namespace Value

universe u

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/--
The encoding of a stored value `z` is one lane of a packed table: when the encoding of `z` is
`op` of the encodings of `x` and `y`, `op` agrees on encodings with a function `f`, and `table`
holds `f a b` in lane `a * n + b` for all encodings `a` and `b` of the format.
-/
theorem toNat_of_table {op f : Nat → Nat → Nat} {w n mask table : Nat}
    {x y z : FloatLib.Floats.ExecFloat F} (hz : toNat z = op (toNat x) (toNat y))
    (hop : ∀ x y : Model format, op x.toNatBits y.toNatBits = f x.toNatBits y.toNatBits)
    (hn : n = 2 ^ format.bitWidth) (hmask : mask = 2 ^ w - 1)
    (hlookup : ∀ a b : Fin n, Packed.lane w (a.val * n + b.val) table = f a.val b.val) :
    toNat z =
      Nat.land (Nat.shiftRight table (Nat.mul w (Nat.add (Nat.mul (toNat x) n) (toNat y))))
        mask := by
  subst hn hmask
  rw [hz, toNat_eq x, toNat_eq y, hop, ← toNat_eq x, ← toNat_eq y]
  rw [← hlookup ⟨toNat x, toNat_lt x⟩ ⟨toNat y, toNat_lt y⟩]
  change Nat.land (Nat.shiftRight table (Nat.mul w _)) (Nat.sub (Packed.pow2 w) 1) = _
  rw [Packed.pow2_eq]
  rfl

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
