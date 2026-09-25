/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.LimbArray.Core.Runtime

/-!
# Limb arrays: addition, subtraction, and multiplication

The carry-propagating loops of multiple-precision integer arithmetic over `LimbArray`. Each loop
recurses on the number of limbs still to process and writes its result with
`Array.setIfInBounds`. The 32-bit limbs leave room for the addition and multiplication
intermediates in `UInt64`.

* `carryLoop` adds one word at a limb position and propagates the carry upward. It is the
  primitive behind `addWordAt`, `addAt`, and the increment used by rounding.
* `add` and `sub` are the schoolbook sum and difference with an incoming carry or borrow; `sub`
  assumes its result is nonnegative and the incoming borrow is at most one.
* `mul` is the schoolbook product; each row adds one limb of the left operand times the right
  operand at the row's offset.

`Arithmetic.Proof` states each kernel's effect on `toNat`, including the required capacity,
borrow, and accumulator invariants.

For the row-accumulation multiplication algorithm, see Richard P. Brent and Paul Zimmermann,
*Modern Computer Arithmetic* (2010), §1.3.1, Algorithm 1.2 (`BasecaseMultiply`).
-/

@[expose] public section

namespace FloatLib.Numerics.LimbArray

/-! ## Carry propagation -/

/--
Add `carry` at limb `index` and propagate upward through `count` limbs.

The loop stops as soon as the carry vanishes, so the common case touches one limb.
-/
def carryLoop : Nat → Nat → UInt32 → Array UInt32 → Array UInt32
  | 0, _, _, out => out
  | count + 1, index, carry, out =>
      if carry == 0 then
        out
      else
        let sum : UInt64 := (out.getD index 0).toUInt64 + carry.toUInt64
        carryLoop count (index + 1) (sum >>> 32).toUInt32 (out.setIfInBounds index sum.toUInt32)

/-- Add the word `w` at limb `index`, discarding any carry beyond the stored array. -/
@[inline] def addWordAt (v : LimbArray) (index : Nat) (w : UInt32) : LimbArray :=
  ⟨carryLoop (v.size - index) index w v.limbs⟩

/--
Add `w * 2^k` to the array.

The word is split at the limb boundary containing bit `k`; both halves are added with carry
propagation. The result is meaningful when the sum still fits the stored limbs.
-/
def addAt (v : LimbArray) (k : Nat) (w : UInt32) : LimbArray :=
  let shifted : UInt64 := w.toUInt64 <<< UInt64.ofNat (k % 32)
  addWordAt (addWordAt v (k / 32) shifted.toUInt32) (k / 32 + 1) (shifted >>> 32).toUInt32

/-! ## Addition and subtraction -/

/-- Add limbs `index`, `index + 1`, ... of two arrays into `out`, then store the final carry. -/
def addLoop (a b : LimbArray) : Nat → Nat → UInt32 → Array UInt32 → Array UInt32
  | 0, index, carry, out => out.setIfInBounds index carry
  | count + 1, index, carry, out =>
      let sum : UInt64 := (a.limb index).toUInt64 + (b.limb index).toUInt64 + carry.toUInt64
      addLoop a b count (index + 1) (sum >>> 32).toUInt32 (out.setIfInBounds index sum.toUInt32)

/-- The sum of two arrays and an incoming carry, in one limb more than the wider operand. -/
def add (a b : LimbArray) (carry : UInt32 := 0) : LimbArray :=
  let count := max a.size b.size
  ⟨addLoop a b count 0 carry (Array.replicate (count + 1) 0)⟩

/-- Subtract limbs `index`, `index + 1`, ... of `b` and a borrow from those of `a` into `out`. -/
def subLoop (a b : LimbArray) : Nat → Nat → UInt32 → Array UInt32 → Array UInt32
  | 0, _, _, out => out
  | count + 1, index, borrow, out =>
      let difference : UInt64 :=
        (a.limb index).toUInt64 + 4294967296 - (b.limb index).toUInt64 - borrow.toUInt64
      subLoop a b count (index + 1) (if difference < 4294967296 then 1 else 0)
        (out.setIfInBounds index difference.toUInt32)

/--
The difference `a - b - borrow`, in as many limbs as the wider operand.

The result is exact when `borrow ≤ 1` and `b + borrow ≤ a`; `Arithmetic.Proof.toNat_sub`
states that contract.
-/
def sub (a b : LimbArray) (borrow : UInt32 := 0) : LimbArray :=
  let count := max a.size b.size
  ⟨subLoop a b count 0 borrow (Array.replicate count 0)⟩

/-! ## Multiplication -/

/--
Add `m` times `count` limbs of `b`, starting at limb `j`, into `out` at offset `offset + j`.
Store the final carry at `offset + j + count`; that slot must initially be zero.

Every intermediate `m * b_j + out_(offset + j) + carry` is below `2^64`.
-/
def mulRow (b : LimbArray) (m : UInt32) (offset : Nat) :
    Nat → Nat → UInt32 → Array UInt32 → Array UInt32
  | 0, j, carry, out => out.setIfInBounds (offset + j) carry
  | count + 1, j, carry, out =>
      let term : UInt64 :=
        m.toUInt64 * (b.limb j).toUInt64 + (out.getD (offset + j) 0).toUInt64 + carry.toUInt64
      mulRow b m offset count (j + 1) (term >>> 32).toUInt32
        (out.setIfInBounds (offset + j) term.toUInt32)

/-- Accumulate `count` rows, starting with row `i`, each contributing `a_i * b * 2^(32 i)`. -/
def mulRows (a b : LimbArray) : Nat → Nat → Array UInt32 → Array UInt32
  | 0, _, out => out
  | count + 1, i, out => mulRows a b count (i + 1) (mulRow b (a.limb i) i b.size 0 0 out)

/-- The schoolbook product, in `a.size + b.size` limbs. -/
def mul (a b : LimbArray) : LimbArray :=
  ⟨mulRows a b a.size 0 (Array.replicate (a.size + b.size) 0)⟩

end FloatLib.Numerics.LimbArray
