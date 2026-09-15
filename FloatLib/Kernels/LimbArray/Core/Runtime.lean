/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Init.Data.UInt.Log2

/-!
# Limb arrays: representation and field access

A `LimbArray` stores a natural number as a little-endian array of 32-bit limbs: limb `i` carries
weight `2^(32 i)`, and reading beyond the stored limbs yields zero, so an array denotes the same
number after zero limbs are appended. The value of an array is `toNat`; `Core.Proof` relates the
accessors to this value, and the arithmetic and shift modules provide their own value theorems.

Using `UInt32` limbs lets each limb product, plus an accumulator limb and a carry, fit in a
`UInt64`: `(2^32 - 1)^2 + 2 * (2^32 - 1) = 2^64 - 1`. Array updates can also reuse storage when
the array is uniquely referenced.

This module defines the representation and the non-arithmetic accessors: reading bits and 32-bit
windows, masking to a bit count, resizing, comparing, and locating the leading set bit. Each loop
is structural recursion over a limb count so its invariant can be stated by induction. The
arithmetic kernels live in `Arithmetic.Runtime` and the shifts in `Shift.Runtime`.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- A natural number stored as little-endian 32-bit limbs. -/
structure LimbArray where
  /-- Little-endian limbs; limb `i` has weight `2^(32 i)`. -/
  limbs : Array UInt32
  deriving DecidableEq, Repr

namespace LimbArray

/-- The limb radix `2^32`. -/
abbrev radix : Nat := 4294967296

/-- Number of stored limbs. -/
@[inline] def size (v : LimbArray) : Nat :=
  v.limbs.size

/-- Limb `i`, or zero beyond the stored limbs. -/
@[inline] def limb (v : LimbArray) (i : Nat) : UInt32 :=
  v.limbs.getD i 0

/--
Value of the `count` limbs starting at index `start`, in units of `2^(32 start)`.

The recursion places the first limb below the remaining segment, which gives the arithmetic
loops a common induction invariant.
-/
def segment (v : LimbArray) (start : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => (v.limb start).toNat + radix * segment v (start + 1) count

/-- The natural number denoted by a limb array. -/
def toNat (v : LimbArray) : Nat :=
  segment v 0 v.size

/-- Horner evaluation from the most significant of `count` limbs down to limb zero. -/
def hornerFrom (v : LimbArray) : Nat → Nat → Nat
  | 0, acc => acc
  | count + 1, acc => hornerFrom v count (acc * radix + (v.limb count).toNat)

/--
Executable evaluation of `toNat`.

`Core.Proof.toNat_eq_toNatImpl` registers this tail-recursive Horner loop as the compiled form of
`toNat`, whose front recursion is convenient for proofs but not tail recursive.
-/
def toNatImpl (v : LimbArray) : Nat :=
  hornerFrom v v.size 0

/-- Append the `count` low base-`2^32` digits of `n` to an accumulator array. -/
def ofNatLoop : Nat → Nat → Array UInt32 → Array UInt32
  | 0, _, acc => acc
  | count + 1, n, acc => ofNatLoop count (n >>> 32) (acc.push (UInt32.ofNat n))

/-- The `count`-limb array holding `n` modulo `2^(32 count)`. -/
def ofNat (n count : Nat) : LimbArray :=
  ⟨ofNatLoop count n (Array.emptyWithCapacity count)⟩

/-- The `count`-limb array holding zero. -/
def zero (count : Nat) : LimbArray :=
  ⟨Array.replicate count 0⟩

/-- One more than the index of the highest nonzero limb below `count`, or zero if there is none. -/
def topLimb (v : LimbArray) : Nat → Nat
  | 0 => 0
  | i + 1 => if v.limb i != 0 then i + 1 else topLimb v i

/-- Whether the array denotes zero. -/
@[inline] def isZero (v : LimbArray) : Bool :=
  topLimb v v.size == 0

/-- Position of the leading set bit; zero for the zero array. -/
def log2 (v : LimbArray) : Nat :=
  match topLimb v v.size with
  | 0 => 0
  | i + 1 => 32 * i + (v.limb i).log2.toNat

/-- Bit `k` of the denoted number. -/
@[inline] def testBit (v : LimbArray) (k : Nat) : Bool :=
  ((v.limb (k / 32) >>> UInt32.ofNat (k % 32)) &&& 1) == 1

/-- The 32-bit window of the denoted number starting at bit `lo`. -/
@[inline] def bitsAt32 (v : LimbArray) (lo : Nat) : UInt32 :=
  let r := lo % 32
  if r == 0 then
    v.limb (lo / 32)
  else
    (v.limb (lo / 32) >>> UInt32.ofNat r) |||
      (v.limb (lo / 32 + 1) <<< UInt32.ofNat (32 - r))

/-- The mask of the low `r` bits of a limb, for `r < 32`. -/
@[inline] def lowMask32 (r : Nat) : UInt32 :=
  ((1 : UInt32) <<< UInt32.ofNat r) - 1

/-- The denoted number modulo `2^k`, keeping the stored limb count. -/
def lowBits (v : LimbArray) (k : Nat) : LimbArray :=
  ⟨v.limbs.mapIdx fun i limb =>
    if i < k / 32 then limb
    else if i == k / 32 then limb &&& lowMask32 (k % 32)
    else 0⟩

/-- The denoted number modulo `2^(32 count)`, stored in exactly `count` limbs. -/
def resize (v : LimbArray) (count : Nat) : LimbArray :=
  ⟨Array.ofFn fun (i : Fin count) => v.limb i⟩

/-- Whether any of the limbs below index `count` is nonzero. -/
def anyLimbBelow (v : LimbArray) : Nat → Bool
  | 0 => false
  | i + 1 => v.limb i != 0 || anyLimbBelow v i

/-- Whether any bit below position `k` is set. -/
@[inline] def anyBelow (v : LimbArray) (k : Nat) : Bool :=
  anyLimbBelow v (k / 32) || (v.limb (k / 32) &&& lowMask32 (k % 32)) != 0

/-- Set the low bit when `sticky` holds; an empty array remains empty. -/
@[inline] def orLowBit (v : LimbArray) (sticky : Bool) : LimbArray :=
  if sticky then ⟨v.limbs.setIfInBounds 0 (v.limb 0 ||| 1)⟩ else v

/-- Compare the limbs below index `count`, most significant first. -/
def compareFrom (a b : LimbArray) : Nat → Ordering
  | 0 => .eq
  | i + 1 =>
      if a.limb i < b.limb i then .lt
      else if b.limb i < a.limb i then .gt
      else compareFrom a b i

/-- Compare the denoted numbers. -/
@[inline] def compare (a b : LimbArray) : Ordering :=
  compareFrom a b (max a.size b.size)

end LimbArray

end FloatLib.Numerics
