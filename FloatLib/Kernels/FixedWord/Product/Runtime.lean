/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Core.Runtime

/-!
# Fixed-limb product runtime

Carry-preserving addition and full products operate over one, two, and four native limbs. The
`UInt256` carrier holds the full product of two `UInt128` values, so the product needs no
arbitrary-precision conversion.

`Product.Proof` shows that each returned value and carry reconstruct the natural-number sum or
product.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

universe u

/-- A fixed-width addition result together with its unsigned carry. -/
structure AddResult (α : Type u) where
  /-- Low fixed-width part of the sum. -/
  value : α
  /-- Carry above the payload's highest bit, represented as a native word. -/
  carry : UInt64
  deriving DecidableEq, Repr

/-- Add two native words and retain the unsigned carry. -/
@[inline] def add64 (x y : UInt64) : AddResult UInt64 :=
  let lo := x + y
  ⟨lo, if lo < x then 1 else 0⟩

/-- Add two words and an incoming carry. -/
@[inline] def addCarry64 (x y carry : UInt64) : AddResult UInt64 :=
  let first := add64 x y
  let second := add64 first.value carry
  ⟨second.value, first.carry + second.carry⟩

/-- Add two two-word values. -/
@[inline] def add128 (x y : UInt128) : AddResult UInt128 :=
  let low := addCarry64 x.lo y.lo 0
  let high := addCarry64 x.hi y.hi low.carry
  ⟨⟨high.value, low.value⟩, high.carry⟩

/-- A 256-bit unsigned value represented by four native 64-bit limbs. -/
structure UInt256 where
  /-- Bits 192 through 255. -/
  limb3 : UInt64
  /-- Bits 128 through 191. -/
  limb2 : UInt64
  /-- Bits 64 through 127. -/
  limb1 : UInt64
  /-- Bits 0 through 63. -/
  limb0 : UInt64
  deriving DecidableEq, Repr

namespace UInt256

/-- Embed a two-limb unsigned value in the low half of a four-limb carrier. -/
@[inline] def ofUInt128 (value : UInt128) : UInt256 :=
  ⟨0, 0, value.hi, value.lo⟩

/--
Embed a two-limb value after shifting it left by `shift` bits, for `64 < shift < 128`.

The two-word kernels for formats of at most 128 bits align a `fracWidth + 1`-bit significand by
`fracWidth` or `fracWidth + 1` places, so division, fused multiply-add, and square root share this
one word shuffle. `toNat_ofUInt128ShiftedLeft` gives its value under the stated shift bounds.
Outside them the native shift counts wrap and the result is unspecified.
-/
@[inline] def ofUInt128ShiftedLeft (value : UInt128) (shift : Nat) : UInt256 :=
  let inner := shift - 64
  let complement := 64 - inner
  {
    limb3 := value.hi >>> UInt64.ofNat complement
    limb2 := (value.hi <<< UInt64.ofNat inner) ||| (value.lo >>> UInt64.ofNat complement)
    limb1 := value.lo <<< UInt64.ofNat inner
    limb0 := 0
  }

/-- Return the low two limbs of a four-limb unsigned value. -/
@[inline] def low128 (value : UInt256) : UInt128 :=
  ⟨value.limb1, value.limb0⟩

/-- Mathematical value of a four-limb unsigned integer. -/
def toNat (value : UInt256) : Nat :=
  value.limb0.toNat +
    value.limb1.toNat * 2 ^ 64 +
    value.limb2.toNat * 2 ^ 128 +
    value.limb3.toNat * 2 ^ 192

/-- Position of the most significant set bit, with zero mapped to zero. -/
@[inline] def log2 (value : UInt256) : Nat :=
  if value.limb3 != 0 then
    192 + (log2Word value.limb3).toNat
  else if value.limb2 != 0 then
    128 + (log2Word value.limb2).toNat
  else if value.limb1 != 0 then
    64 + (log2Word value.limb1).toNat
  else
    (log2Word value.limb0).toNat

end UInt256

/-- Add two four-word values. -/
@[inline] def add256 (x y : UInt256) : AddResult UInt256 :=
  let limb0 := addCarry64 x.limb0 y.limb0 0
  let limb1 := addCarry64 x.limb1 y.limb1 limb0.carry
  let limb2 := addCarry64 x.limb2 y.limb2 limb1.carry
  let limb3 := addCarry64 x.limb3 y.limb3 limb2.carry
  ⟨⟨limb3.value, limb2.value, limb1.value, limb0.value⟩, limb3.carry⟩

/--
Full 256-bit product of two two-limb values in native arithmetic.

Four `mul64` products form the schoolbook product. Each output column is reduced with `add64`, and
the resulting carry count is passed to the next column.
-/
@[inline] def mul128 (x y : UInt128) : UInt256 :=
  let p00 := mul64 x.lo y.lo
  let p01 := mul64 x.lo y.hi
  let p10 := mul64 x.hi y.lo
  let p11 := mul64 x.hi y.hi
  let first1 := add64 p00.hi p01.lo
  let second1 := add64 first1.value p10.lo
  let carry1 := first1.carry + second1.carry
  let first2 := add64 p01.hi p10.hi
  let second2 := add64 first2.value p11.lo
  let third2 := add64 second2.value carry1
  let carry2 := first2.carry + second2.carry + third2.carry
  ⟨p11.hi + carry2, third2.value, second1.value, p00.lo⟩

/-! ## Scalar-carry implementations

`AddResult UInt64` boxes its `value` field, and the generated code materializes the record behind
the carry branch, so every `add64` inside a larger kernel allocates. The definitions below repeat
the same column arithmetic with every intermediate sum and carry as a native word. Each is
definitionally equal to the definition it replaces, and `@[csimp]` installs it in compiled code.
-/

/-- `addCarry64` with its intermediate sums and carries kept as native words. -/
@[inline] def Internal.addCarry64 (x y carry : UInt64) : AddResult UInt64 :=
  let first := x + y
  let firstCarry : UInt64 := if first < x then 1 else 0
  let second := first + carry
  let secondCarry : UInt64 := if second < first then 1 else 0
  ⟨second, firstCarry + secondCarry⟩

/-- Compiled code runs `addCarry64` as `Internal.addCarry64`. -/
-- grind: no rule; this equation selects a compiler implementation.
@[csimp] theorem addCarry64_eq_internal : @addCarry64 = @Internal.addCarry64 := rfl

/-- `add128` with its column sums and carries kept as native words. -/
@[inline] def Internal.add128 (x y : UInt128) : AddResult UInt128 :=
  let low := x.lo + y.lo
  let lowCarry : UInt64 := if low < x.lo then 1 else 0
  let lowSum := low + 0
  let lowSumCarry : UInt64 := if lowSum < low then 1 else 0
  let high := x.hi + y.hi
  let highCarry : UInt64 := if high < x.hi then 1 else 0
  let highSum := high + (lowCarry + lowSumCarry)
  let highSumCarry : UInt64 := if highSum < high then 1 else 0
  ⟨⟨highSum, lowSum⟩, highCarry + highSumCarry⟩

/-- Compiled code runs `add128` as `Internal.add128`. -/
-- grind: no rule; this equation selects a compiler implementation.
@[csimp] theorem add128_eq_internal : @add128 = @Internal.add128 := rfl

/-- `add256` with its column sums and carries kept as native words. -/
@[inline] def Internal.add256 (x y : UInt256) : AddResult UInt256 :=
  let s0 := x.limb0 + y.limb0
  let c0a : UInt64 := if s0 < x.limb0 then 1 else 0
  let t0 := s0 + 0
  let c0b : UInt64 := if t0 < s0 then 1 else 0
  let s1 := x.limb1 + y.limb1
  let c1a : UInt64 := if s1 < x.limb1 then 1 else 0
  let t1 := s1 + (c0a + c0b)
  let c1b : UInt64 := if t1 < s1 then 1 else 0
  let s2 := x.limb2 + y.limb2
  let c2a : UInt64 := if s2 < x.limb2 then 1 else 0
  let t2 := s2 + (c1a + c1b)
  let c2b : UInt64 := if t2 < s2 then 1 else 0
  let s3 := x.limb3 + y.limb3
  let c3a : UInt64 := if s3 < x.limb3 then 1 else 0
  let t3 := s3 + (c2a + c2b)
  let c3b : UInt64 := if t3 < s3 then 1 else 0
  ⟨⟨t3, t2, t1, t0⟩, c3a + c3b⟩

/-- Compiled code runs `add256` as `Internal.add256`. -/
-- grind: no rule; this equation selects a compiler implementation.
@[csimp] theorem add256_eq_internal : @add256 = @Internal.add256 := rfl

/-- `mul128` with its column sums and carries kept as native words. -/
@[inline] def Internal.mul128 (x y : UInt128) : UInt256 :=
  let p00 := mul64 x.lo y.lo
  let p01 := mul64 x.lo y.hi
  let p10 := mul64 x.hi y.lo
  let p11 := mul64 x.hi y.hi
  let first1 := p00.hi + p01.lo
  let second1 := first1 + p10.lo
  let carry1 :=
    (if first1 < p00.hi then (1 : UInt64) else 0) +
      (if second1 < first1 then 1 else 0)
  let first2 := p01.hi + p10.hi
  let second2 := first2 + p11.lo
  let third2 := second2 + carry1
  let carry2 :=
    (if first2 < p01.hi then (1 : UInt64) else 0) +
      (if second2 < first2 then 1 else 0) +
      (if third2 < second2 then 1 else 0)
  ⟨p11.hi + carry2, third2, second1, p00.lo⟩

/-- Compiled code runs `mul128` as `Internal.mul128`. -/
-- grind: no rule; this equation selects a compiler implementation.
@[csimp] theorem mul128_eq_internal : @mul128 = @Internal.mul128 := rfl

end FloatLib.Numerics.FixedWord
