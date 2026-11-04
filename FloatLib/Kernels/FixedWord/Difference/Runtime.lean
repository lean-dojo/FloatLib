/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Core.Runtime

/-!
# Fixed-limb difference runtime

Unsigned two-limb comparison, subtraction, leading-bit discovery, and normalization all use the same
borrow and shift conventions, and we keep them in one place so that the dyadic comparison and
rounding kernels don't grow subtly different copies.

The hot path works on `UInt64` limbs and never converts through `Nat`. `Difference.Proof` proves
their natural-number meanings, along with the preconditions under which wrapping subtraction means
ordinary subtraction.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.UInt128

/-- Compare two two-word unsigned values. -/
@[inline] def less (x y : UInt128) : Bool :=
  x.hi < y.hi || (x.hi == y.hi && x.lo < y.lo)

/--
Three-way comparison of two two-word unsigned values.

Exact dyadic certificates use this comparison on widened products without rebuilding them as
arbitrary-precision naturals.
-/
@[inline] def compare (x y : UInt128) : Ordering :=
  if less x y then
    .lt
  else if less y x then
    .gt
  else
    .eq

/-- Subtract two two-word values with borrow. The result wraps modulo `2^128`. -/
@[inline] def sub (x y : UInt128) : UInt128 :=
  let borrow : UInt64 := if x.lo < y.lo then 1 else 0
  {
    hi := x.hi - y.hi - borrow
    lo := x.lo - y.lo
  }

/-- Position of the most significant set bit, with zero mapped to zero. -/
@[inline] def log2 (value : UInt128) : Nat :=
  if value.hi == 0 then (log2Word value.lo).toNat
  else 64 + (log2Word value.hi).toNat

/--
Shift a two-word value right, returning zero at and beyond the 128-bit carrier width.

The explicit ranges avoid the modulo reduction performed by native machine-word shifts.
-/
@[inline] def shiftRight (value : UInt128) (shift : Nat) : UInt128 :=
  if shift == 0 then
    value
  else if shift < 64 then
    {
      hi := value.hi >>> UInt64.ofNat shift
      lo :=
        (value.lo >>> UInt64.ofNat shift) |||
          (lowBitsWord value.hi (UInt64.ofNat shift) <<<
            UInt64.ofNat (64 - shift))
    }
  else if shift < 128 then
    {
      hi := 0
      lo := value.hi >>> UInt64.ofNat (shift - 64)
    }
  else
    ⟨0, 0⟩

/--
A two-word value with a single bit set, or zero when the index is beyond the 128-bit carrier.

Building the bit inside its own limb keeps fixed-width significands from going through an
arbitrary-precision power before their final mathematical conversion.
-/
@[inline] def singleBit (index : Nat) : UInt128 :=
  if index < 64 then
    ⟨0, (1 : UInt64) <<< UInt64.ofNat index⟩
  else if index < 128 then
    ⟨(1 : UInt64) <<< UInt64.ofNat (index - 64), 0⟩
  else
    ⟨0, 0⟩

/--
Shift a two-word value left, returning zero at and beyond the 128-bit carrier width.

Bits carried above position 127 are discarded, so the result is `value * 2^shift` reduced modulo
`2^128`. `shiftLeft_toNat` gives the exact product when no bit is lost, and `shiftLeft_of_ge`
covers the total branch. The explicit ranges avoid the modulo reduction
performed by native machine-word shifts.
-/
@[inline] def shiftLeft (value : UInt128) (shift : Nat) : UInt128 :=
  if shift == 0 then
    value
  else if shift < 64 then
    {
      hi :=
        (value.hi <<< UInt64.ofNat shift) |||
          (value.lo >>> UInt64.ofNat (64 - shift))
      lo := value.lo <<< UInt64.ofNat shift
    }
  else if shift < 128 then
    {
      hi := value.lo <<< UInt64.ofNat (shift - 64)
      lo := 0
    }
  else
    ⟨0, 0⟩

end FloatLib.Numerics.FixedWord.UInt128
