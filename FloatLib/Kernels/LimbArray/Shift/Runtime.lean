/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.LimbArray.Arithmetic.Runtime

/-!
# Limb arrays: shifts and nearest-even rounding

Bit shifts of a `LimbArray` by an arbitrary count, with optional nearest-even rounding.
A shift by `k` bits moves whole limbs by `k / 32` and then combines
adjacent limbs to shift by the remaining `k % 32` bits; `Array.ofFn` builds each result limb from
at most two source limbs.

`roundShiftRightEven` reads the guard bit and the sticky bits directly from the source array and
increments the shifted quotient with one carry-propagating `addAt`; it never forms the halfway
value `2^(shift - 1)` that the arbitrary-precision rounder compares against. `Shift.Proof` proves
that it agrees with `Numerics.roundShiftRightEven`.
-/

@[expose] public section

namespace FloatLib.Numerics.LimbArray

/-- Result limb `i` of a left shift by `32 q + r` bits, for `r < 32`. -/
@[inline] def shiftLeftLimb (v : LimbArray) (q r i : Nat) : UInt32 :=
  if i < q then
    0
  else
    let j := i - q
    let high := v.limb j <<< UInt32.ofNat r
    if r == 0 || j == 0 then
      high
    else
      high ||| (v.limb (j - 1) >>> UInt32.ofNat (32 - r))

/-- The value shifted left by `k` bits, in `size + k / 32 + 1` limbs. -/
def shiftLeft (v : LimbArray) (k : Nat) : LimbArray :=
  ⟨Array.ofFn fun (i : Fin (v.size + k / 32 + 1)) => shiftLeftLimb v (k / 32) (k % 32) i⟩

/-- Result limb `i` of a right shift by `32 q + r` bits, for `r < 32`. -/
@[inline] def shiftRightLimb (v : LimbArray) (q r i : Nat) : UInt32 :=
  let low := v.limb (i + q) >>> UInt32.ofNat r
  if r == 0 then
    low
  else
    low ||| (v.limb (i + q + 1) <<< UInt32.ofNat (32 - r))

/-- The value shifted right by `k` bits, keeping the stored limb count. -/
def shiftRight (v : LimbArray) (k : Nat) : LimbArray :=
  ⟨Array.ofFn fun (i : Fin v.size) => shiftRightLimb v (k / 32) (k % 32) i⟩

/--
The value divided by `2^shift`, rounded to nearest with ties to even.

The guard bit is bit `shift - 1`, the sticky bits are those below it, and the quotient is odd
exactly when bit `shift` is set. The quotient is incremented when the guard bit is set and either
a sticky bit or the quotient's low bit is set. A zero shift returns the array unchanged.
-/
def roundShiftRightEven (v : LimbArray) (shift : Nat) : LimbArray :=
  if shift == 0 then
    v
  else
    let quotient := shiftRight v shift
    if v.testBit (shift - 1) && (v.anyBelow (shift - 1) || v.testBit shift) then
      addAt quotient 0 1
    else
      quotient

end FloatLib.Numerics.LimbArray
