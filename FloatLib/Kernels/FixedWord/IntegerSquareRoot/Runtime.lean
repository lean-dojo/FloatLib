/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Native-word integer square-root runtime

Bounded integer square root uses an overflow-free average and Newton iteration. Its `Nat.sqrt`
refinement is isolated in `IntegerSquareRoot.Proof`.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.IntegerSquareRoot

/--
Floor of the average of two native words, without overflowing their sum.

The low-bit conjunction supplies the carry exactly when both operands are odd.
-/
@[inline] def average (left right : UInt64) : UInt64 :=
  (left >>> 1) + (right >>> 1) + (left &&& right &&& 1)

/-- Newton iteration for a native-word integer square root. -/
@[inline] def sqrtIter (value guess : UInt64) : UInt64 :=
  let next := average guess (value / guess)
  if _h : next < guess then
    sqrtIter value next
  else
    guess
termination_by guess.toNat
decreasing_by
  exact UInt64.lt_iff_toNat_lt.mp _h

/-- Integer square root of one native word. -/
@[inline] def sqrt (value : UInt64) : UInt64 :=
  if value ≤ 1 then
    value
  else
    let shift := value.log2.toNat / 2 + 1
    sqrtIter value ((1 : UInt64) <<< UInt64.ofNat shift)

/--
Use the native-word square root for bounded natural numbers.

The arbitrary-precision branch repeats the logical definition so compiler simplification cannot
recurse through the replacement theorem.
-/
@[inline] def sqrtNat (value : Nat) : Nat :=
  let arbitraryPrecision := fun _ : Unit =>
    if value ≤ 1 then
      value
    else
      Nat.sqrt.iter value (1 <<< (value.log2 / 2 + 1))
  if _hfit : value < 2 ^ 64 then
    (sqrt (UInt64.ofNat value)).toNat
  else
    arbitraryPrecision ()

end FloatLib.Numerics.FixedWord.IntegerSquareRoot
