/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Core.Runtime
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Native and arbitrary-precision integer square-root runtime

Bounded integer square root uses an overflow-free average and Newton iteration. In compiled
code, `sqrtChecked` replaces it with a floating-point candidate checked by exact squares. Their
`Nat.sqrt` refinements are proved in `IntegerSquareRoot.Proof`.

Larger inputs use a checked Newton candidate with increasing precision. The refinement follows
CPython 3.13's `Modules/mathmodule.c`, "Integer square root". A final square certificate supplies
the root and remainder, and a rejected candidate falls back to full-precision iteration.

The full-precision integer Newton iteration is Algorithm 1.13 (`SqrtInt`) in Richard P. Brent and
Paul Zimmermann, *Modern Computer Arithmetic* (2010), §1.5.1.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.IntegerSquareRoot

/--
Floor of the average of two native words, without overflowing their sum.

The low-bit conjunction supplies the carry exactly when both operands are odd.
-/
@[inline] def average (left right : UInt64) : UInt64 :=
  (left >>> 1) + (right >>> 1) + (left &&& right &&& 1)

/--
Newton iteration starting from an upper bound on the floor square root.

The result is the floor root only when `Nat.sqrt value.toNat ≤ guess.toNat`. An undersized guess
can come back unchanged, as in `sqrtIter 16 1 = 1`. The `sqrt` wrapper supplies a valid initial
bound.
-/
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
    let shift := (log2Word value).toNat / 2 + 1
    sqrtIter value ((1 : UInt64) <<< UInt64.ofNat shift)

/-- Whether `guess` is the floor square root of `value`, decided in word arithmetic that cannot
overflow. -/
@[inline] def isFloorRoot (value guess : UInt64) : Bool :=
  guess < 0x100000000 && guess * guess ≤ value &&
    (guess == 0xffffffff || value < (guess + 1) * (guess + 1))

/--
`sqrt` through a floating-point candidate. The hardware square root of the rounded value proposes
the root, and `isFloorRoot` accepts it or a neighbour only after an exact square check, so no
property of floating-point arithmetic is assumed. Rejected candidates run `sqrt`.
`IntegerSquareRoot.Compiler` installs this as the compiled implementation of `sqrt`.
-/
@[inline] def sqrtChecked (value : UInt64) : UInt64 :=
  let guess := (Float.sqrt value.toFloat).toUInt64
  if isFloorRoot value guess then guess
  else if isFloorRoot value (guess - 1) then guess - 1
  else if isFloorRoot value (guess + 1) then guess + 1
  else sqrt value

/--
Approximate a square root from a leading native-word seed and increasing-precision refinements.

The intended `precision` is `value.log2 / 2`. The recursive call retains approximately half the
root bits, and each return performs one division at the next precision. `checkRoot?` validates
the final candidate, so no correctness assumption on the seed or refinement enters `sqrtRem`.
-/
def approxRoot (value precision : Nat) : Nat :=
  if _hsmall : precision < 32 then
    (sqrt (UInt64.ofNat value)).toNat
  else
    let retained := precision / 2
    let shift := precision - retained
    let root := approxRoot (value >>> (2 * shift)) retained
    (root <<< (shift - 1)) + (value >>> (shift + 1)) / root
termination_by precision
decreasing_by omega

/--
Check an integer-root candidate, allowing correction by one.

Only one square is computed. In the lower branch the remainder bound is equivalent to
`value < (guess + 1)²`, and in the upper branch `(guess - 1)² = guess² - (2 * guess - 1)`.
Every accepted pair is the floor square root with its remainder.
-/
def checkRoot? (value guess : Nat) : Option (Nat × Nat) :=
  let square := guess * guess
  if square ≤ value then
    let remainder := value - square
    if remainder ≤ guess + guess then some (guess, remainder) else none
  else
    let predecessorSquare := square - (guess + guess - 1)
    if predecessorSquare ≤ value then
      some (guess - 1, value - predecessorSquare)
    else
      none

/--
Floor square root and exact remainder, with checked increasing-precision Newton as a candidate.

The fallback spells out `Nat.sqrt.iter` instead of calling `Nat.sqrt`, which keeps the global
compiler replacement of `Nat.sqrt` by `sqrtNat` acyclic.
-/
def sqrtRem (value : Nat) : Nat × Nat :=
  match checkRoot? value (approxRoot value (value.log2 / 2)) with
  | some result => result
  | none =>
      let root :=
        if value ≤ 1 then value else Nat.sqrt.iter value (1 <<< (value.log2 / 2 + 1))
      (root, value - root * root)

/--
Use native-word square root below `2^64` and checked increasing-precision Newton above it.

The arbitrary-precision branch computes the remainder anyway while certifying the root, so
callers that need both can call `sqrtRem`.
-/
@[inline] def sqrtNat (value : Nat) : Nat :=
  if _hfit : value < 2 ^ 64 then
    (sqrt (UInt64.ofNat value)).toNat
  else
    (sqrtRem value).1

end FloatLib.Numerics.FixedWord.IntegerSquareRoot
