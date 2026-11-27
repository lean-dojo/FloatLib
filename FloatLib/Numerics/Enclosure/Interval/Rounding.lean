/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.BinaryGrid
public import FloatLib.Numerics.Kernel.Log2

/-!
# Outward rounding of rational intervals to binary grids

Exact rational interval arithmetic never rounds, so its denominators grow with every operation.
The roundings here keep them short. Each moves the lower endpoint of an interval down and the
upper endpoint up to a multiple of a power of two, so the result contains the input interval.

`dyadicDown e q` and `dyadicUp e q` are the multiples of `2 ^ (-e)` just below and just above
`q`, for an exponent `e` of either sign. The three interval roundings differ only in how they
choose `e` for an endpoint `q`:

* `dyadicHull bits` takes `e = bits`, the fixed grid of spacing `2 ^ (-bits)`.
* `relativeHull bits` takes `e = relativeExponent bits q`, so that the grid follows the
  magnitude of `q` and the rounded endpoint has about `bits` significant bits.
* `quotientHull bits` takes `e = gridBits bits q`: `bits` fractional bits, plus one for each bit
  by which the denominator of `q` is longer than its numerator. That is `bits` for `|q| ≥ 1`
  and more for small `|q|`, so a small reciprocal such as `1 / 10 ^ 30` keeps its leading bits,
  where the fixed grid of 8 bits rounds it to `[0, 1 / 256]`.

`RoundingProof` gives each rounding as an `OutwardRounding ℚ ℚ`, proves that the rounded
intervals contain every real member of the input, and states the endpoints with floors and
ceilings.

## Evaluation in Lean's kernel

The definitions are written with the kernel functions of `FloatLib.Numerics.Kernel`, as those of
`BinaryGrid` are. For `e ≥ 0` the rounding is the grid enclosure `BinaryGrid.enclose e q`, one
floor division of the shifted numerator, read back with `BinaryGrid.toRat`. For `e < 0` it is one
floor or ceiling division of the numerator by the shifted denominator. The exponents use the bit
length `Kernel.size` and `Kernel.log2`, which the kernel computes in a few operations for a
number of any size, while it unfolds `Nat.log2` once per binary digit. Compiled code runs core's
operations in place of the kernel functions.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

open FloatLib.Numerics.Kernel

/--
The largest multiple of `2 ^ (-e)` that is at most `q`, for an exponent `e` of either sign:
`⌊q * 2 ^ e⌋ / 2 ^ e` (`dyadicDown_def`). For `e ≥ 0` it is the lower end of the grid enclosure
`BinaryGrid.enclose e q`.
-/
def dyadicDown (e : ℤ) (q : ℚ) : ℚ :=
  Bool.casesOn (motive := fun _ => ℚ) (Int.blt' e (Int.ofNat 0))
    (BinaryGrid.toRat (Z.toNat e) (BinaryGrid.enclose (Z.toNat e) q).lo)
    ((fun k => Q.mk (Z.shiftLeft (Z.floorDiv q.num (Nat.shiftLeft q.den k)) k) 1)
      (Z.toNat (Z.neg e)))

/--
The smallest multiple of `2 ^ (-e)` that is at least `q`, for an exponent `e` of either sign:
`⌈q * 2 ^ e⌉ / 2 ^ e` (`dyadicUp_def`). For `e ≥ 0` it is the upper end of the grid enclosure
`BinaryGrid.enclose e q`.
-/
def dyadicUp (e : ℤ) (q : ℚ) : ℚ :=
  Bool.casesOn (motive := fun _ => ℚ) (Int.blt' e (Int.ofNat 0))
    (BinaryGrid.toRat (Z.toNat e) (BinaryGrid.enclose (Z.toNat e) q).hi)
    ((fun k => Q.mk (Z.shiftLeft (Z.ceilDiv q.num (Nat.shiftLeft q.den k)) k) 1)
      (Z.toNat (Z.neg e)))

/--
`I` with its lower endpoint rounded down and its upper endpoint rounded up to the grid of spacing
`2 ^ (-bits)`. The endpoints are `⌊I.lo * 2 ^ bits⌋ / 2 ^ bits` and `⌈I.hi * 2 ^ bits⌉ / 2 ^ bits`
(`dyadicHull_lo`, `dyadicHull_hi`).
-/
def dyadicHull (bits : ℕ) (I : Interval ℚ) : Interval ℚ :=
  ⟨dyadicDown (Int.ofNat bits) I.lo, dyadicUp (Int.ofNat bits) I.hi⟩

/--
The exponent with which `relativeHull bits` rounds `q`: `bits - ⌊log₂ |num q|⌋ + ⌊log₂ (den q)⌋`
(`relativeExponent_def`). It is chosen so that the rounded `q` keeps about `bits` significant
bits, whatever the size of `q`.
-/
def relativeExponent (bits : ℕ) (q : ℚ) : ℤ :=
  Z.add (Z.subNat bits (Kernel.log2 (Z.natAbs q.num))) (Int.ofNat (Kernel.log2 q.den))

/-- `q` rounded down to a multiple of `2 ^ (-relativeExponent bits q)`. -/
def roundDownRel (bits : ℕ) (q : ℚ) : ℚ :=
  dyadicDown (relativeExponent bits q) q

/-- `q` rounded up to a multiple of `2 ^ (-relativeExponent bits q)`. -/
def roundUpRel (bits : ℕ) (q : ℚ) : ℚ :=
  dyadicUp (relativeExponent bits q) q

/-- The interval with both endpoints rounded outward to about `bits` significant bits. -/
def relativeHull (bits : ℕ) (I : Interval ℚ) : Interval ℚ :=
  ⟨roundDownRel bits I.lo, roundUpRel bits I.hi⟩

/--
The fractional bits of the grid on which `quotientHull bits` rounds the endpoint `q`: `bits`,
plus the bit length of the denominator of `q` less that of its numerator when this is positive
(`gridBits_def`).
-/
def gridBits (bits : ℕ) (q : ℚ) : ℕ :=
  Nat.add bits (Nat.sub (Kernel.size q.den) (Kernel.size (Z.natAbs q.num)))

/--
Both endpoints of `I` rounded outward, each endpoint `q` on the grid of spacing
`2 ^ (-gridBits bits q)` (`quotientHull_lo`, `quotientHull_hi`).
-/
def quotientHull (bits : ℕ) (I : Interval ℚ) : Interval ℚ :=
  ⟨dyadicDown (Int.ofNat (gridBits bits I.lo)) I.lo,
    dyadicUp (Int.ofNat (gridBits bits I.hi)) I.hi⟩

end FloatLib.Numerics.Interval
