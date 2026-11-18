/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Frac

/-!
# Dyadic numbers for Lean's kernel

A `Dyad` is three naturals `plus`, `minus`, `scale` and stands for the rational
`(plus - minus) / 2 ^ scale` (`toRat`). It is a `Frac` whose denominator is a power of two, kept
as the exponent: a sum aligns the two numerators with shifts, a product multiplies the numerators
and adds the scales, and rounding to a coarser scale is one shift. No operation computes a gcd or
a division, and none distinguishes cases on a sign, so each is a few of the `Nat` functions that
the kernel computes with GMP.

A number `m * 2 ^ e` with `e ≥ 0` is stored with the factor in the numerator (`ofScaled`).

Rounding comes in three forms, each downward and upward:

* `dropDown k`, `dropUp k` remove the lowest `k` bits of the numerator;
* `roundDown p`, `roundUp p` round to a multiple of `2 ^ (-p)`, and return the number itself when
  its scale is at most `p`;
* `trimDown bits`, `trimUp bits` keep the leading `bits` bits of the numerator, as a
  floating-point format with that precision would.

The theorems are in `FloatLib.Numerics.Kernel.DyadProof`. They hold for all values, normal
numerator or not.

## Main definitions

* `Dyad.toRat`, `Dyad.toFrac`, `Dyad.ofNat`, `Dyad.ofInt`, `Dyad.ofSigned`, `Dyad.ofScaled`.
* `add`, `sub`, `neg`, `mul`, `mulPow2`, `divPow2`, `norm`.
* `le`, `lt`, `beq`, `isNeg`: comparisons as Booleans.
* `dropDown`, `dropUp`, `roundDown`, `roundUp`, `trimDown`, `trimUp`.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/--
The dyadic number `(plus - minus) / 2 ^ scale`, kept as three naturals so that Lean's kernel
computes on it natively.
-/
structure Dyad where
  /-- The part of the numerator that counts positively. -/
  plus : Nat
  /-- The part of the numerator that counts negatively. -/
  minus : Nat
  /-- The exponent of the denominator `2 ^ scale`. -/
  scale : Nat
  deriving DecidableEq, Repr

namespace Dyad

/-- The numerator, as a pair. -/
def num (x : Dyad) : Signed := ⟨x.plus, x.minus⟩

/-- The same number as a fraction with the denominator `2 ^ scale`. -/
def toFrac (x : Dyad) : Frac :=
  ⟨x.plus, x.minus, Nat.shiftLeft 1 x.scale, Frac.shiftLeft_pos Nat.zero_lt_one x.scale⟩

/-- The rational number `(plus - minus) / 2 ^ scale`. -/
def toRat (x : Dyad) : Rat := x.toFrac.toRat

/-- The dyadic number of a natural number. -/
def ofNat (n : Nat) : Dyad := ⟨n, 0, 0⟩

/-- The dyadic number of an integer given as a pair. -/
def ofSigned (z : Signed) : Dyad := ⟨z.plus, z.minus, 0⟩

/-- The dyadic number of an integer. -/
def ofInt (z : Int) : Dyad :=
  Int.casesOn (motive := fun _ => Dyad) z (fun n => ⟨n, 0, 0⟩) (fun n => ⟨0, Nat.succ n, 0⟩)

/--
The dyadic number `z * 2 ^ e` of an integer significand and an integer exponent. A positive
exponent goes into the numerator.
-/
def ofScaled (z e : Int) : Dyad :=
  Int.casesOn (motive := fun _ => Dyad) e
    (fun k => Int.casesOn (motive := fun _ => Dyad) z (fun n => ⟨Nat.shiftLeft n k, 0, 0⟩)
      (fun n => ⟨0, Nat.shiftLeft (Nat.succ n) k, 0⟩))
    (fun k => Int.casesOn (motive := fun _ => Dyad) z (fun n => ⟨n, 0, Nat.succ k⟩)
      (fun n => ⟨0, Nat.succ n, Nat.succ k⟩))

/-- The same number with a normal numerator: the smaller part is subtracted from both. -/
def norm (x : Dyad) : Dyad := ⟨Nat.sub x.plus x.minus, Nat.sub x.minus x.plus, x.scale⟩

/--
The sum, with a normal numerator. The numerator of the number with the smaller scale is shifted
left by the difference of the scales, and the result has the larger scale.
-/
def add (x y : Dyad) : Dyad :=
  (fun s t =>
    (fun p m => (⟨Nat.sub p m, Nat.sub m p, Nat.add x.scale s⟩ : Dyad))
      (Nat.add (Nat.shiftLeft x.plus s) (Nat.shiftLeft y.plus t))
      (Nat.add (Nat.shiftLeft x.minus s) (Nat.shiftLeft y.minus t)))
    (Nat.sub y.scale x.scale) (Nat.sub x.scale y.scale)

/-- The difference, with a normal numerator. -/
def sub (x y : Dyad) : Dyad :=
  (fun s t =>
    (fun p m => (⟨Nat.sub p m, Nat.sub m p, Nat.add x.scale s⟩ : Dyad))
      (Nat.add (Nat.shiftLeft x.plus s) (Nat.shiftLeft y.minus t))
      (Nat.add (Nat.shiftLeft x.minus s) (Nat.shiftLeft y.plus t)))
    (Nat.sub y.scale x.scale) (Nat.sub x.scale y.scale)

/-- The negation: the two parts of the numerator change places. -/
def neg (x : Dyad) : Dyad := ⟨x.minus, x.plus, x.scale⟩

/-- The product: the numerators are multiplied and the scales added. Nothing is rounded. -/
def mul (x y : Dyad) : Dyad :=
  ⟨Nat.add (Nat.mul x.plus y.plus) (Nat.mul x.minus y.minus),
    Nat.add (Nat.mul x.plus y.minus) (Nat.mul x.minus y.plus), Nat.add x.scale y.scale⟩

/-- `x * 2 ^ k`: the scale goes down by `k`, and what it cannot give is shifted into the
numerator. -/
def mulPow2 (x : Dyad) (k : Nat) : Dyad :=
  ⟨Nat.shiftLeft x.plus (Nat.sub k x.scale), Nat.shiftLeft x.minus (Nat.sub k x.scale),
    Nat.sub x.scale k⟩

/-- `x / 2 ^ k`. -/
def divPow2 (x : Dyad) (k : Nat) : Dyad := ⟨x.plus, x.minus, Nat.add x.scale k⟩

/-- Whether `x ≤ y`: the numerators are compared after alignment. -/
def le (x y : Dyad) : Bool :=
  (fun s t =>
    Nat.ble (Nat.add (Nat.shiftLeft x.plus s) (Nat.shiftLeft y.minus t))
      (Nat.add (Nat.shiftLeft y.plus t) (Nat.shiftLeft x.minus s)))
    (Nat.sub y.scale x.scale) (Nat.sub x.scale y.scale)

/-- Whether `x < y`. -/
def lt (x y : Dyad) : Bool :=
  (fun s t =>
    Nat.ble (Nat.succ (Nat.add (Nat.shiftLeft x.plus s) (Nat.shiftLeft y.minus t)))
      (Nat.add (Nat.shiftLeft y.plus t) (Nat.shiftLeft x.minus s)))
    (Nat.sub y.scale x.scale) (Nat.sub x.scale y.scale)

/-- Whether `x` and `y` are the same number. -/
def beq (x y : Dyad) : Bool :=
  (fun s t =>
    Nat.beq (Nat.add (Nat.shiftLeft x.plus s) (Nat.shiftLeft y.minus t))
      (Nat.add (Nat.shiftLeft y.plus t) (Nat.shiftLeft x.minus s)))
    (Nat.sub y.scale x.scale) (Nat.sub x.scale y.scale)

/-- Whether `x < 0`. -/
def isNeg (x : Dyad) : Bool := Nat.ble (Nat.succ x.plus) x.minus

/--
The lowest `k` bits of the numerator removed, rounding down: the largest multiple of
`2 ^ k / 2 ^ scale` that is at most `x`. The result has the scale `scale - k`; for `k > scale` the
numerator is shifted back left by the rest.
-/
def dropDown (x : Dyad) (k : Nat) : Dyad :=
  ⟨Nat.shiftLeft (Nat.shiftRight (Nat.sub x.plus x.minus) k) (Nat.sub k x.scale),
    Nat.shiftLeft (Kernel.ceilShift (Nat.sub x.minus x.plus) k) (Nat.sub k x.scale),
    Nat.sub x.scale k⟩

/-- The lowest `k` bits of the numerator removed, rounding up. -/
def dropUp (x : Dyad) (k : Nat) : Dyad :=
  ⟨Nat.shiftLeft (Kernel.ceilShift (Nat.sub x.plus x.minus) k) (Nat.sub k x.scale),
    Nat.shiftLeft (Nat.shiftRight (Nat.sub x.minus x.plus) k) (Nat.sub k x.scale),
    Nat.sub x.scale k⟩

/--
The largest multiple of `2 ^ (-p)` that is at most `x`. A number whose scale is at most `p` is
such a multiple and is returned with a normal numerator.
-/
def roundDown (x : Dyad) (p : Nat) : Dyad := x.dropDown (Nat.sub x.scale p)

/-- The smallest multiple of `2 ^ (-p)` that is at least `x`. -/
def roundUp (x : Dyad) (p : Nat) : Dyad := x.dropUp (Nat.sub x.scale p)

/-- The number of bits of the absolute value of the numerator. -/
def bits (x : Dyad) : Nat :=
  size (Nat.add (Nat.sub x.plus x.minus) (Nat.sub x.minus x.plus))

/--
The numerator cut to its leading `count` bits, rounding down: what rounding toward minus infinity
gives in a floating-point format with `count` bits of precision and no exponent bounds.
-/
def trimDown (x : Dyad) (count : Nat) : Dyad := x.dropDown (Nat.sub x.bits count)

/-- The numerator cut to its leading `count` bits, rounding up. -/
def trimUp (x : Dyad) (count : Nat) : Dyad := x.dropUp (Nat.sub x.bits count)

end Dyad

end FloatLib.Numerics.Kernel
