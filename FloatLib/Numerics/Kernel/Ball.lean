/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Dyad

/-!
# Balls with a dyadic midpoint for Lean's kernel

A `Ball` is four naturals `plus`, `minus`, `rad`, `scale` and stands for the set of numbers within
`rad / 2 ^ scale` of the midpoint `(plus - minus) / 2 ^ scale`. Addition and multiplication
compute the new midpoint exactly. The radius encloses the sums or products of all pairs of
input values. In a product this enclosure can be wider than the range of the exact products.

Nothing is rounded until the caller asks for it:

* `drop k` removes the lowest `k` bits of the midpoint and adds what it moved to the radius;
* `round p` does so down to multiples of `2 ^ (-p)` and returns a ball of scale at most `p`
  unchanged;
* `trim count` keeps the leading `count` bits of the midpoint.

The comparison `le x y` holds when every number of `x` is at most every number of `y`.

`inv x p` encloses the reciprocals of the members of a ball that does not contain zero, which
`apart x` tests, with its two ends rounded outward to multiples of `2 ^ (-p)`. `div x y p` is the
product with that reciprocal.

`FloatLib.Numerics.Kernel.BallProof` proves the enclosures for members in any ordered field.
The binary-grid elementary-function enclosures are in `FloatLib.Numerics.Enclosure.BinaryGrid`.

## Main definitions

* `Ball.mid`, `Ball.radius`, `Ball.lower`, `Ball.upper`: the midpoint, the radius and the two
  ends, as dyadic numbers.
* `Ball.ofDyad`, `Ball.ofNat`, `Ball.ofFrac q p` (a ball of radius `2 ^ (-p)` around a fraction),
  `Ball.ofBounds`.
* `add`, `sub`, `neg`, `mul`, `inv`, `div`, `drop`, `round`, `trim`.
* `le`, `lt`: comparisons of all members, as Booleans; `apart`: zero is not a member.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/--
The numbers within `rad / 2 ^ scale` of `(plus - minus) / 2 ^ scale`, kept as four naturals so
that Lean's kernel computes on them natively.
-/
structure Ball where
  /-- The part of the midpoint's numerator that counts positively. -/
  plus : Nat
  /-- The part of the midpoint's numerator that counts negatively. -/
  minus : Nat
  /-- The radius, in units of `2 ^ (-scale)`. -/
  rad : Nat
  /-- The exponent of the common denominator `2 ^ scale`. -/
  scale : Nat
  deriving DecidableEq, Repr

namespace Ball

/-- The midpoint. -/
def mid (b : Ball) : Dyad := ⟨b.plus, b.minus, b.scale⟩

/-- The radius. -/
def radius (b : Ball) : Dyad := ⟨b.rad, 0, b.scale⟩

/-- The lower end: the midpoint minus the radius. -/
def lower (b : Ball) : Dyad := ⟨b.plus, Nat.add b.minus b.rad, b.scale⟩

/-- The upper end: the midpoint plus the radius. -/
def upper (b : Ball) : Dyad := ⟨Nat.add b.plus b.rad, b.minus, b.scale⟩

/-- The ball of radius zero around a dyadic number. -/
def ofDyad (d : Dyad) : Ball := ⟨d.plus, d.minus, 0, d.scale⟩

/-- The ball of radius zero around a natural number. -/
def ofNat (n : Nat) : Ball := ⟨n, 0, 0, 0⟩

/--
A ball of radius `2 ^ (-p)` that contains the fraction `q`: its midpoint is `q` rounded down to
a multiple of `2 ^ (-p)`.
-/
def ofFrac (q : Frac) (p : Nat) : Ball :=
  (fun z : Signed => (⟨z.plus, z.minus, 1, p⟩ : Ball)) ((q.num.shiftLeft p).floorDiv q.den)

/--
The smallest ball that contains the numbers from `lo` to `hi`: the midpoint `(lo + hi) / 2` and
the radius `(hi - lo) / 2`, at one bit more than the larger scale. For `hi < lo` the radius is
zero.
-/
def ofBounds (lo hi : Dyad) : Ball :=
  (fun s t =>
    (fun p m =>
      (⟨Nat.sub p m, Nat.sub m p,
        Nat.sub (Nat.add (Nat.shiftLeft hi.plus t) (Nat.shiftLeft lo.minus s))
          (Nat.add (Nat.shiftLeft hi.minus t) (Nat.shiftLeft lo.plus s)),
        Nat.succ (Nat.add lo.scale s)⟩ : Ball))
      (Nat.add (Nat.shiftLeft lo.plus s) (Nat.shiftLeft hi.plus t))
      (Nat.add (Nat.shiftLeft lo.minus s) (Nat.shiftLeft hi.minus t)))
    (Nat.sub hi.scale lo.scale) (Nat.sub lo.scale hi.scale)

/-- The sums of the members: the midpoints and the radii are added after alignment. -/
def add (x y : Ball) : Ball :=
  (fun s t =>
    (fun p m =>
      (⟨Nat.sub p m, Nat.sub m p, Nat.add (Nat.shiftLeft x.rad s) (Nat.shiftLeft y.rad t),
        Nat.add x.scale s⟩ : Ball))
      (Nat.add (Nat.shiftLeft x.plus s) (Nat.shiftLeft y.plus t))
      (Nat.add (Nat.shiftLeft x.minus s) (Nat.shiftLeft y.minus t)))
    (Nat.sub y.scale x.scale) (Nat.sub x.scale y.scale)

/-- The negations of the members. -/
def neg (x : Ball) : Ball := ⟨x.minus, x.plus, x.rad, x.scale⟩

/-- The differences of the members. -/
def sub (x y : Ball) : Ball := x.add y.neg

/--
A ball enclosing the products of the members. Its midpoint is the exact product of the
midpoints. For a midpoint with numerator `plus - minus`, the radius calculation bounds the
magnitude of that numerator by `plus + minus`.
-/
def mul (x y : Ball) : Ball :=
  (fun p m =>
    (⟨Nat.sub p m, Nat.sub m p,
      Nat.add (Nat.mul (Nat.add x.plus x.minus) y.rad)
        (Nat.mul (Nat.add (Nat.add y.plus y.minus) y.rad) x.rad),
      Nat.add x.scale y.scale⟩ : Ball))
    (Nat.add (Nat.mul x.plus y.plus) (Nat.mul x.minus y.minus))
    (Nat.add (Nat.mul x.plus y.minus) (Nat.mul x.minus y.plus))

/--
Whether zero is not a member (`apart_iff`): the midpoint is farther from zero than the radius.
-/
def apart (x : Ball) : Bool :=
  Nat.ble (Nat.succ x.rad) (Nat.add (Nat.sub x.plus x.minus) (Nat.sub x.minus x.plus))

/--
The reciprocals of the members of a ball that does not contain zero (`contains_inv`). With `c`
the magnitude of the midpoint's numerator, the magnitudes of the members lie between
`(c - rad) / 2 ^ scale` and `(c + rad) / 2 ^ scale`, so their reciprocals lie between
`2 ^ scale / (c + rad)` and `2 ^ scale / (c - rad)`. These two ends are rounded outward to
multiples of `2 ^ (-p)` by one division each, and the result is the ball between them, of scale
`p + 1`, with the sign of the midpoint. For a ball that contains zero the result means nothing.
-/
def inv (x : Ball) (p : Nat) : Ball :=
  (fun c n =>
    (fun L U =>
      Bool.casesOn (motive := fun _ => Ball) (Nat.ble x.minus x.plus)
        ⟨0, Nat.add L U, Nat.sub U L, Nat.succ p⟩
        ⟨Nat.add L U, 0, Nat.sub U L, Nat.succ p⟩)
      (Nat.div n (Nat.add c x.rad))
      (Kernel.ceilDiv n (Nat.sub c x.rad)))
    (Nat.add (Nat.sub x.plus x.minus) (Nat.sub x.minus x.plus))
    (Nat.shiftLeft 1 (Nat.add x.scale p))

/--
The quotients of the members of `x` by the members of `y`, for `y` apart from zero
(`contains_div`): the product of `x` and the reciprocal of `y` to `p` binary digits.
-/
def div (x y : Ball) (p : Nat) : Ball := x.mul (y.inv p)

/--
The lowest `k` bits of the midpoint removed. The midpoint moves down by at most
`(2 ^ k - 1) / 2 ^ scale`, which the new radius includes: it is
`⌊(rad + 2 * (2 ^ k - 1)) / 2 ^ k⌋` in the new unit, and `rad` itself for `k = 0`.
-/
def drop (x : Ball) (k : Nat) : Ball :=
  ⟨Nat.shiftLeft (Nat.shiftRight (Nat.sub x.plus x.minus) k) (Nat.sub k x.scale),
    Nat.shiftLeft (Kernel.ceilShift (Nat.sub x.minus x.plus) k) (Nat.sub k x.scale),
    Nat.shiftLeft
      (Nat.shiftRight (Nat.add x.rad (Nat.mul 2 (Nat.sub (Nat.shiftLeft 1 k) 1))) k)
      (Nat.sub k x.scale),
    Nat.sub x.scale k⟩

/--
The ball with its midpoint rounded to a multiple of `2 ^ (-p)`. A ball whose scale is at most
`p` is returned with the same members.
-/
def round (x : Ball) (p : Nat) : Ball := x.drop (Nat.sub x.scale p)

/-- The ball with its midpoint cut to its leading `count` bits. -/
def trim (x : Ball) (count : Nat) : Ball := x.drop (Nat.sub x.mid.bits count)

/-- Whether every member of `x` is at most every member of `y`. -/
def le (x y : Ball) : Bool := x.upper.le y.lower

/-- Whether every member of `x` is less than every member of `y`. -/
def lt (x y : Ball) : Bool := x.upper.lt y.lower

end Ball

end FloatLib.Numerics.Kernel
