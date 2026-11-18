/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Ball

/-!
# Complex balls for Lean's kernel

A `CBall` is a pair of real balls, one for the real part and one for the imaginary part, so it
stands for a rectangle of complex numbers. Every operation is a few operations of
`FloatLib.Numerics.Kernel.Ball` on the parts. Sums, differences and products enclose the
corresponding complex results. The midpoints in these operations are computed exactly.
The caller can round the rectangle with `round p` at any precision `p`. Rounding
is outward: `Ball.round` adds what it removes from a midpoint to the radius.

The exponential of an imaginary argument, `exp (i t)` for `t` in a real ball, is here in three
pieces, with the following enclosure guarantees:

* `expISmall x j n p` evaluates the Taylor polynomial of degree `n - 1` by Horner's rule on balls,
  with integer coefficients and one division at the end, and adds the remainder bound
  `(n + 1) / (2 ^ (j * n) * n! * n)` of the series for `|t| ≤ 2 ^ (-j)`. When the ball is not
  within `2 ^ (-j)` of zero, or `n = 0`, it returns the square `[-1, 1] × [-1, 1]`, which contains
  every value of `exp (i t)`.
* `expIWith f x h p` removes the nearest multiple `k` of a quarter turn, given a ball `h` around
  `π / 2`, calls `f` on the rest and multiplies by `i ^ k`, which only exchanges and negates parts.
  `expI x h j n p` is `expIWith` with `expISmall`.
* `expIStep x step tbl j n p` removes the nearest multiple `k` of a step instead, multiplies the
  series of the rest by the entry `tbl k` of a table of `exp (i k step)`, and uses the conjugate
  entry for a negative argument. Its theorem requires `step` to contain a real step `s` and
  every `tbl k` to contain `exp (i * (k * s))`.

`FloatLib.Numerics.Kernel.CBall.Arithmetic` proves the component enclosures over every ordered
field. `CBall.Complex` specializes them to complex numbers, and `CBall.Exponential` proves
the exponential enclosures for real `t`.

## Main definitions

* `Ball.error`, `Ball.widen`, `Ball.within`, `Ball.unit`: a ball around zero, a larger radius, a
  bound on all members, and `[-1, 1]`.
* `CBall.ofReal`, `CBall.ofNat`, `add`, `sub`, `neg`, `conj`, `mul`, `smul` (scaling by a real
  ball), `mulI`, `mulIPow`, `round`.
* `CBall.expITerms`, `expIPoly`, `expIRemainder`, `expISmall`, `quarterTurns`, `expIWith`, `expI`,
  `expIStep`, and `CBall.halfPi`, a ball of 66 bits around `π / 2`.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

namespace Ball

/-- The ball of radius `r / 2 ^ s` around zero. -/
def error (r s : Nat) : Ball := ⟨0, 0, r, s⟩

/-- The ball with `r / 2 ^ s` added to its radius. -/
def widen (x : Ball) (r s : Nat) : Ball := x.add (error r s)

/-- Whether every member is at most `2 ^ (-j)` in absolute value. -/
def within (x : Ball) (j : Nat) : Bool :=
  Bool.and (x.upper.le ⟨1, 0, j⟩) (Dyad.le ⟨0, 1, j⟩ x.lower)

/-- The ball `[-1, 1]`. -/
def unit : Ball := ⟨0, 0, 1, 0⟩

end Ball

/--
The complex numbers whose real part is a member of `re` and whose imaginary part is a member of
`im`.
-/
structure CBall where
  /-- The ball of the real parts. -/
  re : Ball
  /-- The ball of the imaginary parts. -/
  im : Ball
  deriving DecidableEq, Repr

namespace CBall

/-- The complex ball of a real ball: the imaginary part is zero. -/
def ofReal (x : Ball) : CBall := ⟨x, Ball.ofNat 0⟩

/-- The complex ball of radius zero around a natural number. -/
def ofNat (n : Nat) : CBall := ⟨Ball.ofNat n, Ball.ofNat 0⟩

/-- The sums of the members. -/
def add (x y : CBall) : CBall := ⟨x.re.add y.re, x.im.add y.im⟩

/-- The negations of the members. -/
def neg (x : CBall) : CBall := ⟨x.re.neg, x.im.neg⟩

/-- The differences of the members. -/
def sub (x y : CBall) : CBall := x.add y.neg

/-- The complex conjugates of the members. -/
def conj (x : CBall) : CBall := ⟨x.re, x.im.neg⟩

/-- A rectangle enclosing the products `(a + i b) (c + i d) = (a c - b d) + i (a d + b c)`. -/
def mul (x y : CBall) : CBall :=
  ⟨(x.re.mul y.re).sub (x.im.mul y.im), (x.re.mul y.im).add (x.im.mul y.re)⟩

/-- The members scaled by the members of a real ball. -/
def smul (c : Ball) (x : CBall) : CBall := ⟨c.mul x.re, c.mul x.im⟩

/-- The members times `i`: `i (a + i b) = -b + i a`. -/
def mulI (x : CBall) : CBall := ⟨x.im.neg, x.re⟩

/-- The members times `i ^ k`, by the remainder of `k` modulo four. -/
def mulIPow (k : Nat) (x : CBall) : CBall :=
  Nat.casesOn (motive := fun _ => CBall) (Nat.mod k 4) x
    (fun a => Nat.casesOn (motive := fun _ => CBall) a (⟨x.im.neg, x.re⟩ : CBall)
      (fun b => Nat.casesOn (motive := fun _ => CBall) b (⟨x.re.neg, x.im.neg⟩ : CBall)
        (fun _ => (⟨x.im, x.re.neg⟩ : CBall))))

/-- Both parts rounded to multiples of `2 ^ (-p)`, outward. -/
def round (x : CBall) (p : Nat) : CBall := ⟨x.re.round p, x.im.round p⟩

/-- A ball around `π / 2` of radius `2 ^ (-66)` (`CBall.contains_halfPi`, from Mathlib's
twenty decimals of `π`). -/
def halfPi : Ball := ⟨115904311329233965478, 0, 1, 66⟩

/-- The square `[-1, 1] × [-1, 1]`, which contains the unit circle. -/
def box : CBall := ⟨Ball.unit, Ball.unit⟩

/--
Horner's rule for the Taylor polynomial of `exp (i t)` with integer coefficients. For `t` in `x`,
`expITerms x k m` is the pair of the natural number `c = (m + k)! / m!` and a complex ball that
contains `∑ j ≤ k, (i t) ^ j * (m + k)! / (m + j)!`. Nothing is rounded.
-/
def expITerms (x : Ball) : Nat → Nat → Nat × CBall
  | 0, _ => (1, CBall.ofNat 1)
  | k + 1, m =>
    (fun r : Nat × CBall =>
      (fun c : Nat =>
        (c, (⟨(Ball.ofNat c).sub (x.mul r.2.im), x.mul r.2.re⟩ : CBall)))
        (Nat.mul (Nat.succ m) r.1))
      (expITerms x k (Nat.succ m))

/--
A complex ball that contains `∑ j < n, (i t) ^ j / j!` for every `t` in `x`, for `n ≥ 1`: the
integer Horner sum times a reciprocal of `(n - 1)!` to `p` binary digits beyond its size.
-/
def expIPoly (x : Ball) (n p : Nat) : CBall :=
  (fun r : Nat × CBall => smul ((Ball.ofNat r.1).inv (Nat.add p (size r.1))) r.2)
    (expITerms x (Nat.sub n 1) 0)

/--
The remainder bound `(n + 1) / (2 ^ (j * n) * n! * n)` of the series after `n` terms for
`|t| ≤ 2 ^ (-j)`, rounded up to a multiple of `2 ^ (-p)`: the numerator of that multiple.
-/
noncomputable def expIRemainder (j n p : Nat) : Nat :=
  ceilDiv (Nat.shiftLeft (Nat.succ n) p)
    (Nat.mul (Nat.shiftLeft (factorial n) (Nat.mul j n)) n)

/--
`exp (i t)` for every `t` in `x`, to about `p` binary digits when all members of `x` are within
`2 ^ (-j)` of zero: `n` terms of the series and its remainder bound, rounded to `p` digits. For a
ball that is not within `2 ^ (-j)` of zero, and for `n = 0`, the result is `box`.
-/
noncomputable def expISmall (x : Ball) (j n p : Nat) : CBall :=
  Bool.casesOn (motive := fun _ => CBall) (Bool.and (x.within j) (Nat.ble 1 n))
    box
    ((fun (w : CBall) (e : Nat) =>
        (⟨(w.re.widen e p).round p, (w.im.widen e p).round p⟩ : CBall))
      (expIPoly x n p) (expIRemainder j n p))

/--
The multiple of `h` nearest to the midpoint of `x`, as the natural number `k` with
`|mid x| ≈ k * |mid h|`. Zero when the midpoint of `h` is zero.
-/
def quarterTurns (x h : Ball) : Nat :=
  (fun X H => Nat.div (Nat.add (Nat.mul 2 X) H) (Nat.mul 2 H))
    (Nat.shiftLeft (Nat.add (Nat.sub x.plus x.minus) (Nat.sub x.minus x.plus))
      (Nat.sub h.scale x.scale))
    (Nat.shiftLeft (Nat.add (Nat.sub h.plus h.minus) (Nat.sub h.minus h.plus))
      (Nat.sub x.scale h.scale))

/--
Reduce by a multiple of `step`, evaluate the rounded remainder with `f`, and apply the
corresponding positive or negative phase action. Both actions receive the same natural
multiple; `negative` is selected when the midpoint of `x` is negative.
-/
def expIReduce (f : Ball → CBall) (positive negative : Nat → CBall → CBall)
    (x step : Ball) (p : Nat) : CBall :=
  (fun k =>
    Bool.casesOn (motive := fun _ => CBall) (Nat.ble x.minus x.plus)
      (negative k (f ((x.add ((Ball.ofNat k).mul step)).round p)))
      (positive k (f ((x.sub ((Ball.ofNat k).mul step)).round p))))
    (quarterTurns x step)

/--
`exp (i t)` for `t` in `x`, from an evaluator `f` for small arguments and a ball `h` around
`π / 2`: with `k` the nearest number of quarter turns, the rest `x ∓ k h` is rounded to `p`
digits and given to `f`, and the result is multiplied by `i ^ k`, or by `i ^ (3 k)` when the
midpoint of `x` is negative.
-/
def expIWith (f : Ball → CBall) (x h : Ball) (p : Nat) : CBall :=
  expIReduce f mulIPow (fun k => mulIPow (Nat.mul 3 k)) x h p

/--
`exp (i t)` for every `t` in `x`, given a ball `h` around `π / 2`: quarter turns removed, then
`n` terms of the series, valid to about `p` digits when the rest is within `2 ^ (-j)` of zero
(`j = 0` after a reduction by quarter turns).
-/
noncomputable def expI (x h : Ball) (j n p : Nat) : CBall :=
  expIWith (fun r => expISmall r j n p) x h p

/--
`exp (i t)` for `t` in `x` from a table: with `k` the nearest multiple of the step, the series
of the rest `x ∓ k step` times the entry `tbl k`, which is to contain `exp (i k s)` for the step
`s` in `step`, or times its conjugate when the midpoint of `x` is negative. The product is
rounded to `p` digits.
-/
noncomputable def expIStep (x step : Ball) (tbl : Nat → CBall) (j n p : Nat) : CBall :=
  expIReduce (fun r => expISmall r j n p)
    (fun k z => ((tbl k).mul z).round p)
    (fun k z => ((tbl k).conj.mul z).round p) x step p

end CBall

end FloatLib.Numerics.Kernel
