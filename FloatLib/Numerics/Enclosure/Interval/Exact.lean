/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Basic
public import FloatLib.Numerics.Kernel.QProof

/-!
# Exact operations on rational intervals

These operations take intervals with rational endpoints to intervals with rational endpoints.
Nothing is rounded and nothing fails, so the result is an interval rather than an `Option`. The
four-corner product of `[-1, 2]` and `[3, 4]`, say, is `[-4, 8]`, the least and the greatest of
`-3`, `-4`, `6` and `8`.

Totality has a price outside an operation's contract: the result is still an interval, but it may
not mean anything. `inv [-1, 1]` is `[1, -1]`, which contains no real number at all. The reciprocal
and the quotient need a denominator strictly on one side of zero, `scaleNonneg` needs a
nonnegative factor, and `divAbsLower I δ` needs `0 < δ`. The containment theorems of `ExactProof`
take these conditions as hypotheses. `intersect` represents an empty intersection by reversed
endpoints.

## Main definitions

* `add`, `neg`, `sub`, `mul`, `inv` and `div`: the arithmetic, with four-corner products and
  quotients.
* `abs`, `powNat` and `scaleNonneg`: the ranges of `|x|`, of `x ^ n` and of `q * x` for `0 ≤ q`.
* `absMax` and `divAbsLower`: the largest absolute value on an interval, and a bound for `x / y`
  that only needs `δ ≤ |y|`.
* `hull`: the smallest interval containing both inputs when each has ordered endpoints.
* `intersect`: the intersection, whether or not the inputs overlap.

## Implementation notes

The operations are written with the kernel rational functions of `FloatLib.Numerics.Kernel.Q`, so
Lean's kernel evaluates them with GMP arithmetic, and compiled code runs core's `Rat` operations.
`ExactProof` states each endpoint in ordinary notation (`add_lo`, `mul_hi` and so on) and shows
that the partial operations `add?`, `mul?`, `inv?`, `hull?`, `intersect?` and the others, with
exact rational endpoints (`Internal.rationalOutwardRounding`), return these same intervals
whenever they succeed, so the two forms are one operation.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval.Exact

/-- The sum `[I.lo + J.lo, I.hi + J.hi]`. -/
def add (I J : Interval ℚ) : Interval ℚ :=
  ⟨Kernel.Q.add I.lo J.lo, Kernel.Q.add I.hi J.hi⟩

/-- The negation `[-I.hi, -I.lo]`. -/
def neg (I : Interval ℚ) : Interval ℚ :=
  ⟨Kernel.Q.neg I.hi, Kernel.Q.neg I.lo⟩

/-- The difference `[I.lo - J.hi, I.hi - J.lo]`. -/
def sub (I J : Interval ℚ) : Interval ℚ :=
  ⟨Kernel.Q.sub I.lo J.hi, Kernel.Q.sub I.hi J.lo⟩

/--
The four-corner product: the least and the greatest of the four endpoint products, grouped as
`min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))`, and the same with
`max`.
-/
def mul (I J : Interval ℚ) : Interval ℚ :=
  let p := Kernel.Q.mul I.lo J.lo
  let q := Kernel.Q.mul I.lo J.hi
  let r := Kernel.Q.mul I.hi J.lo
  let s := Kernel.Q.mul I.hi J.hi
  ⟨Kernel.Q.min (Kernel.Q.min p q) (Kernel.Q.min r s),
    Kernel.Q.max (Kernel.Q.max p q) (Kernel.Q.max r s)⟩

/--
The range of `|x|` for `x` in `I`: `I` itself when `0 ≤ I.lo`, the negation when `I.hi ≤ 0`, and
`[0, max (-I.lo) I.hi]` when `I` crosses zero.
-/
def abs (I : Interval ℚ) : Interval ℚ :=
  Bool.casesOn (motive := fun _ => Interval ℚ) (Kernel.Q.le 0 I.lo)
    (Bool.casesOn (motive := fun _ => Interval ℚ) (Kernel.Q.le I.hi 0)
      ⟨0, Kernel.Q.max (Kernel.Q.neg I.lo) I.hi⟩ (neg I))
    I

/--
The range of `x ^ n` for `x` in `I`. The zeroth power is `[1, 1]`, an odd power raises both
endpoints, and an even power raises the endpoints of `abs I`, so it starts at zero when `I`
crosses zero.
-/
def powNat (I : Interval ℚ) (n : ℕ) : Interval ℚ :=
  Bool.casesOn (motive := fun _ => Interval ℚ) (Nat.beq n 0)
    (Bool.casesOn (motive := fun _ => Interval ℚ) (Nat.beq (Nat.mod n 2) 0)
      ⟨Kernel.Q.pow I.lo n, Kernel.Q.pow I.hi n⟩
      (let a := abs I
       ⟨Kernel.Q.pow a.lo n, Kernel.Q.pow a.hi n⟩))
    (point 1)

/--
Scaling by a nonnegative factor `q`, `[q * I.lo, q * I.hi]`. For `0 ≤ q` and an ordered `I` it is
the product with `[q, q]`.
-/
def scaleNonneg (q : ℚ) (I : Interval ℚ) : Interval ℚ :=
  ⟨Kernel.Q.mul q I.lo, Kernel.Q.mul q I.hi⟩

/--
The reciprocal `[I.hi⁻¹, I.lo⁻¹]`. It contains the reciprocal of every member when `I` lies
strictly on one side of zero.
-/
def inv (I : Interval ℚ) : Interval ℚ :=
  ⟨Kernel.Q.inv I.hi, Kernel.Q.inv I.lo⟩

/--
The four-corner quotient, computed as the product of `I` with the reciprocal of `J`. It contains
`x / y` for all members `x` of `I` and `y` of `J` when `J` lies strictly on one side of zero.
-/
def div (I J : Interval ℚ) : Interval ℚ :=
  mul I (inv J)

/-- The larger absolute value of the two endpoints, `max |I.lo| |I.hi|`. It bounds `|x|` on `I`. -/
def absMax (I : Interval ℚ) : ℚ :=
  Kernel.Q.max (Kernel.Q.abs I.lo) (Kernel.Q.abs I.hi)

/--
The symmetric quotient bound `[-(absMax I / δ), absMax I / δ]`. For `0 < δ` it contains `x / y`
for every member `x` of `I` and every real `y` with `δ ≤ |y|`, so the denominator needs a lower
bound on its size but no known sign.
-/
def divAbsLower (I : Interval ℚ) (δ : ℚ) : Interval ℚ :=
  let m := Kernel.Q.div (absMax I) δ
  ⟨Kernel.Q.neg m, m⟩

/-- The hull `[min I.lo J.lo, max I.hi J.hi]`, which contains both intervals. -/
def hull (I J : Interval ℚ) : Interval ℚ :=
  ⟨Kernel.Q.min I.lo J.lo, Kernel.Q.max I.hi J.hi⟩

/--
The intersection `[max I.lo J.lo, min I.hi J.hi]`. Its endpoints are reversed exactly when the
inputs have no common member.
-/
def intersect (I J : Interval ℚ) : Interval ℚ :=
  ⟨Kernel.Q.max I.lo J.lo, Kernel.Q.min I.hi J.hi⟩

end FloatLib.Numerics.Interval.Exact
