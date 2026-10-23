/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Bounds
public import Mathlib.Data.Rat.Defs

/-!
# Integer arithmetic on a binary interval grid

At `precision` fractional bits, an integer coefficient `z` represents `z / 2^precision`.
Intervals are the existing `Interval Int`, and each operation takes the scale as an argument
instead of storing it in the interval. Coefficients have unbounded magnitude, so arithmetic cannot
overflow.

Addition, subtraction, and negation are exact. Multiplication rounds the smallest and largest
integer products with signed shifts. Division uses four integer quotients and rejects a divisor
interval containing zero. Values are decoded to rationals at the interface, never between
arithmetic steps.

The endpoint construction follows S. M. Rump,
[Verification methods: Rigorous results using floating-point
arithmetic](https://doi.org/10.1017/S096249291000005X), *Acta Numerica* 19 (2010), §§5.1–5.3.
`BinaryGridProof` proves containment for arbitrary real members of the input intervals.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval.BinaryGrid

/-- Positive integer scale `2 ^ precision` of a grid with `precision` fractional bits. -/
def scale (precision : Nat) : Int :=
  (1 : Int) <<< precision

/-- Exact rational interpretation of an integer coefficient on the binary grid. -/
def toRat (precision : Nat) (z : Int) : ℚ :=
  Rat.divInt z (scale precision)

/-- Decode a coefficient as its rational value. Every coefficient is finite. -/
def decode (precision : Nat) (z : Int) : Option ℚ :=
  some (toRat precision z)

/-- Floor of `z / 2^precision`. The signed shift rounds negative values downward too. -/
def roundDown (precision : Nat) (z : Int) : Int :=
  z >>> precision

/-- Ceiling of `z / 2^precision`, obtained by negating a downward-rounded negative. -/
def roundUp (precision : Nat) (z : Int) : Int :=
  -((-z) >>> precision)

/-- Coarsen a grid interval by `shift` fractional bits, rounding both endpoints outward. -/
def coarsen (shift : Nat) (I : Interval Int) : Interval Int :=
  ⟨roundDown shift I.lo, roundUp shift I.hi⟩

/--
Integer floor and ceiling of `a / b`, for a nonzero denominator of either sign.

One signed floor division supplies both endpoints. Testing the integer product detects exact
division without computing another quotient or a rational greatest common divisor.
-/
def divBounds (a b : Int) : Interval Int :=
  let q := a.fdiv b
  ⟨q, if q * b = a then q else q + 1⟩

/-- Enclose an exact rational by neighboring grid coefficients. -/
def enclose (precision : Nat) (q : ℚ) : Interval Int :=
  divBounds (q.num <<< precision) q.den

/-- Exact negation on the grid, with the endpoints exchanged. -/
def neg (I : Interval Int) : Interval Int :=
  ⟨-I.hi, -I.lo⟩

/-- Exact addition of intervals on the same grid. -/
def add (I J : Interval Int) : Interval Int :=
  ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- Exact subtraction of intervals on the same grid. -/
def sub (I J : Interval Int) : Interval Int :=
  ⟨I.lo - J.hi, I.hi - J.lo⟩

/-- Multiply using four integer products and two outward-rounded shifts. -/
def mul (precision : Nat) (I J : Interval Int) : Interval Int :=
  let a := I.lo * J.lo
  let b := I.lo * J.hi
  let c := I.hi * J.lo
  let d := I.hi * J.hi
  ⟨roundDown precision (minOfFour a b c d), roundUp precision (maxOfFour a b c d)⟩

/--
Divide using scaled integer numerators, returning `none` for a denominator containing zero.

The four corner divisions round outward on the same grid as the input endpoints. No rational
normalization occurs in this operation.
-/
def div? (precision : Nat) (I J : Interval Int) : Option (Interval Int) :=
  if J.hi < 0 ∨ 0 < J.lo then
    let lo := I.lo <<< precision
    let hi := I.hi <<< precision
    let a := divBounds lo J.lo
    let b := divBounds lo J.hi
    let c := divBounds hi J.lo
    let d := divBounds hi J.hi
    some ⟨minOfFour a.lo b.lo c.lo d.lo, maxOfFour a.hi b.hi c.hi d.hi⟩
  else none

/-- Exact absolute-value enclosure, taking a zero lower bound when the interval crosses zero. -/
def abs (I : Interval Int) : Interval Int :=
  if 0 ≤ I.lo then I
  else if I.hi ≤ 0 then neg I
  else ⟨0, max (-I.lo) I.hi⟩

/--
Square with a nonnegative lower bound, including for intervals that cross zero.

Using the range of the square avoids the negative lower endpoint produced by treating the two
occurrences of the input as independent factors.
-/
def square (precision : Nat) (I : Interval Int) : Interval Int :=
  let a := I.lo * I.lo
  let b := I.hi * I.hi
  let lo := if 0 ≤ I.lo then a else if I.hi ≤ 0 then b else 0
  ⟨roundDown precision lo, roundUp precision (max a b)⟩

namespace Internal

/--
Repeated squaring for the endpoint evaluations in `BinaryGrid.pow`.

With the squaring in its own helper, the public operation can use monotonicity before interval
evaluation. The exponent-one branch avoids multiplying by a scaled representation of one.
-/
def pow (precision : Nat) (I : Interval Int) (n : Nat) : Interval Int :=
  if h : n = 0 then
    point (scale precision)
  else if n = 1 then
    I
  else
    let a := square precision (pow precision I (n / 2))
    if n % 2 = 0 then a else mul precision a I
termination_by n

end Internal

/--
Natural powers with logarithmically many interval operations.

Odd powers are increasing, so their lower and upper bounds come from evaluating at each endpoint.
Even powers use the absolute-value interval. These choices avoid treating repeated occurrences of
the input as independent values. Each evaluation still rounds outward at intermediate steps.
Exponents zero and one are exact, and a point interval needs one repeated-squaring evaluation.
-/
def pow (precision : Nat) (I : Interval Int) (n : Nat) : Interval Int :=
  if n = 0 then point (scale precision)
  else if n = 1 then I
  else if n % 2 = 0 then Internal.pow precision (abs I) n
  else if I.lo = I.hi then Internal.pow precision I n
  else
    ⟨(Internal.pow precision (point I.lo) n).lo,
      (Internal.pow precision (point I.hi) n).hi⟩

end FloatLib.Numerics.Interval.BinaryGrid
