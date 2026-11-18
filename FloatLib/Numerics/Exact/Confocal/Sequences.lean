/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Tanh.Sequences
public import FloatLib.Numerics.Enclosure.Interval.Elementary

/-!
# Enclosures of the confocal coordinates of a rational point

The inverse sine and cosine of a complex number, and their hyperbolic counterparts, are given by
the distances of the point to two foci. For the point `(p, q)` and the foci `(0, -1)` and `(0, 1)`
the distances are `√(p² + (q + 1)²)` and `√(p² + (q - 1)²)`. Their half sum is at least one and is
the hyperbolic cosine of one part of the result, and their half difference lies in `[-1, 1]` and is
the sine or cosine of the other part.

`majorLadder` and `minorLadder` enclose the half sum and the half difference with integer square
roots on grids of doubling precision, and `coshLadder` encloses a hyperbolic cosine with the
exponential ladders of the complex tangent.
-/

@[expose] public section

namespace FloatLib.Numerics.ConfocalComparison

open RationalInterval

/-- Enclosures of `√x` between neighbours of the grid of `32 * 2 ^ n` fractional bits. -/
def sqrtLadder (x : ℚ) (n : Nat) : RationalInterval :=
  let bounds := Interval.sqrtPointBounds x (32 * 2 ^ n)
  ⟨bounds.lo, bounds.hi⟩

/-- Enclosures of the half sum of the distances of `(p, q)` to the foci `(0, -1)` and `(0, 1)`. -/
def majorLadder (p q : ℚ) (n : Nat) : RationalInterval :=
  ((sqrtLadder (p ^ 2 + (q + 1) ^ 2) n).add (sqrtLadder (p ^ 2 + (q - 1) ^ 2) n)).scale (1 / 2)

/--
Enclosures of the half difference of the distances of `(p, q)` to the foci `(0, -1)` and
`(0, 1)`.
-/
def minorLadder (p q : ℚ) (n : Nat) : RationalInterval :=
  ((sqrtLadder (p ^ 2 + (q + 1) ^ 2) n).sub (sqrtLadder (p ^ 2 + (q - 1) ^ 2) n)).scale (1 / 2)

/-- Enclosures of `cosh t` from the exponential ladders of `t` and `-t`. -/
def coshLadder (t : ℚ) (n : Nat) : RationalInterval :=
  ((TanhComparison.expLadder t n).add (TanhComparison.expLadder (-t) n)).scale (1 / 2)

/--
A natural number above the inverse hyperbolic cosine of the half sum of the distances of
`(p, q)`: two more than the binary logarithm of `|p| + |q| + 1` rounded up. No comparison of that
inverse hyperbolic cosine evaluates an exponential beyond it.
-/
def guard (p q : ℚ) : Nat :=
  ⌈|p| + |q| + 1⌉₊.log2 + 2

end FloatLib.Numerics.ConfocalComparison
