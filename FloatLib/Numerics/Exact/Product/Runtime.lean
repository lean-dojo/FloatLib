/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Rational.Runtime
public import FloatLib.Numerics.Order.Search.Runtime

/-!
# Exact comparison of a product with one unbounded factor

The parts of the complex exponential and hyperbolic functions are products `F * C` of a positive
factor that can be astronomically large or small, such as `exp a`, with a bounded nonzero factor,
such as `cos b`. Forming an enclosure of `F` itself would overflow memory long before the product
leaves the range of a format.

`compare` orders such a product against a rational boundary without evaluating `F`. It asks an
exact comparator of `F`, which can work through a logarithm, where `F` lies relative to
`boundary / C` for rational bounds on `C`, and refines those bounds until one answer settles the
order. The termination argument is a proposition, so it is erased from compiled code, and the
search is `findLeastFrom`, which Lean's kernel runs without reducing that proposition.
`Product.Proof` proves the answer and that the refinement terminates.
-/

@[expose] public section

namespace FloatLib.Numerics.ProductComparison

/--
Order `F * C` against `boundary`, where `compareFactor` orders the positive factor `F` against
every rational and `interval` encloses `C`, or `none` when the enclosure does not settle it.

An enclosure that contains zero settles nothing. Otherwise the sign of `C` is known, and `F`
against `boundary` over either endpoint decides the order when the product is clear of the
boundary by more than the width of the enclosure.
-/
def decide? (compareFactor : ℚ → Ordering) (interval : RationalInterval) (boundary : ℚ) :
    Option Ordering :=
  if 0 < interval.lo then
    if boundary ≤ 0 then some .gt
    else if compareFactor (boundary / interval.hi) = .lt then some .lt
    else if compareFactor (boundary / interval.lo) = .gt then some .gt
    else none
  else if interval.hi < 0 then
    if 0 ≤ boundary then some .lt
    else if compareFactor (boundary / interval.lo) = .lt then some .gt
    else if compareFactor (boundary / interval.hi) = .gt then some .lt
    else none
  else none

/--
Order `F * C` against `boundary` at the first enclosure of `C` that settles it. `terminates` says
that some enclosure does.
-/
def compare (compareFactor : ℚ → Ordering) (intervals : Nat → RationalInterval) (boundary : ℚ)
    (terminates : ∃ n, (decide? compareFactor (intervals n) boundary).isSome) : Ordering :=
  let found := findLeastFrom (fun n => (decide? compareFactor (intervals n) boundary).isSome)
    terminates 0 fun _ h => absurd h (Nat.not_lt_zero _)
  (decide? compareFactor (intervals found.1) boundary).get found.2.1

end FloatLib.Numerics.ProductComparison
