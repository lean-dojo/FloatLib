---
number: "20"
slug: proving-numerical-bounds
title: Proving numerical bounds
summary: Certified interval evaluation turns rational input bounds into Lean proofs of real inequalities.
phases: [status-and-directed]
---

Suppose a proof needs $x(1-x)\le 1/3$ for every $x\in[0,1]$. We can establish it
algebraically by completing the square. We can also let FloatLib enclose the expression
over that whole interval:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : x * (1 - x) ≤ 1 / 3 := by
  interval (depth := 4)
```

The examples in this chapter use `import FloatLib`.

The variable is a real number. It need not be rational, representable as a float, or known
when the proof is checked. The tactic computes bounds that cover every value allowed by
`hx`, then uses its soundness theorem to close the inequality. The same method applies
when the expression includes division or elementary functions:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : Real.exp x * Real.cos x < 3 := by
  interval (degree := 12)

example (x y : ℝ) (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc 2 3) :
    |x| ^ 3 / y ≤ 1 / 2 := by
  interval
```

These are proofs about the real expressions as written. To bound the error of a
floating-point program, we also need a theorem connecting that program to its real
expression, such as the [rounding and reduction bounds](#/chapter/the-mathematics-of-rounding).
Interval evaluation can discharge numerical inequalities in those arguments.

## Why subdivide?

On $[0,1]$, both $x$ and $1-x$ lie in $[0,1]$. Multiplying these two ranges gives
$[0,1]$, whose upper endpoint is too large to prove our claim. The difficulty is the
repeated variable: the two factors cannot both equal one, but the interval product
does not retain that relationship. This loss of dependency is a standard feature of
interval arithmetic [@moore1966] [@rump2010].

Smaller input intervals give more information. On $[0,1/2]$, for example, the factors
lie in $[0,1/2]$ and $[1/2,1]$, so their product is at most $1/2$. Repeating the split
narrows the bound further. With exact rational endpoint arithmetic, the largest upper
endpoint across a uniform partition is:

| Midpoint splits along each branch | Number of input intervals | Upper bound for $x(1-x)$ |
| --- | --- | --- |
| 0 | 1 | $1$ |
| 1 | 2 | $1/2$ |
| 2 | 4 | $3/8$ |
| 3 | 8 | $5/16$ |

Since $5/16<1/3$, the last row is already sufficient. The tactic works adaptively:
it accepts an interval as soon as its bound proves the goal, and otherwise bisects
the widest input coordinate. Both children must pass. The children share their
midpoint, so their union covers the original interval without leaving a gap.

Increasing precision alone would not fix the first row: those endpoints are already
exact. Conversely, a very fine partition cannot recover digits discarded by a coarse
endpoint grid. The controls address different sources of width.

## Precision, approximation, and domains

The default invocation is equivalent to:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc 1 2) : Real.log x + Real.sqrt x < 5 / 2 := by
  interval (precision := 64) (degree := 16) (depth := 8)
```

`precision` is the number of **fractional bits** in the endpoint grid. With precision
$p$, an integer coefficient $z$ represents $z\,2^{-p}$. The integers have arbitrary
size; $p$ fixes the absolute grid spacing rather than a floating-point significand
width. Arithmetic rounds lower endpoints down and upper endpoints up.

`degree` controls the rational Taylor approximations used for elementary functions.
Their remainder bounds are included in the enclosure. Increasing it can improve an
approximation even when the endpoint grid is already fine enough. `depth` limits
midpoint subdivisions along any branch; zero requests one evaluation with no splits.

The tactic recognizes addition, subtraction, multiplication, division, negation,
absolute value, natural powers whose exponent reduces to a numeral, minimum, maximum,
and multiply-add. Its elementary functions are `exp`, `log`, `sqrt`, `sin`, `cos`, `tan`,
`arcsin`, `arccos`, `arctan`,
`sinh`, `cosh`, and `tanh`. It collects rational bounds from weak or strict inequalities,
equalities, conjunctions, and `Set.Icc` membership. Strict input bounds are conservatively
widened to closed intervals. If several bounds describe the same term, it selects the
strongest lower and upper endpoints.

In the interval backend, division and reciprocal require a denominator interval that
excludes zero. Logarithm requires a positive lower endpoint; square root requires a
nonnegative one. Inverse sine and cosine require an input interval contained in $[-1,1]$,
including the endpoints. Tangent divides sine bounds by cosine bounds, so its cosine
enclosure must exclude zero. Subdivision or a higher approximation degree can separate
a coarse cosine enclosure from zero, but cannot certify a bound across an actual pole.
Likewise, a hypothesis $x\in[-1,1]$ is insufficient for this evaluator to enclose $1/x$.
A failed check reports the expression and enclosure that blocked it. For example, a
zero-containing denominator range explains why division failed; it does not claim that
the denominator actually equals zero. An insufficient upper bound is reported separately,
with the input box and subdivision depth. Closed rational expressions are simplified
using Lean's real arithmetic before enclosure.

Hyperbolic cosine needs special care because its minimum can lie inside the input interval.
We first take the absolute-value range and use monotonicity on the nonnegative half-line.
Thus an interval crossing zero retains the lower bound one:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) : 1 ≤ Real.cosh x := by
  interval (depth := 0)
```

On $[-1/2,1/2]$, the inverse-sine enclosure is narrow enough to prove:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc (-1 / 2) (1 / 2)) :
    |Real.arcsin x| < 2 / 3 := by
  interval
```

Unknown real subexpressions can still appear if their bounds are available:

```lean
example (f : ℝ → ℝ) (x : ℝ) (hx : f x ∈ Set.Icc 0 1) : 2 * f x ≤ 2 := by
  interval
```

Here `f x` is one bounded input. The tactic needs no information about how `f` is defined.

## Sums and matrices

Concrete finite sums, dot products, and matrix entries expand into the same scalar
operations. A pointwise hypothesis supplies bounds for every entry used in the expression:

```lean
open scoped BigOperators

example (x : Fin 4 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (-1) 1) :
    ∑ i, (x i) ^ 2 ≤ 4 := by
  interval (depth := 0)

example (A : Matrix (Fin 2) (Fin 3) ℝ) (x : Fin 3 → ℝ)
    (hA : ∀ i j, A i j ∈ Set.Icc (-1) 1) (hx : ∀ i, x i ∈ Set.Icc (-1) 1) :
    ‖A.mulVec x‖ ≤ 3 := by
  interval (depth := 0)
```

The second norm is the maximum absolute entry of the output vector. Each entry sums
three products bounded by one, so its norm is at most three. The tactic also expands
`WithLp`'s $\ell^1$ norm into a sum of absolute values. For matrices, it supports the
elementwise maximum and maximum row sum, using the norm instance selected in the goal.
Dimensions must reduce to concrete numbers; symbolic dimensions call
for a general sum or norm lemma first. Finite range and explicit-set sums can use guarded
hypotheses such as `∀ i ∈ Finset.range 4, x i ∈ Set.Icc 0 1`.

## The computation behind the proof

[[FloatLib.Numerics.Interval.Expr]] records constants, numbered variables, and operations.
Its executable evaluator accepts a backend and an interval for each variable.
[[FloatLib.Numerics.Interval.Expr.containsReal_eval?]] proves that a successful evaluation
contains the expression's value at every real assignment in those input intervals.
Each backend supplies the same [[FloatLib.Numerics.Interval.Backend.Sound]] contract.

For a goal $a\le b$, the checker encloses $a-b$ and checks whether its upper endpoint is
nonpositive. A strict goal uses a strictly negative endpoint.
[[FloatLib.Numerics.Interval.Expr.check_sound]] extends the enclosure theorem through
subdivision. The tactic proves the translation from the original Lean expression,
builds the input membership proof from the hypotheses, and verifies the closed Boolean
check with `decide +kernel`. Lean then checks the resulting proof term.

This use of a proved evaluator to discharge a proposition is called *proof by reflection*.
The Interval package for Rocq uses the same broad approach to numerical inequalities
and also provides automatic differentiation, Taylor models, integration, and root
enclosures [@rocqInterval]. FloatLib's checker here uses ordinary interval expressions
and midpoint subdivision. Its elementary Taylor approximations bound individual function
calls; they are not Taylor models of a complete expression.

The sine and cosine enclosures illustrate why the individual operation proofs matter.
Taking only endpoint values would miss an extremum inside the interval. Instead, we
enclose the midpoint value and widen it by the input half-width, using
$|\sin x-\sin m|\le |x-m|$ and the corresponding cosine inequality. The result is
intersected with $[-1,1]$. Large midpoint arguments use rational period reduction,
including the uncertainty in the period; an interval at least four units wide can
return the whole unit range directly.

## Using the evaluator in a program

The evaluator is also ordinary executable Lean code. Here is the expression $x^2/2$,
evaluated on $[-1,1]$ with exact rational endpoints:

```lean
open FloatLib.Numerics

def halfSquare : Interval.Expr :=
  .binary .div (.unary (.pow 2) (.var 0)) (.const 2)

#eval halfSquare.eval? (Interval.Backend.rational {})
  (fun _ => some ⟨-1, 1⟩) == some ⟨0, 1 / 2⟩
-- true
```

Squaring uses the dependence of the two factors, so its lower bound is zero even
though the input crosses zero. `#eval` lets us inspect the computed result.
The containment theorem is what allows a proof to use that result.

`Interval.Expr` supports ordinary `+` and `*` for building expressions. The endpoint
representation and rounding still come from the backend supplied to `eval?`:

```lean
open FloatLib.Numerics.Interval

def polynomial : Expr :=
  Expr.var 0 * Expr.var 0 + Expr.const (1 / 2)

example : polynomial.eval? (Backend.rational {}) (fun _ => some ⟨1, 2⟩) =
    some ⟨3 / 2, 9 / 2⟩ := by decide +kernel
```

There are three ways to choose endpoints:

| Backend | Endpoint calculation |
| --- | --- |
| `Backend.rational` | Exact rational arithmetic for algebraic operations; certified rational enclosures for elementary functions. |
| `Backend.binaryGrid` | Integer arithmetic on a chosen binary grid; elementary bounds are rounded outward onto that grid. |
| `Backend.ofRounding` | Any endpoint representation with a proved rational outward-rounding contract. |

The binary grid keeps algebraic intermediates as integers instead of repeatedly
normalizing rational fractions. Addition and subtraction preserve the grid exactly;
multiplication uses directed shifts, and division uses integer floor and ceiling
bounds. A term `a * b + c` uses multiply-add: the exact endpoint products and the addend
are combined before the final outward rounding. With a finite endpoint format, this
also permits cancellation when an intermediate product would not fit but the final
bounds do. It encloses the real expression; bounding a sequence of rounded floating-point
operations still requires their rounding-error contracts.
Elementary functions use rational analytic enclosures internally.
The costs therefore depend on how much of an expression is algebraic, its endpoint
sizes, and the requested approximation degree.

For a custom format, [[FloatLib.Numerics.Interval.Backend.ofRounding_sound]] obtains
the expression contract from its `OutwardRounding` proof. The existing binary,
decimal, and posit rounders from [chapter 21](#/chapter/further-examples/choosing-a-different-endpoint-format)
can be used this way:

```lean
def decimalBackend :=
  Interval.Backend.ofRounding
    (FloatLib.Floats.Formats.DecimalInterchange.intervalRounding .decimal32 .bid)

#eval (do
  let inputs ← Interval.Box.enclose? [⟨-1, 1⟩] decimalBackend
  let result ← halfSquare.eval? decimalBackend (fun i => inputs[i]?)
  let lo ← decimalBackend.decode result.lo
  let hi ← decimalBackend.decode result.hi
  pure (lo, hi)) == some (0, 1 / 2)
-- true
```

Finite formats may be unable to enclose an output endpoint; that failure propagates
as `none`. A new representation can supply the same contract without changing the
expression language or its proof.
