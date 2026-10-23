---
number: "20"
slug: proving-numerical-bounds
title: Proving numerical bounds
summary: Certified interval evaluation turns rational input bounds into Lean proofs of real inequalities.
phases: [status-and-directed]
---

Suppose a proof needs $x(1-x)\le 1/3$ for every $x\in[0,1]$. Completing the square gives the sharper bound $x(1-x)=1/4-(x-1/2)^2\le1/4$. We can also let FloatLib enclose the expression, splitting the input interval into pieces until each piece proves the requested bound:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : x * (1 - x) ≤ 1 / 3 := by
  interval (depth := 4)
```

With `import FloatLib`, this is a complete proof about an arbitrary real number. The variable
doesn't need to be rational, representable as a float, or known when Lean checks the proof. The
tactic computes bounds that cover every value allowed by `hx`, then closes the inequality with its soundness theorem. Division and elementary functions work the same way:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : Real.exp x * Real.cos x < 3 := by
  interval (degree := 12)

example (x y : ℝ) (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc 2 3) :
    |x| ^ 3 / y ≤ 1 / 2 := by
  interval
```

These are proofs about the real expressions as written. Bounding the error of a floating-point
program also takes a theorem connecting that program to its real expression, such as the [rounding
and reduction bounds](#/chapter/the-mathematics-of-rounding). Interval evaluation can then discharge
the numerical inequalities in those arguments.

## Why subdivide?

On $[0,1]$, both $x$ and $1-x$ lie in $[0,1]$, and multiplying the two ranges gives $[0,1]$, whose
upper endpoint is too large to prove our claim. The trouble is the repeated variable. No point makes
both factors equal one, but the interval product forgets that they're related. Losing that
dependency is a standard feature of interval arithmetic [@moore1966] [@rump2010].

Smaller input
intervals tell us more. On $[0,1/2]$, for example, the factors lie in $[0,1/2]$ and $[1/2,1]$, so
their product is at most $1/2$, and each further split narrows the bound again. With exact rational
endpoint arithmetic, here is the largest upper endpoint across a uniform partition:

| Midpoint splits along each branch | Number of input intervals | Upper bound for $x(1-x)$ |
| --- | --- | --- |
| 0 | 1 | $1$ |
| 1 | 2 | $1/2$ |
| 2 | 4 | $3/8$ |
| 3 | 8 | $5/16$ |

Since $5/16<1/3$, the last row is already enough. In practice the tactic works adaptively: it
accepts an interval as soon as its bound proves the goal, and otherwise it bisects the widest input
coordinate. Both children must pass, and because they share their midpoint, their union covers the
original interval with no gap.

More precision alone wouldn't fix the first row, because those
endpoints are already exact. Going the other way, no partition is fine enough to recover digits that
a coarse endpoint grid threw away. So precision and subdivision deal with different sources of
width.

## Precision, approximation, and domains

Writing the tactic with no options is the same as:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc 1 2) : Real.log x + Real.sqrt x < 5 / 2 := by
  interval (precision := 64) (degree := 16) (depth := 8)
```

`precision` is the number of **fractional bits** in the endpoint grid. With precision $p$, an
integer coefficient $z$ represents $z\,2^{-p}$, and those integers can be any size. What $p$ fixes
is the absolute grid spacing, which isn't a floating-point significand width. Arithmetic rounds
lower endpoints down and upper endpoints up.

`degree` controls the rational Taylor approximations
for elementary functions, and their remainder bounds go into the enclosure. Raising it can improve
an approximation even when the endpoint grid is already fine enough. `depth` limits midpoint
subdivisions along any branch, and zero asks for one evaluation with no splits.

The tactic recognizes addition, subtraction, multiplication, division, negation, absolute value,
natural powers whose exponent reduces to a numeral, minimum, maximum, and multiply-add. Its
elementary functions are `exp`, `log`, `sqrt`, `sin`, `cos`, `tan`, `arcsin`, `arccos`, `arctan`,
`sinh`, `cosh`, `tanh`, `arsinh`, `arcosh`, and `artanh`. It also handles real powers `x ^ (y : ℝ)`
and base-specific logarithms `Real.logb b x`, variable exponents and bases included. It reads
rational bounds off weak or strict inequalities, equalities, conjunctions, and `Set.Icc` membership.
Strict input bounds get widened to closed intervals, which is conservative. When several bounds
describe the same term, it picks the strongest lower and upper endpoints.

In the interval backend, division and reciprocal need a denominator interval that excludes zero.
Logarithm needs a positive lower endpoint and square root a nonnegative one, and inverse sine and
cosine need an input interval inside $[-1,1]$, endpoints included. Tangent divides sine bounds by
cosine bounds, so its cosine enclosure must exclude zero. Subdivision or a higher approximation
degree can separate a coarse cosine enclosure from zero, but neither can certify a bound across an
actual pole. In the same way, a hypothesis $x\in[-1,1]$ isn't enough for this evaluator to enclose
$1/x$.

Real powers need a strictly positive base interval, and on that domain negative and zero real
exponents are fine. `Real.logb b x` needs positive base and argument intervals and an enclosure of
`log b` that excludes zero. Bases below one are accepted. A base interval that reaches one is
rejected, and near one a coarse enclosure may need a higher degree. Inverse hyperbolic cosine needs
inputs of at least one, and inverse hyperbolic tangent needs an interval strictly inside $(-1,1)$.
For inverse hyperbolic sine we use monotonicity and odd symmetry. We evaluate $\log(x+\sqrt{1+x^2})$
at nonnegative endpoints, so negative inputs don't suffer cancellation. Here are a few of these at
work:

```lean
example (x y : ℝ) (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc (-2) 2) :
    x ^ y < 5 := by
  interval (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc 1 100) : Real.logb 10 x < 21 / 10 := by
  interval (degree := 24) (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc (-1 / 2) (1 / 2)) : |Real.artanh x| < 3 / 5 := by
  interval (depth := 0)
```

There's no fixed maximum endpoint precision, but raising `precision` alone doesn't promise that many
accurate bits. The Taylor remainder and the width of the input box can dominate the grid spacing,
and when those are the limiting factors, increase `degree` or `depth`. For algebraic goals the
tactic first tries exact rational endpoints without subdivision, which keeps a touching non-dyadic
bound intact:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc 0 (1 / 3 : ℝ)) : x ≤ 1 / 3 := by
  interval
```

Before kernel reduction, an advisory executable check rejects failing arithmetic leaves. Registered
calls use bounded kernel reduction, and every successful goal still needs a kernel-checked
certificate.

Each verification attempt has its own budget of 20,000 heartbeats, and so do the
failure diagnostics. That limit stays active even when the surrounding declaration sets
`maxHeartbeats` to zero, and you can ask for a larger finite budget with
`interval (maxHeartbeats := 40000)`. If the budget runs out, the tactic reports an inconclusive
check and restores the original goal.

When arithmetic fails, the diagnostics tell you why. They
report the obstructing range or the upper bound that wasn't small enough, and for registered calls
they inspect the actual enclosure on the original box and report rejected domains separately. A
zero-containing denominator range, for example, explains why division failed without claiming that
the denominator equals zero. Closed rational expressions are simplified with Lean's real arithmetic
before enclosure.

Hyperbolic cosine reaches its minimum at zero, which can lie inside the input interval. We first
take the absolute-value range, then use monotonicity on the nonnegative half-line, so an interval that crosses zero keeps the lower bound one:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) : 1 ≤ Real.cosh x := by
  interval (depth := 0)
```

On $[-1/2,1/2]$ the inverse-sine enclosure is narrow enough to prove this:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc (-1 / 2) (1 / 2)) :
    |Real.arcsin x| < 2 / 3 := by
  interval
```

Unknown real subexpressions are fine too, as long as their bounds are available:

```lean
example (f : ℝ → ℝ) (x : ℝ) (hx : f x ∈ Set.Icc 0 1) : 2 * f x ≤ 2 := by
  interval
```

Here the tactic treats `f x` as one bounded input. It uses the hypotheses without unfolding `f`, so
it never needs to know what the function computes.

## User-defined constants and functions

To register a constant with `interval`, supply rational lower and upper bounds and prove that the
constant lies between them. `ConstantBounds` keeps both in one definition, and the
attribute registers it automatically. Here are fixed bounds for a named square root of two:

```lean
open FloatLib.Numerics.Interval

noncomputable def sqrtTwo : ℝ := Real.sqrt 2

@[interval_extension]
def sqrtTwoBounds : ConstantBounds sqrtTwo where
  bounds _ := ⟨1.4, 1.5⟩
  valid _ := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnonneg := Real.sqrt_nonneg (2 : ℝ)
    norm_num [sqrtTwo]
    constructor <;> nlinarith

example : sqrtTwo < (1.6 : ℝ) := by interval
example : Real.logb 2 sqrtTwo < (1 : ℝ) := by interval
```

`bounds` returns the two endpoints, and `valid` proves the usual inequalities `lower ≤ constant` and
`constant ≤ upper`. The `_` argument is the requested precision. These fixed bounds ignore it, but a
provider can use it to compute narrower bounds instead. FloatLib turns the registered bounds and
their proof into an enclosure the evaluator can use.

For Catalan's constant, a provider
would define the real value, an executable approximation, and a theorem bounding the remainder.
Registering it makes that certificate available to the tactic, but registration doesn't derive the
approximation or the remainder theorem for you.

Importing the provider's module brings its
registration along. If you export executable certificate definitions from a Lean module, mark them
with `@[expose]`. Local and scoped registrations follow Lean's ordinary attribute visibility rules,
and a later applicable registration replaces an earlier one.

Functions go through the general `Extension` interface and register a theorem `E.Sound f` with the
same attribute. To adapt an existing procedure, use `Extension.unary` or `Extension.binary`, whose
`unary_sound` and `binary_sound` theorems lift containment proofs covering every real member of the
input intervals. For other arities you supply an `Extension` record and prove `Extension.Sound`
yourself. The evaluator checks argument counts, propagates `none` for rejected domains, and
recomputes function enclosures on each subdivided input box. Parameters of other types can be fixed
in named wrappers.

## Sums and matrices

Concrete finite sums, dot products, and matrix entries expand into the same scalar operations, and a
pointwise hypothesis supplies bounds for every entry the expression uses. In these two examples,
that is enough for a sum of four squares and a bound on a matrix-vector product:

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

In the second example the norm is the maximum absolute entry of the output vector. Each entry sums
three products bounded by one, so the norm is at most three. The tactic also expands `WithLp`'s
$\ell^1$ norm into a sum of absolute values, and for matrices it supports the elementwise maximum
and the maximum row sum, using whichever norm instance the goal selects. Dimensions have to reduce
to concrete numbers, so with symbolic dimensions you need a general sum or norm lemma first. Sums
over a finite range or an explicit set can use guarded hypotheses such as
`∀ i ∈ Finset.range 4, x i ∈ Set.Icc 0 1`.

## The computation behind the proof

[[FloatLib.Numerics.Interval.Expr]] records constants, numbered variables, and operations, and its
executable evaluator takes a backend and an interval for each variable. The theorem
[[FloatLib.Numerics.Interval.Expr.containsReal_eval?]] proves that a successful evaluation contains
the expression's value at every real assignment in those input intervals. Every backend supplies the
same [[FloatLib.Numerics.Interval.Backend.Sound]] contract.

For a goal $a\le b$, the checker
encloses $a-b$ and checks whether its upper endpoint is nonpositive, and for a strict goal it has to
be strictly negative. [[FloatLib.Numerics.Interval.Expr.check_sound]] extends the enclosure theorem
through subdivision. The tactic itself proves the translation from the original Lean expression and
builds the input membership proof from the hypotheses. It verifies the closed Boolean check with
`decide +kernel`, and Lean then checks the resulting proof term.

Using a proved evaluator to
discharge a proposition like this is called *proof by reflection*. Rocq's Interval package takes the
same broad approach to numerical inequalities, and it also provides automatic differentiation,
Taylor models, integration, and root enclosures [@rocqInterval]. FloatLib uses ordinary interval
expressions and midpoint subdivision. Its elementary
Taylor approximations bound individual function calls and aren't Taylor models of a complete
expression.

Sine and cosine show why the individual operation proofs matter. If we took only the endpoint
values, we'd miss an extremum inside the interval. So we enclose the midpoint value and widen it by
the input half-width, using $|\sin x-\sin m|\le |x-m|$ and the corresponding cosine inequality, and
then we intersect the result with $[-1,1]$. Large midpoint arguments go through rational period
reduction, uncertainty in the period included. An interval at least four units wide can return the
whole unit range right away.

## Using the evaluator in a program

The same evaluator runs outside a tactic. This call encloses $x^2/2$ on $[-1,1]$ using exact
rational endpoints:

```lean
open FloatLib.Numerics

def halfSquare : Interval.Expr :=
  .binary .div (.unary (.pow 2) (.var 0)) (.const 2)

#eval halfSquare.eval? (Interval.Backend.rational {})
  (fun _ => some ⟨-1, 1⟩) == some ⟨0, 1 / 2⟩
-- true
```

Squaring accounts for the dependence between its two factors, so its lower bound is zero even though
the input crosses zero. `#eval` lets us look at the computed result, but it's the containment
theorem that lets a proof use it. You can build an `Interval.Expr` with ordinary `+` and `*`, while
the endpoint representation and rounding still come from the backend you pass to `eval?`:

```lean
open FloatLib.Numerics.Interval

def polynomial : Expr :=
  Expr.var 0 * Expr.var 0 + Expr.const (1 / 2)

example : polynomial.eval? (Backend.rational {}) (fun _ => some ⟨1, 2⟩) =
    some ⟨3 / 2, 9 / 2⟩ := by decide +kernel
```

The evaluator accepts these endpoint backends:

| Backend | Endpoint calculation |
| --- | --- |
| `Backend.rational` | Exact rational arithmetic for algebraic operations; certified rational enclosures for elementary functions. |
| `Backend.binaryGrid` | Integer arithmetic on a chosen binary grid; elementary bounds are rounded outward onto that grid. |
| `Backend.ofRounding` | Any endpoint representation with a proved rational outward-rounding contract. |

On the binary grid, algebraic intermediates stay integers, which saves normalizing rational
fractions over and over. Addition and subtraction stay exactly on the grid, multiplication uses
directed shifts, and division uses integer floor and ceiling bounds. A term `a * b + c` uses
multiply-add, combining the exact endpoint products and the addend before the final outward
rounding. With a finite endpoint format this also allows cancellation when an intermediate product
wouldn't fit but the final bounds do. What it encloses is the real expression. To bound a sequence
of rounded floating-point operations you still need their rounding-error contracts. Elementary
functions use rational analytic enclosures internally, so the cost depends on how much of an
expression is algebraic, how big its endpoints are, and the requested approximation degree.

For a
custom format, [[FloatLib.Numerics.Interval.Backend.ofRounding_sound]] gets the expression contract
from its `OutwardRounding` proof, and the existing binary, decimal, and posit rounders from [chapter
21](#/chapter/further-examples/choosing-a-different-endpoint-format) can be used this way too:

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

A finite format may be unable to enclose an output endpoint, and that failure propagates as `none`.
Any new representation can supply the same contract without changing the expression language or its
proof. So if you have a favourite format and can prove its outward rounding, you can plug it in :)