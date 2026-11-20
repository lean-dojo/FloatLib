---
number: "11"
slug: proving-numerical-bounds
title: "Intervals and roundoff bounds"
summary: "How to prove a real inequality with the `interval` tactic, how to get a forward or a backward error bound for floating-point code with the `roundoff` tactic, how `interval` bounds a polynomial over its whole domain from its coefficients, and what each one assumes."
phases: [status-and-directed, planner-and-configured, ieee-formats, binary-arithmetic]
---

On $[0,1]$, the real expression $x(1-x)$ is at most $1/4$. If a binary32 program evaluates the same formula, its subtraction and multiplication each round. A proof about the program needs to account for those steps. FloatLib's `interval` tactic bounds the real expression over the whole input interval. The `roundoff` tactic bounds the difference between a floating-point calculation and its real counterpart.

## How to prove an inequality with `interval`

To prove the simpler bound $x(1-x)\le 1/3$, give `interval` the expression and a hypothesis on $x$. In Lean, `Set.Icc 0 1` denotes the closed interval $[0,1]$.

```lean
example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : x * (1 - x) ≤ 1 / 3 := by
  interval (depth := 4)
```

This proof applies to every real $x$ satisfying `hx`; the value of $x$ need not be known when
Lean checks it. An *enclosure* is an interval containing the expression's value at every point
of the input intervals. The tactic computes an enclosure for $x(1-x)$ and, if necessary,
subdivides the input interval until the bound holds on every part. Its soundness theorem turns
the successful check into a proof of the goal. The same procedure supports division and
elementary functions:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : Real.exp x * Real.cos x < 3 := by
  interval (degree := 12)

example (x y : ℝ) (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc 2 3) :
    |x| ^ 3 / y ≤ 1 / 2 := by
  interval
```

For a floating-point implementation, [`roundoff`](#/chapter/proving-numerical-bounds/how-to-get-an-error-bound-for-floating-point-code) applies the [rounding and reduction bounds](#/chapter/the-mathematics-of-rounding) of each operation. You can use `interval` on the resulting real inequalities.

## Why does `interval` cut the range into pieces?

Let's try our first proof without cutting $[0,1]$ into pieces. On $[0,1]$, both $x$ and $1-x$ lie in
$[0,1]$, and multiplying the two ranges gives $[0,1]$, whose upper endpoint is far too big for our
claim. The trouble is the repeated variable. No point makes both factors equal one, but the interval
product forgets that they're related, as if each factor got its own copy of $x$. Interval arithmetic
is known for losing that dependency [@moore1966] [@rump2010].

Smaller pieces tell us more. On $[0,1/2]$, for example, the factors lie in $[0,1/2]$ and $[1/2,1]$,
so their product is at most $1/2$. With exact rational endpoints, a uniform partition, where every
piece is cut at its midpoint, gives these largest upper endpoints:

| Midpoint splits along each branch | Number of input intervals | Upper bound for $x(1-x)$ |
| --- | --- | --- |
| 0 | 1 | $1$ |
| 1 | 2 | $1/2$ |
| 2 | 4 | $3/8$ |
| 3 | 8 | $5/16$ |

Since $5/16<1/3$, three rounds of splitting are enough. The tactic only splits where it has to,
though. It accepts an interval as soon as its bound proves the goal. Otherwise it cuts the widest
input coordinate, the variable whose interval is widest, in half, and both halves, which share their
midpoint, have to pass.

## How to tighten an enclosure

Cutting the input into pieces is called *subdivision*, and it isn't the only way to get a tighter
enclosure. `interval` has three knobs, and our first two examples set `depth` and `degree` below the
defaults shown next. Writing `interval` with no options is the same as writing:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc 1 2) : Real.log x + Real.sqrt x < 5 / 2 := by
  interval (precision := 64) (degree := 16) (depth := 8)
```

- `precision` is the number of **fractional bits** in the endpoint grid. With precision $p$, an
  integer $z$ of any size represents $z\,2^{-p}$. The grid has fixed absolute spacing $2^{-p}$
  and no bound on the integer part. This parameter differs from a floating-point significand
  width. Lower endpoints round down and upper endpoints round up.
- `degree` controls the rational Taylor approximations for elementary functions. These are
  polynomials that stand in for `exp` and its relatives, and their remainder bounds go into the
  enclosure.
- `depth` caps the midpoint splits along any branch, and zero means no splits.

`precision` has no fixed ceiling, but more grid bits can't make up for a large Taylor remainder or a
wide input box, and that's when to raise `degree` or `depth`. Precision and subdivision fight
different sources of width. More precision wouldn't rescue the first row of the table above, whose
endpoints are already exact, and no partition brings back digits that a coarse endpoint grid threw
away.

For algebraic goals, the ones without elementary functions, the tactic first tries exact rational
endpoints without subdivision. That keeps intact a bound the expression reaches, even a non-dyadic
one, with no power of two as its denominator. Here the bound is exactly one third, which no binary
grid can hold:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc 0 (1 / 3 : ℝ)) : x ≤ 1 / 3 := by
  interval
```

Every successful goal needs a certificate checked by the kernel, the small core of Lean that checks
every proof. Each attempt gets its own 20,000 heartbeats (Lean's measure of tactic work), even when
the surrounding declaration sets `maxHeartbeats` to zero. `interval (maxHeartbeats := 40000)` asks
for more, and every failure restores the original goal.

## What can a goal contain?

Expressions can use:

- the four arithmetic operations, negation, absolute value, minimum, maximum and multiply-add,
- natural powers whose exponent reduces to a numeral,
- `exp`, `log`, `sqrt`, `sin`, `cos`, `tan`, `arcsin`, `arccos`, `arctan`, `sinh`, `cosh`, `tanh`,
  `arsinh`, `arcosh` and `artanh`,
- real powers `x ^ (y : ℝ)` and `Real.logb b x`, variable exponents and bases included.

Bounds come from hypotheses: weak or strict inequalities, equalities, conjunctions and `Set.Icc`
membership. Strict ones are widened to closed intervals, and when several bounds land on one term,
the strongest wins. Unknown real subexpressions are fine too, as long as something bounds them. Here
`interval` treats `f x` as one more bounded input and never unfolds `f` to look inside it:

```lean
example (f : ℝ → ℝ) (x : ℝ) (hx : f x ∈ Set.Icc 0 1) : 2 * f x ≤ 2 := by
  interval
```

## Which inputs does each operation accept?

Some operations are picky about their inputs. In the interval backend (the code that computes the
endpoints), division and reciprocal need a denominator interval that excludes zero, logarithm a
positive lower endpoint, square root a nonnegative one, and inverse sine and cosine an input inside
$[-1,1]$, endpoints included. Tangent needs a cosine enclosure that excludes zero. Subdivision or a
higher degree can pull a coarse one away from zero, but nothing certifies a bound across an actual
pole, a point where the function blows up, and for the same reason $x\in[-1,1]$ isn't enough to
enclose $1/x$.

Real powers need a strictly positive base interval, though negative and zero exponents are fine.
`Real.logb b x` needs positive base and argument intervals and an enclosure of `log b` that excludes
zero. So a base interval reaching one is rejected, while bases below one are accepted and a base
near one may need a higher degree. Inverse hyperbolic cosine needs inputs of at least one, and
inverse hyperbolic tangent an interval strictly inside $(-1,1)$:

```lean
example (x y : ℝ) (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc (-2) 2) :
    x ^ y < 5 := by
  interval (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc 1 100) : Real.logb 10 x < 21 / 10 := by
  interval (degree := 24) (depth := 0)

example (x : ℝ) (hx : x ∈ Set.Icc (-1 / 2) (1 / 2)) : |Real.artanh x| < 3 / 5 := by
  interval (depth := 0)
```

## What about functions that go up and down?

Functions that aren't monotone, rising in some places and falling in others, need a little care.
Hyperbolic cosine has its minimum at zero, where endpoint values would miss it, so we take the range
of the absolute value first:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) : 1 ≤ Real.cosh x := by
  interval (depth := 0)
```

Here's one you can check in your head. On $[-1/2,1/2]$ the largest $|\arcsin x|$ is
$\pi/6\approx0.524$, so a bound of two thirds goes through:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc (-1 / 2) (1 / 2)) :
    |Real.arcsin x| < 2 / 3 := by
  interval
```

## How to teach `interval` a new constant or function

What if your goal mentions a constant or a function that `interval` doesn't know? You can teach it.
For a constant, that takes rational lower and upper bounds and a proof that the constant lies
between them. They go together in a `ConstantBounds` definition, and you register it with the
`@[interval_extension]` attribute, a tag written above the definition. Let's look at fixed bounds
for a named square root of two:

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

`bounds` returns the two endpoints and `valid` proves `lower ≤ constant` and `constant ≤ upper`.
Both take the requested precision as `_`. Fixed bounds ignore it, and a provider, whoever registers
the bounds, can use it for narrower ones. A fixed rational enclosure also works for Catalan's constant once you prove it. To obtain tighter
bounds as precision increases, supply an executable approximation with a proved error bound. Importing the provider's module brings its registration along, and
executable certificate definitions exported from a Lean module need `@[expose]`. A later applicable
registration replaces an earlier one.

Functions go through the more general `Extension` interface, and you register a theorem `E.Sound f`
with the same attribute. `Extension.unary` and `Extension.binary` adapt a procedure you already
have, with `unary_sound` and `binary_sound` lifting containment proofs that cover every real member
of the input intervals. Other arities (numbers of arguments) need an `Extension` record and your own
proof of `Extension.Sound`, and parameters of other types can be fixed in named wrappers.

## How to bound sums and matrices

Your goal can also be about a whole vector or matrix. Concrete finite sums, dot products and matrix
entries, whose sizes are known numbers, expand into the same scalar operations. A pointwise
hypothesis, one statement about all the entries at once, bounds every entry the expression uses.
That's enough for a sum of four squares and a bound on a matrix-vector product:

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

In the second example the norm, the size of the output vector, is its largest absolute entry, and
each entry sums three products bounded by one. The tactic also expands `WithLp`'s $\ell^1$ norm and,
for matrices, the elementwise maximum and the maximum row sum, whichever norm instance the goal
selects. Dimensions have to reduce to concrete numbers (symbolic ones need a general sum or norm
lemma first), and sums over a finite range or a listed set can use guarded hypotheses such as
`∀ i ∈ Finset.range 4, x i ∈ Set.Icc 0 1`.

## How to prove that constraints have no common point

Often the statement isn't one inequality. A region of attraction, a safety argument or one case of a larger proof says that a set of constraints is empty: no point satisfies all of them. `interval` proves that too. Your goal can be `False` with the constraints as hypotheses, a negated existential, or an implication to `False` under binders, and the constraints can be any combination by `∧`, `∨`, `¬` and `→` of `≤`, `<`, `=` and `≠` between the expressions of the sections above. Let's start with a disc and a half-plane that don't meet:

```lean
example (x y : ℝ) (hx : -2 ≤ x) (hx' : x ≤ 2) (hy : -2 ≤ y) (hy' : y ≤ 2)
    (h1 : x ^ 2 + y ^ 2 ≤ 1) (h2 : x + y ≥ 3 / 2) : False := by
  interval

example : ¬ ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ x * (1 - x) > 13 / 50 := by
  interval

example (x : ℝ) (h : (0 ≤ x ∧ x ≤ 1) ∨ (2 ≤ x ∧ x ≤ 3)) (hx : -1 ≤ x) (hx' : x ≤ 4)
    (h' : (x - 3 / 2) ^ 2 < 1 / 5) : False := by
  interval
```

Any other goal that isn't one inequality is proved by refuting its negation, so a conjunction, a membership, an equality or an inclusion of sets works as well:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2) : x ^ 2 ∈ Set.Icc (1 : ℝ) 4 := by
  interval

example : {x : ℝ | 0 ≤ x ∧ x ≤ 1} ⊆ {x : ℝ | x ^ 2 ≤ 1} := by
  interval
```

The coordinates can be plain variables, the entries of a vector `Fin n → ℝ`, the fields of a structure, or any real terms that hypotheses bound. A hypothesis `∀ i, P (x i)` over the indices of such a vector is read for each entry. Membership in a named set is unfolded, and so is a definition whose value has no bound of its own.

### What does the tactic do with a set of constraints?

It plays a game of elimination on boxes. It reads a box from the bounds among the constraints and then searches, with compiled code, for a tree of smaller boxes. On each box every comparison has one of three values: it fails at every point, it holds at every point, or the enclosure can't tell. A box where one comparison of a conjunction fails, or every case of a disjunction, is done. A box that is undecided is cut in half, and the search goes on in both halves. What comes out is a certificate, a [[FloatLib.Numerics.Interval.Refutation]]: the tree of cuts, and for each leaf the comparison that fails there.

Then the kernel checks the certificate in one evaluation of [[FloatLib.Numerics.Interval.Constraint.refutes]], which evaluates only the comparison that each leaf names, and [[FloatLib.Numerics.Interval.Constraint.refutes_sound]] turns the answer into the proof. Nothing from the search is trusted, so the search is free to guess.

### What if a constraint holds with no margin?

Then no box separates it from zero and cutting never ends. The standard case is an equilibrium: a Lyapunov function whose derivative along the flow is negative everywhere except at the origin, where it is zero. Here is the claim that it is never nonnegative away from the origin:

```lean
example (x y : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : -1 ≤ y) (hy' : y ≤ 1)
    (h0 : x ^ 2 + y ^ 2 > 0)
    (h : 2 * x * (-x + y / 2 - x * y ^ 2 / 10) + 2 * y * (-x / 2 - y) ≥ 0) : False := by
  interval
```

When the search stops at a small box, `interval` writes each undecided comparison $a \le b$ as a quadratic form around the simplest rational point $c$ of that box,

$$a - b = \sum_k M_{kk}(x)\,d_k^2 + 2\sum_{k<l} M_{kl}(x)\,d_k d_l,\qquad d_k = x_k - c_k,$$

where the entries of the matrix $M(x)$ are whatever is left of each term: numbers, other variables, function values. `ring` proves the identity. If $M(x)$ is positive definite for every $x$ in a box around $c$, the form is positive there except at $c$, so $a \le b$ leaves only the point $c$, and the other constraints are checked at that point. The kernel checks definiteness with intervals, in any dimension, by eliminating one coordinate at a time ([[FloatLib.Numerics.Interval.Form.definiteOn]], with [[FloatLib.Numerics.Interval.Form.vanishes_of_definiteOn]] as the theorem behind it). In the example the matrix has the entries $2 + y^2/5$, $0$ and $2$.

The same idea decides a strict comparison whose form is only semidefinite, a sum of nonnegative terms that a comparison bounds by zero, two comparisons that touch at a point when one combination $a - b + \mu\,(c - d)$ with a rational $\mu > 0$ is definite, a quotient whose comparison holds with equality at a point, and values of the sine, the cosine, the hyperbolic tangent and the arctangent that vanish at the point. When a level is given with $\pi$, as for a disc of radius $\pi/4$ against a half-plane, the multiplier is a rational times $\pi$: the tactic then multiplies the comparisons by $\pi$ and takes $\pi$ for one more coordinate, so the matrix is rational again. It doesn't decide two sets that touch when the multiplier is irrational in another way, as for the unit disc and the half-plane $x + y > \sqrt 2$, a zero margin that needs three or more constraints at once unless products of pairs decide it, or one where an exponential, a logarithm or a square root vanishes with the form.

An inequality goal still goes to the boxes of the first section. When they don't prove it, the tactic tries the constraint that the inequality fails, which is how $x(1-x) \le 1/4$ on $[0,1]$ is proved: the bound is attained at $x = 1/2$, and the form $(x - 1/2)^2$ decides it.

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  interval
```

### What if the constraints give no box?

A variable needs bounds, and when the hypotheses don't state them the tactic derives them, with proof. An ellipsoid bounds its variables:

```lean
example (x y : ℝ) (h : 3 / 2 * x ^ 2 - x * y + y ^ 2 ≤ 3 / 20)
    (h' : x < -6 / 5 ∨ x > 6 / 5 ∨ y < -6 / 5 ∨ y > 6 / 5 ∨ x ^ 2 + y ^ 2 > 36 / 25) : False := by
  interval
```

Bounds also come from `|t| ≤ r`, `max` and `min`, from comparisons that are affine in the variable, and from a comparison with an expression in bounded variables, such as $y \le e^x$. A variable with a bound on one side only still has a range, one with an infinite end, and the enclosures work on such ranges: $e^{-x}$ is in $[0, 1]$ for every $x \ge 0$. When the constraints fail on the whole range, the goal is closed. When they fail on a tail, the variable gets the bound that it lacked. Below, the left side is under $2$ for every $x \ge 2$, so the tactic proves $x < 2$ and goes on with the box $[0, 2]$:

```lean
example (x : ℝ) (hx : 0 ≤ x) :
    -(173 / 250) * Real.exp (-(13 / 10) * x) + 319 / 100 - x - Real.exp (-(11 / 10) * x) < 2 := by
  interval
```

The search never cuts a range with an infinite end, so a comparison whose two sides grow together, such as $x e^{-x} \le 1$, isn't decided this way, and a variable that still has no bounds is an error that names it. What is left for a set that is unbounded in a variable is arithmetic on the comparisons, through `linarith`, products of the linear comparisons and `nlinarith`, which is enough for polynomial comparisons such as this one:

```lean
example {x y : ℝ} (hx : x ≤ -2) (hy : 3 ≤ y) : 16 ≤ x ^ 4 ∧ x ^ 3 ≤ -8 ∧ 6 ≤ -x * y := by
  interval
```

### What if the two sides are equal at an end of the range?

Then no box separates them there, and often no form does either: $1 + x \le e^x$ holds with equality at $0$, and so does every bound that was made to be sharp there. What decides such a comparison is a derivative. The difference of the two sides is zero at the end, and if its derivative is nonnegative beyond, the difference is nonnegative too. So when everything above has failed and the goal is one comparison in one variable, with bounds that have no variables, the tactic differentiates the difference by the rules for the elementary functions, proves its sign at the end of the range, and hands the sign of the derivative to itself as a new goal. That goal may need the next derivative in the same way, up to five in a row, and the goals of one call together have one and a half times the heartbeats of `maxHeartbeats`, so a larger `(maxHeartbeats := 80000)` lets a long chain end.

```lean
example (x : ℝ) (hx : 0 ≤ x) : (x + 4) ^ 4 / 256 ≤ Real.exp x := by
  interval

example (x : ℝ) (hx : 0 ≤ x) : 2 * x / (2 + x) ≤ Real.log (1 + x) := by
  interval
```

The first takes three derivatives: the difference and its first derivative are zero at $0$, the second is $1/4$ there, and the third, $e^x - 3(x+4)/32$, is positive for every $x \ge 0$ by the tangent of the exponential. In the second the derivative is a quotient of polynomials, and the arithmetic steps prove its sign. A derivative may keep its sign only near the end. So the tactic evaluates it at four points of the range first, and where the sign turns it cuts the range before that point: the derivative decides the part at the end, and boxes the rest, where the two sides are apart.

```lean
example (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 4) : x * Real.cos x ≤ Real.sin x := by
  interval
```

Here the derivative of the difference is $x \sin x$, which is negative beyond $\pi$. The tactic cuts the range at $2$.

Both ends of a range are tried, the lower one first, and a bound $|a| \le b$ is taken as the two comparisons of $a$ and of $-a$ with $b$. This doesn't prove a comparison in two variables, or one whose sides meet inside the range, as $\log x \le x/e$ does at $x = e$. The theorems are [[FloatLib.Numerics.Interval.le_of_deriv_nonneg]] and [[FloatLib.Numerics.Interval.lt_of_deriv_pos]], with [[FloatLib.Numerics.Interval.le_of_deriv_nonpos]] and [[FloatLib.Numerics.Interval.lt_of_deriv_neg]] from an upper end.

### What about a goal that says something exists?

The negation of $\exists x,\ P(x)$ says something about every $x$, and that isn't a set of constraints. So for such a goal the tactic looks for a witness. It tries the real variables in sight, also shifted by one, and then rational values, the simplest first: zero, the powers of two from $2^{-20}$ to $2^{20}$ with both signs, and the numbers that the statement itself names, each with its two neighbours at distance one and the mean of each two. So $5 < x \land x < 7$ finds $6$. It proves $P$ at the first value where its enclosures find it true. There's one limit. At a value above $2^{10}$ in size, a statement that takes the exponential of a number that large is passed over, because that enclosure is long.

```lean
example : ∃ x : ℝ, Real.cosh x > 2000000 := by
  interval

example : ∃ x y : ℝ, y + Real.log x < Real.log y := by
  interval
```

The first witness is $16$, and the second is the pair $(1/4, 1)$. A statement whose witnesses all lie outside the list, such as $\tan x > 651800$, isn't proved this way. Give the witness yourself and let `interval` prove the rest.

### Which hints can you give?

Every hint is checked by the kernel like the rest, so a wrong one costs time and nothing else. `(cut := [(x, 0), (y, 1 / 2)])` cuts the box at these points first. `(ball := [(x, 0, 1 / 4)])` names a box around a point, which is decided by the forms around its center, and `(form := …)` states the upper triangle of the matrix yourself. `(box := [(x, -2, 2)])` states bounds that follow from the constraints, and `(facts := [sq_nonneg (x - y)])` gives terms to every step that calls `linarith` or `nlinarith`. `(depth := 60)` and `(boxes := 100000)` raise the limits of the search, which are 40 cuts along a branch and 20000 boxes, and `(maxHeartbeats := 400000)` the limit of the kernel check, which is 20000 and 200 more for each box of the certificate.

```lean
example (x y : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) (hy : -1 ≤ y) (hy' : y ≤ 1)
    (h0 : x ^ 2 + y ^ 2 > 0) (h : x ^ 2 * Real.exp (2 * y) + y ^ 2 ≤ 0) : False := by
  interval (ball := [(x, 0, 1 / 2), (y, 0, 1 / 2)]) (form := [[Real.exp (2 * y), 0], [1]])

example (x y : ℝ) (h : x ^ 2 + y ^ 2 + Real.cos x ≤ 2) (h' : x * y > 4) : False := by
  interval (box := [(x, -2, 2), (y, -2, 2)]) (facts := [sq_nonneg x, sq_nonneg y])
```

When the tactic fails, the message names the box where the search stopped, the constraints that are undecided there with the enclosures that fail to exclude them, and the limit that stopped it. You get the same report when the declaration is about to run out of heartbeats: the tactic stops while there is still time to say where it stands. If every constraint holds on a whole box, it says so: the set isn't empty and the goal is false as stated, unless some hypothesis was not read as a constraint, in which case the message lists those. A failed call leaves the goal as it was, and `set_option trace.interval.constraints true` lists the steps it took.

### How much does `interval` prove on other projects' goals?

We measured on goals we didn't write for this engine: the tests of `interval` in FloatLib, of `dyadic_interval` in Mathlib, of `cega` in SymLean, and the IEANTN floors, each goal as its own file with one tactic call.

| Corpus | Goals | `interval` | Mathlib `dyadic_interval` | SymLean `cega` |
| --- | ---: | ---: | ---: | ---: |
| FloatLib tests of `interval` | 52 | 46 | 1 | 13 |
| Mathlib tests of `dyadic_interval` | 56 | 55 | 56 | 34 |
| SymLean tests of `cega` | 56 | 55 | 9 | 56 |
| IEANTN floors | 5 | 5 | 0 | 5 |
| all | 169 | 161 | 66 | 108 |

A count for a corpus says what an engine did on that corpus, not what it does on all goals. Why doesn't `interval` close everything? One Mathlib test has a hypothesis in Mathlib's own interval type, and six FloatLib tests need definitions of their test module, so no engine closes those six as single files. `dyadic_interval` and `cega` each close all of their own tests and far fewer of the others', which is what you'd expect of tests written for one tool :) A closed goal takes 6.0 seconds at the median, most of it the imports of the file.

## How to get an error bound for floating-point code

Now let's put the rounding back in. A program on `Binary32` values rounds after every operation, so
its result drifts from the real expression it was written from, and `roundoff` proves by how much.
It reads the computation as written on configured values, FloatLib's executable float types,
`Binary32` among them. For each operation it takes the rounding theorem of the capability behind it,
the implementation FloatLib picked for that operation. For `+` that theorem is
`ExecFloat.Binary.add_rounding`.

The tactic combines these local errors into a bound against a *reference*: the corresponding
computation in exact real arithmetic on the decoded inputs, with the exceptions described below.
Each operation contributes a local rounding error and propagates errors from its operands.
The composition theorems bound the resulting error of the complete expression.

The bound compares the computed value with the reference. It's absolute, $|x-x_0|\le\beta$, or
mixed, where `MixedError x x₀ r a` means $|x-x_0|\le r|x_0|+a$, a relative part plus an absolute
part. Finiteness (no infinity or NaN), exact decoded values and signs are proved the same way. The
tactic needs its own import, `FloatLib.Tactic.Roundoff`, as in
this example from the library's tests:

```lean standalone
import FloatLib
import FloatLib.Tactic.Roundoff

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- A finite fused multiply-add of the descriptor model rounds once. -/
theorem fma_error (x y z : Model format) (hformat : format.isIEEE = true)
    (hresult : Model.isFinite (Model.fma x y z) = true) :
    |Model.toReal (Model.fma x y z) - (Model.toReal x * Model.toReal y + Model.toReal z)| ≤
      Model.halfUlpAt format (Model.toReal x * Model.toReal y + Model.toReal z) := by
  roundoff

/-- The dot product of two functions on `Fin n`, from zero. -/
def dot {n : Nat} (x y : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => s + x j * y j) 0

roundoff mixed theorem dot_mixedError :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)

#check @dot_mixedError
-- @dot_mixedError : ∀ {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
--   [inst : ExecFloat.ModelCodec plan (Model format) code]
--   [inst_1 : ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] {n : ℕ} (x y : Fin n → Value),
--   format.isIEEE = true →
--     have step := fun s j => s + x j * y j;
--     have referenceStep := fun reference value =>
--       reference + ExecFloat.Binary.toReal (x value) * ExecFloat.Binary.toReal (y value);
--     have relativeStep := fun accumulator reference relative absolute value => Model.unitRoundoffAt format;
--     have absoluteStep := fun accumulator reference relative absolute value =>
--       (1 + Model.unitRoundoffAt format) *
--         (relative * |reference| + absolute +
--           (Model.unitRoundoffAt format * |ExecFloat.Binary.toReal (x value) * ExecFloat.Binary.toReal (y value)| +
--             Model.underflowErrorAt format));
--     have relativeError := List.foldRelative step referenceStep relativeStep absoluteStep 0 0 0 0 (List.finRange n);
--     have absoluteError := List.foldAbsolute step referenceStep relativeStep absoluteStep 0 0 0 0 (List.finRange n);
--     have output := dot x y;
--     have reference := List.foldl referenceStep 0 (List.finRange n);
--     List.AllSteps (List.mixedFoldStep step referenceStep relativeStep absoluteStep)
--         (fun state value =>
--           ExecFloat.Binary.isFinite (x value) = true ∧
--             ExecFloat.Binary.isFinite (y value) = true ∧
--               |ExecFloat.Binary.toReal (x value) * ExecFloat.Binary.toReal (y value)| ≤
--                   (Model.posMaxFinite format).toReal ∧
--                 |state.2.1 + ExecFloat.Binary.toReal (x value) * ExecFloat.Binary.toReal (y value)| +
--                     (state.2.2.1 * |state.2.1| + state.2.2.2 +
--                       (Model.unitRoundoffAt format *
--                           |ExecFloat.Binary.toReal (x value) * ExecFloat.Binary.toReal (y value)| +
--                         Model.underflowErrorAt format)) ≤
--                   (Model.posMaxFinite format).toReal)
--         (0, 0, 0, 0) (List.finRange n) →
--       ExecFloat.Binary.isFinite output = true ∧
--         MixedError (ExecFloat.Binary.toReal output) reference relativeError absoluteError

/-- The generated bound in closed form. -/
example := fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) hvalid =>
  List.abs_sub_le_of_sumFold (Model.unitRoundoffAt format) (Model.unitRoundoffAt_pos _).le _ _
    (fun j : Fin n => Model.unitRoundoffAt format *
      |ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)| +
        Model.underflowErrorAt format)
    (fun _ => add_nonneg (mul_nonneg (Model.unitRoundoffAt_pos _).le (abs_nonneg _))
      (Model.underflowErrorAt_pos _).le) _ _ (dot_mixedError x y hformat hvalid).2

/-- The range conditions follow from bounds on the terms. -/
example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) (b : ℝ)
    (hx : ∀ j, ExecFloat.Binary.isFinite (x j) = true)
    (hy : ∀ j, ExecFloat.Binary.isFinite (y j) = true)
    (hb : ∀ j, |ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)| ≤ b)
    (hgrowth : (1 + Model.unitRoundoffAt format) ^ (n + 1) ≤ 2)
    (hrange : 2 * (n + 1) * (b + Model.underflowErrorAt format) ≤
      Model.toReal (Model.posMaxFinite format)) :
    ExecFloat.Binary.isFinite (dot x y) = true :=
  (dot_mixedError x y hformat ((List.AllSteps.of_forall _ _ _ _ fun _ j => hx j).and
    ((List.AllSteps.of_forall _ _ _ _ fun _ j => hy j).and
      (List.allSteps_sumFold_of_abs_le _ _ b _ (Model.unitRoundoffAt_pos _).le
        (Model.underflowErrorAt_pos _).le _ _ _
        (fun _ => add_nonneg (mul_nonneg (Model.unitRoundoffAt_pos _).le (abs_nonneg _))
          (Model.underflowErrorAt_pos _).le) _ _
        (fun j _ => hb j) (fun _ _ => le_rfl) (by simpa using hgrowth)
        (by simpa using hrange))))).1
```

The first theorem states its own goal, a model fused multiply-add within
[[FloatLib.Floats.Formats.BinaryInterchange.Model.halfUlpAt]] of $xy+z$, which is half an ulp, half
the gap between neighbouring floats at that value. Plain `roundoff` closes it from `hresult` with
the one rounding the operation performs.

With the dot product it gets more interesting, because we write only the value we want bounded, and
the tactic writes the theorem. `roundoff mixed theorem` analyzes the loop over `Fin n` once, for a
symbolic accumulator, a running sum of unknown value, and lifts that step through the traversal with
`List.fold_mixedError`. So nothing is unrolled (written out step by step), and the statement holds
at every length, for every IEEE descriptor (the `FloatFormat` record of a format's widths), storage
plan and codec.

### How to read the generated theorem

Let's read what `#check` prints. Its reference, `List.foldl referenceStep 0 (List.finRange n)`, is
the exact dot product of the decoded entries. Each addition gets relative error $u$, the unit
roundoff `Model.unitRoundoffAt format`. Each step then turns the previous relative part $r$ and
absolute part $a$ into the absolute part $(1+u)(r\,|\mathit{ref}|+a+u\,|x_jy_j|+\eta)$, where
$\eta$, `Model.underflowErrorAt format`, is half the spacing of the subnormals, the tiny evenly
spaced numbers next to zero.

The premise, what you prove to use the theorem, is a `List.AllSteps` condition on the states the
loop visits:

- both entries finite,
- the product at most the largest finite value $\Omega$,
- the next partial sum plus its budget at most $\Omega$.

In return you get a finite output and its mixed bound.

### How to turn the bound into a number

The two examples after the `#check` put the statement to work. `List.abs_sub_le_of_sumFold` turns the
recurrence into the closed form
$$
\Bigl|x-\sum_j p_j\Bigr|\le\bigl((1+u)^n-1\bigr)\sum_j|p_j|+(1+u)^n\sum_j\bigl(u\,|p_j|+\eta\bigr),
\qquad p_j=x_jy_j.
$$
In binary32, $u=2^{-24}$ and $\eta=2^{-150}$. For four products of magnitude at most one, the first
term is about $4u\cdot4=16u$ and the second about $4u+4\eta$, so the computed dot product lands
within about $20u\approx1.19\times10^{-6}$ of the exact one. That's a little above the textbook bound
$\gamma_4\sum_j|p_j|\approx16u$ [@higham2002], because the loop charges every addition the same
relative error, including the first one from zero, which is exact. The closed form that
`roundoff closed theorem` generates, in the section on backward error below, weights each product
by its own roundings and comes to about $14u$.

In the second example the premise comes from four plain conditions: finite entries, $|p_j|\le b$,
$(1+u)^{n+1}\le2$, and $2(n+1)(b+\eta)\le\Omega$. In binary32 the growth condition holds while
$n+1\le\ln2/\ln(1+u)$, up to 11,629,079 terms, and with $b=1$ and $n=4$ the last condition asks for
$10(1+2^{-150})\le\Omega\approx3.40\times10^{38}$, which is hardly asking at all.

### What changes when storage is narrower than arithmetic?

"A bfloat16 dot product" can mean two different programs. One rounds every product and every partial sum to bfloat16. Another reads bfloat16 entries, widens them to binary32, and multiplies and accumulates there. `roundoff` can't guess which one you mean, so you write the casts:

```lean standalone
import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Rounding
import FloatLib.Tactic.Roundoff

open FloatLib.Floats.Formats.BinaryInterchange

roundoff mixed theorem stored_dot_error :=
  fun (xs : List (Model FloatFormat.bfloat16 × Model FloatFormat.bfloat16)) =>
    Model.toReal (xs.foldl (fun acc pair => Model.add acc
      (Model.mul (Model.cast _ FloatFormat.binary32 pair.1)
        (Model.cast _ FloatFormat.binary32 pair.2))) (Model.zero _ false))
```

Here only the additions round. Widening a bfloat16 value to binary32 introduces no error when the result is finite. And the product is exact too: bfloat16 has eight bits of precision, so the product of two of its significands needs at most sixteen, and binary32 has twenty-four. It's like multiplying two two-digit numbers on a calculator with eight digits, where nothing can be cut off. So the generated bound drops the product's allowance, and the factor that repeats in the accumulation is $1+2^{-24}$ where the all-bfloat16 program has $1+2^{-8}$.

There are four rules behind this, each stated once for all descriptors:

- **Widening casts are exact** when the destination's grid contains the source's and the result is finite.
- **A product is exact** when the two source precisions sum to at most the destination's, the destination's subnormal grid contains both source grids, the product is finite, and the exact product is zero or in the destination's normal range ([[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_mul_cast_exact]]). For binary32 products the precision and grid conditions hold with two bfloat16, binary16, E4M3, E5M2, E2M1, E2M3 or E3M2 values.
- **Narrowing casts round once**, with the destination's budget $(u,\eta)$, plus a term for saturation where the destination saturates ([[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_rounding_policy]]). The bound is written out below.
- **Scaling by a power of two is exact** when the input and output are finite and either the shift is nonnegative, the input is zero, or the scaled value stays normal.

With $M$ for the destination's largest finite magnitude, the narrowing bound is

$$|\operatorname{cast}(x)-x|\le u|x|+\eta+\max(0,|x|-M).$$

A fused multiply-add into the wide format keeps the one-rounding rule it already had, and a different reduction tree needs a theorem for that tree.

Don't skip the conditions that depend on the values. Take the smallest positive bfloat16 subnormal, $2^{-133}$. Both operands widen exactly, but their square is $2^{-266}$, far below binary32's smallest subnormal $2^{-149}$, so the binary32 product is zero. Precision alone can't justify an exact product, which is why the rule asks for the range. Saturation is the same kind of trap on the other side: casting binary32's exactly represented $1000$ to E2M1 returns $6$, its largest finite value. That result is finite and its error is $994$, and the last term of the narrowing bound is there to say so. A negative shift can lose bits as well. Scaling binary32's smallest subnormal by $2^{-1}$ gives zero.

Two things to keep in mind when you read a generated bound. If a hidden activation is stored back in bfloat16 or FP8, that cast must appear in the program, and its error survives into the next layer: widening it again doesn't undo it. And the bounds start from the decoded stored inputs. To include the quantization of master weights, put those casts in the analyzed program or supply their input-error bounds. What the theorem accounts for is the schedule you wrote, and connecting a device kernel to that schedule is a separate obligation.

## What else can `roundoff` read?

Literals go through the same analysis, exact when the format represents them, and so do integer
conversions, rounding to integral values and the C maximum loop `if m < x then x else m`. FloatLib's
correctly rounded exponential, logarithm, `expm1`, `logp1`, `expMul` and `expm1x` each
contribute one rounding at their real result on an IEEE descriptor, while sine, cosine and the
hyperbolic functions use FloatLib's rational enclosures. A `match`, a program on Lean's native
floats and the function `expm1x` have their own sections below. Loops can run over lists, arrays, vectors and matrices, and a
loop whose state is a pair or a nondependent record carries one relation for all its components.

Say such a loop tests a rounded component, like a sum that stops once an addition leaves it
unchanged. A step's condition can ask that the rounded test agree with the same test on the exact
references, and the theorem covers the runs where they agree. For that sum, those are the runs that
never stall, since an exact sum doesn't stall on a nonzero entry. So the bound says nothing about a
stop that rounding caused.

## How to get an absolute bound, or one inside a proof

If you'd rather have an absolute bound than a mixed one, `roundoff theorem` states that instead, and
for the dot product its premise asks every visited partial sum and product to be finite. Inside a
proof you don't need a named theorem:
`have bound := by roundoff (ExecFloat.Binary.toReal (program x))` infers a bound once its range
premises are provable. `[roundoff_rule]` registers a bound of your own, and another library
registers its containers with `@[roundoff_extension]`. Rules that match the same computation
are tried in the order in which they were registered.

## What does `roundoff` ask you to prove?

The arithmetic rounding rules hold for IEEE descriptors; the cast rules also cover the other
encoding policies described above. The tactic proves the required descriptor conditions from the
context or leaves them as goals. The rules need finite
results, division a finite divisor and square root a finite operand in its domain, and whatever the
tactic can't prove comes back as a premise or a goal. For a loop the budget is a symbolic
recurrence, a step-by-step formula, so comparing it with a numerical tolerance of your own is a
separate step, like the closed form above.

**Note:** The operator rules are the nearest-even rounding theorems of the ordinary operators. A
sum, a difference, a product or a fused multiply-add called with a rounding mode, such as
`ExecFloat.Binary.add x y (mode := .up)`, has its own rule, with the unit roundoff of that mode,
and so has the rounding of a real, `Model.roundAt format x mode`. The section on tightness below
shows one. A quotient or a square root with a mode other than the default has no rule, so
`roundoff` asks you for a bound on those.

## Which reference does the bound use?

Here are the cases we set aside, where the reference isn't the program redone in exact arithmetic.
Some choices stay in the reference just as the program makes them. If your program reads a stored
container at an index computed from rounded values, the reference keeps that choice, and a branch
whose condition compares computed values takes the branch the program takes. An exact test of a loop
component can inherit such a choice, while an agreement test that depends on it is rejected.

The reference also reads the program as Lean states it. A variable that a `have` introduces, with no
visible definition or supplied error bound, is an input, whatever computed it, and so is an entry
that an input option's own getter returns. A call of a function the program takes as an argument is
a different case. When the analysis has no rule for that function's real model, the reference
applies the model to the decoded computed argument, as in `g (toReal (x * y))`, so the statement
shows that argument and the bound leaves out its rounding.

## What have you proved when `roundoff` succeeds?

With a tactic writing theorems for you, it's a fair question. Part of the answer is easy:

- What `roundoff` produces is an ordinary Lean proof, and the kernel checks it like any other.
- Our axiom audit loads the analysis and accepts only propositional extensionality, quotient
  soundness and choice. An axiom is a statement Lean accepts without proof.

What neither of them shows is that the reference in the statement is the exact computation the
program means. The analysis does check three parts of that, two of them about reads another library
registers:

1. A read like that counts as reading a stored entry only when it uses the dictionaries (type class
   instances) of Lean's own list, array and vector getters or has a checked selection equality to
   such a read.
2. A storage class that such a read trusts has to come with laws that pin each of its methods to the
   read's observers and use no constant holding a number. Index data is data such as lengths,
   offsets and indices, which computes no numerical value, and the storage class's dictionaries
   count as index data only as inputs, local definitions of accepted ones, or constants whose
   optional decisions of equality reduce to `none` or `some`.
3. The third plays it safe. If your statement has a type parameter, a value of that type counts as
   possibly numerical, unless one of those storage classes supplies its type.

The rest you take on trust:

- You're trusting that the opaque constants and axioms of Lean's own library, other than
  `Classical.choice`, hold no number when their types hold none.
- FloatLib's IEEE comparisons on configured values compare the decoded values, while their decidable
  equality compares stored words, so the two zeros differ and a NaN equals itself.
- A configured type's codec and storage plan define what its stored words mean.
- The observers a read registers mean what they say about its storage.
- The types a storage class supplies, such as a tensor's buffer, are assumed to stay abstract,
  meaning nothing tests their identity to produce data or transports their values to expose another
  representation.
- Index data isn't checked inside the types it mentions, so you're also trusting that a type there
  isn't chosen by a rounded value, as `if x * x == x then Unit else Empty` would be.

Inside index data, though, a function over numerical values is checked wherever it travels, in a
list, a record or a generic helper, and applied only at plain index data.

## Backward error

A forward bound says how far the computed value is from the exact one. A backward-error statement turns the question around: for which inputs is the computed value exactly right? If those inputs are within a few rounding errors of yours, the program has done as well as your data allows. `roundoff (backward := true) theorem` writes and proves that statement from the same code, and `roundoff closed theorem` turns it into a forward bound in closed form:

```lean standalone
import FloatLib
import FloatLib.Tactic.Roundoff

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- The dot product of two functions on `Fin n`, from zero. -/
def dot {n : Nat} (x y : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => s + x j * y j) 0

roundoff (backward := true) theorem dot_backward :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)

#check @dot_backward
-- @dot_backward : ∀ {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
--   [inst : ExecFloat.ModelCodec plan (Model format) code]
--   [inst_1 : ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] {n : ℕ} (x y : Fin n → Value),
--   format.isIEEE = true →
--     ExecFloat.Binary.isFinite (dot x y) = true →
--       ∃ δx,
--         (∀ (j : Fin n), |δx j| ≤ (1 + Model.unitRoundoffAt format) ^ (n - 1 - ↑j + 2) - 1) ∧
--           |ExecFloat.Binary.toReal (dot x y) -
--                 List.foldl (fun s j => s + ExecFloat.Binary.toReal (x j) * (1 + δx j) * ExecFloat.Binary.toReal (y j)) 0
--                   (List.finRange n)| ≤
--             Model.underflowErrorAt format * (1 + Model.unitRoundoffAt format) *
--               ∑ k ∈ Finset.range n, (1 + Model.unitRoundoffAt format) ^ k

roundoff closed theorem dot_closed :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)

#check @dot_closed
-- @dot_closed : ∀ {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
--   [inst : ExecFloat.ModelCodec plan (Model format) code]
--   [inst_1 : ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] {n : ℕ} (x y : Fin n → Value),
--   format.isIEEE = true →
--     ExecFloat.Binary.isFinite (dot x y) = true →
--       |ExecFloat.Binary.toReal (dot x y) -
--             List.foldl (fun s j => s + ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)) 0
--               (List.finRange n)| ≤
--         ∑ j,
--             |ExecFloat.Binary.toReal (x j)| * ((1 + Model.unitRoundoffAt format) ^ (n - 1 - ↑j + 2) - 1) *
--               |ExecFloat.Binary.toReal (y j)| +
--           Model.underflowErrorAt format * (1 + Model.unitRoundoffAt format) *
--             ∑ k ∈ Finset.range n, (1 + Model.unitRoundoffAt format) ^ k
```

### How to read the backward-error theorem

`#check @dot_backward` prints one statement for every length, every IEEE descriptor and every storage plan. It says there is a perturbation `δx j` for each entry of `x`, such that the computed dot product is the exact dot product of the entries `x j * (1 + δx j)` with `y`, up to the term on its last two lines.

Each `δx j` is bounded by a count of the roundings that entry went through. Its product rounds once, and so does each addition from its own on. One rounding multiplies by a factor within $u$ of one, so $k$ roundings give $(1+u)^k-1$, here with $k=n-1-j+2$. The first entry takes $n+1$ roundings and the last one two. Higham's bound for the same loop is $\gamma_n=nu/(1-nu)$ [@higham2002]. We have $n+1$ where he has $n$ because the analysis charges the first addition, to an exact zero, a rounding it doesn't make.

The last term is there because a product can underflow. A product in the subnormal range is off by up to $\eta$, and no small relative change of `x j` accounts for that. So the statement is an equality up to about $n\eta$, which Higham calls mixed forward-backward stability. A program whose operations can't underflow gets a plain equality. And look at the premise: the forward theorem asks for a range condition at every step of the loop, and this one asks only that the result is finite, because a finite sum has finite terms and a finite product has finite factors.

### How to choose the perturbed inputs

By default every input may carry a perturbation, and a product gives its rounding to its left factor. `(perturb := [y])` names the inputs that may be perturbed, and `(factor := right)` gives the rounding of every product to its right factor. Sometimes the analysis has to choose for you. In Horner's rule `(a * x + b) * x + c` the point `x` is read twice, and the two reads would need different perturbations. So the analysis leaves `x` alone and moves every rounding onto the coefficients, which is the classical result: `a` takes four roundings, `b` three and `c` one. `roundoff (backward := true) mixed theorem` states the forward mixed bound and the backward statement together.

What does the mode read? Loops over lists, arrays, vectors, `Fin n` and matrices, squares, branches, a maximum or minimum of finite values, the mixed-precision rules and the fused multiply-add. It refuses when a rounding has nowhere to go, and the message names the subterm and the reason. It never states a weaker theorem instead. A literal in a rounded sum (`x + 1`), an input read with roundings that differ (`x * x + x`), cancellation between computed intermediates, a compensated sum and a function such as the exponential are refused, and each message suggests `roundoff mixed theorem`, which gives a forward bound for all of these.

### How to get the forward bound in closed form

A backward statement gives a forward bound: perturbing `x j` by `δx j` changes the product `x j * y j` by at most $|\delta x_j|\,|x_jy_j|$. `dot_closed` above states the result of that argument directly,

$$
\Bigl|\hat s-\sum_j x_jy_j\Bigr|\le\sum_j\bigl((1+u)^{n-1-j+2}-1\bigr)|x_jy_j|
+\eta(1+u)\sum_{k<n}(1+u)^k .
$$

Each product is weighted by the bound of its own perturbation, not by the largest one. For four products of magnitude at most one, that is about $(5+4+3+2)u=14u$, where the closed form of the recurrence gives $20u$. Each read is bounded by itself here, so `x * x + x`, `x + 1` and a softmax weight all have closed forward bounds although none has a backward-error form.

Which forward theorem should you use? The recurrence of `roundoff mixed theorem` follows the partial sums, so it sees cancellation, and it can be relative. By contrast, the closed form reads only the magnitudes of the terms. For positive terms the two agree. For 4,096 random terms of mixed signs in binary32, our benchmark script measured a recurrence bound of 120 times the actual error and a closed form of 9,470 times it. These numbers are the script's, not Lean's. `#roundoff_shape name` reads the mixed bound of a generated theorem and says whether it is relative, which is a reading of the statement, not a theorem about it.

### How does this compare with earlier work?

The statements are the ones in Higham's book [@higham2002], where each algorithm gets its own proof by hand. LAProof [@laproof2023] is a Coq library with hand-written proofs of backward and mixed bounds, underflow included, for inner products and matrix operations. Bean [@bean2025] is a typed first-order language in which a program's type is its backward error bound, and a variable is not used twice. The tool eggshel [@eggshel2026] works with a more general definition of backward stability and searches for a proof within a syntactic class of programs.

What is new here is that the program is ordinary Lean code over FloatLib's executable formats, the code you run, and each theorem is a Lean proof that the kernel checks against the model of the arithmetic. No soundness theorem of a type system or of a search stands between the program and the bound. One statement covers every IEEE descriptor, with underflow in it, loops have symbolic length, and each entry gets the bound of its own position in place of one $\gamma_n$ for all. What it doesn't do: compensated sums and functions such as the exponential have no backward theorem, a whole matrix product is stated entry by entry or row by row, and the definition of backward error is the classical one.

## How does `roundoff` read a `match`, a branch or a native float?

Code that depends on a size or on a case of an inductive type has a `match` in it, and each alternative is a different computation with its own error. `roundoff` analyzes the alternatives one by one, each under the facts its patterns give. In the forward theorem the reference, the budgets and the premise are each the `match` of what the alternatives have. Closed and backward theorems are stated the other way round: the statement is the `match` of the statements of the alternatives, each with its own premises and perturbations. Three things are refused, each with a message that names the `match`: a pattern that binds part of a value computed from floating-point values, a pattern that takes a number apart, and overlapping patterns in the closed and backward modes. The forward mode handles overlapping patterns.

A program on Lean's own `Float32` or `Float` is observed through `ExecFloat.Binary.ofFloat32` or `ExecFloat.Binary.ofFloat`, which read the same value as a `Binary32` or a `Binary64`. `roundoff` moves that import inward by proved laws of the native operations: addition, subtraction, multiplication, division, square root, negation, natural-number literals and the round trips. What you get is the theorem of the same program on `Binary32`, in all four modes:

```lean standalone
import FloatLib
import FloatLib.Tactic.Roundoff

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- `a x + y` on Lean's native binary32. -/
def axpy (a x y : Float32) : Float32 := a * x + y

roundoff mixed theorem axpy_mixedError :=
  fun (a x y : Float32) =>
    ExecFloat.Binary.toReal (ExecFloat.Binary.ofFloat32 (axpy a x y) : Binary32)
```

What do these theorems rest on? Each law is a theorem about Lean's logical model of `Float32` and `Float`. That the compiled code and the processor compute what the model says is trusted, and [TRUST.md](https://github.com/lean-dojo/FloatLib/blob/main/TRUST.md) says so. Elementary functions of the native types are different: `Float32.exp` calls the host's C library, which promises no rounding, so there is no law for it and `roundoff` refuses it with that reason. An import into another format, such as a `Float32` read as a `Binary64`, and the native 16-bit carriers have no rule yet.

## How to check that a bound is useful

A proved bound can still be useless. If it is larger than the value it bounds, it doesn't even tell you the sign of the result, and that is what cancellation does to a bound. `#roundoff_check` runs the program at inputs, evaluates the reference and the bound of a generated theorem there, and warns when the bound is at least the magnitude of the reference. Here is the gradient of cross-entropy with respect to the target logit, written two ways:

```lean standalone
import FloatLib
import FloatLib.Tactic.Roundoff

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- The target gradient of cross-entropy as `1 / (1 + s) - 1`. -/
roundoff mixed theorem subtracted :=
  fun (s : Value) (hformat : format.isIEEE = true) (hs : 0 ≤ ExecFloat.Binary.toReal s) =>
    ExecFloat.Binary.toReal (1 / (1 + s) - 1)

/-- The same gradient as `-(s / (1 + s))`. -/
roundoff mixed theorem divided :=
  fun (s : Value) (hformat : format.isIEEE = true) (hs : 0 ≤ ExecFloat.Binary.toReal s) =>
    ExecFloat.Binary.toReal (-(s / (1 + s)))

/--
warning: evaluated at 1 input
  computed value  0
  reference       -5.9604641e-8 (exact)
  error           5.960e-8
  bound           1.192e-7 (bound / error = 2.00)
  premises        3 hold, 0 do not, 0 not evaluated
  The bound is at least the magnitude 5.960e-8 of the reference: there the theorem does not fix the sign of the result. The computation cancels, or the bound is not relative to its result.
  This is a report at the inputs above, not a proof.
-/
#guard_msgs (whitespace := lax) in
#roundoff_check subtracted (5.9604645e-8 : Binary32)

#roundoff_check divided (5.9604645e-8 : Binary32)
-- evaluated at 1 input
--   computed value  -5.9604645e-8
--   reference       -5.9604641e-8 (exact)
--   error           3.553e-15
--   bound           7.105e-15 (bound / error = 2.00)
--   premises        3 hold, 0 do not, 0 not evaluated
--   bound / |reference| = 1.19e-7: the bound fixes the sign of the result.
--   This is a report at the inputs above, not a proof.
```

At $s=2^{-24}$ in binary32 the sum `1 + s` rounds to one, and the first form computes zero. You give the inputs as arguments of the theorem, and whatever you leave out is sampled. This command reports and nothing more: it proves nothing, no theorem depends on it, and a sample that looks fine says nothing about the inputs you didn't try. It runs the compiled program, so in a file that begins with `module` the functions your program calls need a `meta import` too.

## How does `roundoff` keep a bound tight?

A rounding that doesn't happen shouldn't be charged, and one that does shouldn't be charged more than it costs. Here is what the analysis recognizes.

Two values within a factor of two of each other subtract exactly (Sterbenz) [@sterbenz1974]. `roundoff` recognizes that from your hypotheses, whether they are the two bounds `y / 2 ≤ x` and `x ≤ 2 * y` or interval facts such as `x ∈ Set.Icc 1 2` and `1 ≤ y ∧ y ≤ 2`, and the subtraction then costs nothing in the forward, the closed and the backward mode. The only rounding left in `(x - y) * z` is that of the product:

```lean standalone
import FloatLib
import FloatLib.Tactic.Roundoff

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- A difference of two values within a factor of two of each other, scaled. -/
roundoff mixed theorem scaledDifference :=
  fun (x y z : Value) (hformat : format.isIEEE = true)
      (hlow : ExecFloat.Binary.toReal y / 2 ≤ ExecFloat.Binary.toReal x)
      (hhigh : ExecFloat.Binary.toReal x ≤ 2 * ExecFloat.Binary.toReal y) =>
    ExecFloat.Binary.toReal ((x - y) * z)

#check @scaledDifference
-- @scaledDifference : ∀ {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
--   [inst : ExecFloat.ModelCodec plan (Model format) code]
--   [inst_1 : ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] (x y z : Value),
--   format.isIEEE = true →
--     ExecFloat.Binary.toReal y / 2 ≤ ExecFloat.Binary.toReal x →
--       ExecFloat.Binary.toReal x ≤ 2 * ExecFloat.Binary.toReal y →
--         have output := (x - y) * z;
--         have reference := (ExecFloat.Binary.toReal x - ExecFloat.Binary.toReal y) * ExecFloat.Binary.toReal z;
--         ExecFloat.Binary.isFinite x = true ∧
--             ExecFloat.Binary.isFinite y = true ∧
--               ExecFloat.Binary.isFinite z = true ∧ |reference| ≤ (Model.posMaxFinite format).toReal →
--           ExecFloat.Binary.isFinite output = true ∧
--             MixedError (ExecFloat.Binary.toReal output) reference (Model.unitRoundoffAt format)
--               (Model.underflowErrorAt format)

/-- The lower endpoint of `x * y + z`: both operations round toward negative infinity. -/
def lowerAffine (x y z : Value) : Value :=
  ExecFloat.Binary.add (ExecFloat.Binary.mul x y (mode := .down)) z (mode := .down)

roundoff mixed theorem lowerAffine_mixed :=
  fun (x y z : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (lowerAffine x y z)
```

A rounding to nearest misses by at most half a unit in the last place and a directed rounding by at most a whole one. So each rounding attribute has its own unit roundoff: `Model.unitRoundoffIn format mode` is `u` for the two nearest modes and `2 u` for the four directed ones. This covers the rounding of a real, `Model.roundAt`, and a sum, a difference, a product or a fused multiply-add called with a mode, as in `lowerAffine` above. Directed rounding can return the largest finite magnitude after overflow. The directed rules therefore require the exact result to be in range. A quotient or a square root with a mode other than the default has no rule yet.

A mixed theorem gives you the computed value in an interval centered at the reference, $x_0\pm(r|x_0|+a)$. It also gives the exact value in an interval centered at the computed one, $x\pm(r|x|+a)/(1-r)$ (`MixedError.mem_Icc_computed`), which reads only quantities your program has.

And for long loops in short formats there are sharper constants than the classical $(1+u)^{n-1}-1$. Rump proved that $(n-1)u$ alone is enough for a sum of $n$ terms [@rump2012], and Jeannerod and Rump that $nu$ is enough for an inner product when no exact product is subnormal [@jeannerodRump2013] [@jeannerodRump2018]. FloatLib's `Model.abs_toReal_foldl_add_sub_le` and `Model.abs_toReal_foldl_add_mul_sub_le` cover left-to-right accumulation of any length in an IEEE format. Both require a seed of real value zero and a finite final result. The inner-product bound also requires each exact product to be zero or in the normal range. The same theorem names under `ExecFloat.Binary` apply to configured values. For 1,024 terms at eight bits of precision the linear constant is 13 times tighter than the power.

What did the benchmark script measure, as bound over actual error? For a scaled difference of two values within a factor of two, the mixed bound is 3.05 times the error. For the lower endpoint of `x * y + z` with both operations rounded downward, the bound is 3.4 times the error in the median, and the computed endpoint was below the exact value in every trial. One thing isn't done: the first addition of a loop, to an exact zero, is still charged a rounding, which costs up to a third at length 4 and nothing visible from length 256 on. These numbers are the script's, not Lean's.

## How to compute `exp x - 1 - x`

Some stable formulas need the exponential without the first two terms of its series. A relative
entropy is one: with $s_i=\log(q_i/p_i)$,

$$\sum_i p_i\log\frac{p_i}{q_i}=\sum_i p_i\,(e^{s_i}-1-s_i)$$

for two distributions, and every term on the right is nonnegative, where the terms on the left
cancel. Near zero the three terms of `exp x - 1 - x` cancel as well: at $x=2^{-30}$ in binary64
the expression evaluated operation by operation is exactly zero, and the value is about
$x^2/2$.

`ExecFloat.Binary.CorrectlyRounded.expm1x x` computes it with one rounding. The name is that of
R's package DPQ [@maechlerDPQ]; the GNU Scientific Library has the scaled form
`gsl_sf_exprel_2`, which is $2(e^x-1-x)/x^2$ [@gslSpecfunc]. Ours is correctly rounded at every
binary precision and in every rounding attribute: `(mode := .down)` and the others, nearest-even
if you don't say.

```lean standalone
import FloatLib
import FloatLib.Tactic.Roundoff

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics
open ExecFloat.Binary.CorrectlyRounded

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

roundoff mixed theorem expm1x_mixedError :=
  fun (x : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (expm1x x)

#check @expm1x_mixedError
-- @expm1x_mixedError : ∀ {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
--   [inst : ExecFloat.ModelCodec plan (Model format) code] (x : Value),
--   format.isIEEE = true →
--     have output := expm1x x;
--     have reference := Real.exp (ExecFloat.Binary.toReal x) - 1 - ExecFloat.Binary.toReal x;
--     ExecFloat.Binary.isFinite x = true ∧ |reference| < ↑(Model.Transcendentals.Certified.overflowThreshold format) →
--       output.isFinite = true ∧
--         MixedError output.toReal reference (Model.unitRoundoffAt format) (Model.underflowErrorAt format)

/-- `2⁻³⁰` in binary64. -/
def tiny : Binary64 := ExecFloat.Binary.ofRat (1 / 1073741824)

#eval (ExecFloat.Binary.toRat? (expm1x tiny)).map fun q => q * 2 ^ 113
-- some 4503599628768597

#eval ExecFloat.Binary.toRat? (exp tiny - 1 - tiny)
-- some 0
```

How is it rounded? Not by a series and a subtraction. The function compares $e^x$ exactly with
rational candidates, which the library already does for the exponential, and a comparison of
$e^x-1-x$ with $b$ is a comparison of $e^x$ with $b+1+x$. So nothing is ever subtracted in
floating point, and there is no cancellation at any argument. For the directed attributes, `AlgebraicRounding.roundDown` and `roundUp` use the shared
comparison-rounding engine to round a positive real downward and upward. The value is irrational for every nonzero
rational argument, so it never sits on a tie and both nearest attributes agree.

For an IEEE format and a finite input, `toReal_expm1x_of_isFinite` says that a finite result
below the overflow threshold is `Model.roundAt format (exp x - 1 - x) mode`, in each of the six
attributes, and `mixedError_toReal_expm1x` gives the mixed error with the unit roundoff of the
attribute. The result is never negative (`toReal_expm1x_nonneg`), so a sum of terms
`p i * expm1x (s i)` with nonnegative `p i` gets the relative step budget of a sum of
nonnegative terms. An inexact argument passes through the function by its derivative $e^t-1$,
which is small where the argument is (`MixedError.exp_sub_one_sub`).

`roundoff` has the contract of the function in every attribute. In the default one the exact
value is asked to be below the overflow threshold. A call such as `expm1x x (mode := .up)` asks
for a little more, an exact value at most the largest finite value, because an upward rounding
of a value between those two is `+∞` (`toReal_expm1x_eq_roundAt_mode`, `isFinite_expm1x_mode`).
It then gets the unit roundoff of its attribute, $2u$ for the directed ones.

`roundoff closed theorem` keeps the rounding of the function on its value. For one call it
proves $|e^x-1-x|\,u+\eta$. Spread over the three terms of the reference it would be
$(e^x+1+|x|)\,u+\eta$, which is about $2u$ however small the value is: at $x=2^{-10}$ that is
four million times larger. The same holds for `expm1`, whose reference $e^x-1$ has two terms.
An inexact argument passes through $e^s-1-s$ by the derivative here too, where the three terms
would let its whole error through twice.

The benchmark script compared the two forms of the relative entropy for 16 outcomes in binary32,
with the logarithms computed by the program. When `q` is within one part in a thousand of `p`,
the bound of the sum of `p * (log p - log q)` is 2.2 times the exact value, so that theorem
doesn't fix the sign, and at one part in ten thousand the computed value was zero or negative
in 39 of 100 trials. The bound of the sum of `p * expm1x (log q - log p)` is a thousandth and a
hundredth of the exact value there. The function decides every rounding by comparisons, with no
enclosure search before them, so it is slower than `exp` and `expm1`.

## Fresh stochastic rounding

Rounding to the nearest value can repeat the same error at every step of a sum. For example, repeated additions of a positive increment smaller than half the local spacing can all round back to the same accumulator. Stochastic rounding flips a biased coin instead. It chooses between the two neighbours of the exact value so that the error has mean zero.

Let's look at one rounding first. In bfloat16, $257/256$ sits between $1$ and $129/128$. Choosing each with probability $1/2$ gives errors $-1/256$ and $1/256$: the mean error is zero and its second moment is $1/65536$. In general, for neighbours $a<b$ and $a\le x\le b$, choose the upper one with probability $(x-a)/(b-a)$. Then the mean is $x$, and the variance is $(x-a)(b-x)\le (b-a)^2/4$. We prove this law once, for a two-point measure, and then connect it to the grids of the formats and to the rounder that runs.

### What can go wrong with a real random word?

That rounder compares `entropy % denominator` with a remainder. Uniform words in `0, …, M-1` give the ideal probabilities when the denominator divides `M`, and not otherwise. For a midpoint and three equally likely words, the residues modulo two are `0, 1, 0`, so this implementation chooses the upper endpoint with probability $2/3$, not $1/2$. So divisibility is a premise. `StochasticSafe` checks it together with the finite, unclipped endpoint conditions, and the theorems below carry it. A fixed entropy width need not satisfy it for every rational input: products of bfloat16 numbers need `M = 65536`, and with `M = 256` the runtime is biased.

Saturation, flushing, overflow and NaNs have results of their own. An unbiased finite-value theorem needs premises that exclude a changed or exceptional endpoint.

### How to get the bound of a whole loop

`roundoff` has a probability version, which follows a computation that consumes fresh entropy at each rounding. Here is a sum of any length, with the format and the entropy range left as parameters, followed by a three-step bfloat16 sum with 16 entropy bits per rounding:

```lean standalone
import FloatLib.Tactic.Roundoff.Stochastic
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.StochasticSupport

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model.Policy
open FloatLib.Numerics.Quantization.Stochastic

roundoff stochastic theorem fresh_sum :=
  fun (fmt : FloatFormat) (M : ℕ) (hM : 0 < M) (xs : ℕ → ℚ) (n : ℕ) ↦
    roundedSum (binaryRounder fmt M) xs 0 n

#check fresh_sum_mean
#check fresh_sum_second
#check fresh_sum_tail
#check fresh_sum_confidence

open MeasureTheory

private abbrev rounder := binaryRounder FloatFormat.bfloat16 65536
private abbrev support := binarySupport FloatFormat.bfloat16 65536

private def terms (k : ℕ) : ℚ := [129 / 128, 3 / 2, 131 / 128].getD k 0

private theorem terms_safe : SumSafe rounder terms 0 3 :=
  support.sum_safe terms 0 3 (by decide +kernel)

example :
    (∫ h, (roundedSum rounder terms 0 3 h : ℝ)
      ∂historyLaw (wordLaw 65536 (by decide)) 3) =
      ((0 : ℚ) : ℝ) + ∑ k ∈ Finset.range 3, (terms k : ℝ) :=
  fresh_sum_mean FloatFormat.bfloat16 65536 (by decide) terms 3 terms_safe

/-- The same sum with a number for its budget. -/
example :
    Certificate (historyLaw (wordLaw 65536 (by decide)) 3)
      (fun h ↦ (roundedSum rounder terms 0 3 h : ℝ))
      (((0 : ℚ) : ℝ) + ∑ k ∈ Finset.range 3, (terms k : ℝ))
      (Real.toNNReal ((3 / 16384 : ℚ) : ℝ)) :=
  support.sum_certificate (binaryRounder_law _ _ _) terms 0 3
    (fun _ ↦ 1 / 16384) (3 / 16384)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
```

You get four theorems about the actual rational output of `roundedSum` under `historyLaw (wordLaw M hM) n`, where each history supplies one independent, uniform word per addition. `fresh_sum_mean` equates the expected output with the exact sum. Its three siblings bound the centered second moment, the tail probability and the confidence radius. All four keep the premise `SumSafe`, which asks for the local admissibility condition at every reachable step and history.

For a concrete loop you don't prove `SumSafe` by hand. `binarySupport` lists the two possible outcomes of each rounding, `Rounder.Support.sum_safe` turns a kernel check of the listed accumulators into `SumSafe` for every history, and `Rounder.Support.sum_certificate` returns the certificate with a rational budget. That is the second half of the example.

### Why does the error of a long sum stay small?

A step's rounding cell can depend on every earlier rounding, so its error need not be independent of the earlier errors. Fresh entropy and the law of one rounding are enough anyway: the cross terms vanish after conditioning on the history so far. If every reachable cell at step $k$ has width at most $g_k$, put $C=\sum_k g_k^2/4$. Then the centered error $E$ satisfies

$$
\mathbb E[E]=0,\qquad \mathbb E[E^2]\le C,\qquad
\Pr(|E|\ge\varepsilon)\le 2\exp\!\left(-\frac{\varepsilon^2}{2C}\right)
$$

for $C>0$ and $\varepsilon\ge0$, so $\sqrt{2C\log(2/\delta)}$ is a confidence radius for $0<\delta<1$. In the example the additions have cells of width at most $1/64$, so $C\le 3/16384$. When $C=0$ the error is zero almost surely.

`roundedDot` spends fresh entropy on each product and each addition, and `roundedAffine` includes the bias addition. One command handles all of these loops and the wrappers around them, matrix entries included, and `Rounder.Support.safe` and `Rounder.Support.affine_certificate` give their certificates.

Two limits. What the command proves comes from the loop and the rounder's law, so it doesn't prove that an external random-number generator supplies independent uniform words. And nonlinear layers need further reasoning, because a mean-zero input error does not give a mean-zero error after a ReLU. Our [network results](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Quantization/Stochastic/Network.lean) propagate bounds that account for uncertain activation signs instead.

## How does `interval` prove infinitely many cases at once?

Back to the question we started with. The enclosures do the covering.
[[FloatLib.Numerics.Interval.Expr]] writes an expression down as data, with constants, numbered
variables and operations, and its executable evaluator takes a backend, the code that computes
endpoints, and an interval for each variable. [[FloatLib.Numerics.Interval.Expr.containsReal_eval?]]
proves that a successful evaluation contains the expression's value at every real assignment in
those input intervals, and every backend supplies the same
[[FloatLib.Numerics.Interval.Backend.Sound]] contract.

For a goal $a\le b$, the checker encloses $a-b$ and asks whether its upper endpoint is nonpositive,
or strictly negative for a strict goal, and [[FloatLib.Numerics.Interval.Expr.check_sound]] carries
the enclosure theorem through subdivision. The tactic runs this check with one more rule in the
evaluation: a product with a factor that is exactly zero needs no enclosure of the other factor
(`Expr.evalZero?`, and [[FloatLib.Numerics.Interval.Expr.checkZero_sound]] is the theorem for it).
The tactic proves its translation of the Lean expression
and builds the input membership proof from the hypotheses. Then it verifies the closed Boolean check
with `decide +kernel`, which has the kernel run the yes-or-no test itself, and Lean checks the
resulting proof term.

This is *proof by reflection*, named for reflecting the goal into data a program can compute with.
You prove the calculator right once, and from then on every yes it gives is a proof. Rocq's Interval
package (Rocq is the proof assistant once called Coq) takes the same broad approach and also
provides automatic differentiation, Taylor models, integration and root enclosures [@rocqInterval].
Our Taylor approximations bound individual function calls, not a complete expression.

## How to run the evaluator yourself

The evaluator inside `interval` is ordinary executable code, so you can run it and look at the
enclosures. This call encloses $x^2/2$ on $[-1,1]$ using exact rational endpoints. Try it yourself:

```lean
open FloatLib.Numerics

def halfSquare : Interval.Expr :=
  .binary .div (.unary (.pow 2) (.var 0)) (.const 2)

#eval halfSquare.eval? (Interval.Backend.rational {})
  (fun _ => some ⟨-1, 1⟩) == some ⟨0, 1 / 2⟩
-- true
```

Squaring knows its two factors are the same number, so its lower bound is zero even though the input
crosses zero. `#eval` shows the result, and the containment theorem is what lets a proof use it. An
`Interval.Expr` can also be built with ordinary `+` and `*`, with endpoints and rounding from the
backend you pass to `eval?`:

```lean
open FloatLib.Numerics.Interval

def polynomial : Expr :=
  Expr.var 0 * Expr.var 0 + Expr.const (1 / 2)

example : polynomial.eval? (Backend.rational {}) (fun _ => some ⟨1, 2⟩) =
    some ⟨3 / 2, 9 / 2⟩ := by decide +kernel
```

On $[1,2]$ the polynomial's enclosure is $[3/2,9/2]$, its values at the two endpoints, and
`decide +kernel` checks that inside Lean.

## How to choose a different endpoint format

Both examples used exact rational endpoints, but that's only one of your choices. These are the
endpoint backends the evaluator accepts:

| Backend | Endpoint calculation |
| --- | --- |
| `Backend.rational` | Exact rational arithmetic for algebraic operations; certified rational enclosures for elementary functions. |
| `Backend.binaryGrid` | Integer arithmetic on a chosen binary grid; elementary bounds are rounded outward onto that grid. |
| `Backend.ofRounding` | Any endpoint representation with a proved rational outward-rounding contract. |

On the binary grid, elementary functions use rational enclosures internally, so the cost depends on
how algebraic an expression is, how big its endpoints are and the requested degree.

Here's a function that encloses two rational inputs, adds their intervals and decodes the answer.
[[FloatLib.Numerics.Interval]] leaves the representation `α` of `Interval α` to you, without fixing
a radix (the base, two or ten) or assuming infinities exist. So the same function handles decimal32,
an IEEE decimal format, and posit8, a small format from the posit family (an alternative to IEEE
floats). In decimal32, $1/10+1/5$ gives the exact interval $[3/10, 3/10]$, because all three numbers
are short decimals, and in posit8 $1+2$ gives $[3,3]$:

```lean standalone
import FloatLib

open FloatLib

def enclosedSum? {α : Type} (R : Numerics.OutwardRounding α ℚ)
    (x y : ℚ) : Option (ℚ × ℚ) := do
  let a ← R.enclose? x
  let b ← R.enclose? y
  let result ← Numerics.Interval.add? R a b
  let lo ← R.decode result.lo
  let hi ← R.decode result.hi
  pure (lo, hi)

def decimalRounder :=
  Floats.Formats.DecimalInterchange.intervalRounding .decimal32 .bid

def positRounder : Numerics.OutwardRounding Floats.Posit8 ℚ :=
  Floats.ExecFloat.Posit.intervalRounding

#eval enclosedSum? decimalRounder (1 / 10) (1 / 5) == some (3 / 10, 3 / 10)
-- true

#eval enclosedSum? positRounder 1 2 == some (3, 3)
-- true
```

Arithmetic goes through [[FloatLib.Numerics.OutwardRounding]], a decoder plus a function that tries
to enclose an exact scalar, so the interval proofs aren't tied to rationals or binary floats. To
change the format, swap the rounder: `.dpd` (densely packed decimal) instead of `.bid` (binary
integer decimal) picks the other IEEE decimal encoding, and a custom endpoint type needs its own
`OutwardRounding` implementation and proof.

Interval operations that take an `OutwardRounding` return `Option`. A `some` result comes with an
enclosure theorem, and `none` means the call couldn't produce finite endpoints that enclose the
answer, as when a denominator interval crosses zero or a posit calculation overflows. Clamping
an upper endpoint to the largest finite value would violate containment when the exact result
is larger than that value. The
[binary-specific API in the getting-started chapter](#/chapter/using-the-library/how-to-trap-a-number-between-two-roundings)
supports infinite endpoints and keeps its whole-range fallback.

The enclosed real value need not be rational or representable in the endpoint format.
[[FloatLib.Numerics.Interval.ContainsReal]] reads the finite bounds in $\mathbb{R}$, and
[[FloatLib.Numerics.Interval.containsReal_mul?]] proves that a successful interval multiplication
encloses the product of any two real members, representable in the endpoint format or not. The
`interval` tactic builds on these contracts.

### How to evaluate a whole expression in another format

For a custom format, [[FloatLib.Numerics.Interval.Backend.ofRounding_sound]] gets the expression
contract from its `OutwardRounding` proof. FloatLib's binary, decimal and posit rounders, like the
two in [the sum above](#/chapter/proving-numerical-bounds/how-to-choose-a-different-endpoint-format), plug in the
same way, here decimal32 in its BID encoding:

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

You get the same $[0,1/2]$ as with rational endpoints. A finite format that can't enclose an output
endpoint returns `none`. Any representation can supply the same contract without changing the
expression language or its proof. A custom endpoint format can use the same evaluator once its
outward-rounding contract has been proved. If you have an endpoint format you'd like to use,
you can connect it through this contract :)

## How to bound a polynomial on the whole circle

Some bounds are about a function of an angle. Take

$$p(u) = \tfrac12 + \cos u + \tfrac12 \cos 2u.$$

Is $p(u) \ge -1/4$ for every real $u$? Cutting $[0, 2\pi]$ into pieces gets expensive as the
number of terms grows or the bound gets tighter. But $p$ is described completely by its three
coefficients, and `interval` notices that. When a goal bounds a series over
its whole domain, `∀ u : ℝ, …` here, it works with the coefficients before it tries any box:

```lean
open Finset in
example : ∀ u : ℝ,
    -1/4 ≤ ∑ k ∈ range 3, (([1/2, 1, 1/2] : List ℚ).getD k 0 : ℝ) * Real.cos (k * u) := by
  interval (lower := [1, 1, 1])
```

The list `[1, 1, 1]` is a *certificate*, the evidence the proof is built from. Write $z = e^{iu}$
for the point on the unit circle. Since $\cos 2u = 2\cos^2 u - 1$, we have
$p(u) = (\cos u + \tfrac12)^2 - \tfrac14$. And $1 + z + z^2 = z(z^{-1} + 1 + z) = z(1 + 2\cos u)$,
so $(\cos u + \tfrac12)^2 = |1 + z + z^2|^2/4$. That makes $p + \tfrac14 = |h(z)|^2/4$ for the
polynomial $h(z) = 1 + z + z^2$, whose coefficients are the certificate. A square is never
negative, so $p \ge -1/4$ everywhere, with equality where $\cos u = -1/2$. The goal may be written
any way you like, as long as it is a sum of such blocks and monomials: the same certificate proves
`∀ u : ℝ, -1/4 ≤ 1/2 + Real.cos u + Real.cos (2 * u) / 2`.

That is the general shape. To prove $p \ge \mathrm{lo}$, the certificate is a polynomial $h$ with
integer coefficients such that $p - \mathrm{lo} - c\,|h|^2$, for a scale $c > 0$ that the tactic
finds, is a trigonometric polynomial whose constant coefficient is at least the sum of the
absolute values of its other coefficients. Such a remainder can't go negative, because
$|e^{iku}| = 1$. A trigonometric polynomial that is nonnegative everywhere is always a square
$|h|^2$, which is the Fejér-Riesz theorem [@fejer1916] [@riesz1916], so a certificate exists for
every lower bound below the minimum. It only has to be found.

Without a certificate, `interval` uses the bound the coefficients give on their own: the constant
term, plus or minus the sum of the absolute values of the others. Here it proves
$|2\sin u - \sin 2u| \le 3$, and needs nothing else:

```lean
example : ∀ u : ℝ,
    |∑ k ∈ Finset.range 3, (([0, 2, -1] : List ℚ).getD k 0 : ℝ) * Real.sin (k * u)| ≤ 3 := by
  interval
```

That bound is fully automatic but often loose: for $p$ it only gives $1/2 - 3/2 = -1$ in place of
$-1/4$. `(lower := h)` and `(upper := h)` give sharp bounds on either side, and both together a
sharp bound on $|p|$. With sine terms the factor needs complex coefficients, given as a pair of
rows for its real and imaginary parts. For instance $1 + \sin u = |1 - iz|^2/2$, so the factor
$1 - iz$ proves that $1 + \sin u \ge 0$:

```lean
example : ∀ u : ℝ, 0 ≤ 1 + Real.sin u := by
  interval (lower := ([1, 0], [0, -1]))
```

### What about intervals and the unit circle of $\mathbb{C}$?

Chebyshev series work, because the Chebyshev polynomials satisfy $T_k(\cos u) = \cos ku$. The same
certificate proves the same minimum on $[-1, 1]$, and the tactic accepts any point that `linarith`
can place in $[-1, 1]$, such as $(x - 4)/2$ for $x \in [2, 6]$:

```lean
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1, -1/4 ≤
    ∑ k ∈ Finset.range 3, (([1/2, 1, 1/2] : List ℚ).getD k 0 : ℝ) *
      (Polynomial.Chebyshev.T ℝ k).eval x := by
  interval (lower := [1, 1, 1])
```

A polynomial in the power basis works on an interval $[\mathrm{lo}, \mathrm{hi}]$ with rational endpoints. Put
$x = m + r\cos u$, with the midpoint $m$ and the radius $r$: then $p(x)$ is a cosine polynomial of
the same degree, and the kernel builds its coefficients itself, with Horner's rule on packed rows
[@horner1819]. This substitution relates power polynomials on an interval to cosine polynomials,
as in Chebyshev approximation [@trefethen2013]. Packed integer arithmetic computes the transformed
coefficients. On $[0, 1]$,
$x^2 - x = \cos(2u)/8 - 1/8$, so the coefficients alone give the exact minimum:

```lean
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, -1/4 ≤ x ^ 2 - x := by
  interval
```

If the coefficient method does not prove an interval bound, the tactic tries subdivision. On the unit circle of
$\mathbb{C}$, `interval` bounds the norm of a polynomial with Gaussian rational coefficients, from
above or from below, by the same checks on $|p|^2$:

```lean
example : ∀ z : ℂ, ‖z‖ = 1 → 1 ≤ ‖2 + z‖ := by
  interval
```

### How does the kernel check a certificate so fast?

Every check ends in Lean's kernel. The kernel computes fifteen operations on natural-number
literals with the GMP library, among them addition, multiplication, division, remainder, the
bitwise operations and the shifts, and it interprets everything else one small step at a time. A
check that walks a list costs tens of microseconds per entry, while one multiplication of two
numbers with a million bits takes a few milliseconds. So FloatLib keeps a whole list of integers
in one natural number, a *packed row*, with one integer per *lane* of $w$ bits. The row
$[1, -2, 3]$ in lanes of 8 bits stores $x + 128$ in each lane, so it is the number
$129 + 126 \cdot 256 + 131 \cdot 256^2 = 8617601$, and it stands for the integer
$1 - 2 \cdot 256 + 3 \cdot 256^2 = 196097$.

Integers multiply the way rows do. The row $[4, -5]$ stands for $4 - 5 \cdot 256 = -1276$, and
$196097 \cdot (-1276)$ is the integer of $[4, -13, 22, -15]$, the coefficients of
$(1 - 2z + 3z^2)(4 - 5z)$, because every coefficient of the product fits its lane. This is
Kronecker substitution [@kronecker1882] [@harvey2009]: one big multiplication computes the whole
product. Here the
kernel checks it:

```lean
open FloatLib.Numerics.Packed in
example :
    entries 8 4 (ofInt 8 4 (toInt 8 3 (pack 8 [1, -2, 3]) * toInt 8 2 (pack 8 [4, -5]))) =
      [4, -13, 22, -15] := by
  decide +kernel
```

Since $2^w \equiv 1$ modulo $2^w - 1$, one remainder adds up all the lanes of
a row, and two of them, with masks that pick out the positive and the negative entries, give the
$\ell^1$ norm. For example, in base $2^8$, the lanes $3, 1, 4$ encode
$3 + 1 \cdot 256 + 4 \cdot 256^2 = 262403$, and
$262403 \bmod 255 = 8 = 3 + 1 + 4$. HAKMEM counts the bits of a word the same way, with a remainder
modulo $63$ [@beelerHakmem1972].

A range check is one addition, one bitwise conjunction and one comparison. So a sum-of-squares
check on a polynomial with $n$ coefficients is one product, $h$ times its reverse, which is $|h|^2$
on the circle, then one subtraction, one lane read and one $\ell^1$ norm, plus the range checks
that rule out a lane overflowing. A complex factor $p + iq$ adds three more products and one more
reversal. `Packed.sosCheck_sound` says what a passing check means for the lists of integers, and
`Coeff.laurent_sosCheck` turns it into the inequality on the circle.

In our measurements on Lean v4.36.0, a two-sided bound on a cosine polynomial with 200 integer
coefficients below $2^{80}$ takes about 0.13 s of kernel time, most of it the link between the 200
coefficients of the goal and their row, and the tactic call about as long. The certified
bound is within $4 \cdot 10^{-7}$ of the maximum, relative to its size, while the $\ell^1$ bound is
3.45 times larger.

### Where do certificates come from?

From any program you like, because nothing it computes is trusted. FloatLib ships
`scripts/coeff_cert.py`, which factors $p - \mathrm{lo} - \eta$, for a small slack $\eta$, from
its roots, rounds the factor to Gaussian integers, and checks the result in exact arithmetic before
it writes it. It reads coefficients as integers, fractions, decimals or the bit patterns of IEEE
values, and `--sin`, `--interval lo hi` and `--laurent` select the other families:

```bash
python3 scripts/coeff_cert.py coefficients.txt --abs auto --slack 1e-7 -o bound
```

This writes `bound_lower.txt` and `bound_upper.txt`, one integer per line, and a second file for
the imaginary part when the factor has one, and prints the bound it certified and the option to
use. `interval (lower := "bound_lower.txt") (upper := "bound_upper.txt")` reads the files from the
directory of the Lean source. For the 200-coefficient polynomial above, the script takes about 6 s
with python-flint [@pythonFlint] and 41 s with mpmath alone. If the certificate is wrong, or the
bound is false, the kernel's check fails and so does the proof.

### How to use coefficients that are floating-point numbers

Coefficients often come out of a numerical program. FloatLib formats with an exact rational meaning
decode to that rational exactly, so a list of binary32, binary64, posit or fixed-point values is a
list of rationals, and `interval` reads the decoded values itself:

```lean
open FloatLib.Floats in
def floatCoefficients : List Binary32 := [0.5, 1, 0.5]

open FloatLib.Floats.ExecFloat.Packed in
def floatValues : List ℚ := (values floatCoefficients).map (·.getD 0)

example : ∀ u : ℝ,
    -1/4 ≤ ∑ k ∈ Finset.range 3, (floatValues.getD k 0 : ℝ) * Real.cos (k * u) := by
  interval (lower := [1, 1, 1])
```

`values` lists the exact value of each lane, `none` for an infinity or a NaN, and the kernel
decodes the values while it checks the link, at about 2 ms per binary64 value. For certificates
written by hand, `packed_values r (width := w) := xs` brings a list of values in as one packed row
at their common denominator, together with a theorem `r.link` that the kernel checked once. The
binary32 values $1.5$, $-0.25$ and $3$, for example, become the row $[6, -1, 12]$ over the
denominator $4$.

### What about $1/f$ and $f^{-1/2}$?

A function like $1/(2 + \cos u)$ is not a polynomial, and its coefficients never end. FloatLib
handles it *a posteriori*, the standard move of verification methods [@rump2010]. An untrusted
program supplies an approximation $v$, and the kernel computes the *defect* $1 - vf$ exactly, as a
finite row, and its $\ell^1$ norm $\delta$. The functions $\sum_n c_n e^{inu}$ with
$\sum_n |c_n| < \infty$ form a Banach algebra, the Wiener algebra [@wiener1932], `Coeff.Wiener`,
whose product is the convolution of the coefficients, so the Neumann series gives
`Coeff.inv_of_defect`: if $\delta < 1$, then $f$ is invertible and
$\|f^{-1} - v\| \le \|v\|\,\delta/(1 - \delta)$. The norm bounds the function, so this bounds
$|1/f(u) - v(u)|$ at every $u$. This use of the Wiener algebra follows PlasmaLean
[@plasmaLean], which constructs the same ring for its plasma-physics certificates.

Here is the smallest example. For $f = 2 + \cos u$, which is the row $[1, 4, 1]$ over $2$, take
$v = [-2, 7, -2]/12$. Then $vf = [-2, -1, 24, -1, -2]/24$, so $\delta = 6/24 = 1/4$, which is one
product and one $\ell^1$ norm in the kernel:

```lean
open FloatLib.Numerics.Packed in
example : absSum 16 5 (shift 16 2 24 - toInt 16 3 (pack 16 [-2, 7, -2]) *
    toInt 16 3 (pack 16 [1, 4, 1])) = 6 := by
  decide +kernel
```

With $\|v\| = 11/12$, `inv_of_defect` gives
$|1/(2 + \cos u) - v(u)| \le (11/12)(1/4)/(3/4) = 11/36$ for every $u$. A longer $v$, with 25
coefficients at $2^{-40}$, brings the error down to $1.003 \cdot 10^{-7}$. The binomial series of
$(1 - t)^{-1/2}$, whose coefficients are all positive, does the same for inverse square roots
(`Coeff.invSqrt_of_defect` and `Coeff.Wiener.eval_invSqrt_of_defect`). From a defect of
$1.6 \cdot 10^{-10}$, the test suite proves $|1/\sqrt{2 + \cos u} - g(u)| \le 8 \cdot 10^{-11}$ for
a cosine polynomial $g$ with 33 coefficients. These are theorems you apply yourself, because
`interval` doesn't read inverses of series yet.

### What exactly is proved?

`interval` proves the goal as stated, for every real $u$, every $x$ in the interval or every $z$ on
the unit circle, with no sampling. The coefficients are exact rationals, so a float coefficient
means its exact decoded value, not a nearby decimal, and the bound has to be a term that `norm_num`
evaluates to a rational. The kernel checks the link between the coefficients of the goal and their
packed rows, the range of every lane and one sum-of-squares check per side. The tactic then applies
`Coeff.trig_sos`, `Coeff.power_sos` or `Coeff.norm_sos`, one of the four bound lemmas such as
`Coeff.bound_le_of_sos`, and for a Chebyshev series `Coeff.forall_Icc_chebyshev`. All of them depend
only on Lean's three standard axioms. The goal's polynomial side is read as a sum of rational
multiples of blocks, monomials and constants, so products of polynomials and inverses aren't read.
