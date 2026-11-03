---
number: "20"
slug: proving-numerical-bounds
title: Proving numerical bounds
summary: Certified interval evaluation turns rational input bounds into Lean proofs of real inequalities, and `roundoff` turns floating-point code into rounding-error theorems.
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

These are proofs about the real expressions as written. A floating-point program rounds at every
operation, so bounding its error also takes a theorem connecting the program to its real
expression. The [`roundoff`
tactic](#/chapter/proving-numerical-bounds/error-bounds-from-floating-point-code) builds that theorem
from the program's own code, using the [rounding and reduction
bounds](#/chapter/the-mathematics-of-rounding) of each operation it meets, and interval evaluation
can discharge the numerical inequalities that are left.

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

For goals without registered calls, the tactic first evaluates the same binary-grid check as an
ordinary program and stops before kernel reduction when that run already returns false. Registered
calls go straight to bounded kernel reduction, and every successful goal needs a kernel-checked
certificate.

Each verification attempt has its own budget of 20,000 heartbeats, and so do the
failure diagnostics. That limit stays active even when the surrounding declaration sets
`maxHeartbeats` to zero, and you can ask for a larger finite budget with
`interval (maxHeartbeats := 40000)`. When the kernel check of an attempt runs out of that budget,
the failure message names the attempt, exact-rational or binary-grid, and suggests a larger
`maxHeartbeats`. Other failures don't come with that advice, and every failure restores the original
goal.

When arithmetic fails, the diagnostics tell you why. They
report the obstructing range or the upper bound that wasn't small enough, and for registered calls
they inspect the actual enclosure on the original box and report rejected domains separately,
naming the operation, its argument enclosures, and what it accepts, such as argument enclosures with
a positive lower endpoint for `Real.log`. A zero-containing denominator range, for example, explains why division failed without claiming that
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

## Error bounds from floating-point code

`interval` proves facts about real expressions. A program on `Binary32` values rounds after every
operation, so its result differs from the real expression it was written from, and the `roundoff`
tactic proves by how much. It reads the configured computation as written and takes the rounding
theorem of the capability behind each operation, such as `ExecFloat.Binary.add_rounding` for `+`.
Then it composes those local errors into a bound against a reference, the same computation in exact
real arithmetic on the decoded inputs, apart from the cases listed at the end of this section. The bound is either absolute, $|x-x_0|\le\beta$, or mixed,
where `MixedError x x₀ r a` means $|x-x_0|\le r|x_0|+a$, and the tactic proves finiteness, exact
decoded values, and signs the same way. It lives in
`FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff`, which `import FloatLib` doesn't
reach, so this example imports it itself. It comes from the library's `roundoff` tests:

```lean standalone
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff

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
[[FloatLib.Floats.Formats.BinaryInterchange.Model.halfUlpAt]] of $xy+z$, and plain `roundoff`
closes it from `hresult` with the one rounding the operation performs. For the dot product we write
only the value we want bounded. `roundoff mixed theorem` takes `ExecFloat.Binary.toReal (dot x y)`,
analyzes the loop over `Fin n` once for a symbolic accumulator, and lifts that step through the
traversal with `List.fold_mixedError`, so the statement holds at every length, for every IEEE
descriptor, storage plan, and codec, without unrolling anything. Reading what `#check` prints, the
reference is `List.foldl referenceStep 0 (List.finRange n)`, the exact dot product of the decoded
entries. Each addition gets relative error $u$, the unit roundoff `Model.unitRoundoffAt format`,
and after each step the absolute part becomes $(1+u)(r\,|\mathit{ref}|+a+u\,|x_jy_j|+\eta)$ in
terms of the previous relative part $r$, absolute part $a$ and reference, where $\eta$ is the
underflow allowance `Model.underflowErrorAt format`, half the spacing of the subnormals. The
premise is a `List.AllSteps` condition on the states the loop actually visits: both entries finite,
the product at most the largest finite value $\Omega$, and the next partial sum together with its
budget at most $\Omega$. In return we get a finite output and its mixed bound.

The two examples after the `#check` use the statement. `List.abs_sub_le_of_sumFold` turns the
recurrence into the closed form
$$
\Bigl|x-\sum_j p_j\Bigr|\le\bigl((1+u)^n-1\bigr)\sum_j|p_j|+(1+u)^n\sum_j\bigl(u\,|p_j|+\eta\bigr),
\qquad p_j=x_jy_j.
$$
In binary32, $u=2^{-24}$ and $\eta=2^{-150}$. For four products of magnitude at most one, the first
term is about $4u\cdot4=16u$ and the second about $4u+4\eta$, so the computed dot product lies
within about $20u\approx1.19\times10^{-6}$ of the exact one. That's a little above the textbook
$\gamma_4\sum_j|p_j|\approx16u$ [@higham2002], because the loop charges every addition the same
relative error, including the first one from zero, which is exact. The second example discharges
the premise from four plain conditions: finite entries, $|p_j|\le b$, $(1+u)^{n+1}\le2$, and
$2(n+1)(b+\eta)\le\Omega$. In binary32 the growth condition holds while $n+1\le\ln2/\ln(1+u)$, that
is for up to 11,629,079 terms, and with $b=1$ and $n=4$ the last condition asks for
$10(1+2^{-150})\le\Omega\approx3.40\times10^{38}$.

The same analysis reads literals, exact when the format represents them, conversions of integers,
rounding to integral values, and the C maximum loop `if m < x then x else m`. FloatLib's correctly
rounded exponential, logarithm, `expMinus1`, `logPlus1` and `expMul` each contribute one rounding at
their real result on an IEEE descriptor, while sine, cosine and the hyperbolic functions use
FloatLib's rational enclosures. Loops can also run over lists, arrays, vectors and matrices, and a
loop whose state is a pair or a nondependent record carries one relation for all its components.
When such a loop tests a rounded component, as a sum that stops once an addition leaves it
unchanged does, the step's condition can ask that the rounded test agree with the same test on the
exact references, and the theorem covers the runs where they agree. For that stopping sum these are
the runs that never stall, because an exact sum doesn't stall on a nonzero entry, so the bound says
nothing about a stop that rounding caused.
`roundoff theorem` states an absolute bound instead, and for the dot product its premise asks every
visited partial sum and product to be finite. Inside a proof,
`have bound := by roundoff (ExecFloat.Binary.toReal (program x))` infers a bound once its range
premises are provable. `[roundoff_rule]` registers a bound of your own, and another library
registers its containers with `@[roundoff_extension]`.

The theorem `roundoff` produces is an ordinary Lean proof, and the kernel checks it like any other.
Our axiom audit loads the analysis and accepts only propositional extensionality, quotient
soundness, and choice. What the analysis doesn't check is that its reference means what the program
means, and that rests on four assumptions. The opaque constants and axioms of Lean's own library,
other than `Classical.choice`, hold no number when their types hold none. FloatLib's order
dictionaries on configured values and its comparison `ExecFloat.Binary.instComparisonFamily`
compare the decoded values. A configured type's codec and storage plan define what its stored words
mean. And the getters of lists, arrays and vectors, the reads that extensions register, and the
classes such a read names as trusted store and fetch entries without computing with them. Inside
index data, a function over numerical values is checked wherever it travels, in a list, a record or
a generic helper, and applied only at plain index data. Some choices do stay in the reference as the program makes
them. A stored container read at an index computed from rounded values keeps that choice, and a
branch whose condition compares computed values takes the branch the program takes. The reference
also reads the program as Lean states it: a variable a `have` introduces is an input, whatever
computed it, and a value of a type variable counts as non-numerical, so a theorem generic in a type
keeps the functions it applies when you specialize it to a numerical one. A call of a function the program takes is a different case. When the analysis has no rule for that
function's real model, the reference applies the model to the decoded computed argument, as in
`g (toReal (x * y))`, so the statement shows that argument and the bound leaves out its rounding.

The rounding rules hold for IEEE descriptors, and the tactic proves that condition from the context
when it can and otherwise leaves it as a goal. The operator rules are the nearest-even rounding
theorems of the ordinary operators, so a named call with a directed mode, such as
`ExecFloat.Binary.add x y (mode := .up)`, has no rule, and `roundoff` asks for an explicit bound on
it. Those rules need finite results, division a finite divisor, and square root a finite operand in
its domain, and whatever the tactic can't prove comes back as a premise or a goal. For a loop the
budget is a symbolic recurrence, so comparing it with a numerical tolerance of your own is a
separate step, like the closed form above.

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
wouldn't fit but the final bounds do. What it encloses is the real expression. A sequence of rounded
floating-point operations needs their rounding-error contracts as well, and that's the job of
[`roundoff`](#/chapter/proving-numerical-bounds/error-bounds-from-floating-point-code). Elementary
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