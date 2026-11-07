---
number: "11"
slug: proving-numerical-bounds
title: Proving error bounds
summary: "How to prove a real inequality with the `interval` tactic, how to get an error bound for floating-point code with the `roundoff` tactic, how `interval` bounds a polynomial over its whole domain from its coefficients, and what each one assumes."
phases: [status-and-directed, planner-and-configured, ieee-formats, binary-arithmetic]
---

The `interval` tactic proves real inequalities by evaluating certified bounds on expressions. The `roundoff` tactic proves error bounds for floating-point programs. Both produce proof terms that Lean checks. This chapter introduces these tactics and the coefficient-based bounds that `interval` can use for polynomials over a whole domain.

## How to prove an inequality with `interval`

Say a proof needs $x(1-x)\le 1/3$ for every $x\in[0,1]$. You can hand the expression to FloatLib.
`Set.Icc 0 1` is the closed interval $[0,1]$, so the hypothesis `hx` says that $x$ lies in it:

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

These are proofs about the real expressions as written. A floating-point program is a different
story, because it rounds at every operation to a number the format can store, and that's what our
[`roundoff` tactic](#/chapter/proving-numerical-bounds/how-to-get-an-error-bound-for-floating-point-code) is
for. It builds the theorem that ties the program to its real expression from the
[rounding and reduction bounds](#/chapter/the-mathematics-of-rounding) of each operation it meets,
and interval evaluation can then close whatever numerical inequalities are left. So there are two
questions here. Is the math true, and how far can the program drift from it? `interval` answers the
first, and `roundoff` the second.

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
the bounds, can use it for narrower ones. A constant like Catalan's takes more work. There the
provider also has to supply an executable approximation and a theorem bounding its remainder, since
registration doesn't derive them. Importing the provider's module brings its registration along, and
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
tactic needs its own import, `FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff`, as in
this example from the library's tests:

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
relative error, including the first one from zero, which is exact.

In the second example the premise comes from four plain conditions: finite entries, $|p_j|\le b$,
$(1+u)^{n+1}\le2$, and $2(n+1)(b+\eta)\le\Omega$. In binary32 the growth condition holds while
$n+1\le\ln2/\ln(1+u)$, up to 11,629,079 terms, and with $b=1$ and $n=4$ the last condition asks for
$10(1+2^{-150})\le\Omega\approx3.40\times10^{38}$, which is hardly asking at all.

## What else can `roundoff` read?

Literals go through the same analysis, exact when the format represents them, and so do integer
conversions, rounding to integral values and the C maximum loop `if m < x then x else m`. FloatLib's
correctly rounded exponential, logarithm, `expMinus1`, `logPlus1` and `expMul` each contribute one
rounding at their real result on an IEEE descriptor, while sine, cosine and the hyperbolic functions
use FloatLib's rational enclosures. Loops can run over lists, arrays, vectors and matrices, and a
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
registers its containers with `@[roundoff_extension]`.

## What does `roundoff` ask you to prove?

Each rounding rule, the theorem `roundoff` uses for one operation, holds for IEEE descriptors, and
the tactic proves that condition from the context or leaves it as a goal. The rules need finite
results, division a finite divisor and square root a finite operand in its domain, and whatever the
tactic can't prove comes back as a premise or a goal. For a loop the budget is a symbolic
recurrence, a step-by-step formula, so comparing it with a numerical tolerance of your own is a
separate step, like the closed form above.

**Note:** The operator rules are the nearest-even rounding theorems of the ordinary operators. A
named call with a directed mode, such as `ExecFloat.Binary.add x y (mode := .up)`, has no rule, so
`roundoff` asks you for a bound on it.

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
the enclosure theorem through subdivision. The tactic proves its translation of the Lean expression
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
answer, as when a denominator interval crosses zero or a posit calculation overflows. Why not
saturate, clamping to the largest finite number? That would break the fence-post promise, because
that number isn't an upper bound for a larger exact result. The
[binary-specific API in the getting-started chapter](#/chapter/using-the-library/how-to-trap-a-number-between-two-roundings)
supports infinite endpoints and keeps its whole-range fallback.

What the rational endpoints fence in can be any real number.
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

A polynomial in the power basis works on any interval $[\mathrm{lo}, \mathrm{hi}]$. Put
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

In our measurements on Lean 4.35, a two-sided bound on a cosine polynomial with 200 integer
coefficients below $2^{80}$ takes about 0.14 s of kernel time, most of it the link between the 200
coefficients of the goal and their row, and the whole tactic call about as long. The certified
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
