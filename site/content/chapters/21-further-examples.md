---
number: "21"
slug: further-examples
title: "Further examples"
summary: "Worked recipes for intervals, reductions, real-valued proofs, mixed formats, and complex arithmetic."
phases: [planner-and-configured, ieee-formats, binary-arithmetic]
---

## Choosing a different endpoint format

Interval addition needs rounders that keep the lower endpoint at or below the exact sum and the upper endpoint at or above it. The algorithm can then stay the same whether we store its bounds in decimal, binary, or posit numbers. FloatLib uses one type, [[FloatLib.Numerics.Interval]], for these endpoint pairs: `Interval α` leaves the representation `α` to the caller, without fixing a radix or assuming infinities exist.

The function below encloses two rational inputs, adds their intervals, and decodes the answer. With decimal32 endpoints, $1/10+1/5$ gives the exact interval $[3/10,3/10]$; with posit8 endpoints, $1+2$ gives $[3,3]$. Each example includes its imports and definitions, as in the [getting-started chapter](#/chapter/using-the-library), so you can paste it into a fresh Lean file.

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

Constructing a pair keeps the values you gave it, and `Interval.ofBounds?` also checks that they decode to ordered finite bounds.

Arithmetic goes through [[FloatLib.Numerics.OutwardRounding]], which supplies a decoder and a function that tries to enclose an exact scalar. The scalar type is also a parameter, so the common interval proofs aren't tied to rationals or binary floats. Our binary, decimal, and posit adapters use exact rationals because that lets their finite interval calculations run.

These finite operations return `Option`. A `some bounds` result comes with an enclosure theorem, and `none` means the operation couldn't produce finite endpoints that enclose the answer. So a denominator interval crossing zero, or a posit calculation that overflows, can fail and say so. The [binary-specific API in the getting-started chapter](#/chapter/using-the-library/an-interval-from-two-directed-roundings) also supports infinite endpoints and keeps its existing whole-range fallback. Saturating to the largest finite number wouldn't work, because it isn't a sound upper bound for a larger exact result.

Swapping the rounder changes the stored format and leaves the interval algorithm alone. Decimal's `.bid` picks the encoding, and `.dpd` uses the other IEEE decimal encoding. A custom endpoint type supplies an `OutwardRounding` implementation and its proof, and the interval operations then use that rounder.

Rational endpoint calculations also describe intervals of arbitrary real numbers. [[FloatLib.Numerics.Interval.ContainsReal]] reads the finite bounds in $\mathbb{R}$, and [[FloatLib.Numerics.Interval.containsReal_mul?]] proves that a successful interval multiplication encloses the product of any two real members. Those members don't have to be rational, or representable in the endpoint format. These contracts are also what the `interval` tactic builds on. Give it bounds on the inputs and it proves real inequalities, for example:

```lean standalone
import FloatLib

example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : Real.exp x < 3 := by
  interval (degree := 12)
```

Subdivision can prove inequalities that a single interval evaluation leaves open, and [Chapter 20](#/chapter/proving-numerical-bounds) explains how, along with the evaluator and its precision controls.

## Sums and dot products with one rounding

Adding the list `[16777216, 1, -16777216]` from the left gives zero in binary32. Its exact sum is one. A binary32 significand has 24 bits, so $2^{24} + 1$, which is $16777216 + 1$, rounds back to $2^{24}$. Subtracting $2^{24}$ then gives zero. `sumList` and `sum` decode every term to an exact dyadic instead, accumulate the whole sum in software, and round once at the end.

```lean standalone
import FloatLib

open FloatLib.Floats

def values : List Binary32 := [16777216, 1, -16777216]

#eval values.foldl (· + ·) 0
-- 0
#eval ExecFloat.Binary.sumList values
-- 1
#eval ExecFloat.Binary.sumList values (status := true)
-- { value := 1,
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := false },
--   ternary := Ordering.eq }
#eval ExecFloat.Binary.dot #[(1.5 : Binary32), 2, 4] #[2, 3, 4]
-- Except.ok 25
#eval ExecFloat.Binary.dotList [(1.5 : Binary32), 2, 4] [2, 3]
-- Except.error (FloatLib.Numerics.ReductionError.lengthMismatch 3 2)
```

Try reordering the list to `[16777216, -16777216, 1]`. The ordinary fold then cancels the large terms first and returns one, while the exact sum gives one in either order, because it keeps every term until the final rounding.

The status form says the exact sum was representable, with no rounding error. [[FloatLib.Floats.ExecFloat.Binary.dot]] keeps every product exact too, so $1.5 \cdot 2 + 2 \cdot 3 + 4 \cdot 4 = 25$ gets one rounding at the end. If the lengths don't match, you get an `Except.error` carrying both lengths before any arithmetic runs, as `dot_status_lengthMismatch` proves. That check is there to prevent the truncation you'd get from `List.zip` on unequal lists.

Each configured function calls the reducer defined for the format's model. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Reduction.sum_status_eq_round_of_finite_nonzero]] says a nonzero finite sum is one rounding of the exact sum, with the status of that one rounding, and [[FloatLib.Floats.ExecFloat.Binary.dot_status_eq_model]] says the configured dot is the model dot, errors and status included.

`#float_info [errors] Binary32` reports a sequential-reduction bound for a different algorithm, one in which casts, products, and accumulator updates each round. That bound adds up an error allowance for each step, including the final output conversion, and it needs the specified IEEE formats and finite intermediate values. The matrix-entry bound applies the same dot-product result to one row and one column. Our exact `dot` holds the products and the sum until its final rounding, so its error argument is a different one.

`dot` has no initial-addend argument. IEEE `fma` already covers one product plus an addend, and the [round-once expressions below](#/chapter/further-examples/evaluating-an-expression-with-one-final-rounding) cover anything larger. A posit quire, the subject of [chapter 13](#/chapter/posits-and-the-quire), also delays rounding, but it's a fixed $16n$-bit accumulator with a NaR outcome and a range condition. The binary reducer uses an unbounded dyadic and follows the IEEE status rules.

## The result as a real number

A [refinement proof](#/chapter/using-the-library/proving-arithmetic-agrees-with-its-specification) pins down the complete word that addition returns. An error analysis usually needs to say how far that word's value lies from the exact sum. `ExecFloat.Binary.toReal` reads the word as a real number, and the configured rounding theorem relates that value to one rounding of the exact sum.

For binary interchange we state the real-valued semantics on [[FloatLib.Floats.Formats.BinaryInterchange.Model]], the descriptor-indexed model of [chapter 06](#/chapter/the-numerical-models), and [[FloatLib.Floats.ExecFloat.Binary.toModel]] converts a configured value to that model. A configured binary32 value is stored as a packed `UInt32`, but the model uses an exact-width record. `toModel` and its inverse `ofModel` connect the two, and `toReal` is the model's real value of the decoded word.

[[FloatLib.Floats.ExecFloat.Binary.toReal_add]] carries the model's rounding theorem [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] over to the notation. For finite operands whose sum doesn't overflow, the real value of `a + b` is the exact real sum rounded once by [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]]. `+` runs the implementation selected for the format, so the theorem takes the instance argument `HasSpec cap Configured.Spec.add`. That argument says the selected capability's reference operation is the model's. Instance search proves it for every capability the library declares. `toReal_sub`, `toReal_mul`, `toReal_div`, and `toReal_sqrt` do the same for `-`, `*`, `/`, and square root. [[FloatLib.Floats.ExecFloat.Binary.abs_toReal_add_sub_le]] and its siblings turn each one into an error bound of half an ulp:

```lean standalone
import FloatLib

open FloatLib.Floats

open Formats.BinaryInterchange

theorem toReal_add_binary32 (a b : Binary32)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hout : (a + b).isFinite = true) :
    (a + b).toReal = Model.roundAt FloatFormat.binary32 (a.toReal + b.toReal) :=
  ExecFloat.Binary.toReal_add (by decide) ha hb hout

theorem add_error_binary32 (a b : Binary32)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hout : (a + b).isFinite = true) :
    |(a + b).toReal - (a.toReal + b.toReal)| ≤
      Model.epsilonAt FloatFormat.binary32 (a.toReal + b.toReal) :=
  ExecFloat.Binary.abs_toReal_add_sub_le (by decide) ha hb hout
```

`ha` and `hb` say the operands are finite, because a NaN or an infinity has no real value to round. `toReal` itself is total and returns zero on those inputs, so it's the finiteness hypotheses that let us read it as the value of a word. `ExecFloat.Binary.toReal?` is the partial reading. It is `none` exactly when the value isn't finite, as `toReal?_eq_none_iff` states. `hout` says the sum didn't overflow, and you can decide it on the result.

If you'd rather not evaluate the sum first, [[FloatLib.Floats.ExecFloat.Binary.toModel_hAdd]] rewrites `a + b` to `Model.add`, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt_of_abs_add_le_posMaxFinite]] accepts the symbolic bound $|a| + |b| \le \Omega$ in its place. Here $\Omega$ is the largest finite value [[FloatLib.Floats.Formats.BinaryInterchange.Model.posMaxFinite]].

The `by decide` proves `format.isIEEE = true`, which requires the IEEE encoding and the conventional bias. `Model.epsilonAt` is half an ulp at the exact result, so it follows the subnormal grid near zero. For rounding a nonzero value in the normal range, `#float_info [errors] Binary32` reports the relative bound $2^{-24}$.

Square root is the one operation without a result-finiteness premise, because [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite_sqrt_of_isFinite]] shows it can't overflow. It does ask for a nonnegative operand, where a signed zero counts. A negative input gives NaN, and NaN has no real value.

For the named operations, [[FloatLib.Floats.ExecFloat.Binary.toModel_add]] and the matching lemmas for the other five operations are registered with `simp` too, in every rounding direction and with the same instance argument. Calls with `(status := true)` have similar lemmas, such as `IEEEOutcome.toModel_div`. So a goal about a configured operation reduces to the corresponding model theorem in one step.

We can also go further and put the represented value in the type. `At` `fmt r` is an encoded value of format `fmt` together with a proof, erased at runtime, that it denotes the real $r$. Operations on it, such as `Model.At.add`, take the finiteness hypotheses as arguments and return a value indexed by the rounded result.

```lean standalone
import FloatLib

open FloatLib.Floats

open Formats.BinaryInterchange

example (a b : Binary32) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.add a b) =
      Model.add (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b) :=
  ExecFloat.Binary.toModel_add a b (mode := .nearest)

example {fmt : FloatFormat} {r s : Real}
    (u : Model.At fmt r) (v : Model.At fmt s)
    (hfmt : fmt.isIEEE = true)
    (hout : Model.isFinite (Model.add u.1 v.1) = true) :
    (Model.numericalSystem fmt).denote (Model.At.add u v hfmt hout).1 =
      .finite (Model.roundAt fmt (r + s)) := by
  numerics
```

The second example adds a value known to denote $r$ to one known to denote $s$, and the format's numerical system interprets the result as the finite real $\mathrm{roundAt}(r + s)$. That's already in the type, since `Model.At.add` carries the rounded sum as its index. `numerics` closes the proof with the general rule, registered under `numerics_simps`, that an `At` value denotes its index.

`u` and `v` carry their own proofs. Their `.1` fields are executable values and their `.2` fields establish the finite denotations, which is why there's no `ha` or `hb` here. The caller still supplies `hout`, because two finite inputs can have a sum that doesn't fit. This view pays off when several operations share the same semantic facts, since a function can return the value together with the proof its caller will need.

All of these theorems are about FloatLib's software arithmetic, and relating it to Lean's native `Float32`, to C operations, or to GPU instructions takes another argument. For Lean's native floats, [chapter 18](#/chapter/lean-native-floats) looks at how it compares.

## Mixing formats

Formats never promote implicitly. When you need a value of one type at another, you name the destination. [[FloatLib.Floats.ExecFloat.cast]], `addAs`, `subAs`, `mulAs`, `divAs`, and `fmaAs` all take a `target`. They also take an optional `mode`, the rounding direction of a binary destination, and an optional `context` for any other destination policy. Each returns a `ConversionOutcome` with the value and its conversion status, or a failure, and `value?` keeps just the value. Naming the destination shows where conversion and rounding can happen, including the conversions we can prove exact.

```lean standalone
import FloatLib

open FloatLib.Floats

#eval ((1.5 : Binary32).cast (target := Binary64)).value?
-- some 1.5
#eval ((-(0 : Binary32)).cast (target := Binary64)).value?
-- some (-0)

def narrowed := (0.1 : Binary64).cast (target := Binary32)

#eval narrowed.value?
-- some 0.1
#eval narrowed.status?.map (·.inexact)
-- some true
#eval ((0.1 : Binary64).cast (target := Binary32) (mode := .down)).value?
-- some 0.099999994

def tenth : Binary32 := 0.1

#eval (1.5 : Binary32) * tenth
-- 0.15

def widenedProduct := ExecFloat.mulAs (target := Binary64) (1.5 : Binary32) tenth

#eval widenedProduct.value?
-- some 0.15000000223517418
#eval widenedProduct.status?.map (·.inexact)
-- some false
#eval ((1.5 : Binary32).cast (target := Posit32)).value?
-- some 1.5
#eval ExecFloat.Binary.toFloat32 ((1.5 : Binary32) + 2.25)
-- 3.750000
```

A mixed operation decodes its operands exactly, computes in the destination's exact domain, and rounds once. For binary destinations that domain is [[FloatLib.Numerics.SignedRat]], a rational carrying an IEEE sign bit. A plain rational has only one zero, so casting through one would turn $-0$ into $+0$, and that sign bit is why the second cast delivers $-0$. The narrowing cast reports `inexact := true` because binary64's $0.1$ doesn't fit in 24 bits, and rounding it downward gives the binary32 neighbour below. `status?.map (·.inexact)` picks that field out of the successful conversion's status.

Both products use the same operands and change only the destination precision. Multiplying $1.5$ by the stored $0.1$ needs 26 significand bits, so `*` at binary32 rounds it to $5033165 \cdot 2^{-25}$. `mulAs` into binary64 has room for all 26 and returns the exact $40265319 \cdot 2^{-28}$ with `inexact := false`. Posits have one zero, so a posit destination computes in plain `Rat`.

That `inexact := false` is about the product of the represented inputs, though. `tenth` was rounded when we defined it, and widening the result can't turn it back into the rational one tenth. The multiplication adds no further error. A comparison with the original decimal data must account for both the literal conversion and the arithmetic.

By default, a cast to a posit follows Posit Standard (2022) §6.5. Either IEEE infinity or any NaN becomes NaR with `mappedSpecial := true`, and either signed zero becomes posit zero. If you'd rather reject those non-finite source values, pass `{ infinity := .reject, exceptional := .reject }` to `cast` as its `context`. Mixed arithmetic such as `mulAs` requires finite operands either way. Give it a non-finite one and it reports a failure before destination conversion.

[[FloatLib.Floats.ExecFloat.spec_cast]] and `preparedSpec_addAs` with its siblings spell those steps out: decode, embed, operate, round once. At the descriptor-model layer, [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_eq_roundAt]] characterizes nearest-even destination rounding for finite sources with finite results. [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_exact_of_gridExtension]] proves exact widening under its grid-inclusion and finiteness hypotheses. Configured conversion goes through its own bridge to rounding. Chapter 08 explains the difference and shows that both paths use the same NaN rule.

At the boundary with Lean's own runtime types, [[FloatLib.Floats.ExecFloat.Binary.ofFloat32]] and [[FloatLib.Floats.ExecFloat.Binary.toFloat32]] move values through the interchange word. The last line prints in Lean's native six-decimal style. NaN payloads don't survive a round trip through the native type, because `Float32.ofBits` canonicalizes them. Use `toBits32` when the payload matters.

### Evaluating an expression with one final rounding

Longer finite expressions can get one final rounding too. [[FloatLib.Floats.ExecFloat.roundOnce]] evaluates a `do` block in the exact domain, with `operand` decoding each numbered input, and quantizes the result once. The cast of `tenth` above printed `0.1`, but the stored binary32 value is exactly $13421773 \cdot 2^{-27}$. `threeTenths` is the stored $0.3$, the value $5033165 \cdot 2^{-24}$. The exact value of `3 * tenth - threeTenths` is

$$3 \cdot 13421773 \cdot 2^{-27} - 5033165 \cdot 2^{-24} = (40265319 - 40265320) \cdot 2^{-27} = -2^{-27},$$

which is representable. Round twice and the answer changes. `3 * tenth` needs 26 bits, rounds up to `threeTenths` itself, and the subtraction then gives $0$. `fma` and `roundOnce` round once and keep the exact difference.

```lean standalone
import FloatLib

open FloatLib.Floats

def tenth : Binary32 := 0.1

def threeTenths : Binary32 := 0.3

#eval 3 * tenth - threeTenths
-- 0
#eval ExecFloat.fma 3 tenth (-threeTenths)
-- -7.450581e-9

def onceRounded : ExecFloat.ConversionOutcome Binary32 :=
  ExecFloat.roundOnce (Exact := FloatLib.Numerics.SignedRat) do
    let a ← ExecFloat.ExactExpression.operand 0 tenth
    let b ← ExecFloat.ExactExpression.operand 1 threeTenths
    let three ← ExecFloat.ExactExpression.operand 2 (3 : Binary32)
    pure (three * a - b)

#eval onceRounded.value?
-- some (-7.450581e-9)
```

`ConversionOutcome Binary32`, the result type, fixes the destination. Inside the `do` block, `operand` decodes each input into `SignedRat`, so `a`, `b`, and `three` are exact values. Multiplying and subtracting them calls no binary32 operation. `0`, `1`, and `2` label the inputs for error reporting, and `pure` hands the exact expression's result to `roundOnce`, which does the destination rounding.

This matches the `fma` line, since one rounding of the exact $-2^{-27}$ is itself. [[FloatLib.Floats.ExecFloat.ConversionProof.preparedSpec_roundOnce]] states that a successful evaluation reaches the destination quantizer exactly once. A non-finite operand comes back as a failure that names its operand index, `InputPosition.operand n`, and a checked division by zero through `ExactExpression.div` comes back as the bare `divisionByZero` failure. Neither reaches the quantizer.

### Directed cancellation and the sign of zero

`roundOnce (mode := .down)` rounds the final quantization downward. If cancellation inside the exact expression has to follow the same direction, use `ExactExpression.add (target := Destination) x y (mode := .down)` or `ExactExpression.sub` inside the `do` block. Plain `SignedRat` addition keeps the nearest-even rule for the sign of an exact zero, and a directed final quantization won't change that intermediate result. Casts preserve the sign of a supplied zero. Exact cancellation under rounding toward negative infinity produces negative zero:

```lean standalone
import FloatLib

open FloatLib.Floats

def cancelledDownward : ExecFloat.ConversionOutcome Binary32 :=
  ExecFloat.roundOnce (mode := .down) do
    let a ← ExecFloat.ExactExpression.operand 0 (1 : Binary32)
    let b ← ExecFloat.ExactExpression.operand 1 (-1 : Binary32)
    ExecFloat.ExactExpression.add (target := Binary32) a b (mode := .down)

#eval cancelledDownward.value?.map ExecFloat.Binary.toBits32
-- some 2147483648
```

That word is `0x80000000`, the sign bit and nothing else, so one plus negative one really is negative zero here :) `addAs`, `subAs`, and `fmaAs` take this cancellation rule from their own `mode` or `context`.

## Complex arithmetic

Multiplying two complex numbers looks like one operation on paper:

$$
(a+bi)(c+di)=(ac-bd)+(ad+bc)i.
$$

With floating-point components, that formula hides six rounding steps. FloatLib's `ExecComplex fmt` stores two `Model fmt` values. Its multiplication rounds each of the four products, then the subtraction and the addition. Writing $R$ for the format's nearest-even rounder, the computed components are

$$
R\bigl(R(ac)-R(bd)\bigr),\qquad
R\bigl(R(ad)+R(bc)\bigr).
$$

If $ac$ and $bd$ nearly cancel, errors in the two products can dominate their difference, so a proof about the implementation has to keep those inner roundings. Replace the first component by $R(ac-bd)$ and you're describing a different algorithm. The multiplication theorem holds for any descriptor with conventional IEEE semantics:

```lean standalone
import FloatLib.Floats.Formats.BinaryInterchange.Complex.Semantics

open FloatLib.Floats.Formats.BinaryInterchange

example {fmt : FloatFormat} (x y : ExecComplex fmt)
    (hfmt : fmt.isIEEE = true) (h : ExecComplex.MulFinite x y) :
    ExecComplex.toComplex (x * y) =
      ExecComplex.roundedMul fmt
        (ExecComplex.toComplex x) (ExecComplex.toComplex y) :=
  ExecComplex.toComplex_mul_eq_roundedMul x y hfmt h
```

`MulFinite` requires finite inputs, four finite rounded products, and finite final components. Those middle conditions matter, because a product can overflow even when the exact complex answer would fit after cancellation. Componentwise addition and subtraction have matching theorems, and each rounds the real and imaginary components independently.

Division has another problem. The familiar denominator $c^2+d^2$ can overflow while $c$ and $d$ are perfectly finite, so `ExecComplex.div` uses the ratio formula from [Robert L. Smith's Algorithm 116 (1962)](https://doi.org/10.1145/368637.368661), with the larger denominator component as the pivot. When $|c|\geq|d|$, it forms a rounded ratio $r=R(d/c)$ and evaluates

$$
\frac{a+br}{c+dr}+i\,\frac{b-ar}{c+dr},
$$

rounding each scalar operation. The other branch swaps the components. `toComplex_div_eq_roundedDiv` records the selected branch and its nine rounding steps. Its `DivFinite` hypothesis asks for a nonzero pivot and rounded denominator along with finite inputs, intermediates, and results. Avoiding the two large squares helps, though other intermediates can still overflow.

Magnitude uses a similar scaling idea. With $s=\max(|a|,|b|)$, it computes the rounded counterpart of

$$
s\sqrt{(a/s)^2+(b/s)^2}.
$$

A zero scale returns zero right away. Otherwise `toReal_magnitude_eq_roundedMagnitude` accounts for seven scalar roundings: two divisions, two squares, the addition, the square root, and the final rescaling. Its `MagnitudeFinite` conditions cover the intermediate ranges and the square-root domain. `normSq` is a different operation, a rounded sum of squares with no scaling.

Exceptional components follow their own rule. If either component is infinite and neither is a signaling NaN, magnitude returns positive infinity, even when the other component is a quiet NaN. A signaling NaN goes through the scalar NaN selection and quieting rules. None of this turns the finite theorem into a correctly rounded hypotenuse operation, and it doesn't show that every intermediate stays finite.

The complex API covers basic arithmetic, conjugation, squared norm, and magnitude. Complex exponential, logarithm, and trigonometric functions aren't implemented, and the scalar transcendental APIs in the binary and posit chapters don't supply them.

## Rounding directions and status flags

Ordinary arithmetic, `x.sqrt`, and `x.fma y z` round to nearest even. Each of the six operations, such as [[FloatLib.Floats.ExecFloat.Binary.add]] or [[FloatLib.Floats.ExecFloat.Binary.div]], also takes a direction from [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]] as the option `(mode := ...)`. After `open FloatLib.Rounding` you can drop the leading dot and write `(mode := up)`. Let's divide one by three in four directions:

```lean standalone
import FloatLib

open FloatLib.Floats
open FloatLib.Rounding

#eval ExecFloat.Binary.div (1 : Binary32) 3 (mode := nearest)
-- 0.33333334
#eval ExecFloat.Binary.div (1 : Binary32) 3 (mode := up)
-- 0.33333334
#eval ExecFloat.Binary.div (1 : Binary32) 3 (mode := down)
-- 0.3333333
#eval ExecFloat.Binary.div (1 : Binary32) 3 (mode := towardZero)
-- 0.3333333
```

Those are the two binary32 neighbours of one third. Over the common denominator $2^{25}$ the lower one is $11184810 \cdot 2^{-25}$, about $0.33333331$, which prints as `0.3333333`. The upper one is $11184811 \cdot 2^{-25}$, which prints as `0.33333334`. They're adjacent significands with one third strictly between them. The [IEEE rounding discussion](#/chapter/ieee-binary-formats/directed-rounding) follows the same four directions on this value, including what changes for negative inputs.

IEEE 754 asks each operation to report five conditions: invalid, divide by zero, overflow, underflow, and inexact. They're called exceptions in the standard, though nothing is thrown. With `(status := true)` the operations return the result together with these five Booleans as an [[FloatLib.Numerics.IEEEStatus]], and also a ternary value comparing the result with the exact one. We compute the flags from the operands, the exact arithmetic, and the rounded result, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.value_add]] states that the returned value is the same as for addition without status.

```lean standalone
import FloatLib

open FloatLib.Floats
open FloatLib.Rounding

#eval ExecFloat.Binary.div (1 : Binary32) 3 (mode := down) (status := true)
-- { value := 0.3333333,
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true },
--   ternary := Ordering.lt }
#eval ExecFloat.Binary.div (1 : Binary32) 0 (status := true)
-- { value := inf,
--   status := { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := false },
--   ternary := Ordering.eq }
#eval ExecFloat.Binary.mul (1e30 : Binary32) 1e30 (status := true)
-- { value := inf,
--   status := { invalid := false, divideByZero := false, overflow := true, underflow := false, inexact := true },
--   ternary := Ordering.gt }
#eval ExecFloat.Binary.mul (1e-30 : Binary32) 1e-30 (status := true)
-- { value := 0,
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := true, inexact := true },
--   ternary := Ordering.lt }

def thirdDown := ExecFloat.Binary.div (1 : Binary32) 3 (mode := down) (status := true)
def oneOverZero := ExecFloat.Binary.div (1 : Binary32) 0 (status := true)

#eval FloatLib.Numerics.IEEEStatus.union thirdDown.status oneOverZero.status
-- { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := true }
```

The first line sets only `inexact`, because rounding changed the value. In the second, $1/0$ with a positive zero denominator returns $\infty$ and sets the divide-by-zero flag, as IEEE specifies. In the third, $10^{30} \cdot 10^{30}$ overflows, and overflow always comes with inexact. And in the fourth, $10^{-30} \cdot 10^{-30}$ lies far below the least binary32 subnormal, so the result is zero, flagged underflow and inexact. There's no global sticky register. To combine the flags from several operations, use [[FloatLib.Numerics.IEEEStatus.union]], as the last line does. Each flag is a Boolean field of the returned status, and [chapter 08](#/chapter/ieee-binary-formats) gives the theorems that characterize it.

In `thirdDown`, `value` selects the rounded number, `status` the flags, and `ternary` the direction of the rounding. So `thirdDown.status.inexact` reads one condition without throwing the value away. Above, the ternary values are `Ordering.lt` for one third rounded down, `Ordering.eq` for the exact infinity of $1/0$, `Ordering.gt` for the overflow, and `Ordering.lt` for the product rounded down to zero. Each status describes one operation on its stored operands. It doesn't report the earlier rounding that created a decimal literal or an input to the operation. If you want conditions across a whole computation, carry the statuses alongside its values and combine them with `union`.

## Choosing imports

`import FloatLib` supplies the format families and their arithmetic. For binary `exp`, `log`, and `sin`, add `FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals`, which also installs the configured and model `MathFunctions` instances. That import provides `Model.pow` and `^` on model values as well. On the default import, configured `ExecFloat.Binary` values have `powInt` for integer exponents but no power operation taking a floating-point exponent. You get the class itself and its host `Float` instance from the main import.

If you want fewer dependencies, import only the layer you need. `FloatLib.Floats.ExecFloat` gives the carrier, arithmetic, conversion, and the `run = spec` equations. `FloatLib.Floats.Formats.BinaryInterchange.Configured` adds `ExecFloat.Binary`, literals, and the configured operations. `FloatLib.Floats.Formats.BinaryInterchange.Semantics` adds the real-valued theorems. `FloatLib.Floats.Formats.Posit` is the posit family and `FloatLib.Numerics` the representation-independent layer. A program that only computes can use `FloatLib.Floats.ExecFloat.Runtime`, which has the same certified arithmetic and conversion, without the proof automation and inspection commands.

One thing these imports don't include is the [Arb adapter](https://github.com/lean-dojo/FloatLib/blob/main/tests/FloatLibTests/Arb/ModelTranscendentals.lean). It lives in the separate test workspace and calls Arb through python-flint, so its results depend on that external library, and the FloatLib library package doesn't supply it as an import.

<a id="examples-and-extension-guides"></a>

## Extending the library

The [custom-format examples](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Examples/CustomFormats.lean) configure a 16-bit binary telemetry type with a custom bias and NaN encoding, with no new format family.

A new backend for an existing format has to compute the same reference operation. The [backend guide](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/README.md) gives the registration procedure and its proof obligations, and the [one-word kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/Small) show an implementation discharging them.

A new format family also needs a meaning for its stored values. The [numerical interfaces](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Numerics/Core) define those contracts, and the [fixed-point family](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/FixedPoint) is a compact example, from encoding through arithmetic and its proofs.
