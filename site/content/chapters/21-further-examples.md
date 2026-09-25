---
number: "21"
slug: further-examples
title: "Further examples"
summary: "Worked recipes for intervals, reductions, real-valued proofs, mixed formats, and complex arithmetic."
phases: [planner-and-configured, ieee-formats, binary-arithmetic]
---

These recipes continue the [getting-started chapter](#/chapter/using-the-library). Each code block includes its own imports and definitions so it can be copied into a fresh Lean file. Choose the calculation or proof you need; the recipes do not depend on earlier blocks.

## Choosing a different endpoint format

The shared type [[FloatLib.Numerics.Interval]] is an endpoint pair `Interval α`. The type `α` can be binary, decimal, posit, or a representation supplied by your program. It does not require a particular radix or assume that the format has infinities. Constructing a pair preserves its values; `Interval.ofBounds?` additionally checks that they decode to ordered finite bounds.

Arithmetic uses [[FloatLib.Numerics.OutwardRounding]], which supplies a decoder and a function that tries to enclose an exact scalar. The scalar type is also a parameter: the common interval proofs are not restricted to rationals or binary floats. Concrete binary, decimal, and posit adapters use exact rationals so their finite interval calculations can execute.

These finite operations return `Option`: `some bounds` comes with an enclosure theorem, while `none` means the operation could not produce finite enclosing endpoints. A denominator interval crossing zero or an overflowing posit calculation can therefore fail explicitly. The [binary-specific API in the getting-started chapter](#/chapter/using-the-library/an-interval-from-two-directed-roundings) also supports infinite endpoints and retains its existing whole-range fallback. Saturating to the largest finite number would not be a sound upper bound for a larger exact result.

Here is one function used with both decimal and posit endpoints. It encloses two rational inputs, adds the intervals, and decodes the resulting bounds for inspection:

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

def positRounder : Numerics.OutwardRounding (Floats.ExecFloat.Posit 8) ℚ :=
  Floats.ExecFloat.Posit.intervalRounding

#eval enclosedSum? decimalRounder (1 / 10) (1 / 5) == some (3 / 10, 3 / 10)
-- true

#eval enclosedSum? positRounder 1 2 == some (3, 3)
-- true
```

Changing the rounder changes the stored format, not the interval algorithm. Decimal's `.bid` selects the encoding; `.dpd` uses the other IEEE decimal encoding. A custom endpoint type supplies the same small contract and can use these operations without adding another format case to the library.

Rational endpoint calculations also describe intervals of arbitrary real numbers. [[FloatLib.Numerics.Interval.ContainsReal]] interprets the finite bounds in $\mathbb{R}$, and [[FloatLib.Numerics.Interval.containsReal_mul?]] proves that a successful interval multiplication encloses the product of any two real members. The members themselves need not be rational or representable in the endpoint format.

The `interval` tactic uses these contracts to prove real inequalities directly from input
bounds. For example:

```lean standalone
import FloatLib

example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : Real.exp x < 3 := by
  interval (degree := 12)
```

[Chapter 20](#/chapter/proving-numerical-bounds) explains the evaluator, its precision controls,
and how subdivision can prove inequalities that a single interval evaluation leaves open.

<a id="reductions-that-round-once"></a>

## Sums and dot products with one rounding

When we sum a list by rounding after each addition, a small term can be lost. A binary32 significand has 24 bits, so $2^{24} + 1$ (that is, $16777216 + 1$) rounds back to $2^{24}$, and subtracting $2^{24}$ then gives zero. `sumList` and `sum` instead decode every term to an exact dyadic, accumulate the complete sum in software, and round once at the end.

```lean standalone
import FloatLib

open FloatLib.Floats

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

def values : List Binary32 := [16777216, 1, -16777216]

#eval values.foldl (· + ·) 0
-- 0
#eval ExecFloat.Binary.sumList values .nearestEven
-- 1
#eval ExecFloat.Binary.sumListWithStatus values .nearestEven
-- (1, { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := false })
#eval ExecFloat.Binary.dot #[(1.5 : Binary32), 2, 4] #[2, 3, 4] .nearestEven
-- Except.ok 25
#eval ExecFloat.Binary.dotList [(1.5 : Binary32), 2, 4] [2, 3] .nearestEven
-- Except.error (FloatLib.Numerics.ReductionError.lengthMismatch 3 2)
```

Reordering the list to `[16777216, -16777216, 1]` lets the ordinary fold cancel the large terms first and return one. The exact sum returns one in either order because it retains every term until the final rounding.

The status form reports that the exact sum was representable, with no rounding error. [[FloatLib.Floats.ExecFloat.Binary.dot]] keeps every product exact as well: $1.5 \cdot 2 + 2 \cdot 3 + 4 \cdot 4 = 25$ with one rounding at the end. A length mismatch returns an `Except.error` carrying both lengths before any arithmetic runs, as `dotWithStatus_lengthMismatch` proves. This check prevents the truncation that would result from using `List.zip` on unequal lists.

The configured functions call the reducer defined for the format's model. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Reduction.sumWithStatus_eq_round_of_finite_nonzero]] says a nonzero finite sum is one rounding of the exact sum, with exactly that rounding's status. [[FloatLib.Floats.ExecFloat.Binary.dotWithStatus_eq_model]] says the configured dot is the model dot, errors and status included.

The sequential-reduction bound reported by `#float_info [errors] Binary32` describes an algorithm in which casts, products, and accumulator updates each round. It adds the error allowance for each step, including the final output conversion, and requires the specified IEEE formats and finite intermediate values. The matrix-entry bound applies that dot-product result to one row and column. The exact `dot` above holds the products and sum until its final rounding, so it has a different error argument.

`dot` has no initial-addend argument. IEEE `fma` already covers one product plus an addend, and the [round-once expressions below](#/chapter/further-examples/evaluating-an-expression-with-one-final-rounding) cover anything larger. A posit quire, the subject of [chapter 13](#/chapter/posits-and-the-quire), also delays rounding, but it is a fixed $16n$-bit accumulator with a NaR outcome and a range condition, whereas the binary reducer uses an unbounded dyadic and follows the IEEE status rules.

## The result as a real number

The [getting-started proof](#/chapter/using-the-library/proving-arithmetic-agrees-with-its-specification) identifies the complete word returned by addition. To interpret that word as a real number, we connect the configured type to its model, then apply the model's rounding theorem.

For binary interchange the real-valued semantics are stated for [[FloatLib.Floats.Formats.BinaryInterchange.Model]], the descriptor-indexed model of [chapter 06](#/chapter/the-numerical-models). The function [[FloatLib.Floats.ExecFloat.Binary.toModel]] converts a configured value to that model. A configured binary32 value is stored as a packed `UInt32`; the model uses an exact-width record. `toModel` and its inverse `ofModel` connect the two representations.

We can build that connection a step at a time. The proof of `toModel_hAdd` below rewrites `a + b` using four facts: the refinement equation, the definition of the configured specification as the model specification lifted through the storage codec, the model's own `add = spec` theorem, and the codec law `decode_liftBinary`. Each tactic line applies one of these facts. Then [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] gives the real-number statement: for finite operands whose sum does not overflow, the decoded sum is the exact real sum rounded once by [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]].

```lean standalone
import FloatLib

open FloatLib.Floats

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

open Formats.BinaryInterchange

theorem toModel_hAdd (a b : Binary32) :
    ExecFloat.Binary.toModel (a + b) =
      Model.add (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b) := by
  rw [show a + b = ExecFloat.Spec.add a b from ExecFloat.Proof.add_eq_spec a b]
  change Configured.Family.toModel (Configured.Spec.add a b) = _
  rw [Model.Proof.add_eq_spec]
  exact ExecFloat.ModelCodec.decode_liftBinary _ _ _

theorem toReal_add_binary32 (a b : Binary32)
    (ha : Model.isFinite (ExecFloat.Binary.toModel a) = true)
    (hb : Model.isFinite (ExecFloat.Binary.toModel b) = true)
    (hout : Model.isFinite (ExecFloat.Binary.toModel (a + b)) = true) :
    Model.toReal (ExecFloat.Binary.toModel (a + b)) =
      Model.roundAt FloatFormat.binary32
        (Model.toReal (ExecFloat.Binary.toModel a) +
          Model.toReal (ExecFloat.Binary.toModel b)) := by
  rw [toModel_hAdd] at hout ⊢
  exact Model.toReal_add_eq_roundAt _ _ (by decide) ha hb hout
```

The line `rw [toModel_hAdd] at hout ⊢` rewrites both the result-finiteness hypothesis and the goal. They now mention the same `Model.add` expression, so `hout` has exactly the form the model theorem expects. The remaining arguments supply its IEEE descriptor and operand-finiteness hypotheses.

`ha` and `hb` say the operands are finite, because a NaN or an infinity has no real value to round. `Model.toReal` is a total function and returns zero on those non-finite inputs; the finiteness hypotheses are what justify interpreting it as the value of a word. `hout` says the sum did not overflow; it is decidable on the result, and when we would rather not evaluate the sum first, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt_of_abs_add_le_posMaxFinite]] accepts the symbolic bound $|a| + |b| \le \Omega$ in its place, where $\Omega$ is the largest finite value [[FloatLib.Floats.Formats.BinaryInterchange.Model.posMaxFinite]]. The `by decide` proves `fmt.isIEEE = true`, requiring the IEEE encoding and conventional bias.

We can also bound the rounding error: [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_toReal_add_sub_le]] bounds one finite nearest-even addition by half an ulp, and `#float_info [errors] Binary32` reports the relative bound $2^{-24}$ for rounding a nonzero value in the normal range. Square root is the one operation without a result-finiteness premise, since [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite_sqrt_of_isFinite]] shows it cannot overflow; it does ask that the operand be nonnegative (a signed zero counts), since a negative input yields NaN rather than a real.

For the named directed operations, [[FloatLib.Floats.ExecFloat.Binary.toModel_addWithRounding]] and the corresponding lemmas for the other five operations are already registered with `simp`. The status variants have similar lemmas, such as `toModel_divWithStatus`. A goal about a configured directed operation therefore reduces to the corresponding model theorem in one step.

We can also put the represented value in the type. `At` `fmt r` is an encoded value of format `fmt` together with a proof, erased at runtime, that it denotes the real $r$. Operations on it, such as `Model.At.add`, take the finiteness hypotheses as arguments and produce a value indexed by the rounded result.

```lean standalone
import FloatLib

open FloatLib.Floats

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

open Formats.BinaryInterchange

example (a b : Binary32) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.addWithRounding a b .nearestEven) =
      Model.addWithRounding .nearestEven
        (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b) :=
  ExecFloat.Binary.toModel_addWithRounding a b .nearestEven

example {fmt : FloatFormat} {r s : Real}
    (u : Model.At fmt r) (v : Model.At fmt s)
    (hfmt : fmt.isIEEE = true)
    (hout : Model.isFinite (Model.add u.1 v.1) = true) :
    (Model.numericalSystem fmt).denote (Model.At.add u v hfmt hout).1 =
      .finite (Model.roundAt fmt (r + s)) := by
  numerics
```

The second example says that adding a value known to denote $r$ to one known to denote $s$ gives a value that the format's numerical system interprets as the finite real $\mathrm{roundAt}(r + s)$. The type of `Model.At.add` already carries the rounded sum as its index. The `numerics` tactic closes the proof using the general rule, registered under `numerics_simps`, that an `At` value denotes its index.

The values `u` and `v` contain their own proofs: their `.1` fields are executable values, and their `.2` fields establish the finite denotations. There is no separate `ha` or `hb` here because those facts follow from the indexed types. The caller still supplies `hout`; knowing two inputs are finite does not ensure their sum fits. This view is useful when several operations share the same semantic facts, since a function can return the value together with the proof its caller will need.

These theorems describe FloatLib's software arithmetic. Relating that arithmetic to Lean's native `Float32`, C operations, or GPU instructions requires a separate argument; [chapter 17](#/chapter/performance/host-arithmetic-as-a-reference) examines the comparison with Lean's native floats.

## Mixing formats

There is no implicit promotion between formats. When a value of one type is needed at another, we name the destination: [[FloatLib.Floats.ExecFloat.cast]] takes a `target`, and `addAs`, `subAs`, `mulAs`, `divAs`, and `fmaAs` take a `result`. Each returns a `ConversionOutcome` carrying the value and its conversion status, or an explicit failure; `value?` keeps just the value. Explicit destinations show where conversion and rounding can happen, including conversions we can prove exact.

```lean standalone
import FloatLib

open FloatLib.Floats

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

abbrev Binary64 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)
abbrev Posit32 := ExecFloat.Posit (bits := 32)

#eval ((1.5 : Binary32).cast (target := Binary64)).value?
-- some 1.5
#eval ((-(0 : Binary32)).cast (target := Binary64)).value?
-- some -0

def narrowed := (0.1 : Binary64).cast (target := Binary32)

#eval narrowed.value?
-- some 13421773 * 2^-27
#eval narrowed.status?.map (·.inexact)
-- some true

def tenth : Binary32 := 0.1

#eval (1.5 : Binary32) * tenth
-- 5033165 * 2^-25

def widenedProduct := ExecFloat.mulAs (result := Binary64) (1.5 : Binary32) tenth

#eval widenedProduct.value?
-- some 40265319 * 2^-28
#eval widenedProduct.status?.map (·.inexact)
-- some false
#eval ((1.5 : Binary32).cast (target := Posit32)).value?
-- some 1.5
#eval ExecFloat.Binary.toFloat32 ((1.5 : Binary32) + 2.25)
-- 3.750000
```

A mixed operation decodes its operands exactly, computes in the destination's exact domain, and rounds once. For binary destinations that domain is [[FloatLib.Numerics.SignedRat]], a rational carrying an IEEE sign bit. A plain rational has only one zero, so casting through one would turn $-0$ into $+0$; the sign bit is why the second cast delivers $-0$. The narrowing cast reports `inexact := true` because binary64's $0.1$ does not fit in 24 bits. `status?.map (·.inexact)` selects that field from the successful conversion's status.

The two products keep the operands fixed and change the destination precision. The product of $1.5$ and the stored $0.1$ needs 26 significand bits, so `*` at binary32 rounds it to $5033165 \cdot 2^{-25}$, while `mulAs` into binary64 has room for all 26 and returns the exact $40265319 \cdot 2^{-28}$ with `inexact := false`. A posit destination computes in plain `Rat`, since posits have one zero.

Here `inexact := false` refers to the product of the represented inputs. `tenth` was already rounded when it was defined, and widening the result cannot turn it back into the rational one tenth. The benefit is that the multiplication adds no further error. This distinction also matters when comparing a computed result with a formula over the original decimal data: literal conversion and arithmetic contribute at different places.

Casting to a posit follows Posit Standard (2022) §6.5 by default: either IEEE infinity or any NaN becomes NaR with `mappedSpecial := true`, and either signed zero becomes posit zero. To reject those non-finite source values, pass `{ infinity := .reject, exceptional := .reject }` to `castWith`. Mixed arithmetic such as `mulAs` still requires finite operands and reports a failure before destination conversion if an operand is non-finite.

We can use [[FloatLib.Floats.ExecFloat.spec_cast]] and `preparedSpec_addAs` with its siblings to make those steps precise: decode, embed, operate, round once. At the descriptor-model layer, [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_eq_roundAt]] characterizes nearest-even destination rounding for finite sources with finite results, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_exact_of_gridExtension]] proves exact widening under its grid-inclusion and finiteness hypotheses. The configured conversion pipeline has its own bridge to rounding; chapter 08 explains the distinction and shows that both paths use the same NaN rule.

At the boundary with Lean's own runtime types, [[FloatLib.Floats.ExecFloat.Binary.ofFloat32]] and [[FloatLib.Floats.ExecFloat.Binary.toFloat32]] move values through the interchange word, and the last line prints in Lean's native six-decimal style. A NaN payload does not round-trip through the native type, because `Float32.ofBits` canonicalizes it; use `toBits32` when the payload matters.

### Evaluating an expression with one final rounding

We can evaluate a longer finite expression with one final rounding. [[FloatLib.Floats.ExecFloat.roundOnce]] evaluates a `do` block in the exact domain, with `operand` decoding each numbered input, and quantizes the result once. `tenth` is the stored binary32 value of $0.1$, which the cast above printed as $13421773 \cdot 2^{-27}$; `threeTenths` is the stored $0.3$, the value $5033165 \cdot 2^{-24}$. The exact value of `3 * tenth - threeTenths` is

$$3 \cdot 13421773 \cdot 2^{-27} - 5033165 \cdot 2^{-24} = (40265319 - 40265320) \cdot 2^{-27} = -2^{-27},$$

which is representable. Rounding twice gives a different answer: `3 * tenth` needs 26 bits, rounds up to exactly `threeTenths`, and the subtraction then gives $0$. `fma` and `roundOnce` round once and preserve the exact difference.

```lean standalone
import FloatLib

open FloatLib.Floats

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

def tenth : Binary32 := 0.1

def threeTenths : Binary32 := 0.3

#eval 3 * tenth - threeTenths
-- 0
#eval ExecFloat.fma 3 tenth (-threeTenths)
-- -1 * 2^-27

def onceRounded : ExecFloat.ConversionOutcome Binary32 :=
  ExecFloat.roundOnce (Exact := FloatLib.Numerics.SignedRat) do
    let a ← ExecFloat.ExactExpression.operand 0 tenth
    let b ← ExecFloat.ExactExpression.operand 1 threeTenths
    let three ← ExecFloat.ExactExpression.operand 2 (3 : Binary32)
    pure (three * a - b)

#eval onceRounded.value?
-- some -1 * 2^-27
```

The result type `ConversionOutcome Binary32` fixes the destination. Inside the `do` block, `operand` decodes each input into `SignedRat`, so `a`, `b`, and `three` are exact values and their multiplication and subtraction do not invoke binary32 operations. The numbers `0`, `1`, and `2` label inputs for error reporting. `pure` returns the exact expression's result to `roundOnce`, which performs the destination rounding.

The result matches the `fma` line: one rounding of the exact $-2^{-27}$ is itself. [[FloatLib.Floats.ExecFloat.ConversionProof.preparedSpec_roundOnce]] states that a successful evaluation reaches the destination quantizer exactly once. A non-finite operand is returned as a failure that names its operand index, `InputPosition.operand n`, and a checked division by zero through `ExactExpression.div` as the bare `divisionByZero` failure; neither reaches the quantizer.

### Directed cancellation and the sign of zero

`roundOnceWith` supplies an explicit context for the final quantization. If cancellation in the exact expression must follow that context, use `ExactExpression.addWith (result := Destination) context x y` or `ExactExpression.subWith (result := Destination) context x y` inside the `do` block. Ordinary `SignedRat` addition still uses the nearest-even rule for the sign of an exact zero; passing a directed context to the final quantizer does not change that intermediate result. Casts preserve the sign of a supplied zero.

For example, exact cancellation under rounding toward negative infinity produces negative zero:

```lean standalone
import FloatLib

open FloatLib.Floats

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

def downwardContext := ExecFloat.Binary.Conversion.Context.withRounding .towardNegative

def cancelledDownward : ExecFloat.ConversionOutcome Binary32 :=
  ExecFloat.roundOnceWith downwardContext do
    let a ← ExecFloat.ExactExpression.operand 0 (1 : Binary32)
    let b ← ExecFloat.ExactExpression.operand 1 (-1 : Binary32)
    ExecFloat.ExactExpression.addWith (result := Binary32) downwardContext a b

#eval cancelledDownward.value?.map ExecFloat.Binary.toBits32
-- some 2147483648
```

The word is `0x80000000`: the sign bit is set and every other bit is zero. `addAsWith`, `subAsWith`, and `fmaAsWith` apply this cancellation rule directly from their supplied context.

## Complex arithmetic

Multiplying two complex numbers looks like one operation on paper:

$$
(a+bi)(c+di)=(ac-bd)+(ad+bc)i.
$$

For floating-point components, that formula contains six rounding steps. FloatLib's `ExecComplex fmt` stores two `Model fmt` values. Its multiplication rounds each of the four products, then rounds the subtraction and addition. Writing $R$ for the format's nearest-even rounder, the computed components are

$$
R\bigl(R(ac)-R(bd)\bigr),\qquad
R\bigl(R(ad)+R(bc)\bigr).
$$

If $ac$ and $bd$ nearly cancel, errors in the two products can dominate their difference. A proof about the implementation has to preserve those inner roundings. Replacing the first component by $R(ac-bd)$ would describe a different algorithm.

Here is the multiplication theorem for any descriptor with conventional IEEE semantics:

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

`MulFinite` requires finite inputs, four finite rounded products, and finite final components. The intermediate conditions matter: a product can overflow even when the exact complex answer would fit after cancellation. Componentwise addition and subtraction have corresponding theorems; each rounds its real and imaginary components separately.

Division raises another problem. The familiar denominator $c^2+d^2$ can overflow while $c$ and $d$ are still finite. `ExecComplex.div` uses the ratio formula from [Robert L. Smith's Algorithm 116 (1962)](https://doi.org/10.1145/368637.368661), choosing the larger denominator component as a pivot. When $|c|\geq|d|$, it forms a rounded ratio $r=R(d/c)$ and evaluates

$$
\frac{a+br}{c+dr}+i\,\frac{b-ar}{c+dr},
$$

rounding each scalar operation. The other branch swaps the components. `toComplex_div_eq_roundedDiv` records the selected branch and its nine rounding steps. The `DivFinite` hypothesis requires a nonzero pivot and rounded denominator, along with finite inputs, intermediates, and results. Avoiding the two large squares helps, but other intermediates can still overflow.

Magnitude uses a similar scaling idea. With $s=\max(|a|,|b|)$, it computes the rounded counterpart of

$$
s\sqrt{(a/s)^2+(b/s)^2}.
$$

A zero scale returns zero directly. Otherwise, `toReal_magnitude_eq_roundedMagnitude` accounts for seven scalar roundings: two divisions, two squares, the addition, square root, and final rescaling. Its `MagnitudeFinite` conditions cover the intermediate ranges and square-root domain. The separate `normSq` operation computes a rounded sum of squares; it does not use this scaling.

Exceptional components follow a separate rule. If either component is infinite and neither is a signaling NaN, magnitude returns positive infinity, even when the other component is a quiet NaN. A signaling NaN instead follows the scalar NaN selection and quieting rules. This does not strengthen the finite theorem into a correctly rounded hypotenuse operation or establish that every intermediate stays finite.

These contracts let a larger proof reason about the operations that actually ran. They cover basic complex arithmetic, conjugation, squared norm, and magnitude. Complex exponential, logarithm, and trigonometric functions are not implemented; the scalar transcendental APIs in the binary and posit chapters do not supply them.

## Rounding directions and status flags

Ordinary arithmetic, `x.sqrt`, and `x.fma y z` use nearest-even rounding. Each of the six operations also has a `*WithRounding` form, such as [[FloatLib.Floats.ExecFloat.Binary.addWithRounding]] or [[FloatLib.Floats.ExecFloat.Binary.divWithRounding]], that requires a direction from [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]]. The argument can be named, `(rounding := ...)`, or positional. After `open scoped FloatLib.IEEERounding`, the two infinite directions may be written `+∞` and `-∞`; the scope keeps this notation separate from $\infty$ in extended-real expressions.

```lean standalone
import FloatLib

open FloatLib.Floats

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

open scoped FloatLib.IEEERounding

#eval ExecFloat.Binary.divWithRounding (1 : Binary32) 3 (rounding := .nearestEven)
-- 11184811 * 2^-25
#eval ExecFloat.Binary.divWithRounding (1 : Binary32) 3 (rounding := +∞)
-- 11184811 * 2^-25
#eval ExecFloat.Binary.divWithRounding (1 : Binary32) 3 (rounding := -∞)
-- 5592405 * 2^-24
#eval ExecFloat.Binary.divWithRounding (1 : Binary32) 3 (rounding := .towardZero)
-- 5592405 * 2^-24
```

The output shows two dyadics in lowest terms. Over the common denominator $2^{25}$ they are $11184810 \cdot 2^{-25}$ (about $0.33333331$, printed as $5592405 \cdot 2^{-24}$) and $11184811 \cdot 2^{-25}$ (about $0.33333334$), adjacent significands with one third strictly between them. The [IEEE rounding discussion](#/chapter/ieee-binary-formats/directed-rounding) follows all four directions on this value, including what changes for negative inputs.

IEEE 754 asks each operation to report five conditions, called exceptions in the standard though nothing is thrown: invalid, divide by zero, overflow, underflow, and inexact. The `WithStatus` variants return the result together with these five Booleans as an [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEStatus]]. They compute the flags from the operands, exact arithmetic, and rounded result. [[FloatLib.Floats.Formats.BinaryInterchange.Model.addWithStatus_value]] states that the returned value is the same as for addition without status.

```lean standalone
import FloatLib

open FloatLib.Floats

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

open scoped FloatLib.IEEERounding

#eval ExecFloat.Binary.divWithStatus (1 : Binary32) 3 (rounding := -∞)
-- (5592405 * 2^-24, { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true })
#eval ExecFloat.Binary.divWithStatus (1 : Binary32) 0 (rounding := .nearestEven)
-- (inf, { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := false })
#eval ExecFloat.Binary.mulWithStatus (1e30 : Binary32) 1e30 (rounding := .nearestEven)
-- (inf, { invalid := false, divideByZero := false, overflow := true, underflow := false, inexact := true })
#eval ExecFloat.Binary.mulWithStatus (1e-30 : Binary32) 1e-30 (rounding := .nearestEven)
-- (0, { invalid := false, divideByZero := false, overflow := false, underflow := true, inexact := true })

def thirdDown := ExecFloat.Binary.divWithStatus (1 : Binary32) 3 (rounding := -∞)
def oneOverZero := ExecFloat.Binary.divWithStatus (1 : Binary32) 0 (rounding := .nearestEven)

#eval FloatLib.Numerics.IEEEStatus.union thirdDown.2 oneOverZero.2
-- { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := true }
```

The first line sets only `inexact`, because rounding changed the value. On the second, $1/0$ with a positive zero denominator returns $\infty$ and sets the divide-by-zero flag, as IEEE specifies. On the third, $10^{30} \cdot 10^{30}$ overflows, and overflow always comes with inexact. On the fourth, $10^{-30} \cdot 10^{-30}$ lies far below the least binary32 subnormal, so the result is zero, flagged underflow and inexact. There is no global sticky register. [[FloatLib.Numerics.IEEEStatus.union]] combines the flags from several operations, as the last line does. Each flag is a Boolean field of the returned status; [chapter 08](#/chapter/ieee-binary-formats) gives the theorems that characterize it.

In `thirdDown`, `.1` selects the rounded number and `.2` selects the status, so `thirdDown.2.inexact` reads one condition without discarding the value. Each status describes that operation on its stored operands. It does not also report the earlier rounding that created a decimal literal or an input to the operation. To retain conditions across a computation, carry the statuses alongside its values and combine them with `union`.

## Choosing imports

`import FloatLib` supplies the format families and their arithmetic. For binary `exp`, `log`, and `sin`, add `FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals`; this installs the configured and model `MathFunctions` instances too. The same import provides `Model.pow` and `^` on model values. Configured `ExecFloat.Binary` values have `powInt` for integer exponents on the default import, but no power operation taking a floating-point exponent. The class itself and its host `Float` instance are available from the main import.

For a smaller set of dependencies, import the layer you need. `FloatLib.Floats.ExecFloat` gives the carrier, arithmetic, conversion, and the `run = spec` equations. `FloatLib.Floats.Formats.BinaryInterchange.Configured` adds `ExecFloat.Binary`, literals, and the configured operations, and `FloatLib.Floats.Formats.BinaryInterchange.Semantics` adds the real-valued theorems. `FloatLib.Floats.Formats.Posit` is the posit family and `FloatLib.Numerics` the representation-independent layer. A program that only computes can use `FloatLib.Floats.ExecFloat.Runtime`, which supplies the same certified arithmetic and conversion without the proof automation and inspection commands.

The [Arb adapter](https://github.com/lean-dojo/FloatLib/blob/main/tests/FloatLibTests/Arb/ModelTranscendentals.lean) belongs to the separate test workspace. It calls Arb through python-flint, so its results depend on that external library; it is not an import supplied by the FloatLib library package.

<a id="examples-and-extension-guides"></a>

## Extending the library

For another layout within an existing family, the [custom-format examples](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Examples/CustomFormats.lean) configure 24-bit and 71-bit binary types without defining a new format family.

A new backend for an existing format must compute the same reference operation. The [backend guide](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/README.md) gives the registration procedure and its proof obligations; the [one-word kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/Small) show how an implementation discharges them. A new format family also needs a meaning for its stored values. The [numerical interfaces](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Numerics/Core) define those contracts, and the [fixed-point family](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/FixedPoint) supplies a compact example, from encoding through arithmetic and its proofs.
