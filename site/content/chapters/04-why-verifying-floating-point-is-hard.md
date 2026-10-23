---
number: "04"
slug: why-verifying-floating-point-is-hard
title: Proving floating-point arithmetic correct
summary: Correctness proofs must account for rounding, exceptional values, and the way an implementation evaluates an expression.
---

Correct rounding specifies one operation: compute its exact result, then select a representable value. In a program, the selected value becomes the input to the next operation. Moving a pair of parentheses can change where rounding happens; changing an intermediate format can change which side of a midpoint the next operation sees. The bit patterns and rounding rule developed in [chapter 02](#/chapter/from-reals-to-machine-numbers) let us follow these effects precisely. To verify an implementation, we also need to show that its shifts, table lookups, and exceptional branches implement that rule for every input.

## Limits of exhaustive testing

A binary64 addition has $2^{64} \cdot 2^{64} = 2^{128}$ possible input pairs. At a billion tests per second that's about $10^{22}$ years. Binary32 has $2^{64}$ pairs, which is a few hundred years at the same rate. Smaller widths are where exhaustive testing becomes feasible. Binary16 has $2^{32}$ ordered pairs, roughly four billion, and an eight-bit format has $2^{16} = 65{,}536$, few enough to fit in a table. Real running time also depends on how expensive the expected result is to compute. [Figure 4.1](#/chapter/why-verifying-floating-point-is-hard/figure-ch02-state-space) compares the counts at the same hypothetical rate for every format.

![Ordered input pairs of one binary operation at 8, 16, 32 and 64 bits, read also as the time to run them all at a billion tests per second; binary32 and binary64 are impractical to enumerate at this rate](assets/ch02-state-space.png "Ordered pairs for one binary operation, on a logarithmic scale. The time scale assumes one billion checks per second and is illustrative, not a measured test run.")

For formats of eight bits or fewer, the table backends evaluate the reference operation once at every pair of inputs and store the results. A `CertifiedBinary` kernel carries that table with two certificates. `table_eq` says every entry equals the operation the table was generated from, and `model_eq_spec` says the generating operation equals the reference. [[FloatLib.Floats.Formats.BinaryInterchange.Configured.ByteTable.runBinary_eq_lift]] then states that calling the table gives the same result as the configured model operation, and corresponding theorems cover operations with one and three arguments.

Binary16 sits in between. You can compare the library's addition and multiplication with MPFR [@fousseMpfr2007] in batches of the $2^{32}$ ordered input pairs. Batching makes an exhaustive comparison manageable, but it's only complete once every batch has run. The completed binary16 and bfloat16 comparisons in [chapter 19](#/chapter/external-validation) cover all $2^{32}$ pairs of each operation in each of the four tested rounding directions.

For binary32 and binary64, tests can exercise known hard cases and search for disagreements, but they can't practically enumerate the whole input space. A proof gets around this because its variables range over arbitrary input words. An argument about how many low bits a shift discards, for example, can cover every significand and exponent at once, without evaluating $2^{128}$ individual cases.

## Rounding changes algebraic identities

Real addition is associative, and real multiplication distributes over addition. Correct rounding breaks both laws, because grouping an expression differently changes which intermediate results get rounded. Our $2^{-24}$ example isolates this effect: all three inputs are exactly representable, and the small term is half the grid spacing at one. We build it from its bit pattern below, so no decimal conversion is involved:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

def halfUlp : Binary32 :=
  ExecFloat.Binary.ofBits32 0x33800000

#eval ExecFloat.Binary.toRat? halfUlp
-- some (1 / 16777216)

#eval ((1 : Binary32) + halfUlp) + halfUlp
-- 1

#eval (1 : Binary32) + (halfUlp + halfUlp)
-- 1.0000001
```

In the first grouping, adding `halfUlp` to one lands halfway between two binary32 values, and the tie goes to one, which has the even significand. The second addition starts from one again and hits the same tie. In the other grouping the two small terms add exactly to $2^{-23}$, a full step on the grid at one. Adding that step is exact too, and the printed `1.0000001` is $1 + 2^{-23}$. Every addition obeyed the rounding rule. Their intermediate exact sums were different. Distributivity fails for the same reason:

```lean
#eval (10 : Binary64) * (0.1 + 0.7)
-- 7.999999999999999

#eval (10 : Binary64) * 0.1 + 10 * 0.7
-- 8
```

The first result is $8 - 2^{-50}$. To see where it comes from, call the stored binary64 values of `0.1` and `0.7` $A$ and $B$. Measured in grid steps of $2^{-53}$, their exact sum is

$$
  A+B = \left(7205759403792793 + \frac14\right)2^{-53}.
$$

The addition throws away the quarter-step, and multiplying its rounded result by ten gives the exact intermediate $8 - 3\cdot2^{-52}$. Just below eight the binary64 values are spaced $2^{-50}$ apart, so that intermediate is three quarters of a step below eight. It rounds to the neighbour below eight, and that's the first printed result. In the distributed expression, the exact products before rounding are

$$
  10A = 1 + 2^{-54}, \qquad 10B = 7 - 2^{-51}.
$$

The first rounds to one. The second sits halfway between seven and the word below it, and since seven has the even significand, the tie goes to seven. Adding the two rounded products gives exactly eight. Both expressions started from the same stored constants, and distributing the multiplication changed which errors reached the final addition. Decimal literals add a rounding before the arithmetic even starts. For $0.1 + 0.2 \ne 0.3$, [chapter 02](#/chapter/from-reals-to-machine-numbers) follows the conversion of each literal and then the addition. In binary64 the sum lands one ulp above the rounded `0.3`:

```lean
#eval ExecFloat.Binary.toBits64 ((0.1 : Binary64) + 0.2)
-- 4599075939470750516

#eval ExecFloat.Binary.toBits64 (0.3 : Binary64)
-- 4599075939470750515

#eval ((0.1 : Binary64) + 0.2) == (0.3 : Binary64)
-- false
```

The two words are `0x3fd3333333333334` and `0x3fd3333333333333`. We got the first by adding two inputs that were already rounded and then rounding their sum, while the second is the exact decimal three-tenths, rounded once.

Another familiar rule breaks too, since $x + y = x$ doesn't imply $y = 0$. In binary32 the integers above $2^{24}$ are spaced two apart, so adding one to $2^{24}$ is a tie, and the tie goes to even, which is the original value. A status-bearing operation can at least report that information was discarded. [[FloatLib.Floats.ExecFloat.Binary.add]] with `(status := true)` returns an outcome containing the value, five IEEE flags, and the direction of rounding relative to the exact answer. In the example, `.2` selects the status field:

```lean
#eval (16777216 : Binary32) + 1
-- 16777216

#eval (ExecFloat.Binary.add (16777216 : Binary32) 1 (status := true)).2
-- { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true }
```

The `inexact` flag records that this addition didn't return its exact real sum, but it says nothing about how big the discarded increment was. So a loop that counts by adding one to a binary32 accumulator stops counting at $2^{24}$, which is not what you want from a counter :) Every addition after that returns the same word and sets the same flag.

Subtraction has its own trap. When a subtraction gives a poor answer, it's tempting to blame the subtraction, but check first where the error came in. Sterbenz's lemma [@sterbenz1974] says that subtracting nearby floating-point values is exact under the conditions stated below. Yet the difference can still be a poor approximation to the quantity we meant to calculate:

```lean
#eval ((1 : Binary32) + 1e-6) - 1
-- 9.536743e-7
```

In real arithmetic the answer is $10^{-6}$. The computed value is $2^{-20} \approx 9.54 \times 10^{-7}$, off by almost five percent, and yet the subtraction itself is exact. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_of_sterbenz_of_same_sign]] covers finite values of the same sign whose magnitudes lie within a factor of two, and for those it states that the decoded difference is the exact real difference. Here it is at binary32, with `by decide` discharging the hypothesis that the format is a conventional IEEE one:

```lean
example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hsign : 0 ≤ Model.toReal x * Model.toReal y)
    (hxy : |Model.toReal x| ≤ 2 * |Model.toReal y|)
    (hyx : |Model.toReal y| ≤ 2 * |Model.toReal x|) :
    Model.toReal (Model.sub x y) = Model.toReal x - Model.toReal y :=
  Model.toReal_sub_eq_of_sterbenz_of_same_sign (by decide) hx hy hsign hxy hyx
```

The error came from the addition. It rounded $1 + 10^{-6}$ to the nearest multiple of $2^{-23}$ and introduced an absolute error of about $4.6 \times 10^{-8}$. Subtracting one leaves that absolute error alone but shrinks the result by a factor of about a million, so the relative error grows sharply. An exact subtraction can't recover what the addition threw away. [Chapter 07](#/chapter/the-mathematics-of-rounding) develops the grid form of Sterbenz's lemma, [[FloatLib.Floats.Formats.Flocq.generic_format_FLX_sterbenz]].

## Rounding twice

Rounding an exact value to an intermediate precision can move it onto a midpoint of the final format, and the second rounding then breaks a tie that the original value never had. Consider

$$x = 1 + 2^{-24} + 2^{-53}.$$

Round it straight to binary32 and it goes up, because it's just above the midpoint between $1$ and $1 + 2^{-23}$. Round it to binary64 first and it's a tie, since $2^{-53}$ is half the binary64 spacing at one. Nearest-even gives $1 + 2^{-24}$, which is a binary32 midpoint, so the final rounding returns $1$. Those two grids are too far apart in spacing to draw on one line. So [Figure 4.2](#/chapter/why-verifying-floating-point-is-hard/figure-ch02-double-rounding) uses three binary digits in place of binary32's 24 and five in place of binary64's 53 to make both rounding steps visible. Otherwise the arithmetic is the same.

![The chapter's double rounding on grids small enough to draw: with three binary digits as the target and five as the intermediate, x = 1 + 2^-3 + 2^-5 rounds once to 1.25 and twice, through the five-digit grid, to 1](assets/ch02-double-rounding.png "The intermediate rounding lands exactly on a target-grid midpoint. Rounding again therefore returns a different value from rounding the original input once.")

On the smaller grids the marked input is $37/32$. The five-digit grid has spacing $1/16$, and the input's two neighbours there, $36/32$ and $38/32$, are equally far away. In units of that spacing their significands are 18 and 19, so the first rounding picks the even one, $36/32 = 9/8$. On the three-digit grid $9/8$ is a new tie, between $1 = 4/4$ and $5/4$, and now the even significand is 4, which gives one. Direct rounding starts from the original $37/32$, and that's closer to $40/32 = 5/4$ than to one. The vertical dotted line in the figure follows the intermediate value that lost this distinction.

We can run this on the model operations too. The value is the dyadic $(2^{53} + 2^{29} + 1) \cdot 2^{-53}$. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Policy.roundDyadic]] rounds an exact dyadic into a format under a [[FloatLib.Numerics.QuantizationPolicy]], and its third argument is entropy for stochastic rounding, which nearest-even ignores:

```lean
open FloatLib.Numerics (QuantizationPolicy)

def justAboveMidpoint : FloatLib.Numerics.Dyadic :=
  { negative := false, significand := 2^53 + 2^29 + 1, exponent := -53 }

def direct32 : Model FloatFormat.binary32 :=
  Model.Policy.roundDyadic FloatFormat.binary32
    QuantizationPolicy.nearest 0 justAboveMidpoint

def via64 : Model FloatFormat.binary64 :=
  Model.Policy.roundDyadic FloatFormat.binary64
    QuantizationPolicy.nearest 0 justAboveMidpoint

#eval Model.toDyadic? direct32
-- some { negative := false, significand := 8388609, exponent := -23 }

#eval Model.toDyadic? via64
-- some { negative := false, significand := 4503599895805952, exponent := -52 }

#eval Model.toDyadic?
  (Model.cast FloatFormat.binary64 FloatFormat.binary32 via64)
-- some { negative := false, significand := 8388608, exponent := -23 }
```

Direct rounding gives significand $8388609$ at exponent $-23$, which is $1 + 2^{-23}$. Going through binary64 gives $1 + 2^{-24}$, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast]] to binary32 then gives significand $8388608$, which is $1$. So the two answers end up one ulp apart.

The same thing can happen on x87, where a computation rounds first in an 80-bit register and again when it's stored to a 64-bit memory slot. Whether an intermediate stays in a register or gets spilled to memory can then change later results. [Chapter 07](#/chapter/the-mathematics-of-rounding) proves double-rounding identities under specific hypotheses, including results for directed modes and for round to odd followed by nearest even on a fixed grid. For nearest-even, the example above shows why no general identity can hold.

You can change the number of roundings on purpose with fused multiply-add. An FMA rounds $xy + z$ once. A multiplication followed by an addition rounds the product before the sum ever sees it, and the bits the product drops can change the final answer:

```lean
def a : Binary32 :=
  ExecFloat.Binary.ofBits32 0x3f800800

#eval ExecFloat.Binary.toRat? a
-- some (4097 / 4096)

#eval ExecFloat.Binary.toRat? (ExecFloat.fma a a (-1))
-- some (8193 / 16777216)

#eval ExecFloat.Binary.toRat? (a * a - 1)
-- some (1 / 2048)
```

Here $a = 1 + 2^{-12}$, so $a^2 - 1 = 2^{-11} + 2^{-24}$ exactly, and that's what the fused operation [[FloatLib.Floats.ExecFloat.fma]] returns. The unfused product needs 25 significant bits, so it rounds to $1 + 2^{-11}$ and the subtraction returns $2^{-11}$. A compiler may contract `a * a - 1` into an FMA when the language and compilation options allow it. So before you can verify that expression, you have to pin down whether contraction is allowed. At the model level, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_fma_eq_roundAt]] specifies the fused operation as one rounding of the exact expression.

## Exceptional values and signed zeros

Arithmetic on stored words also has to handle infinities, NaNs, and signed zeros. You can't derive their behaviour from arithmetic on the reals, so they need rules of their own. An infinity absorbs every finite addend, so $x + \infty = \infty$ doesn't determine $x$. A NaN isn't equal to itself under IEEE comparison, so IEEE equality isn't reflexive, but Lean's structural equality on the stored word is:

```lean
#eval ((0 : Binary32) / 0) == ((0 : Binary32) / 0)
-- false

#eval ((0 : Binary32) / 0) = ((0 : Binary32) / 0)
-- true
```

The first expression uses the IEEE comparison installed as `==` for `ExecFloat` types, and the second decides equality of bit patterns. So `x == x` is false for a NaN, while `x = x` holds for every stored word. A theorem about structural equality can establish that two computations return the same NaN word without asserting that IEEE comparison returns true.

Every IEEE ordered comparison with a NaN operand returns false, so for a NaN `x`, both `x < 1` and `1 < x` fail. That means a clamp written as `if x < bound then x else bound` returns `bound`, and it replaces the NaN with a finite value when the bound is finite. Arithmetic, on the other hand, can propagate a quiet NaN without raising `invalid` again. Below, `invalid` is set by an operation that creates a NaN and clear in an addition that propagates one:

```lean
def nan32 : Binary32 := (0 : Binary32) / 0
def inf32 : Binary32 := (1 : Binary32) / 0

#eval nan32 < 1
-- false

#eval (1 : Binary32) < nan32
-- false

#eval if nan32 < 1 then nan32 else (1 : Binary32)
-- 1

#eval inf32 + (-1000000) == inf32
-- true

#eval (ExecFloat.Binary.sub inf32 inf32 (status := true)).2
-- { invalid := true, divideByZero := false, overflow := false, underflow := false, inexact := false }

#eval (2 : Binary32) * (nan32 + 1)
-- nan

#eval (ExecFloat.Binary.add nan32 1 (status := true)).2
-- { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := false }
```

A propagated quiet NaN still shows that the value is a NaN, but its status flags need not show which earlier operation created it. And once the program replaces it with a finite value, as the clamp does, even that is gone, unless the program kept the earlier status or checked the input.

The two zeros are equal under `==` and different under `=`, the other way round from a NaN. Default nearest-even arithmetic distinguishes them, with $(-0) + (-0) = -0$ but $(-0) + 0 = +0$, and $(-0) \cdot 3 = -0$.

Status flags are one more piece of state that real arithmetic doesn't have. Every status-bearing operation returns five of them, the fields of [[FloatLib.Numerics.IEEEStatus]], and they record conditions such as overflow and inexactness. Dividing by zero and dividing zero by zero return different nonfinite values and set different flags:

```lean
#eval (ExecFloat.Binary.div (1 : Binary32) 0 (status := true)).2
-- { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := false }

#eval (ExecFloat.Binary.div (0 : Binary32) 0 (status := true)).2
-- { invalid := true, divideByZero := false, overflow := false, underflow := false, inexact := false }
```

Hardware usually accumulates these flags in a status register. We return them with each result instead, so ordinary program logic can use them. [[FloatLib.Floats.Formats.BinaryInterchange.Model.div_divideByZero]] says the divide-by-zero flag is set exactly when a finite nonzero operand is divided by a zero, and `div_invalid` gives the exact invalid predicate, including a signaling NaN operand and infinity divided by infinity. None of this survives decoding the result to a real number.

## Error bounds and exact output words

Higham's textbook [@higham2002] and Goldberg's survey [@goldberg1991] use the classic analysis throughout. It writes $\mathrm{fl}(x \circ y) = (x \circ y)(1 + \delta)$ with $|\delta| \le u$, where $u$ is the unit roundoff, and under its range assumptions this bounds the error an operation introduces. It's useful because the analysis can go ahead without knowing the exact rounded result. The catch is that the bound admits any result within the allowed error. Subnormal results need an absolute-error treatment, and overflow needs its own handling. Even where the relative bound applies, meeting it doesn't establish correct rounding.

Take the halfway value $t = 1 + 2^{-24}$ in binary32. Both one and $1 + 2^{-23}$ are $2^{-24}$ away from it. Either candidate satisfies the relative bound, because dividing that error by $t>1$ makes it smaller than the unit roundoff $2^{-24}$. Nearest-even still requires one, since its significand is even and the upper neighbour's is odd. So an implementation that returned the upper neighbour would pass this error-bound check and fail the rounding specification. The bound accepts both candidates, while the rounding rule accepts only one.

A bit specification fixes one output word for each input and rounding mode. To prove it you need enough information about the exact intermediate to choose that word, including the tie-breaking bits and the exceptional cases. From the equality with the specified rounding, we can derive an error bound using the rounding rule's properties. The layers in [chapter 06](#/chapter/the-numerical-models) retain both kinds of result, equalities for implementations and bounds for numerical analysis.

## Compilers and hardware

A proof about source code depends on the execution rules assigned to that code. Monniaux's paper on the pitfalls of verifying floating-point computations [@monniaux2008] documents several ways those rules can depend on the environment. Where it's permitted, a compiler may contract multiplication and addition into an FMA, keep an intermediate in an 80-bit register, or reassociate a sum under a fast-math option. A processor may run with flush-to-zero on, replacing subnormal results with zero, and a call may see a rounding mode that earlier code set. Each of these changes the arithmetic the proof has to describe.

A theorem about Lean definitions tells us nothing about an `addss` instruction until some argument connects the two. Certified `ExecFloat` arithmetic is software. The definitions used in proofs are the ones compiled into the program, and we assume that the Lean compiler implements integer and bit-vector operations correctly. The optional host operations, with calls such as `Unchecked.add32`, are a different story. They live in the [unchecked host-arithmetic module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean), which is outside the default `import FloatLib` path, and their hardware calls rest on different assumptions from the certified software operations. [Chapter 18](#/chapter/lean-native-floats/opting-into-guarded-host-operations) describes the guards and execution conditions that matter when you compare their results.

## Overflow policy and the sign of zero

An encoding says which values the bits can represent, but a conversion policy also has to say what happens when the exact input lies outside that set. That second question matters most for small formats, whose conventions for infinities and zeros differ. E4M3FN, for example, is an 8-bit format with no infinity. When a positive result is too large to round back to its largest finite value $448$, the conversion policy has to pick an outcome. FloatLib supports two, returning a NaN word or saturating at $448$. Both policies use the same E4M3FN encoding. The field widths don't decide between them, and a proof under one policy doesn't carry over to the other. A [[FloatLib.Numerics.QuantizationPolicy]] argument selects the policy, so the same input can produce different words:

```lean
def exact500 : FloatLib.Numerics.Dyadic :=
  { negative := false, significand := 500, exponent := 0 }

#eval Model.toNatBits <| Model.Policy.roundDyadic FloatFormat.e4m3fn
  QuantizationPolicy.nearest 0 exact500
-- 127

#eval Model.toNatBits <| Model.Policy.roundDyadic FloatFormat.e4m3fn
  QuantizationPolicy.saturating 0 exact500
-- 126
```

The word $127$ is `0x7f`, the NaN code, and $126$ is `0x7e`, which encodes $448$. [Chapter 11](#/chapter/low-precision-formats-for-machine-learning) has the mathematics of both policies.

A cast between formats also has to keep whatever later operations need, and that includes the sign of zero. Convert through the rational numbers and you forget whether a zero was negative, because $\mathbb{Q}$ has one zero. Our exact conversion domain, `SignedRat`, keeps it. It's a rational together with an IEEE sign bit, and its arithmetic implements the IEEE sign rules. [[FloatLib.Floats.ExecFloat.Binary.decode]] returns such a value and keeps the sign, while [[FloatLib.Floats.ExecFloat.Binary.toRat?]] returns a plain rational and doesn't:

```lean
#eval ExecFloat.Binary.decode ((-(0 : Binary32)) + (-(0 : Binary32)))
-- FloatLib.Numerics.NumericalValue.finite -0

#eval ExecFloat.Binary.decode ((-(0 : Binary32)) + 0)
-- FloatLib.Numerics.NumericalValue.finite 0

#eval ExecFloat.Binary.toRat? (-(0 : Binary32))
-- some 0
```

For the default nearest-even addition, `negative_add_of_eq_zero` states the rule, which is that an exact zero sum is negative exactly when both operands are. [[FloatLib.Floats.ExecFloat.Binary.Conversion.run_default_negZero_value?]] then says that converting an exact $-0$ into any binary destination gives that destination's negative zero, or its single zero when the encoding has only one, as the FNUZ formats do. A cast that lost the sign would still pass tests that compared the two zeros with `==`.

## Connecting an implementation to its specification

An implementation and its specification are both Lean functions on the same input words. [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] identifies their complete outputs for every input, ties and exceptional values included, and whichever implementation is selected has to supply the proof behind this equation. [Chapter 05](#/chapter/why-execution-and-proofs-are-separate) follows that certificate from the arithmetic kernel to the public operation. A real-valued theorem answers a different question. For a conventional IEEE descriptor, finite operands, and a finite result, the decoded sum equals one nearest-even rounding of the exact real sum on a Flocq-style grid [@boldoMelquiond2011]. Finite inputs alone don't rule out overflow, and [Chapter 06](#/chapter/the-numerical-models/proving-inputs-and-results-are-finite) shows how to prove the result is finite, including cases where cancellation makes a simple magnitude bound too conservative.

## What a proof does not cover

Running the compiled program also requires the Lean compiler to implement the definitions correctly, including any substitutions made for faster execution, and returning unchecked host arithmetic results relies on the host's arithmetic behaviour too. [Chapter 05](#/chapter/why-execution-and-proofs-are-separate) explains how these execution assumptions differ from the axioms listed by `#print axioms`.

The refinement theorems prove agreement with the formal reference, but they can't tell you whether the reference faithfully represents the standard it's meant to follow. Comparing with independent implementations can expose a mistake that the implementation and its own specification share. [Chapter 19](#/chapter/external-validation) describes the comparisons with TestFloat, MPFR, published value tables, and host arithmetic that look for such disagreements.

The historical failures in [chapter 03](#/chapter/a-short-history-of-floating-point/what-imprecision-has-cost) also involve assumptions outside any single arithmetic operation, about the ranges of physical inputs, accumulation over time, and the model being computed. A proof that addition rounds correctly can support that kind of analysis, but the application still has to establish its own input bounds and error budget.