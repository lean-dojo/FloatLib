---
number: "19"
slug: external-validation
title: Related work and external validation
summary: How FloatLib relates to other verified numerical libraries, and what comparisons with independent implementations tell us.
---

We checked every binary16 and bfloat16 addition, subtraction, multiplication, and division on all
$2^{32}$ operand pairs, in each of the four rounding directions, and every binary32 square root.
That's 154,618,822,656 cases, each with its value and all five exception flags, and we got the same
answers as SoftFloat and MPFR throughout. Berkeley TestFloat adds 102,454,320 cases in the wider
formats listed below. Against SoftPosit, 32,893,800 cases produced 7,564 differences, all from seven
distinct inputs. Seven is few enough to work through by hand, and in each one the exact calculation
agrees with FloatLib, while two bugs in SoftPosit's generic implementation explain the other
answers. Our comparisons with MPFX found four bugs in that library, and we've reported all four to
its authors.

## The SoftPosit differences

At widths 2 through 8 the SoftPosit comparison [@softPosit] is exhaustive for the operations we
tested. Above that it samples inputs, at every width from 9 through 16 and at 32 bits, and those
9,175,040 comparisons at widths 9 through 15 cover all ten operations at each width. Widths 9
through 13 agreed throughout. We saw one FMA difference at 14 bits and one at 15 bits, two
differences in 1,310,720 16-bit cases, and 7,560 in 2,621,440 32-bit cases.

We traced all of them to
two defects in the SoftPosit version we tested. At the 32-bit end, SoftPosit's generic pX2 functions
disagree with its own named p32 functions on three inputs, and those three repeat across the 7,560
cases. Each of the other four inputs is an FMA boundary where pX2 overwrites sticky information that
rounding needs. On all seven inputs we evaluated FloatLib's public operation and its exact rational
specification together, and they agreed every time.

For the positive 16-bit FMA example, we can check the rounding with an exact calculation. Its operand words are `0x7680`, `0x6128`, and `0x0001`, which decode to $2560$,
$165/8$, and $2^{-56}$, and we'll keep that tiny addend visible all the way through the exact
calculation:

$$
2560\cdot\frac{165}{8}+2^{-56}=52800+2^{-56}.
$$

Two result words sit on either side: `0x7b9c`, which represents 52,736, and `0x7b9d`, which
represents 52,864. Their midpoint is 52,800. So the exact FMA result lies just above the midpoint,
$64+2^{-56}$ from the lower neighbour and $64-2^{-56}$ from the upper one. FloatLib's executable and
its exact specification both choose the closer upper word, `0x7b9d`. SoftPosit pX2 returned
`0x7b9c`.

Lose the $2^{-56}$ term and the implementation sees an exact tie at 52,800 instead.
Ties-to-even settles it in favour of the lower word, because that word's final bit is even. The $2^{-56}$ term is far below the result's spacing, but it still decides the last bit of this
fused operation. That's the information a sticky bit has to preserve. A sticky bit records whether
any of the discarded lower bits were nonzero, and when we read the source, we found that pX2 first
recorded this information and later overwrote it. SoftPosit's other 16-bit disagreement, with exact
value $-65536000-2^{-50}$, sits just below a midpoint and hits the same loss on the negative side.
At 14 and 15 bits the cases fail the same way:

| Width | Exact FMA result | SoftPosit result | FloatLib result |
| --- | --- | ---: | ---: |
| 14 | $64768 + 2^{-48}$ | 64,512 | 65,024 |
| 15 | $-3060 - 2^{-52}$ | -3,056 | -3,064 |

In both, removing the tiny addend turns the calculation into an exact tie. We changed one rounding
assignment in a copy of SoftPosit's `s_mulAddPX2.c`, from `bitsMore = ...` to `bitsMore |= ...`,
which keeps the earlier sticky information. Both outputs came out
right, and so did the two 16-bit examples. All the counts above are for the original SoftPosit code,
and the patched copy tells us about these inputs only.

At 32 bits there's a nice extra check, because we can compare SoftPosit's two implementations
against each other. For `0xfffffffd + 0xfffffffe`, generic pX2 returned `0xfffffffe`, while
SoftPosit's own named p32 function and FloatLib's exact specification both returned `0xfffffffd`.
Agreeing with FloatLib's specification alone wouldn't settle it, because that specification could be
wrong too. But two entry points of the same library disagreeing, together with the exact calculation
and a read of the source, point us to the mistake.

It comes down to one shift. At these three
boundaries the regime leaves room for one exponent bit, and the generic addition, multiplication,
and division paths reach `regA = 29` and `expA = 2` and then try `expA << (28 - regA)`. That's a
left shift by $-1$, which is undefined in C. Packing the remaining leading exponent bit needs a
right shift here, $2 \mathbin{\gg} 1 = 1$, and the dedicated p32 path handles that case. Fixing only
this shift in a copy of the code corrected all three results.

In the addition example the exact
operands are $-2^{-114}$ and $-2^{-116}$, so the sum is $-5\cdot2^{-116}$. FloatLib returns
$-2^{-114}$, one unit of $2^{-116}$ away. Generic pX2 returns $-2^{-116}$, four such units away, and
no tie-breaking convention explains that. It's a numerical error you can observe on that input.

![Total comparison counts by external tool on a logarithmic scale, with SoftPosit's differences marked separately](assets/ch11-conformance-evidence.png "Bars count compared cases, not time or a percentage of input coverage. The marked SoftPosit differences are examined against exact arithmetic.")

[Figure 19.1](#/chapter/external-validation/figure-ch11-conformance-evidence) counts cases in the
retained release suites that report a comparable case counter. The exhaustive and MPFX comparisons
aren't part of it. Its logarithmic axis runs from 400 MPFR primitive cases to more than 102 million
TestFloat cases. What a case means depends on its suite. It can be a table entry, a generated
operation, or a bounded expression, so the bars don't measure a common percentage of all possible
inputs. Other checks, such as Arb enclosures and comparisons with native arithmetic, answer
different questions.

<details>
<summary>Comparison counts by encoded width</summary>

[Figure 19.2](#/chapter/external-validation/figure-ch11-conformance-widths)
groups the comparisons by bit width. P3109 contributes 576 table cases
at 5 bits and 1,408 at 6 bits, while SoftPosit contributes 40,000 and 290,944 arithmetic cases
at those widths. Those counts differ because the questions and the enumerations differ. A larger
bar is not a stronger theorem.

![P3109 value-table checks and SoftPosit arithmetic checks grouped by bit width, with hatched bars for sampled comparisons and diamonds at widths with differences](assets/ch11-conformance-widths.png "Compared cases by encoded width, not execution times. SoftPosit differs once each at 14 and 15 bits, twice at 16 bits, and 7,560 times at 32 bits.")

</details>

## The MPFX differences

MPFX [@saikiDoubleRounding2026] simulates a narrow format by computing a round-to-odd result in a
`double` or `float` container and then rounding it again. Its paper gives format-containment
conditions for safe double rounding, among them two extra precision bits for nearest rounding, a
fine enough minimum quantum, and an upper-bound margin, and its rounding theorems apply when the
final rounding doesn't overflow. MPFX has two fast engines. One emulates round-to-odd with the
hardware's round-toward-zero mode and its inexact flag, and the other reads the rounding error from
an error-free transformation.

We compared both with FloatLib on binary16, bfloat16, IEEE-style
`e4m3` and `e5m2`, and the two formats at the edge of the class MPFX supports. That's 316,800,000
comparisons on chosen operands, plus every binary16 and bfloat16 pair of the exhaustive campaign
above. Each of the four problems below reproduces without FloatLib at all, using MPFR, SoftFloat, or
the host FPU as appropriate. In the sampled comparison we grouped the remaining EFT differences by
engine, but that grouping alone doesn't tell us their cause.

For an exact zero sum under roundTowardNegative, IEEE 754 makes
$1 + (-1)$ equal to $-0$, so that $x - x$ keeps the sign the rounding direction points to. MPFX
returns $+0$ for every such sum, difference, and FMA, in both engines and every format. That's
63,488 binary16 pairs and 65,280 bfloat16 pairs per operation, one for each finite $x$. Its square
root of $-\infty$ returns a NaN without the invalid flag. And when the container's own result
overflows, as happens for bfloat16 products in a `float`, the overflow flag is lost even though the
rounded result is infinite.

The error-free engine has a less visible failure. It computes the rounding error of a product, quotient, or square root with an
FMA. When a nonzero residual rounds to zero in the container, the engine mistakes the result for exact, and the error disappears before it can tell the rounder what happened. For example,
rounding $\sqrt{3\cdot 2^{-1072}}$ to 51 bits gives `0x1.bb67ae8584cacp-536` with both the hardware
engine and FloatLib, while the error-free engine gives `0x1.bb67ae8584ca8p-536`, one unit lower.

In
bfloat16 the same loss hits every product that underflows the `float` container. Say we round
$2^{-70}\cdot 2^{-90}$ toward positive infinity. The answer must be the least positive bfloat16
value, $2^{-133}$, and the engine returns zero with no inexact or underflow flag, so nothing in the
result says that anything was lost.

MPFX's notes already record this failure for binary64 products,
quotients, and FMAs, but the square root and the `float` container are new. We reported all four
classes in [bksaiki/mpfx#36](https://github.com/bksaiki/mpfx/issues/36), with reproducers that use
only MPFR, SoftFloat, and the host FPU.

## Other verified numerical libraries

A rounding theorem describes which result to choose. An implementation theorem connects that choice
to executable arithmetic, and a program-level error bound accounts for all the rounding steps in a
calculation. The libraries below address these questions at different levels, and our comparisons
use the operations and guarantees they have in common. Much of the mathematical foundation comes
from Flocq [@boldoMelquiond2011], with generic radix-and-exponent formats, rounding, error bounds,
and binary arithmetic in Rocq. FloatLib's [rounding theory](#/chapter/the-mathematics-of-rounding)
follows that formulation, and our [matched Flocq
comparison](#/chapter/performance/matched-binary-arithmetic-with-flocq-and-mpfr) times Flocq's
extracted rounded arithmetic next to FloatLib and MPFR.

### FloatSpec and Flocq-style arithmetic

FloatSpec ports Flocq's organization and arithmetic to Lean [@floatSpec]. With its generic formats,
rounding predicates, ulp theory, and error lemmas, a proof can describe arithmetic without starting
from a fixed machine word. Its IEEE modules then connect those ideas to bounded binary
representations. That helps when you're translating a Flocq argument into Lean, studying a rounding
rule, or relating an algorithm's integer intermediates to its real-valued specification.

You can see
the split between exact and rounded operations in the API.
[`Calc.Operations.Fplus`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/Calc/Operations.lean#L187-L202)
aligns integer significands and adds them, and its `F2R_plus` theorem states that the decoded result
is the exact real sum, assuming a radix greater than one. `Fmult` multiplies significands and adds
exponents, and neither operation chooses a destination precision. They're exact building blocks, but
timing them alone would leave out the rounding work that FloatLib's public encoded arithmetic does.

FloatSpec also has the complete rounded layer. Its
[`BinarySingleNaNFloat prec emax`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/IEEE754/BinarySingleNaN.lean#L96-L107)
represents signed zero, signed infinity, one NaN, and finite values whose constructors carry
positivity and format-bound proofs. `BinarySingleNaN.Bplus`, `Bminus`, `Bmult`, `Bdiv`, `Bsqrt`,
and `Bfma` take a rounding mode, and their correctness theorems are about the rounded result, with
the relevant sign, finiteness, and overflow conditions. For example,
[`Bplus_correct`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/IEEE754/BinarySingleNaN.lean#L14884-L14904)
assumes finite operands. It identifies the result with real rounding when the rounded magnitude is
below the overflow bound, and its other branch specifies overflow.
[`Bdiv_correct`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/IEEE754/BinarySingleNaN.lean#L15465-L15484)
requires a nonzero decoded divisor. A second interface, `Binary`, keeps NaN signs and payloads.
These proof-carrying representations are different from the permissive compatibility carriers that
share their source files.

FloatSpec's primitive-float bridge answers another question.
[`FaithfulPrimFloat.PrimitiveFloat.toModel_add`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/IEEE754/PrimFloat.lean#L1574-L1580)
relates its arithmetic to Lean's logical `Float.Model`, and corresponding theorems cover
multiplication, division, and square root. A model equation like that doesn't certify the processor
instruction a compiled native `Float` call uses, which is the same boundary we met with Lean's own
float model.

FloatSpec marks the rounded SingleNaN definitions `noncomputable`, so an ordinary
compiled definition can't call them. That keyword alone doesn't mean their arithmetic needs a
non-executable real-number operation, though. Our [benchmark
driver](assets/floatspec-rounded-evidence.zip) unfolds selected upstream definitions and substitutes
the real-valued let bindings that only proofs use, while keeping the sharing of integer
computations. Five theorems, each proved by `rfl`, identify the resulting functions with the
upstream rounded operations. Those compiled wrappers are what we timed, final rounding included,
without replacing any arithmetic algorithm. As the [results
below](#/chapter/external-validation/rounded-arithmetic-with-floatspec) show, arbitrary-precision
execution works, and the addition path has a costly conversion.

### FLoPS and P3109

For P3109 the closest comparison is FLoPS [@flopsPaper] [@flopsArtifact]. Chang, Park, Lim, and
Nagarakatte formalize the four format parameters, all nine rounding modes, saturation, and
projection. They also examine two consequences that are easy to miss if you carry IEEE intuitions
into P3109: FastTwoSum can recover an overflow error under saturation, and familiar ExtractScalar
properties can fail at one-bit precision. FLoPS's bit-level addition, multiplication, division, and
fused operations also have refinement proofs relating their results to the closed arithmetic and
projection specifications. The shared arithmetic and the differences in scope are:

| Question | FLoPS | FloatLib |
| --- | --- | --- |
| P3109 arithmetic | Parameterized formats, rounding, saturation, projection, and executable core arithmetic | The same core questions within a library that also supports IEEE binary and decimal, posits, and block formats |
| Stochastic rounding | Supplied-randomness operations, finite-randomness bias analysis, and summation RMS bounds under stated assumptions | Supplied-random-bit rounding and refinement; no general stochastic summation RMS theorem |
| Further operations | P3109 core arithmetic and numerical-algorithm properties | Square root, reciprocal square root, hypot, scaled operations, and independently chosen source and destination formats |

The FLoPS paper describes report 3.2.1, while [our P3109 chapter](#/chapter/p3109) follows
4.0.3, so a shared format name doesn't establish that every operation and policy means the
same thing. Our arithmetic comparison below fixes the encoded inputs, nearest-even rounding,
and no saturation, and then checks the result words.

### Error bounds for a complete expression

Say a program computes a rounded product and then a rounded sum, $t=\operatorname{RN}(xy)$ and
$r=\operatorname{RN}(t+z)$. If we know both calls implement nearest-even rounding, we know what the
program means. Bounding $|r-(xy+z)|$ over an input box takes another proof, though, and cancellation
can make that bound very different from the relative error of either call. VCFloat2, by Andrew W.
Appel and Ariel E. Kellison, addresses this expression-level problem in Rocq, building on Flocq and
the [Interval package](https://coqinterval.gitlabpages.inria.fr/) [@vcfloat2]. Gappa, by Marc Daumas
and Guillaume Melquiond, combines interval reasoning and properties of rounded operators to certify
numerical bounds [@gappa]. These are natural tools to compare against for error-bound automation:
which expressions they accept, which input assumptions they need, and how tight a bound they prove.
FloatLib's operation refinements and rounding theorems are ingredients for such arguments, but on
their own they aren't that automation.

Closer to home, LeanCert uses interval arithmetic and Taylor
models to automate proofs of bounds, roots, and integrals for real-valued functions in Lean
[@leanCert]. Both libraries provide proved interval enclosures, but FloatLib's focus is customizable
numerical formats, rounding rules, and certified executable arithmetic. FloatLib's [interval
tactic](#/chapter/proving-numerical-bounds) proves real inequalities from rational input bounds by
evaluating the expression and subdividing. It can discharge numerical subgoals in an error analysis
once a separate theorem accounts for the program's rounding steps.

### Symbolic arithmetic and tensors

SymFPU implements SMT-LIB floating-point operations with bit-vector operations
[@symfpu]. Pick a backend and the same arithmetic either runs on concrete values or
builds symbolic formulas for an SMT solver. Our Z3 comparisons below exercise
floating-point semantics through a solver. Comparing with SymFPU itself would mean choosing
a concrete backend and comparing encoded operations, and solver time and arithmetic
time answer different performance questions.

TensorLib covers the storage side [@tensorLib]. Its Lean APIs represent tensor shapes, strides, byte
storage, broadcasting, and elementwise operations. It also supplies scalar conversions between
`Float32` and FP16, BF16, and several FP8 layouts. We built and ran those casts, which let us
compare with FloatLib before any tensor indexing or memory traffic comes in. On our finite fixtures
their specialized routines were faster than FloatLib's general descriptor cast. The conversion
results are below, and the timings are in [chapter
17](#/chapter/performance/scalar-conversions-with-tensorlib).

For floating tensor arithmetic,
TensorLib decodes FP16, BF16, and the supported FP8 operands to `Float32`, does the operation, and
encodes the result back. Binary32 runs in `Float32` itself and binary64 uses `Float`, so compiled
calls rely on native floating-point operations agreeing with Lean's logical model. We offer that
execution choice too, through the opt-in [`NativeFPU.Unchecked`
interface](#/chapter/lean-native-floats/opting-into-guarded-host-operations) for supported binary32
and binary64 operations. A host call carries no FloatLib refinement certificate, so it adds trust in
the FPU, the runtime primitives, and the floating-point settings. The certified software path proves
the arithmetic algorithm against its specification, but it still relies on the compiler, runtime,
and hardware to run that software correctly. Our scalar conversion timings don't compare these two
paths.

## What the comparisons check

We can prove that an implementation agrees with our specification and still have misread the
standard, and an independent implementation helps catch that kind of mistake. TestFloat can expose a
wrong exception rule, and a published value table can expose a bad decoder. Comparing with hardware
also tests the compiler and the floating-point settings of that run.

### IEEE arithmetic and flags

Berkeley TestFloat [@hauserTestFloat], backed by SoftFloat [@hauserSoftFloat], is our main
independent arithmetic reference. Our level-1 comparison covers binary16, binary32, binary64, and
binary128 arithmetic, comparisons, and the supported conversions. It runs in nearest-even and in
rounding toward zero, positive infinity, and negative infinity, with tininess detected after
rounding. Non-NaN results must match bit for bit. NaNs are compared by class and signaling behavior,
including the invalid flag, instead of by a universal payload-selection rule.

If we checked only the
returned number, we'd miss errors in the flags. Say we halve the smallest positive binary32
subnormal, $2^{-149}$. We get the exact value $2^{-150}$, halfway between zero and the smallest
subnormal, and nearest-even rounding turns it into zero and reports both underflow and inexact. So
an implementation that returned zero without those flags would still fail the comparison. Going the
other way, an exactly representable subnormal shouldn't pick up underflow just because it's small.
You can see these value/status distinctions through the public API in the worked calls of [the
native-floats chapter](#/chapter/lean-native-floats/formats-rounding-directions-and-status).

All 102,454,320 level-1 cases of the full profile passed, with no value or flag mismatch. TestFloat
drives the model operations, which share the kernels of the October 2026 speed work, and when we
reran the full profile on those kernels, it gave the same result. Three selected level-2 generators
added another 1,272,128 cases. All three completed, but we haven't run every level-2 combination.
This comparison also leaves out binary80, decimal formats, nearest-away, round-to-odd, and
tininess-before-rounding.

For binary16 and bfloat16 we don't have to choose cases. A 16-bit
operation has $2^{32}$ ordered operand pairs, few enough to evaluate every one in each of the four
rounding directions required for binary formats. We ran FloatLib's status-returning operations on
every pair for addition, subtraction, multiplication, and division, and on every binary32 square
root. Each value and all five flags were compared with SoftFloat for binary16 and binary32. For
bfloat16 the reference was MPFR, set to the format's precision and exponent range. Both references
ran for binary16, so we checked the MPFR emulation against SoftFloat on every pair before relying on
it for bfloat16. In nearest-even mode each case also compared the planner's kernel with the model.
All 154,618,822,656 cases agreed.

We also ran the certified `expMinus1` and `logPlus1` on all $2^{32}$ binary32 inputs and on
CORE-MATH's binary64 worst cases, and every result they returned was MPFR's correctly rounded value.
IBM FPgen [@ibmFpgen] supplied 81,513 more supported inputs, and we compared 27,492 bounded ground
QF_FP cases with Z3 [@z3] [@smtLibQfFp]. Neither check found a mismatch. SMT floating-point NaNs are
abstract, so the Z3 adapter checks the exact encoding where the theory determines it and the right
class where it doesn't. Another, larger comparison evaluated 147,876 FloatLib/Z3 cases with zero
mismatches.

### Binary arithmetic with Flocq and MPFR

Our [matched timing comparison](#/chapter/performance/matched-binary-arithmetic-with-flocq-and-mpfr)
gives FloatLib, Flocq, and MPFR the same rational inputs, binary precision, exponent bounds, and
nearest-even rounding. Before timing, we compare the complete significand, exponent, and sign of the
prepared inputs and of each operation's results. Once redundant powers of two are removed, all 528
inputs and 1,056 results agree across the three implementations. At each of eleven widths, addition,
subtraction, multiplication, division, square root, and FMA each use sixteen input sets, and the
timed loops also check result and input-selection checksums on a common prefix. These fixtures
contain finite values and positive zeros, so exception flags and NaN handling are covered by other
checks in this chapter. The complete values are in the [result
archive](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/flocq-matched/README.md),
with a script that compares them again.

### Rounded arithmetic with FloatSpec

We compared FloatSpec's rounded SingleNaN operations with FloatLib at matching significand
precisions from 8 to 4,096 bits, with nearest-even rounding and the same exponent range. Both got
the same exactly representable dyadic inputs, 256 pairs for each of three patterns: equal exponents,
small exponent gaps, or gaps between one and two significand widths. Square root used the absolute
value of the first operand.

Before timing, an independent integer/rational oracle checked each
returned value, and for square root it used integer square root and an exact halfway comparison. We
checked signed zero and NaN/infinity classification as well, and then each timed loop's rolling
checksum against the verified outputs. We didn't check NaN payloads or exception flags. All 108
completed precision/pattern/operation pairs passed their numerical and checksum checks. The
remaining 42 pairs failed during FloatSpec verification, so they have no timing ratio.

In the table
below, each entry is FloatSpec time divided by FloatLib time, geometrically averaged over the three
input patterns. Anything above 1 means FloatLib was faster, and anything below 1 means FloatSpec
was. Every underlying case has one timing round, so these are observations from that run, with no
estimate of timing variability.

| Significand bits | Add | Subtract | Multiply | Divide | Square root |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 8 | 57.91× | 54.99× | 9.69× | 5.30× | 0.46× |
| 16 | 7,901.25× | 8,272.18× | 19.78× | 9.04× | 0.76× |
| 24 | 821,241.75× | 834,087.80× | 42.90× | 7.39× | 0.91× |
| 53 | N/A | N/A | 10.64× | 4.00× | 2.12× |
| 113 | N/A | N/A | 38.21× | 29.65× | 36.45× |
| 256 | N/A | N/A | 46.22× | 55.45× | 29.15× |
| 512 | N/A | N/A | 94.42× | 113.38× | 48.44× |
| 1,024 | N/A | N/A | 184.25× | 208.59× | 76.53× |
| 2,048 | N/A | N/A | 350.11× | 335.92× | 95.03× |
| 4,096 | N/A | N/A | 613.53× | 432.17× | 90.63× |

FloatSpec's square root was faster at 8, 16, and 24 significand bits, and its multiplication,
division, and square root all completed through 4,096 bits.

One conversion in the measured
implementation explains the huge addition and subtraction ratios. Let's follow a finite addition
through `BinarySingleNaN.Bplus`. It aligns the operands, adds their integer significands, and calls
`Binary.normalize`. Then the result passes through `standardFloatToBinaryFloatOfNotNaN`, which
converts its natural-number significand to the recursive `Positive` representation. The
[`binaryPositiveOfNatSucc`
implementation](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/IEEE754/Binary.lean#L529-L542)
first recurses on the predecessor and then increments the positive number it gets back. So
converting a significand $m$ takes $m-1$ recursive descent steps. For a normal $p$-bit significand
that's at least $2^{p-1}-1$ steps, even though the final representation has only $p$ bits. At $p=24$
the lower bound is 8,388,607 steps.

Subtraction calls addition with a negated operand, so it inherits this path. Multiplication,
division, and square root in the measured SingleNaN wrappers avoid the runtime conversion. Some
conversions still appear in their proof terms, but compilation erases those. On the addition path,
that expensive conversion builds runtime data, so it isn't proof checking, and it isn't evaluation
of `Real`.

For scale, the geometric-mean 24-bit addition times were 110.29 ns for FloatLib and 90.57
ms for FloatSpec, and subtraction took 109.10 ns and 91.00 ms, respectively. Gaps that large tell
you about the conversion bottleneck. They don't measure an inherent cost of verification, and they
don't rank the two libraries for every operation.

Addition and subtraction entries are missing
because they failed during verification. At 53, 113, and 256 bits they hit stack overflow,
post-crash deadlocks included, and at 512 through 4,096 bits the 8 GiB memory limit. Our [diagnostic
records](assets/floatspec-rounded-evidence.zip) back up these classifications. They describe the
paths we tested and our resource settings, so they aren't limits on which formats FloatSpec
supports, and they give no speed ratios.

<details>
<summary>FloatSpec source revisions and measurement protocol</summary>

The comparison uses FloatSpec `158263e983ec3925e02b10f5b312498bf414e0f1` and FloatLib based on
`0d91825727839f597fd06b22fdd038ea21480f0c`. You can get source and binary hashes, drivers,
protocols, results, and diagnostic records from the [evidence
download](assets/floatspec-rounded-evidence.zip), but not the full input fixtures or verification
streams. Both arms used the same Lean toolchain and Mathlib. FloatLib needed import-path
compatibility edits, but its arithmetic bodies were unchanged. The FloatSpec driver used definition
expansion and proof-only let substitution, with `@[inline]` generic wrappers and `@[noinline]`
functions specialized to each precision. Each arm selected its format and operation before timing.
Driver equality theorems cover addition, subtraction, multiplication, division, and square root, and
we didn't measure FMA.

Every format had 15 exponent bits, bias 16,383, and FloatSpec `emax = 16384`,
and the minimum significand exponent was $3-16384-p$. So a 24-bit point means 24 significand bits in
a custom format, which isn't the named IEEE binary32 layout. A binary32 spot check outside this
timing workload passed eight cases.

Each pair ran sequentially on the same pinned logical CPU of an Intel Xeon Platinum 8488C,
alternating arm order by case, with input construction outside the timer. A 256-call warmup came
before 64 passes over 256 fixtures, 16,384 timed calls per arm. Timing covered input selection,
arithmetic, allocation, result projection, and checksum work, and the two representations cost
different amounts to consume a result. Pinning didn't reserve an exclusive core. With one round,
these results can't quantify repeatability, and they can't be pooled with the Flocq/MPFR
experiment.

</details>

### P3109 arithmetic with FLoPS

We compared FloatLib with FLoPS's executable P3109 kernel [@flopsArtifact] on 529,152 arithmetic
cases in three formats, Binary4p2sf, Binary8p4se, and Binary8p3se. All used nearest-even rounding
and no saturation, and the encoded results never differed.

For addition, multiplication, and
division we enumerate every ordered pair of codes in each format, NaN, zero, and the infinities of
the extended formats included. FMA covers all 4,096 four-bit triples, and for each eight-bit format
it covers every pair $(x,y)$, with the third code chosen as $(17x+29y+43)\bmod256$. Here $x$, $y$,
and the formula for the third operand are integer *codes*, not decoded real values, so the eight-bit
FMA comparison samples the triples. It also checks all 192 input/output fixtures of the [P3109
timing experiment](#/chapter/performance/p3109-arithmetic-with-flops), which adds an independent
arithmetic check to the published-table checks below. Stochastic rounding and the two saturation
modes still need comparisons of their own.

### Scalar conversions with TensorLib

We compared FloatLib's descriptor cast with TensorLib's `Float32` conversions for FP16, BF16,
E4M3FN, and E5M2 [@tensorLib]. Both libraries passed 952,612 numerical checks against an
independent nearest-even reference based on adjacent representable values.

| Format | Small format to Float32 | Float32 to small format |
| --- | ---: | ---: |
| FP16 | 65,536 | 393,050 |
| BF16 | 65,536 | 399,890 |
| E4M3FN | 256 | 14,132 |
| E5M2 | 256 | 13,956 |

Widening checks enumerate every small-format word. Narrowing checks include every finite destination
value, every midpoint between adjacent finite values, their immediate Float32 neighbors, and the
overflow threshold, all with both signs. We add source-exponent and NaN-payload boundaries and 8,192
seeded random words per format. That exercises subnormal rounding and ties as well as ordinary
values, though it doesn't enumerate all $2^{32}$ source words.

Non-NaN results agree bit for bit,
signed zeros and infinities included. All 2,964 differing words are E4M3FN NaN signs on negative
overflow or negative infinity, where FloatLib returns `0x7f` and TensorLib returns `0xff`. Both
convert $-512$ to NaN, for example, one with each encoding. Neither word is a finite number or an
infinity, so we record the bit difference and don't count it as a numerical error.

TensorLib's input
type also decides what the comparison can observe. Lean's `Float32.ofBits` canonicalizes NaN signs
and payloads before an encoding function ever sees them, and we tested that boundary on its own.
TensorLib's conversion functions return values or bits instead of IEEE status flags, so this
comparison checks result values and NaN classes and makes no claim about signaling behavior or
exception flags. TensorLib's finite conversion results passed throughout, and we found no numerical
defect in these cases.

### Encoding tables and MPFR

Our format-table suite checked 7,602,160 P3109 cases and 1,296 ONNX cases, with zero mismatches. Its
P3109 descriptors come from the public 4.0.3 tables and cover encoded widths 3 through 16, and at
each width the suite enumerates the values of the published layouts, small formats with no familiar
IEEE name included.

That shows FloatLib's exact dyadic decoding agrees with those tables. It doesn't
establish complete P3109 arithmetic, exception handling, saturation, block scaling, or OCP MX
interoperability, because a representation test can cover every word of a small format and still
leave its arithmetic contract untested.

Counting inputs shows the gap. One 16-bit layout has
$2^{16}=65,536$ words to decode, but a binary operation on that layout has
$2^{16}\times2^{16}=2^{32}$ ordered operand pairs before you even choose a rounding mode.
Enumerating the decoding table reaches every word once and never enumerates addition on every pair
of words. The P3109 total also sums over several descriptors, so dividing it by one format's word
count wouldn't give an arithmetic coverage percentage.

Our MPFR suites cover finite primitive arithmetic and exact sums and dot products: 400 primitive
cases, 672 reduction cases, and 131,072 binary16 cases, split equally between addition and
multiplication. All passed. Each binary16 operation has $2^{32}=4,294,967,296$ possible ordered
bit-pattern pairs, and we checked 65,536 of them. MPFR checks the rounded finite values, but its NaN
representation can't check every IEEE payload or NaN-selection rule.

That retained run used the four
rounding directions IEEE 754 requires for binary formats. Now the primitive and reduction oracles
run every case in all six directions of [chapter
07](#/chapter/the-mathematics-of-rounding/rounding-directions-and-the-ternary-value) and compare the
delivered encoding and all five flags. Rounding away from zero is `MPFR_RNDA`. MPFR's nearest mode
with ties away from zero doesn't support subnormalization, so for `nearestAway` the oracle rounds to
nearest even and then corrects an exact tie.

Ternary values aren't part of these oracles. We check
them in the test suite against its own exact rational reference, on every operand pair of `ieee 4 3`
in all six directions.

The last independent check here is Arb [@johanssonArb2017], which we reach
through python-flint [@pythonFlint]. It supplies rigorous enclosures for the tested interval and
transcendental inputs, an independent check on those computations, but agreeing on these inputs
doesn't prove a global error bound, or correct rounding everywhere.

### Elementary functions against MPFR

The binary approximation kernels of [chapter
10](#/chapter/elementary-functions/calling-the-approximation-kernels) have no accuracy theorem. The
two exceptions are the correctly rounded `Model.pi` and the cases of `pow` covered by its
integral-power theorem or by a settled enclosure search. For the remaining approximation kernels, the
transcendental gate supplies test evidence. It compares `exp`, `log`, `sin`,
`cos`, `sinh`, `cosh`, `tanh`, `pow`, and `pi` with MPFR in binary16, bfloat16, binary32, binary64,
binary128, and `ieee 31 23`, whose exponent field has 31 bits. Every case carries its operation, its
MPFR rounding mode, the full format descriptor, and the operands. The C oracle transports any binary
layout exactly through GMP and emulates the format's exponent range and subnormals. It reports the
sign of MPFR's ternary value in any of the five MPFR modes, RNDN, RNDZ, RNDU, RNDD, and RNDA.
FloatLib's functions round to nearest, so the cases use RNDN.

Its corpus mixes edge cases, fixed-seed random arguments, and checked-in hard cases. The hard cases
are continued-fraction arguments near multiples of $\pi/2$ in every binade, and the overflow,
underflow, saturation, and midpoint boundaries of the other functions. A checked-in census pins down
the case set of each tier. The default tier has 28,671 cases and the release tier has 39,393 cases,
while the qualification tier has 1,140,927 and adds every binary16 and bfloat16 input and the
binary128 continued-fraction cases with both signs and their neighbours. The gate fails on any
difference its list of known failures doesn't name, on a listed case that changes, and on a listed
case that starts to match. That list is empty. Every case of the three tiers matches MPFR.

## Why logarithms near 1 are difficult

For binary elementary functions we compared FloatLib with MPFR, CORE-MATH [@coreMath], OpenLibm
[@openLibm], and the supported RLIBM functions [@rlibmAll], which offer different functions and
accuracy guarantees. FloatLib's [certified exponential and
logarithm](#/chapter/elementary-functions/certified-exponential-and-logarithm) are a different set
of functions, and they prove nearest-even rounding for every successful finite result. The [proved
posit exponentials and logarithms](#/chapter/posits-and-the-quire/exponentials-and-logarithms) use
their own algorithms.

Take the representable value just below 1. If you approximate the logarithm of
a significand near 2 and then subtract an approximation to `log 2`, cancellation eats the accuracy.
The answer is tiny, and errors in the two larger approximations can overwhelm its last bits.
Centering the significand around 1 avoids that subtraction, but we still have to watch the rounding
midpoint. In $\log(1-\delta)=-\delta-\delta^2/2-\delta^3/3-\cdots$ the quadratic term can land
exactly on a rounding midpoint, and discarding the remaining terms can pick the wrong neighbor.

Hyperbolic functions raise a related rounding question. Round each exponential before combining them
and you can lose information that the final result needs. Combining internal dyadic approximations
before rounding avoids that intermediate rounding, and for small arguments a Taylor series can
preserve corrections that subtraction would lose.

Wide exponent fields bring a different problem,
because an input can be cheap to store and still enormous to expand into fixed-point arithmetic.
Looking at the exponent first can avoid those huge intermediates for tiny inputs, or for inputs far
beyond saturation or overflow. Then boundary checks have to establish when it's valid to return a
rounded limiting value.

## Why some performance markers are missing

![Universal comparisons for six operations at thirteen posit widths; seven square-root results differ.](assets/ch11-universal-preflight.png "Width/operation comparisons against Universal, not execution times. Each blue cell matched on all sixteen benchmark inputs; seven wide square-root configurations differed and are omitted from timings.")

Square-root differences in [Figure
19.3](#/chapter/external-validation/figure-ch11-universal-preflight) explain the gaps in the timing
plots. Before timing Universal, we compared six operations at thirteen posit widths from 5 through
4,096 bits. Of these 78 combinations, 71 agreed on every input and seven differed, all of them in
square root, at widths 64, 128, 256, 512, 1,024, 2,048, and 4,096. Each comparison checks all
sixteen inputs the benchmark uses, and agreeing on those doesn't imply agreement on every input of
that posit format. Universal's square-root configurations go through a host binary64 conversion and
square root, so their passing measurements are labelled hardware-assisted and kept apart from
software posit arithmetic. We leave the differing results out of the timing plots, and that's why
the wide Universal square-root markers are missing.

Follow a wider posit through binary64 and you
can see why that label matters. Once the posit has been rounded to a binary64 input, whatever
precision that conversion lost is gone for the host square-root call, and converting the answer back
to a wide posit can't recover it. That doesn't diagnose every differing input by itself. It does
explain why a fast host-assisted result needs its own agreement check and can't stand in for
arbitrary-precision posit square root.

## Running the comparisons

To reproduce the comparisons, see [tests/EXTERNAL.md](https://github.com/lean-dojo/FloatLib/blob/main/tests/EXTERNAL.md).
