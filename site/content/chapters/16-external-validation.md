---
number: "16"
slug: external-validation
title: Related work and external validation
summary: How FloatLib relates to other verified numerical libraries, and what comparisons with independent implementations tell us.
---

We checked FloatLib against Berkeley TestFloat on **102,454,320 cases** and got the same
answers throughout. That comparison covers the formats and operations listed below.
Against SoftPosit, **32,893,800 cases** produced **7,564 differences**, all from seven
distinct inputs. We can work through those seven by hand: the exact calculation agrees
with FloatLib, and two bugs in SoftPosit's generic implementation explain the other answers.

![Direct comparison counts and the widths tested, with green SoftPosit bars at every measured width.](assets/ch11-conformance-evidence.png "Bars count compared cases, not time or a percentage of input coverage. Orange diamonds mark SoftPosit differences: one each at 14 and 15 bits, two at 16 bits, and 7,560 at 32 bits.")

The upper panel of [Figure 16.1](#/chapter/external-validation/figure-ch11-conformance-evidence)
counts cases in suites that report a comparable case counter. Its logarithmic
axis spans 400 MPFR primitive cases to more than 102 million TestFloat cases. A case has the
meaning assigned by its suite: a table entry, a generated operation, or a bounded expression.
These bars do not measure a common percentage of all possible inputs. Other checks, including
Arb enclosures and comparisons with native arithmetic, answer different questions; we discuss
them below.

The lower panel groups the comparisons by bit width. P3109 contributes 576 table cases
at 5 bits and 1,408 at 6 bits; SoftPosit contributes 40,000 and 290,944 arithmetic cases at those
widths. Those different counts reflect different questions and different enumerations. A larger
bar is not a stronger theorem.

## Other verified numerical libraries

We spent a lot of time reading the numerical-verification literature and working through
the implementations behind it, including the related projects being developed in Lean.
We wanted to evaluate FloatLib properly and understand what these libraries do especially
well. That meant following definitions through rounding and exceptional cases, reading
theorems alongside their assumptions, and building comparisons where the operations overlap.

There are several useful meanings of “verified floating-point arithmetic.” A rounding
theorem, an executable operation proved to implement that rounding rule, and an error bound
for a complete numerical program answer different questions. We explain those distinctions
here because they help us learn from the other projects and choose useful comparisons.

Flocq [@boldoMelquiond2011] supplies much of the mathematical foundation: generic radix-and-exponent
formats, rounding, error bounds, and binary arithmetic in Rocq. FloatLib's
[rounding theory](#/chapter/the-mathematics-of-rounding) follows that formulation. **FloatSpec**
brings a Flocq-style organization to Lean, with generic formats, Hoare-style specifications,
IEEE representation modules, and connections to Lean's native float models [@floatSpec].
Its separation of representations, arithmetic, and rounding makes it a useful reference
for the mathematical layer. For example, FloatSpec's
`Calc.Operations.Fplus` aligns integer significands and represents their exact sum; destination
rounding is a further operation. FloatLib's public encoded addition includes the
destination rounding and exceptional-value policy in the operation being specified.

Following that final rounding step matters for benchmarking. FloatSpec's rounded
`BinarySingleNaN.Bplus`, `Bmult`, `Bdiv`, and `Bsqrt` interfaces, and its
`FaithfulPrimFloat.add` and `mul`, are defined as `noncomputable`: they serve as
mathematical definitions rather than directly compiled arithmetic. Its computable
representation helpers and native-float bridges remain useful. We compared these
interfaces and their contracts, but did not time the noncomputable definitions.
Timing `Fplus` alone would omit rounding; timing an addition through Lean's native
`Float` would measure the host operation.

**FLoPS** is the closest comparison for P3109 [@flopsPaper] [@flopsArtifact].
Chang, Park, Lim, and Nagarakatte formalize the four format parameters, all nine rounding
modes, saturation, and projection. Their work examines two consequences that are easy to
miss when carrying IEEE intuitions into P3109: FastTwoSum can recover an overflow error
under saturation, and familiar ExtractScalar properties can fail at one-bit precision.
The executable artifact goes beyond a mathematical model: its bit-level addition,
multiplication, division, and fused operations have refinement proofs relating their
results to the closed arithmetic and projection specifications.

The overlap is substantial, and the differences are useful:

| Question | FLoPS | FloatLib |
| --- | --- | --- |
| P3109 arithmetic | Parameterized formats, rounding, saturation, projection, and executable core arithmetic | The same core questions within a library that also supports IEEE binary and decimal, posits, and block formats |
| Stochastic rounding | Supplied-randomness operations, finite-randomness bias analysis, and summation RMS bounds under stated assumptions | Supplied-random-bit rounding and refinement; no general stochastic summation RMS theorem |
| Further operations | P3109 core arithmetic and numerical-algorithm properties | Square root, reciprocal square root, hypot, scaled operations, and independently chosen source and destination formats |

The FLoPS paper describes report 3.2.1; [our P3109 chapter](#/chapter/p3109) follows
4.0.3. A shared format name alone therefore does not establish that every operation and
policy has the same meaning. The arithmetic comparison below fixes the encoded inputs,
nearest-even rounding, and no saturation, then checks the result words directly.

### Error bounds for a complete expression

Suppose a program computes a rounded product and then a rounded sum,
$t=\operatorname{RN}(xy)$ and $r=\operatorname{RN}(t+z)$.
Knowing that both calls implement nearest-even rounding gives us the semantics of the
program. Bounding $|r-(xy+z)|$ over an input box is a further proof, and cancellation can
make that bound very different from the relative error of either individual call.

**VCFloat2**, by Andrew W. Appel and Ariel E. Kellison, addresses this expression-level
problem in Rocq, building on Flocq and Interval [@vcfloat2]. **Gappa**, by Marc Daumas
and Guillaume Melquiond, combines interval reasoning and properties of rounded operators
to certify numerical bounds [@gappa]. These tools are natural comparisons for error-bound
automation: which expressions they accept, which input assumptions they need, and how
tight a bound they prove. FloatLib's operation refinements and rounding theorems supply
ingredients for such arguments; they do not by themselves constitute the same automation.

### Symbolic arithmetic and tensors

**SymFPU** implements SMT-LIB floating-point operations using bit-vector operations
[@symfpu]. Its choice of backend lets the same arithmetic execute on concrete values or
construct symbolic formulas for an SMT solver. Our Z3 comparisons below exercise
floating-point semantics through a solver; a direct comparison with SymFPU would instead
choose a concrete backend and compare encoded operations. Solver time and arithmetic
time answer different performance questions.

**TensorLib** makes the storage side concrete [@tensorLib]. Its Lean APIs represent tensor
shapes, strides, byte storage, broadcasting, and elementwise operations. It also supplies
scalar conversions between `Float32` and FP16, BF16, and several FP8 layouts. Those casts
give us a direct comparison with FloatLib before introducing tensor indexing or memory
traffic. We built and ran them, and their specialized routines were faster than FloatLib's
general descriptor cast on our finite fixtures. The conversion results appear below;
[chapter 15](#/chapter/performance/scalar-conversions-with-tensorlib) gives the timings.

For floating tensor arithmetic, TensorLib decodes FP16, BF16, and the supported FP8
operands to `Float32`, performs the operation, and encodes the result back. Binary32
operates directly in `Float32`, and binary64 uses `Float`. Compiled calls therefore rely
on native floating-point operations agreeing with Lean's logical model.

We offer that execution choice too, through the explicit
[`NativeFPU.Unchecked` interface](#/chapter/performance/opting-into-guarded-host-operations)
for supported binary32 and binary64 operations. A host call has no FloatLib refinement
certificate: it adds trust in the FPU, runtime primitives, and floating-point settings.
The certified software path proves the arithmetic algorithm against its specification,
while still relying on the compiler, runtime, and hardware to execute that software
correctly. Our scalar conversion timings do not compare these two arithmetic paths.

## What the comparisons check

We can prove an implementation agrees with our specification and still have misread the
standard. Comparing with an independent implementation helps catch that mistake. TestFloat
can expose an incorrect exception rule; a published value table can expose a bad decoder.
Comparing with hardware also checks the compiler and floating-point settings used by that run.
For each comparison below, we give the formats, inputs, and rules we checked.

### IEEE arithmetic and flags

Berkeley TestFloat [@hauserTestFloat], backed by SoftFloat [@hauserSoftFloat], is the main
independent arithmetic reference. Our level-1 comparison covers binary16, binary32,
binary64, and binary128 arithmetic, comparisons, and the supported conversions. It checks
nearest-even and rounding toward zero, positive infinity, and negative infinity, with tininess
detected after rounding. Non-NaN results must match bit for bit. NaNs are checked by class and
signaling behavior, including the invalid flag, rather than by a universal payload-selection
rule.

If we checked only the returned number, we'd miss errors in the flags. We can see this by halving
the smallest positive binary32 subnormal, $2^{-149}$, which gives the exact value $2^{-150}$.
That is halfway between zero and the smallest subnormal, so nearest-even rounding returns zero and reports
both underflow and inexact. An implementation returning zero without those flags would still
fail the comparison. Conversely, an exactly representable subnormal should not acquire
underflow merely because it is small. The worked calls in
[chapter 15](#/chapter/performance/comparing-with-leans-native-floats) show these value/status distinctions
through the public API.

The 102,454,320 level-1 cases passed these checks. Another **1,272,128 cases** came from three
selected level-2 generators. All three completed, but we have not run every level-2
combination. Binary80, decimal formats, nearest-away, round-to-odd, and
tininess-before-rounding are not included in this comparison.

IBM FPgen [@ibmFpgen] supplied **81,513** additional supported inputs. We also compared
**27,492** bounded ground QF_FP cases with Z3 [@z3] [@smtLibQfFp]. Both checks reported zero mismatches.
SMT floating-point NaNs are abstract, so the Z3 adapter checks exact encodings where the theory
determines them and the appropriate class where it does not. A separate, larger comparison
evaluated **147,876 FloatLib/Z3 cases with zero mismatches**.

Numerical order alone cannot check an ordering rule for NaN signs, signaling bits, and
payloads. Those comparisons need a bit-level reference, as do custom exponent fields outside
MPFR's supported range.

Parsing and formatting need both value checks and syntax checks. A round trip should recover
the original word, including signed zero and NaN metadata where the syntax preserves them.
An exact rational parser can check a finite decimal or hexadecimal spelling without first
rounding it through a host float. Requested-precision output also needs a rounding comparison:
a string can be valid syntax and still denote the wrong neighbor.

### Decimal values, cohorts, and flags

A [decimal result](#/chapter/ieee-binary-formats/decimal-interchange)
has a sign, coefficient, and quantum exponent, or a special-value datum,
together with its flags. We need to distinguish $1.50$ from $1.5$: they differ as datums even
though they denote the same rational. A comparison through libmpdec can check arithmetic and
cohort choices; an independent rational calculation can check projection into a decimal grid.
For an irrational square root, outward MPFR bounds can provide a reference when both endpoints
round to the same decimal datum.

NaN choices need a stated policy before comparing the complete result. With several NaN
operands, a permitted difference in sign or payload selection should not be confused with a
wrong numerical result or a missing invalid flag. Subnormals, exact tiny results, range
boundaries, signed zeros, and quiet and signaling NaNs exercise different rules.

Quantize needs a comparison of the requested quantum as well as the value. Classification and
total ordering need raw-word cases, including redundant encodings. Remainder and neighboring-value
operations need their own reference calculations; agreement on addition does not test them.
For text, we need exact-datum round trips, independent parsing, requested-precision rounding,
invalid syntax, and the BID and DPD codecs.

Conversions add destination-specific questions. Decimal-to-binary conversion usually changes
the value, while decimal-to-decimal conversion may preserve it but choose another cohort.
Integer conversion must round before checking the destination range: a small negative fraction
can round to unsigned zero. Custom descriptors whose exponent ranges lie entirely above or
below zero test assumptions that the three named decimal formats would not reveal.

### P3109 arithmetic with FLoPS

We compared FloatLib with FLoPS's executable P3109 kernel [@flopsArtifact] on
**529,152 arithmetic cases**, with no differences in the encoded results. The formats
are Binary4p2sf, Binary8p4se, and Binary8p3se, all using nearest-even rounding and no
saturation.

For addition, multiplication, and division, we enumerate every ordered pair of
codes in each format. That includes NaN, zero, and the infinities in the extended
formats. FMA covers all 4,096 four-bit triples; for each eight-bit format it covers
every pair $(x,y)$ with the third code chosen as $(17x+29y+43)\bmod256$.
Here $x$, $y$, and the formula for the third operand are integer *codes*, not decoded
real values. The eight-bit FMA comparison is therefore sampled over triples.

The comparison also checks all **192 input/output fixtures** used by the
[P3109 timing experiment](#/chapter/performance/p3109-arithmetic-with-flops).
This adds an independent arithmetic check to the published-table checks below.
Stochastic rounding and the two saturation modes need their own comparisons.

### Scalar conversions with TensorLib

We compared FloatLib's descriptor cast with TensorLib's `Float32` conversions for
**FP16, BF16, E4M3FN, and E5M2** [@tensorLib]. Both libraries passed
**952,612 numerical checks** against an independent nearest-even reference based on
adjacent representable values.

| Format | Small format to Float32 | Float32 to small format |
| --- | ---: | ---: |
| FP16 | 65,536 | 393,050 |
| BF16 | 65,536 | 399,890 |
| E4M3FN | 256 | 14,132 |
| E5M2 | 256 | 13,956 |

The widening checks enumerate every small-format word. Narrowing checks include every
finite destination value, every midpoint between adjacent finite values, their immediate
Float32 neighbors, and the overflow threshold, with both signs. We add source-exponent
and NaN-payload boundaries and 8,192 seeded random words per format. This exercises
subnormal rounding and ties as well as ordinary values; it does not enumerate all
$2^{32}$ source words.

Non-NaN results agree bit for bit, including signed zeros and infinities.
The **2,964 differing words** are all E4M3FN NaN signs on negative overflow or negative infinity:
FloatLib returns `0x7f`, while TensorLib returns `0xff`. For example, both convert
$-512$ to NaN, using those two encodings. Neither represents a finite number or infinity,
so we record the bit difference without counting it as a numerical error.

TensorLib's input type also determines what the comparison can observe. Lean's
`Float32.ofBits` canonicalizes NaN signs and payloads before an encoding function sees
them; we checked that boundary separately. Its conversion functions return values or
bits rather than IEEE status flags. This comparison therefore checks result values and
NaN classes, with no claim about signaling behavior or exception flags. TensorLib's
finite conversion results passed throughout; we found no numerical defect in these cases.

<a id="published-encodings-and-finite-numerical-references"></a>

### Encoding tables and MPFR

The format-table suite checked **7,602,160 P3109 cases** and **1,296 ONNX cases**, with zero
mismatches. P3109 descriptors come from the public 4.0.3 tables and cover encoded widths
3 through 16. At each width, the suite enumerates the values of the published layouts, including
small formats that have no familiar IEEE name.

This establishes agreement between FloatLib's exact dyadic decoding and those tables. It does
not establish complete P3109 arithmetic, exception handling, saturation, block scaling, or OCP MX
interoperability. Representation tests can cover every word in a small format while leaving
its arithmetic contract untested.

We can check the difference ourselves by counting inputs. One 16-bit layout has $2^{16}=65,536$
words to decode. A binary operation on that layout has $2^{16}\times2^{16}=2^{32}$ ordered
operand pairs before choosing a rounding mode. Enumerating the decoding table reaches every
word once; it does not enumerate addition on every pair of words. The P3109 total also sums
over multiple descriptors, so dividing it by one format's word count would not produce an
arithmetic coverage percentage.

The MPFR suites cover finite primitive arithmetic and exact sums and dot products. The case
counts are **400 primitive cases**, **672 reduction cases**, and **131,072 binary16 cases**,
split equally between addition and multiplication. All passed. Each binary16 operation has
$2^{32}=4,294,967,296$ possible ordered bit-pattern pairs; we checked 65,536 of them.
MPFR checks the rounded finite values.
Its NaN representation cannot check every IEEE payload or NaN-selection rule.

Arb, through python-flint, supplies rigorous enclosures for the tested interval and
transcendental inputs. Those enclosures give an independent check on the computations.
Agreement on these inputs does not prove a global error bound or correct rounding everywhere.

<a id="natural-posit-exponentials-and-logarithms"></a>

### Posit exponentials and logarithms

The [real-rounding proofs](#/chapter/posits-and-the-quire/exponentials-and-logarithms) cover
`exp`, `expMinus1`, `log`, and `logPlus1` on every finite input in each function's domain.

For an independent check, we can decode the input as an exact dyadic, enclose the real
function with directed MPFR bounds, and round both bounds with a separate implementation of
the posit rule. When both select the same word, they determine the expected result.
At eight bits, every input word can be enumerated. Wider formats need selected inputs around
domain endpoints, rounding boundaries, zero, and the finite extremes. The approximate binary
kernels below require a separate accuracy comparison.

### Exact trigonometric comparisons

The [exact trigonometric comparison module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Exact/Trigonometric/Proof.lean) supplies comparisons between a real
trigonometric value at a rational input and a rational boundary. For sine, cosine, tangent,
and arctangent, the ordering theorems cover every rational input and boundary. Inverse sine
and cosine cover inputs in $[-1,1]$, including both endpoints.

An independent ordering check needs strict interval separation for unequal values and a
separate treatment of exact equality. Input-conversion error must be enclosed too: rounding a
rational to an MPFR input without accounting for that change can reverse a close comparison.
Useful cases include neighbors of tangent poles, inverse-domain endpoints, and large inputs
that require argument reduction.

Prepared comparators cache enclosure levels. To exercise that runtime path, we need to reuse
one prepared object across several boundaries and force refinement beyond its initial cache.
Checking the ordering layer would still be separate from checking final rounded posit words.

<a id="ordinary-posit-trigonometric-results"></a>

### Posit trigonometric functions

The [radian functions](#/chapter/posits-and-the-quire/ordinary-trigonometric-functions)
have model and configured real-rounding proofs. An independent output comparison must use
the standard's appended-bit threshold, which need not be the arithmetic midpoint between
two posits. Reusing an IEEE nearest-value rounder would check a different rule. The test also
needs NaR and inputs outside the inverse functions' real domains.

<a id="pi-scaled-posit-trigonometric-results"></a>

### Pi-scaled posit trigonometric functions

For a pi-scaled function, exact rational period reduction should precede the numerical
reference call. Forming a large approximate product with π can lose the very phase we want
to test. Integer and half-integer arguments also give exact zeros, extrema, and poles that
need explicit classification. At an integer multiple of π, for example, cosine's sign is
determined by the integer's parity, even when that integer is too large for a host float.

<a id="two-coordinate-posit-angles"></a>

### Posit atan2

The two-coordinate functions `arcTan2` and `arcTan2Pi` need pairs of inputs. Axes and
diagonals give exact special cases, while points close to an axis test whether the sign and
small angular displacement survive the comparison. An independent check should include all
quadrants, NaR, and operands of very different magnitudes. A correct result and a practical
running time are separate properties, especially at wide precisions.

### Posit hyperbolic functions

The [hyperbolic functions](#/chapter/posits-and-the-quire/hyperbolic-functions) have
real-rounding proofs, including their inverse-domain conditions. Independent checks should
exercise those boundaries and both signs of extreme finite inputs. As with the natural
functions, directed bounds must select the same posit before they determine an expected
word. A fixed amount of oracle precision is insufficient if the bounds still straddle a
rounding threshold.

### Posit decimal text

Every finite posit is a dyadic rational, so it has a terminating exact decimal expansion.
We can check a printed string with an independent rational decoder and parser, avoiding
conversion through binary64. Exact output can be long at wide formats. Invalid syntax and
NaR need separate checks, and configured storage should be exercised as well as model words.
The [all-width round-trip proofs](#/chapter/posits-and-the-quire/exact-decimal-text)
establish recovery of the original word; executable comparisons would additionally exercise
the compiler and text interface.

### Posit integer conversion

For unsigned conversion, a negative input is not enough to predict failure: a negative
fraction can round to zero. The exceptional integer word also collides with the ordinary
unsigned value $2^{w-1}$. An independent comparison needs to distinguish the conversion's
success conditions from the delivered bits, which alone cannot identify that exceptional case.

## The SoftPosit differences

The SoftPosit comparison [@softPosit] is exhaustive for the operations tested at widths 2
through 8 and samples wider inputs at every width from 9 through 16, plus 32 bits.

The **9,175,040 comparisons at widths 9 through 15** cover all ten operations at each width.
Widths 9 through 13 agreed throughout. There was one FMA difference at 14 bits and one at
15 bits, **two differences in 1,310,720 16-bit cases**, and **7,560 in 2,621,440 32-bit cases**.

We traced the differences to two defects in the tested SoftPosit version. At the 32-bit
endpoint, SoftPosit's generic pX2 functions disagree with its own named p32 functions on three
inputs repeated across 7,560 cases. The other four inputs are FMA boundaries where pX2
overwrites sticky information used in rounding. We evaluated FloatLib's public
operation and exact rational specification together on all seven inputs; they agreed every time.

Let's work through the positive 16-bit FMA example. Its operands have words `0x7680`,
`0x6128`, and `0x0001`, decoding to $2560$, $165/8$, and $2^{-56}$. We can keep the tiny
addend visible throughout the exact calculation:

$$
2560\cdot\frac{165}{8}+2^{-56}=52800+2^{-56}.
$$

The neighbouring result words are `0x7b9c`, which represents 52,736, and `0x7b9d`, which
represents 52,864. Their midpoint is 52,800. The exact FMA result lies just above it: its
distance from the lower neighbour is $64+2^{-56}$, while its distance from the upper neighbour
is $64-2^{-56}$. FloatLib's executable and exact specification choose the closer upper word,
`0x7b9d`. SoftPosit pX2 returned `0x7b9c`.

If the implementation loses the $2^{-56}$ term, it sees an exact tie at 52,800 instead.
The lower word has an even final bit, so ties-to-even selects it. This explains why a term
far below the result's spacing can still decide the last bit of a fused operation. A sticky
bit records whether discarded lower bits contained any nonzero information. The
source diagnosis found that pX2 first recorded this information and later overwrote it.
The other 16-bit disagreement, with exact value $-65536000-2^{-50}$, sits just below a midpoint
and exercises the same loss on the negative side.

The 14-bit and 15-bit cases have the same problem:

| Width | Exact FMA result | SoftPosit result | FloatLib result |
| --- | --- | ---: | ---: |
| 14 | $64768 + 2^{-48}$ | 64,512 | 65,024 |
| 15 | $-3060 - 2^{-52}$ | -3,056 | -3,064 |

In both cases, removing the tiny addend turns the calculation into an exact tie. In a
copy of SoftPosit, changing the rounding assignment in `s_mulAddPX2.c` from
`bitsMore = ...` to `bitsMore |= ...` preserved the earlier sticky information and corrected
both outputs. The same change corrected the two 16-bit examples. The counts above are for
the original SoftPosit code.

For either row, we can average the two returned values to find the midpoint, then put
the tiny addend back. That tells us which neighbor is closer without running either
implementation.

At 32 bits, we can also compare SoftPosit's two implementations. For `0xfffffffd + 0xfffffffe`, generic pX2
returned `0xfffffffe`, while SoftPosit's own named p32 function and FloatLib's exact
specification returned `0xfffffffd`. Agreement with FloatLib's specification alone would
still leave open whether that specification was wrong. The discrepancy between two entry
points in the same library, together with the exact calculation and source review,
help us locate the mistake.

The source error is precise. At these three boundaries the regime leaves room for one
exponent bit. The generic addition, multiplication, and division paths reach `regA = 29`
and `expA = 2`, then try `expA << (28 - regA)`: a left shift by $-1$, which is undefined
in C. Packing the remaining leading exponent bit requires a right shift here:
$2 \mathbin{\gg} 1 = 1$. The dedicated p32 path handles that case explicitly.
Correcting only this shift in a copy of the code corrected all three results.

For the addition example, the exact operands are $-2^{-114}$ and $-2^{-116}$.
Their sum is $-5\cdot2^{-116}$. FloatLib returns $-2^{-114}$, one unit of
$2^{-116}$ away; generic pX2 returns $-2^{-116}$, four such units away.
This is an observable numerical error on that input, not a different tie-breaking convention.

Seven distinct inputs explain all 7,564 differences in these comparisons. The exact
calculations and the small source changes let us say why each result differs, rather than
merely counting disagreements.

<a id="duration-and-the-release-outcome"></a>
<a id="a-small-input-that-exposed-a-logarithm-bug"></a>

## Why logarithms near 1 are difficult

For binary elementary functions, we compared FloatLib with MPFR, CORE-MATH [@coreMath],
OpenLibm [@openLibm], and the supported RLIBM functions [@rlibmAll]. These libraries offer
different functions and accuracy guarantees. FloatLib's binary kernels have no general
correct-rounding theorem.
The [proved posit exponentials and logarithms](#/chapter/posits-and-the-quire/exponentials-and-logarithms)
use separate algorithms.

Consider the representable value immediately below 1. Approximating the logarithm of a
significand near 2 and then subtracting an
approximation to `log 2` loses accuracy through cancellation. The answer is tiny; errors in
the two larger approximations can overwhelm its last bits. Centering the significand around
1 avoids that subtraction, but we still have to watch the rounding midpoint. In
$\log(1-\delta)=-\delta-\delta^2/2-\delta^3/3-\cdots$, the quadratic term can land exactly
on a rounding midpoint. Discarding the cubic term then chooses the wrong neighbor.

The hyperbolic functions raise a related rounding question. Rounding each exponential before
combining them can lose information that the final result needs. Combining internal dyadic
approximations before rounding avoids that intermediate rounding; a small-argument Taylor
series can preserve corrections that subtraction would lose.

With wide exponent fields, an input can be cheap to store yet enormous
to expand into fixed-point arithmetic. Inspecting the exponent first can avoid enormous
intermediates for tiny inputs or inputs far beyond saturation or overflow. Boundary checks
must establish when returning a rounded limiting value is valid.

<a id="the-wider-ecosystem-campaign"></a>
<a id="learning-from-other-numerical-tools"></a>
<a id="other-libraries-own-tests"></a>

## Why some performance markers are missing

![Universal comparisons for six operations at thirteen posit widths; seven square-root results differ.](assets/ch11-universal-preflight.png "Width/operation comparisons against Universal, not execution times. Each blue cell matched on all sixteen benchmark inputs; seven wide square-root configurations differed and are omitted from timings.")

The square-root differences in
[Figure 16.2](#/chapter/external-validation/figure-ch11-universal-preflight) explain
the gaps in the timing plots.
Before timing Universal, we compared six operations at thirteen posit widths from 5 through
4,096 bits. Of these **78 combinations**, **71 agreed** on every input and **seven differed**.
All seven differences were in square root, at widths 64, 128, 256, 512, 1,024, 2,048, and 4,096.

Each comparison checks all sixteen inputs used by the benchmark. Agreement on these inputs
does not imply agreement on every input in that posit format. Universal's square-root configurations
use a host binary64 conversion and square root; their passing measurements are labelled
hardware-assisted, separately from software posit arithmetic. We exclude the differing results
from the timing plots. That is why the wide Universal square-root markers are missing.

We can see why that label matters by following a wider posit through binary64. Once it has
been rounded to a binary64 input, any precision lost at that conversion is unavailable to the
host square-root call. Converting the answer back to a wide posit cannot recover it. This
does not by itself diagnose every differing input, but it explains why a fast host-assisted
result needs its own agreement check and cannot stand in for arbitrary-precision posit
square root.

<a id="inspecting-the-comparison-records"></a>
<a id="tests-what-is-validated"></a>

<a id="exploring-the-comparisons-yourself"></a>

## Running the comparisons

To reproduce the comparisons, see [tests/EXTERNAL.md](https://github.com/lean-dojo/FloatLib/blob/main/tests/EXTERNAL.md).
