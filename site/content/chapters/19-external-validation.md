---
number: "19"
slug: external-validation
title: Related work and external validation
summary: How FloatLib relates to other verified numerical libraries, and what comparisons with independent implementations tell us.
---

We checked FloatLib against Berkeley TestFloat on **102,454,320 cases** and got the same
answers throughout. That comparison covers the formats and operations listed below.
Against SoftPosit, **32,893,800 cases** produced **7,564 differences**, all from seven
distinct inputs. We can work through those seven by hand: the exact calculation agrees
with FloatLib, and two bugs in SoftPosit's generic implementation explain the other answers.

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

The positive 16-bit FMA example has operand words `0x7680`,
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

![Total comparison counts by external tool on a logarithmic scale, with SoftPosit's differences marked separately](assets/ch11-conformance-evidence.png "Bars count compared cases, not time or a percentage of input coverage. The marked SoftPosit differences are examined against exact arithmetic.")

[Figure 19.1](#/chapter/external-validation/figure-ch11-conformance-evidence)
counts cases in suites that report a comparable case counter. Its logarithmic
axis spans 400 MPFR primitive cases to more than 102 million TestFloat cases. A case has the
meaning assigned by its suite: a table entry, a generated operation, or a bounded expression.
These bars do not measure a common percentage of all possible inputs. Other checks, including
Arb enclosures and comparisons with native arithmetic, answer different questions; we discuss
them below.

<details>
<summary>Comparison counts by encoded width</summary>

[Figure 19.2](#/chapter/external-validation/figure-ch11-conformance-widths)
groups the comparisons by bit width. P3109 contributes 576 table cases
at 5 bits and 1,408 at 6 bits; SoftPosit contributes 40,000 and 290,944 arithmetic cases at those
widths. Those different counts reflect different questions and different enumerations. A larger
bar is not a stronger theorem.

![P3109 value-table checks and SoftPosit arithmetic checks grouped by bit width, with hatched bars for sampled comparisons and diamonds at widths with differences](assets/ch11-conformance-widths.png "Compared cases by encoded width, not execution times. SoftPosit differs once each at 14 and 15 bits, twice at 16 bits, and 7,560 times at 32 bits.")

</details>

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
[rounding theory](#/chapter/the-mathematics-of-rounding) follows that formulation. The
[matched Flocq comparison](#/chapter/performance/matched-binary-arithmetic-with-flocq-and-mpfr)
measures its extracted rounded arithmetic alongside FloatLib and MPFR.

### FloatSpec and Flocq-style arithmetic

**FloatSpec** ports Flocq's organization and arithmetic to Lean [@floatSpec]. Its generic
formats, rounding predicates, ulp theory, and error lemmas let a proof describe arithmetic
without starting from a fixed machine word. Its IEEE modules then connect those ideas to
bounded binary representations. This is useful when translating a Flocq argument into Lean,
studying a rounding rule, or relating an algorithm's integer intermediates to its real-valued
specification.

The distinction between exact and rounded operations is visible in the API.
[`Calc.Operations.Fplus`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/Calc/Operations.lean#L187-L202)
aligns integer significands and adds them. Its `F2R_plus` theorem states that the decoded
result is the exact real sum, assuming a radix greater than one. `Fmult` similarly multiplies
significands and adds exponents. Neither operation chooses a destination precision.
They are useful exact building blocks, but timing them alone would omit the rounding work
in FloatLib's public encoded arithmetic.

FloatSpec also has the complete rounded layer. Its
[`BinarySingleNaNFloat prec emax`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/IEEE754/BinarySingleNaN.lean#L96-L107)
represents signed zero, signed infinity, one NaN, and finite values whose constructors carry
positivity and format-bound proofs. `BinarySingleNaN.Bplus`, `Bminus`, `Bmult`, `Bdiv`,
`Bsqrt`, and `Bfma` take a rounding mode. Their correctness theorems concern the rounded
result, including the relevant sign, finiteness, and overflow conditions. For example,
[`Bplus_correct`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/IEEE754/BinarySingleNaN.lean#L14884-L14904)
assumes finite operands and identifies the result with real rounding when the rounded
magnitude is below the overflow bound; its other branch specifies overflow.
[`Bdiv_correct`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/IEEE754/BinarySingleNaN.lean#L15465-L15484)
requires a nonzero decoded divisor.
The separate `Binary` interface retains NaN signs and payloads. These proof-carrying
representations should not be confused with the permissive compatibility carriers in the
same source files.

The primitive-float bridge answers another useful question:
[`FaithfulPrimFloat.PrimitiveFloat.toModel_add`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/IEEE754/PrimFloat.lean#L1574-L1580)
relates its arithmetic to Lean's logical `Float.Model`; corresponding theorems cover
multiplication, division, and square root. Such a model equation is distinct from certifying
the processor instruction used by a compiled native `Float` call.

The rounded SingleNaN definitions are marked `noncomputable`, so calling them directly from
an ordinary compiled definition fails. That keyword does not establish that their arithmetic
needs a non-executable real-number operation. Our
[benchmark driver](assets/floatspec-rounded-evidence.zip) unfolds selected upstream definitions
and substitutes real-valued let bindings used only in proofs, while preserving the sharing of
integer computations. Five theorems, each proved by `rfl`, identify the resulting functions
with the upstream rounded operations. We timed those compiled wrappers, including final
rounding, without replacing the arithmetic algorithms. The
[results below](#/chapter/external-validation/rounded-arithmetic-with-floatspec) show both
successful arbitrary-precision execution and a costly conversion on the addition path.

### FLoPS and P3109

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
problem in Rocq, building on Flocq and the [Interval package](https://coqinterval.gitlabpages.inria.fr/) [@vcfloat2]. **Gappa**, by Marc Daumas
and Guillaume Melquiond, combines interval reasoning and properties of rounded operators
to certify numerical bounds [@gappa]. These tools are natural comparisons for error-bound
automation: which expressions they accept, which input assumptions they need, and how
tight a bound they prove. FloatLib's operation refinements and rounding theorems supply
ingredients for such arguments; they do not by themselves constitute the same automation.

**LeanCert** uses interval arithmetic and Taylor models to automate proofs of bounds,
roots, and integrals for real-valued functions in Lean [@leanCert]. Both libraries
provide proved interval enclosures; FloatLib focuses on customizable numerical formats,
rounding rules, and certified executable arithmetic.
Its [interval tactic](#/chapter/proving-numerical-bounds) proves real inequalities from
rational input bounds using expression evaluation and subdivision. It can discharge
numerical subgoals in an error analysis; the rounding model and its connection to the
program remain explicit.

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
[chapter 17](#/chapter/performance/scalar-conversions-with-tensorlib) gives the timings.

For floating tensor arithmetic, TensorLib decodes FP16, BF16, and the supported FP8
operands to `Float32`, performs the operation, and encodes the result back. Binary32
operates directly in `Float32`, and binary64 uses `Float`. Compiled calls therefore rely
on native floating-point operations agreeing with Lean's logical model.

We offer that execution choice too, through the explicit
[`NativeFPU.Unchecked` interface](#/chapter/lean-native-floats/opting-into-guarded-host-operations)
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
[the native-floats chapter](#/chapter/lean-native-floats/formats-rounding-directions-and-status)
show these value/status distinctions
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

### Binary arithmetic with Flocq and MPFR

The [matched timing comparison](#/chapter/performance/matched-binary-arithmetic-with-flocq-and-mpfr)
uses the same rational inputs, binary precision, exponent bounds, and nearest-even rounding
in FloatLib, Flocq, and MPFR. Before timing, we compare the complete significand, exponent,
and sign of the prepared inputs and each operation's results. All 528 inputs and 1,056
results agree across the three implementations, after removing redundant powers of two.

There are sixteen input sets for each of eleven widths and six operations: addition,
subtraction, multiplication, division, square root, and FMA. The timed loops also check
result and input-selection checksums on a common prefix. These fixtures contain finite
values and positive zeros; exception flags and NaN handling are covered by other checks
in this chapter. The [result archive](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/flocq-matched/README.md)
includes the complete values and a script that compares them again.

### Rounded arithmetic with FloatSpec

We compared the rounded SingleNaN operations with FloatLib at matching significand
precisions from 8 to 4,096 bits, using nearest-even rounding and the same exponent range.
Both received the same exactly representable dyadic inputs: 256 pairs for each of three
patterns, with equal exponents, small exponent gaps, or gaps between one and two significand
widths. Square root used the absolute value of the first operand.

An independent integer/rational oracle checked each returned value before timing; square
root used integer square root and an exact halfway comparison. We checked signed zero and
NaN/infinity classification as well, then checked each timed loop's rolling checksum against
the verified outputs. This comparison does not check NaN payloads or exception flags.
All **108 completed precision/pattern/operation pairs** passed their numerical and checksum
checks. The remaining 42 pairs failed during FloatSpec verification and have no timing ratio.

The table reports **FloatSpec time divided by FloatLib time**, geometrically averaged over
the three input patterns. Above 1 means FloatLib was faster; below 1 means FloatSpec was
faster. Each underlying case has one timing round, so these are observations from that run,
without an estimate of timing variability.

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

FloatSpec's square root was faster at 8, 16, and 24 significand bits. Its multiplication,
division, and square root all completed through 4,096 bits. The much larger addition and
subtraction ratios come from a specific conversion in the measured implementation.

Follow a finite addition through `BinarySingleNaN.Bplus`: it aligns the operands, adds
their integer significands, and calls `Binary.normalize`. The result then passes through
`standardFloatToBinaryFloatOfNotNaN`, which converts its natural-number significand to
the recursive `Positive` representation. The
[`binaryPositiveOfNatSucc` implementation](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/IEEE754/Binary.lean#L529-L542)
first recurses on the predecessor and then increments the returned positive number.
Converting a significand $m$ therefore makes $m-1$ recursive descent steps. For a normal
$p$-bit significand, that is at least $2^{p-1}-1$ steps, although the final representation
has only $p$ bits. At $p=24$, the lower bound is 8,388,607 steps.

Subtraction calls addition with a negated operand and inherits this path. Multiplication,
division, and square root in the measured SingleNaN wrappers avoid this runtime conversion.
Some conversions still appear in their proof terms, which compilation erases. The expensive
addition conversion constructs runtime data; it is not proof checking or evaluation of
`Real`.

For scale, the geometric-mean 24-bit addition times were **110.29 ns for FloatLib and
90.57 ms for FloatSpec**. Subtraction took **109.10 ns and 91.00 ms**, respectively.
These large gaps characterize that conversion bottleneck. They do not measure an inherent
cost of verification or establish an ordering between the libraries for every operation.

The missing addition/subtraction entries failed during verification: stack overflow at
53, 113, and 256 bits, including post-crash deadlocks, and the 8 GiB memory limit at
512 through 4,096 bits. The [diagnostic records](assets/floatspec-rounded-evidence.zip)
support these classifications. They describe the tested paths and resource settings,
not format-support limits, and provide no speed ratios.

<a id="floatspec-measurement-record"></a>

<details>
<summary>FloatSpec source revisions and measurement protocol</summary>

The comparison uses FloatSpec `158263e983ec3925e02b10f5b312498bf414e0f1` and FloatLib
based on `0d91825727839f597fd06b22fdd038ea21480f0c`. The
[evidence download](assets/floatspec-rounded-evidence.zip) includes source and binary
hashes, drivers, protocols, results, and diagnostic records; full input fixtures and
verification streams are not included.

Both arms used **Lean 4.34.0-rc2 and the same Mathlib**. FloatLib needed import-path
compatibility edits; its arithmetic bodies were unchanged. The FloatSpec driver used
definition expansion and proof-only let substitution, with `@[inline]` generic wrappers
and `@[noinline]` functions specialized to each precision. Each arm selected its format
and operation before timing. The driver equality theorems cover addition, subtraction,
multiplication, division, and square root; FMA was not measured.

Every format had **15 exponent bits**, bias 16,383, and FloatSpec `emax = 16384`;
the minimum significand exponent was $3-16384-p$. Thus a 24-bit point means 24 significand
bits in a custom format, not the named IEEE binary32 layout. A separate binary32
spot check passed eight cases; it was not this timing workload.

Each pair ran sequentially on the same pinned logical CPU of an **Intel Xeon Platinum
8488C**, alternating arm order by case. Input construction was outside the timer.
A 256-call warmup preceded 64 passes over 256 fixtures: **16,384 timed calls per arm**.
Input selection, arithmetic, allocation, result projection, and checksum work were included;
the representations have different result-consumption costs. Pinning did not reserve an
exclusive core. The one-round results cannot quantify repeatability or be pooled with the
separate Flocq/MPFR experiment.

</details>

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

Arb [@johanssonArb2017], through python-flint [@pythonFlint], supplies rigorous enclosures for the tested interval and
transcendental inputs. Those enclosures give an independent check on the computations.
Agreement on these inputs does not prove a global error bound or correct rounding everywhere.

<a id="duration-and-the-release-outcome"></a>
<a id="a-small-input-that-exposed-a-logarithm-bug"></a>

## Why logarithms near 1 are difficult

For binary elementary functions, we compared FloatLib with MPFR, CORE-MATH [@coreMath],
OpenLibm [@openLibm], and the supported RLIBM functions [@rlibmAll]. These libraries offer
different functions and accuracy guarantees. The binary approximation kernels compared here
have no general correct-rounding theorem. FloatLib's separate
[certified exponential and logarithm](#/chapter/elementary-functions/certified-exponential-and-logarithm)
prove nearest-even rounding for every successful finite result.
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
[Figure 19.3](#/chapter/external-validation/figure-ch11-universal-preflight) explain
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

## Designing independent comparisons

The completed suites above check particular inputs and contracts. Extending them requires
choosing an independent reference and deciding exactly what agreement means. The following
requirements guide those extensions; they are not additional completed comparison counts.

### Words, flags, and conversion success

Numerical order alone cannot check an ordering rule for NaN signs, signaling bits, and
payloads. Those comparisons need a bit-level reference, as do custom exponent fields outside
MPFR's supported range. With several NaN operands, the comparison must state a selection
policy: a permitted sign or payload choice can differ even when both results are valid.
The invalid flag still needs its own check.

<a id="posit-integer-conversion"></a>

Integer conversion must apply its rounding rule before checking the destination range.
A negative fraction can round to unsigned zero. For posits, the exceptional integer word
also collides with the ordinary unsigned value $2^{w-1}$. A comparison must check success
conditions as well as delivered bits, which alone cannot identify that exceptional case.

<a id="decimal-values-cohorts-and-flags"></a>

### Decimal datums and exact text

A [decimal result](#/chapter/decimal-arithmetic/encoding-the-complete-datum)
has a sign, coefficient, and quantum exponent, or a special-value datum,
together with its flags. We need to distinguish $1.50$ from $1.5$: they differ as datums even
though they denote the same rational. A comparison through libmpdec can check arithmetic and
cohort choices; an independent rational calculation can check projection into a decimal grid.
For an irrational square root, outward MPFR bounds can provide a reference when both endpoints
round to the same decimal datum.

Subnormals, exact tiny results, range boundaries, signed zeros, and quiet and signaling NaNs
exercise different rules, so each belongs in the comparison inputs.

Quantize needs a comparison of the requested quantum as well as the value. Classification and
total ordering need raw-word cases, including redundant encodings. Remainder and neighboring-value
operations need their own reference calculations; agreement on addition does not test them.
The BID and DPD codecs also need exact-datum round trips.

Conversions add destination-specific questions. Decimal-to-binary conversion usually changes
the value, while decimal-to-decimal conversion may preserve it but choose another cohort.
Custom descriptors whose exponent ranges lie entirely above or below zero test assumptions
that the three named decimal formats would not reveal.

Parsing and formatting need both value checks and syntax checks. A round trip should recover
the original word, including signed zero and NaN metadata where the syntax preserves them.
An exact rational parser can check a finite decimal or hexadecimal spelling without first
rounding it through a host float. Requested-precision output also needs a rounding comparison:
a string can be valid syntax and still denote the wrong neighbor. Invalid syntax needs
separate rejection tests.

<a id="posit-decimal-text"></a>

Every finite posit is a dyadic rational, so it has a terminating exact decimal expansion.
We can check a printed string with an independent rational decoder and parser, avoiding
conversion through binary64. Exact output can be long at wide formats. Invalid syntax and
NaR need separate checks, and configured storage should be exercised as well as model words.
The [all-width round-trip proofs](#/chapter/posits-and-the-quire/exact-decimal-text)
establish recovery of the original word; executable comparisons would additionally exercise
the compiler and text interface.

<a id="natural-posit-exponentials-and-logarithms"></a>
<a id="posit-exponentials-and-logarithms"></a>
<a id="posit-hyperbolic-functions"></a>

### Rounding transcendental results

The [real-rounding proofs](#/chapter/posits-and-the-quire/exponentials-and-logarithms) cover
`exp`, `expMinus1`, `log`, and `logPlus1` on every finite input in each function's domain.
The [hyperbolic functions](#/chapter/posits-and-the-quire/hyperbolic-functions) also have
real-rounding proofs with their inverse-domain conditions. Independent executable checks
would exercise another implementation of these rules.

Decode the input as an exact dyadic, enclose the real function with directed MPFR bounds,
and round both bounds with a separate implementation of the posit rule. When both select
the same word, they determine the expected result. Fixed oracle precision is insufficient
while the bounds still straddle a rounding threshold. At eight bits, every input word can
be enumerated. Wider formats need selected inputs around domain endpoints, rounding
boundaries, zero, and both signs of the finite extremes. The binary approximation kernels
discussed above require a separate accuracy comparison.

<a id="exact-trigonometric-comparisons"></a>

### Trigonometric ordering and argument reduction

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
<a id="posit-trigonometric-functions"></a>

To check the [rounded radian functions](#/chapter/posits-and-the-quire/ordinary-trigonometric-functions),
whose model and configured operations have real-rounding proofs, the independent rounder must use
the standard's appended-bit threshold, which need not be the arithmetic midpoint between
two posits. Reusing an IEEE nearest-value rounder would check a different rule. The test also
needs NaR and inputs outside the inverse functions' real domains.

<a id="pi-scaled-posit-trigonometric-results"></a>
<a id="pi-scaled-posit-trigonometric-functions"></a>

For a pi-scaled function, exact rational period reduction should precede the numerical
reference call. Forming a large approximate product with π can lose the very phase we want
to test. Integer and half-integer arguments also give exact zeros, extrema, and poles that
need explicit classification. At an integer multiple of π, for example, cosine's sign is
determined by the integer's parity, even when that integer is too large for a host float.

<a id="two-coordinate-posit-angles"></a>
<a id="posit-atan2"></a>

The two-coordinate functions `arcTan2` and `arcTan2Pi` need pairs of inputs. Axes and
diagonals give exact special cases, while points close to an axis test whether the sign and
small angular displacement survive the comparison. An independent check should include all
quadrants, NaR, and operands of very different magnitudes. A correct result and a practical
running time remain separate properties, especially at wide precisions.

<a id="inspecting-the-comparison-records"></a>
<a id="tests-what-is-validated"></a>

<a id="exploring-the-comparisons-yourself"></a>

## Running the comparisons

To reproduce the comparisons, see [tests/EXTERNAL.md](https://github.com/lean-dojo/FloatLib/blob/main/tests/EXTERNAL.md).
