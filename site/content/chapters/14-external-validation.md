---
number: "14"
slug: external-validation
title: How we test FloatLib
summary: "Why a proved library still needs testing, which independent libraries and tables we compared FloatLib with, which runs tried every input and which sampled, and every difference we found and its cause."
---

FloatLib's proofs establish that implementations satisfy their specifications. Independent tests compare the resulting values and exception flags with other libraries and published format tables. This chapter describes those comparisons, the differences they found and the conclusions each test supports.

## Why does a proved library need testing?

Suppose we misread a standard such as IEEE 754 somewhere. How would you know? Not from our proofs. A proof shows that the code matches our specification, our mathematical statement of what each operation returns. If the specification is wrong, the two agree perfectly on the wrong answer.

A refinement proof establishes that an implementation agrees with its specification. If that specification misinterprets the standard, the proof alone cannot identify the error. Comparisons with independent implementations can reveal such discrepancies.

## What did we compare FloatLib against?

We used three kinds of second watch. The first is software that computes the same answers. For IEEE arithmetic that's Berkeley SoftFloat, a software implementation of IEEE floating point, with its test program TestFloat, and MPFR [@fousseMpfr2007], a C library for correctly rounded arithmetic at any precision. Correctly rounded means you get the exact answer rounded once. For posits, the alternative number format of the posits chapter, it's SoftPosit and the Universal library, and for narrow formats simulated inside wider ones, MPFX.

The second kind is a published value table, which lists what each bit pattern of a format means, such as those for the small machine-learning formats of the IEEE P3109 working group. The third is another verified library, such as Flocq, FloatSpec, FLoPS or TensorLib. Each kind catches its own mistakes. TestFloat can expose a wrong exception rule, a published value table a bad decoder (the code that reads a bit pattern as a number), and a comparison with hardware also tests the compiler and floating-point settings of that run.

![Total comparison counts by external tool on a logarithmic scale, with SoftPosit's differences marked separately](assets/ch11-conformance-evidence.png "Bars count compared cases, not time or a percentage of input coverage. The marked SoftPosit differences are examined against exact arithmetic.")

[Figure 14.1](#/chapter/external-validation/figure-ch11-conformance-evidence) counts the cases of the release suites we kept, the ones that report a case counter we can compare. It leaves out the MPFX runs and the exhaustive runs, which try every input and come in the next section. A case can be a table entry, a generated operation or a bounded expression, so don't read the bars as a common percentage of possible inputs.

<details>
<summary>Comparison counts by encoded width</summary>

[Figure 14.2](#/chapter/external-validation/figure-ch11-conformance-widths) groups the comparisons by bit width. At 5 bits P3109 contributes 576 table cases and SoftPosit 40,000 arithmetic cases, and at 6 bits it's 1,408 and 290,944, but they ask different questions, so a taller bar isn't a stronger theorem.

![P3109 value-table checks and SoftPosit arithmetic checks grouped by bit width, with hatched bars for sampled comparisons and diamonds at widths with differences](assets/ch11-conformance-widths.png "Compared cases by encoded width, not execution times. SoftPosit differs once each at 14 and 15 bits, twice at 16 bits, and 7,560 times at 32 bits.")

</details>

## Can you test every input?

Sometimes you can. A 16-bit format has $2^{16}=65,536$ bit patterns, so a two-operand operation has $2^{32}$ ordered operand pairs, about four billion. That's few enough to try every one. Binary16 is IEEE's 16-bit format, and bfloat16 is the 16-bit machine-learning format with binary32's exponent range. We ran every binary16 and bfloat16 addition, subtraction, multiplication and division on all of these pairs, in each of the four rounding directions (nearest-even, up, down and toward zero), plus every binary32 square root.

That's 154,618,822,656 cases. Each one compared the value and all five exception flags, the conditions IEEE 754 asks every operation to report: invalid, divide by zero, overflow, underflow and inexact. SoftFloat and MPFR agreed with FloatLib on every single one. The run used FloatLib's status-returning operations, which hand back the flags with the value. SoftFloat was the reference for values and all five flags in binary16 and binary32. For bfloat16 it was MPFR, set to the format's precision and exponent range, after we checked it against SoftFloat on every binary16 pair.

In nearest-even mode each case also compared two parts of FloatLib: the planner's kernel, the fast word-level code chosen to run the operation, and the model, FloatLib's arithmetic written once for every format. Two certified functions, `ExecFloat.Binary.Certified.expMinus1` and `logPlus1`, got an exhaustive binary32 run too. Every result they returned on all $2^{32}$ binary32 inputs and on CORE-MATH's binary64 worst cases, the hardest inputs to round, was MPFR's correctly rounded value.

Runs like these are the exception, since a binary32 operation already has $2^{64}$ operand pairs, far too many to try. Besides them, every input was tried for SoftPosit up to 8 bits, MPFX on the binary16 and bfloat16 pairs, FLoPS addition, multiplication, division and four-bit FMA, TensorLib's widening conversions, our ternary-value test on `ieee 4 3`, and the binary16 and bfloat16 inputs of the elementary-function qualification tier. We'll come back to each of these below. The other comparisons use chosen inputs, and each section says which.

## How do we test the wider IEEE formats?

For the wider formats we turn to Berkeley TestFloat [@hauserTestFloat], backed by SoftFloat [@hauserSoftFloat], our main independent arithmetic reference. TestFloat generates test cases and compares the answers with SoftFloat's, and its level 2 runs many more cases than level 1. IEEE 754 lets an implementation decide before or after rounding whether a result is tiny enough to underflow, which is called detecting tininess. Our level-1 comparison covers binary16, binary32, binary64 and binary128 arithmetic, comparisons and supported conversions in the four IEEE rounding directions, with tininess detected after rounding.

NaNs, the not-a-number results of operations such as $0/0$, are compared by class, signaling behavior and invalid flag, not by a universal rule for choosing the payload, a NaN's spare bits. All other results must match bit for bit. The flags matter too. Halve $2^{-149}$, the smallest positive binary32 subnormal (one of the tiny values below the normal range), and you get a tie that nearest-even rounds to zero with underflow and inexact, as the [native-floats chapter's worked calls](#/chapter/lean-native-floats/what-does-floatlib-add-to-float-and-float32) show. Return the right zero without those flags and the test fails.

All 102,454,320 level-1 cases of the full profile passed, values and flags. TestFloat calls the model operations, which share their kernels with the [October 2026 speed work](#/chapter/performance/what-made-floatlib-faster-in-october-2026). Three selected level-2 generators added 1,272,128 cases and all three completed, but we haven't run every level-2 combination, and binary80, decimal formats, nearest-away, round-to-odd and tininess-before-rounding are left out.

Separately, IBM's test generator FPgen [@ibmFpgen] supplied 81,513 more inputs, and the SMT solver Z3 [@z3], a program that decides logical formulas, gave 27,492 bounded ground cases (concrete cases with no unknowns) in SMT-LIB's floating-point logic QF_FP [@smtLibQfFp] and 147,876 in a second run, with no mismatch. SMT, short for satisfiability modulo theories, treats floating-point NaNs abstractly, so the Z3 adapter checks the exact encoding where the theory pins it down and the class where it doesn't.

## What can a value table check?

Published format tables provide another independent reference. The format-table suite checked 7,602,160 P3109 cases from the public 4.0.3 tables at widths 3 through 16, and 1,296 ONNX cases, with zero mismatches. These tests establish agreement of decoding with the tables for the tested entries. They do not establish correctness of P3109 arithmetic, exception handling, saturation, block scaling or OCP MX interoperability.

Checking entries is where MPFR comes in. Our suites against it passed 400 primitive cases, 672 cases of exact sums and dot products, and 131,072 binary16 cases split between addition and multiplication, 65,536 of each operation's $2^{32}=4,294,967,296$ pairs, in the four IEEE rounding directions. MPFR checks rounded finite values, though, and can't check every NaN payload or NaN-selection rule.

Outside the release record, the repository's primitive and reduction oracles, references that give the right answer, also run all six directions of [the rounding chapter](#/chapter/the-mathematics-of-rounding/how-to-choose-a-rounding-direction), comparing encodings and all five flags. The test suite checks ternary values, which say whether a result lies below, at or above the exact one, against an exact rational reference on every operand pair of `ieee 4 3`, the 8-bit format with four exponent and three fraction bits, in all six directions. And for the tested interval and transcendental inputs, Arb [@johanssonArb2017], through python-flint [@pythonFlint], gives a second opinion from rigorous enclosures, intervals guaranteed to hold the true value, which doesn't prove a global error bound or correct rounding everywhere.

## How do we test the elementary functions?

Next come the elementary functions, the familiar functions of calculus such as `exp`, `log` and `sin`. The binary approximation kernels of [the elementary functions chapter](#/chapter/elementary-functions/how-to-compute-exp-log-and-sine) have no accuracy theorem, apart from the correctly rounded `Model.pi` and the cases of `pow` covered by its integral-power theorem or a settled enclosure search. The rest is tested.

A gate, a test that has to pass, compares `exp`, `log`, `sin`, `cos`, `sinh`, `cosh`, `tanh`, `pow` and `pi` with MPFR's round-to-nearest in binary16, bfloat16, binary32, binary64, binary128 and `ieee 31 23`, through a C oracle that carries any binary layout exactly with the GMP big-number library. Its cases include edge cases, random arguments from a fixed seed (so every run sees the same ones) and continued-fraction arguments near multiples of $\pi/2$ in every binade, the stretch between two neighbouring powers of two. The gate has three tiers. The default tier has 28,671 cases, the release tier 39,393 and the qualification tier 1,140,927, which adds every binary16 and bfloat16 input. Every case matches MPFR, and the gate's list of known failures is empty.

### Why are logarithms near 1 hard?

A few of FloatLib's elementary functions promise more than the kernels do, because they're correctly rounded, and for logarithms near 1 that's a hard promise to keep. For binary elementary functions we compared FloatLib with MPFR, CORE-MATH [@coreMath], OpenLibm [@openLibm] and the supported RLIBM functions [@rlibmAll], which offer different functions and accuracy guarantees, so let's spell out what ours promise.

FloatLib's correctly rounded `ExecFloat.Binary.CorrectlyRounded.exp`, `log`, `expMinus1`, `logPlus1` and weighted `exp x * w`, from the `Configured.CorrectlyRounded` import, always return a value on an IEEE format. Every finite result on a finite input in the domain is the nearest-even rounding of the exact value, and a result at or beyond the overflow threshold is the infinity with the exact result's sign. Underneath, `exp` and `expMinus1` start from a [certified search](#/chapter/elementary-functions/how-to-get-an-exp-or-log-with-a-proof), `ExecFloat.Binary.Certified.exp` and `expMinus1`, and the search returns an error when it can't settle. Posits have [proved exponentials and logarithms](#/chapter/posits-and-the-quire/how-to-compute-exponentials-and-logarithms) of their own.

So what makes them hard? Take the representable value just below 1. The obvious route approximates the logarithm of a significand near 2 and subtracts an approximation to `log 2`. Both are near 0.69 and their difference is the tiny answer, so errors in the two larger approximations can overwhelm its last bits. Centering the significand around 1 avoids that subtraction, but in $\log(1-\delta)=-\delta-\delta^2/2-\delta^3/3-\cdots$ the quadratic term can land exactly on a rounding midpoint, and discarding the remaining terms can pick the wrong neighbor.

## Why did SoftPosit disagree with FloatLib?

A posit spends most of its precision near one and less at the extremes, as [the posits chapter](#/chapter/posits-and-the-quire) explains, and SoftPosit [@softPosit] is a C library of posit arithmetic. Against it, 32,893,800 cases produced 7,564 differences. That sounds like a lot, but they all came from just seven distinct inputs and two defects in the SoftPosit version we tested, and on every one the exact calculation sides with FloatLib. From 2 through 8 bits the comparison is exhaustive for the operations we tested, and above that it samples, at every width from 9 through 16 and at 32 bits. Its 9,175,040 comparisons at widths 9 through 15 cover all ten operations at each width.

Widths 9 through 13 agreed everywhere. Then, at 14 bits, the trouble starts. There's one difference in a fused multiply-add there, the FMA that computes $xy+z$ with a single rounding, one at 15, two in 1,310,720 cases at 16 bits and 7,560 in 2,621,440 at 32 bits. On all seven inputs, FloatLib's public operation and its exact rational specification agreed.

### How to settle a difference by hand

Let's settle the positive one of the two 16-bit differences. A posit is stored as a word, a raw bit pattern, written here in hexadecimal. If you start with the operand words `0x7680`, `0x6128` and `0x0001`, they decode to $2560$, $165/8$ and $2^{-56}$, and the exact multiply-add is

$$
2560\cdot\frac{165}{8}+2^{-56}=52800+2^{-56}.
$$

The adjacent result words are `0x7b9c`, denoting $52736$, and `0x7b9d`, denoting $52864$. Their midpoint is $52800$. The exact result $52800+2^{-56}$ is strictly above the midpoint, so nearest rounding selects the upper word, `0x7b9d`, as FloatLib does. SoftPosit's generic pX2 code returned `0x7b9c`, the result obtained by discarding $2^{-56}$ and rounding the resulting tie to the even lower word.

A sticky bit records whether any discarded low-order bits were nonzero. Once set, it must remain set as further bits are discarded. The pX2 code initially records this information but later overwrites it. The other 16-bit case, $-65536000-2^{-50}$, loses the sticky information just below a midpoint. The following cases have the same problem:

| Width | Exact FMA result | SoftPosit result | FloatLib result |
| --- | --- | ---: | ---: |
| 14 | $64768 + 2^{-48}$ | 64,512 | 65,024 |
| 15 | $-3060 - 2^{-52}$ | -3,056 | -3,064 |

In a copy of SoftPosit's `s_mulAddPX2.c`, changing `bitsMore = ...` to `bitsMore |= ...` preserves previously recorded sticky information by combining the new bits with the old ones. This change corrects all four FMA results. The counts above refer to the original version; the patched comparison establishes agreement only for these four inputs.

### Where SoftPosit disagrees with itself

The other three inputs come from the second defect. SoftPosit has a generic variable-width path, pX2, and dedicated p32 functions for 32-bit posits. The three inputs are 32-bit boundaries where the two disagree, so the library contradicts itself. For `0xfffffffd + 0xfffffffe`, whose exact sum is $-5\cdot2^{-116}$, FloatLib and p32 return `0xfffffffd`, one unit of $2^{-116}$ away, and pX2 returns `0xfffffffe`, four units away.

After its sign bit, a posit word starts with the regime, a run of identical bits that sets the scale. At these boundaries the regime leaves room for one exponent bit, and the generic addition, multiplication and division paths reach `regA = 29` and `expA = 2` and compute `expA << (28 - regA)`, a left shift by $-1$, which is undefined in C. The p32 path does the right shift this case needs, $2 \mathbin{\gg} 1 = 1$, and fixing only this shift in a copy of the code corrected all three results.

## What bugs did we find in MPFX?

The comparisons with MPFX [@saikiDoubleRounding2026] found four bugs. MPFX simulates a narrow format using a wider C `double` or `float` as a container. It first computes a round-to-odd result, then rounds that value to the target format. The odd last bit distinguishes an inexact intermediate result from an exact midpoint under the precision conditions described in the [rounding chapter](#/chapter/the-mathematics-of-rounding/why-rounding-twice-can-go-wrong).

MPFX's rounding theorems need format-containment conditions, such as two extra precision bits for nearest rounding, and a final rounding that doesn't overflow. One fast engine gets round-to-odd from the hardware's round-toward-zero mode and inexact flag, the other from an error-free transformation (EFT), extra operations that compute the rounding error.

To find the bugs, we compared both engines with FloatLib on binary16, bfloat16, the 8-bit IEEE-style `e4m3` and `e5m2`, and the two formats at the edge of the class MPFX supports. That's 316,800,000 comparisons on chosen operands, plus every binary16 and bfloat16 pair of the exhaustive run. Each of the four problems below reproduces without FloatLib. The sampled run turned up other EFT differences too. We grouped those by engine, and that alone doesn't tell us their cause.

The first bug is the sign of zero. Under roundTowardNegative, the standard's name for rounding down, IEEE 754 makes an exact zero sum such as $1 + (-1)$ equal to $-0$, but MPFX returns $+0$ for every such sum, difference and FMA, in both engines and every format. That's 63,488 binary16 pairs and 65,280 bfloat16 pairs per operation, one $x - x$ for each finite $x$. The next two are missing flags. MPFX's square root of $-\infty$ returns a NaN without the invalid flag, and when the container's own result overflows, as for large bfloat16 products in a `float`, the overflow flag goes missing although the rounded result is infinite.

The fourth bug is in the EFT engine. The engine uses an FMA to compute the residual for a product, quotient or square root. If that residual rounds to zero in the container format, the engine treats the result as exact. In bfloat16, $2^{-70}\cdot2^{-90}$ rounded toward positive infinity should produce $2^{-133}$, the least positive value. Instead, it returns zero without inexact or underflow flags because the product underflows in the `float` container. When rounding $\sqrt{3\cdot2^{-1072}}$ to 51 bits, the engine returns `0x1.bb67ae8584ca8p-536`, one unit below the `0x1.bb67ae8584cacp-536` returned by the hardware engine and FloatLib.

MPFX's notes record this failure for binary64 products, quotients and FMAs, but not for square root or the `float` container. We reported all four classes in [bksaiki/mpfx#36](https://github.com/bksaiki/mpfx/issues/36), with reproducers that use only MPFR, SoftFloat and the host FPU.

## Why are some posit timings missing?

![Universal comparisons for six operations at thirteen posit widths, where seven square-root results differ.](assets/ch11-universal-preflight.png "Width/operation comparisons against Universal, not execution times. Each blue cell matched on all sixteen benchmark inputs, and seven wide square-root configurations differed and are omitted from timings.")

A comparison can also decide what's fair to time. Some timing markers are missing on purpose, and [Figure 14.3](#/chapter/external-validation/figure-ch11-universal-preflight) shows why. Before timing posits against the Universal library, we compared six operations at thirteen posit widths from 5 through 4,096 bits on the sixteen inputs the benchmark uses, which doesn't imply agreement on every input. Of these 78 combinations, 71 agreed and seven differed, all in square root, at widths 64, 128, 256, 512, 1,024, 2,048 and 4,096. Universal's square root goes through a host binary64 conversion, so its passing measurements are labelled hardware-assisted and kept apart from software posit arithmetic, and the differing ones stay out of the timing plots.

Converting a wide posit to binary64 can discard precision. Converting the host result back to a posit cannot recover the discarded information. This observation does not explain every disagreement, but it shows why a host-assisted implementation needs an independent agreement check and cannot serve as a general reference for arbitrary-precision posit square root.

## How does FloatLib relate to other verified libraries?

Where does FloatLib sit among the other verified numerical libraries? Verified floating point works at three levels. A rounding theorem says which result to choose, an implementation theorem connects that choice to code that runs, and a program-level error bound accounts for every rounding step in a calculation. Much of the mathematical foundation comes from Flocq [@boldoMelquiond2011], in the Rocq proof assistant, and FloatLib's [rounding theory](#/chapter/the-mathematics-of-rounding) follows its formulation.

### How FloatLib compares with Flocq and MPFR

Our [matched timing comparison](#/chapter/performance/how-does-floatlib-compare-with-flocq) checks the answers too. It gives FloatLib, Flocq and MPFR the same rational inputs, precision, exponent bounds and nearest-even rounding, with sixteen input sets for each of addition, subtraction, multiplication, division, square root and FMA at eleven widths. With redundant powers of two removed, all 528 inputs and 1,056 results agree in significand, exponent and sign across the three. The fixtures hold only finite values and positive zeros, so flags and NaNs are left to the other checks. The [result archive](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/flocq-matched/README.md) has the values and a script that compares them again.

### How FloatLib compares with FloatSpec

FloatSpec ports Flocq's organization and arithmetic to Lean [@floatSpec]. Its rounded layer, [`BinarySingleNaNFloat prec emax`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/IEEE754/BinarySingleNaN.lean#L96-L107), named for its single NaN value, comes with correctness theorems for its rounded operations under sign, finiteness and overflow conditions. FloatSpec's bridge, [`FaithfulPrimFloat.PrimitiveFloat.toModel_add`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/IEEE754/PrimFloat.lean#L1574-L1580), relates its arithmetic to Lean's logical `Float.Model`, but that equation doesn't certify the processor instruction a compiled `Float` call uses. It's the same boundary we met with Lean's own float model.

How do you time a `noncomputable` definition, one Lean won't compile into running code? FloatSpec's rounded definitions are noncomputable, so our [benchmark driver](assets/floatspec-rounded-evidence.zip) unfolds them and substitutes the real-valued let bindings that only proofs use, and five theorems, each proved by `rfl`, identify the results with the upstream operations. The times below come from those compiled wrappers, with no arithmetic algorithm replaced.

We compared FloatSpec's rounded SingleNaN operations with FloatLib at significand precisions from 8 to 4,096 bits, with nearest-even rounding and the same exponent range, on 256 exactly representable input pairs for each of three patterns: equal exponents, small gaps, and gaps between one and two significand widths. An independent integer and rational oracle checked each value, and we checked signed zero, NaN/infinity class and each timed loop's checksum, but not NaN payloads or flags. All 108 completed precision/pattern/operation combinations passed, and the other 42 failed during FloatSpec verification, so they have no ratio in the table below.

Each entry is FloatSpec's time divided by FloatLib's, from a single timing round, geometrically averaged over the patterns, so above 1 means FloatLib was faster, and there's no estimate of variability. Every format had 15 exponent bits, so the 24-bit row is a custom format, not the IEEE binary32 layout. FloatSpec's square root was faster at 8, 16 and 24 bits, and its multiplication, division and square root completed through 4,096 bits.

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

The addition column looks like a typo, but one conversion explains it. After `BinarySingleNaN.Bplus` adds the aligned significands, [`binaryPositiveOfNatSucc`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/158263e983ec3925e02b10f5b312498bf414e0f1/FloatSpec/src/IEEE754/Binary.lean#L529-L542) converts the result to the recursive `Positive` type by recursing on the predecessor and incrementing. It writes a number down by counting up to it, so a significand $m$ takes $m-1$ steps, at least 8,388,607 for a normal 24-bit significand. Subtraction calls addition and inherits this path, and multiplication, division and square root avoid it. The conversion builds runtime data, so the cost isn't proof checking or evaluation of `Real`. The geometric-mean 24-bit addition took 110.29 ns in FloatLib and 90.57 ms in FloatSpec, and subtraction 109.10 ns and 91.00 ms, which measures this bottleneck, not an inherent cost of verification or a ranking for every operation.

What about the N/A entries? They failed during verification, by stack overflow at 53, 113 and 256 bits, post-crash deadlocks included, and by the 8 GiB memory limit at 512 through 4,096 bits. Our [diagnostic records](assets/floatspec-rounded-evidence.zip) back this up, but they describe our paths and resource settings, not limits on the formats FloatSpec supports.

<details>
<summary>FloatSpec source revisions and measurement protocol</summary>

We used FloatSpec `158263e983ec3925e02b10f5b312498bf414e0f1` and FloatLib based on `0d91825727839f597fd06b22fdd038ea21480f0c`, with the same Lean toolchain and Mathlib. The [evidence download](assets/floatspec-rounded-evidence.zip) has hashes, drivers, protocols, results and diagnostic records, but not the full input fixtures. The FloatSpec and FloatLib arms alternated by case on one pinned, not exclusive, logical CPU of an Intel Xeon Platinum 8488C, with a 256-call warmup and 16,384 timed calls per arm, and the timer also covers consuming each result, which costs differently in the two representations. We didn't measure FMA, the results can't be pooled with the Flocq/MPFR experiment, and a separate binary32 spot check passed eight cases.

</details>

### How FloatLib compares with FLoPS

For P3109, our closest neighbour is FLoPS [@flopsPaper] [@flopsArtifact]. Chang, Park, Lim and Nagarakatte formalize the four format parameters, all nine rounding modes, saturation and projection, and prove that their bit-level arithmetic refines the specifications. They also show that FastTwoSum can recover an overflow error under saturation, while ExtractScalar properties can fail at one-bit precision. One caution before the table: the FLoPS paper describes report 3.2.1 and [our P3109 material](#/chapter/low-precision-formats-for-machine-learning/what-is-ieee-p3109) follows 4.0.3, so a shared format name doesn't mean every operation and policy agrees.

| Question | FLoPS | FloatLib |
| --- | --- | --- |
| P3109 arithmetic | Parameterized formats, rounding, saturation, projection, and executable core arithmetic | The same core questions within a library that also supports IEEE binary and decimal, posits, and block formats |
| Stochastic rounding | Supplied-randomness operations, finite-randomness bias analysis, and summation RMS bounds under stated assumptions | Supplied-random-bit rounding and refinement; no general stochastic summation RMS theorem |
| Further operations | P3109 core arithmetic and numerical-algorithm properties | Square root, reciprocal square root, hypot, scaled operations, and independently chosen source and destination formats |

FLoPS's P3109 kernel [@flopsArtifact] is executable, so we could run it against FloatLib. On 529,152 arithmetic cases in Binary4p2sf, Binary8p4se and Binary8p3se, with nearest-even rounding and no saturation, the two never differed in the encoded result. The names give the width, the precision, and whether the format is signed and finite or extended with infinities. Addition, multiplication and division take every ordered pair of codes, NaN, zero and the infinities of the extended formats included. FMA takes all 4,096 four-bit triples but samples the eight-bit ones, pairing each $(x,y)$ with the third integer code $(17x+29y+43)\bmod256$. The run also checks the 192 fixtures of the [P3109 timing experiment](#/chapter/performance/how-does-floatlib-compare-with-flops). Stochastic rounding and the two saturation modes aren't covered.

### How FloatLib compares with TensorLib

TensorLib [@tensorLib] covers tensor storage in Lean, the multi-dimensional arrays that machine learning computes with. Its scalar conversions between `Float32` and FP16, BF16 and several FP8 layouts were faster than FloatLib's general descriptor cast, which reads both formats from their descriptions, on our fixtures, as [the performance chapter](#/chapter/performance/how-fast-are-conversions-between-formats) shows. Its tensor arithmetic runs the small formats and binary32 in `Float32` and binary64 in `Float`, trusting native floating point to agree with Lean's logical model.

FloatLib's opt-in [`NativeFPU.Unchecked` interface](#/chapter/lean-native-floats/how-to-use-the-processors-own-arithmetic) offers the same for supported binary32 and binary64 operations. A host call there carries no FloatLib refinement certificate, so it adds trust in the FPU, the runtime primitives and the floating-point settings. Even the certified software path relies on the compiler, runtime and hardware, and our conversion timings don't compare the two paths.

TensorLib's conversions are faster, but do they give the same answers? We compared FloatLib's descriptor cast with TensorLib's `Float32` conversions for FP16, BF16, E4M3FN and E5M2 [@tensorLib]. Both libraries passed 952,612 numerical checks against an independent nearest-even reference built from adjacent representable values.

| Format | Small format to Float32 | Float32 to small format |
| --- | ---: | ---: |
| FP16 | 65,536 | 393,050 |
| BF16 | 65,536 | 399,890 |
| E4M3FN | 256 | 14,132 |
| E5M2 | 256 | 13,956 |

Widening checks every small-format word. Narrowing checks every finite destination value, every midpoint between adjacent finite values, their immediate Float32 neighbours and the overflow threshold, with both signs, plus source-exponent and NaN-payload boundaries and 8,192 seeded random words per format, but not all $2^{32}$ source words.

Non-NaN results agree bit for bit, signed zeros and infinities included. All 2,423 differing words are NaN inputs where both results are NaNs. FloatLib keeps the sign and the payload bits that fit, as [its casts do](#/chapter/ieee-binary-formats/how-to-cast-between-widths), and TensorLib returns a canonical NaN, so the FP16 word `0x7c01` widens to `0x7fc00001` in FloatLib and `0x7fc00000` in TensorLib. We don't count that as a numerical error. Lean's `Float32.ofBits` canonicalizes NaNs before an encoding function sees them, which we tested separately, and TensorLib returns no status flags, so we claim nothing about signaling behavior or exception flags.

### Tools for error bounds and SMT

The third level bounds the error of a whole calculation, not of one operation. Say a program computes $t=\operatorname{RN}(xy)$ and then $r=\operatorname{RN}(t+z)$, where RN rounds to nearest. Bounding $|r-(xy+z)|$ over an input box takes another proof, since cancellation can make that bound very different from either call's relative error. VCFloat2, by Andrew W. Appel and Ariel E. Kellison, does this in Rocq on top of Flocq and the [Interval package](https://coqinterval.gitlabpages.inria.fr/) [@vcfloat2], and Gappa, by Marc Daumas and Guillaume Melquiond, certifies such bounds from interval reasoning and properties of rounded operators [@gappa]. FloatLib's [`roundoff` tactic](#/chapter/proving-numerical-bounds/how-to-get-an-error-bound-for-floating-point-code) proves an absolute or mixed error bound from each operation's rounding theorem, leaving the range conditions it can't prove as hypotheses. We haven't compared it with VCFloat2 or Gappa on common programs.

LeanCert automates interval and Taylor-model proofs of bounds, roots and integrals in Lean [@leanCert], and FloatLib's [interval tactic](#/chapter/proving-numerical-bounds) proves real inequalities from rational input bounds by evaluation and subdivision, and once the rounding steps are accounted for, it can finish the numerical subgoals of an error analysis.

The last neighbour comes at floating point from another direction, SMT solving. SymFPU builds SMT-LIB floating-point operations from bit-vector operations, for concrete evaluation or for formulas an SMT solver reads [@symfpu]. We haven't compared encoded operations with SymFPU or timed it.

## How to run the comparisons yourself

If you'd like to check our numbers yourself, every command for reproducing these comparisons is in the [external comparison guide](https://github.com/lean-dojo/FloatLib/blob/main/tests/EXTERNAL.md).
