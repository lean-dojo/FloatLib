---
number: "12"
slug: performance
title: "Arithmetic performance"
summary: "Compiled arithmetic from small formats to 4,096 bits, the kernels behind the timings, and results on independent benchmark suites."
phases: [kernels, backends, planner-and-configured, execution, trust]
---

We timed `x * y` on binary64 values on one pinned Xeon core. FloatLib took 11.2 ns per call and MPFR took 27.0 ns at the same precision and exponent range. MPFR was faster for binary64 division and square root, and for every operation we measured above 64 bits. These are compiled programs, with the proofs erased before execution [@leanReference]. For timings inside a proof, see [Speeding up computation in Lean's kernel](#/chapter/proof-by-computation).

<a id="timing-results"></a>

## Public binary operations

We compared addition, subtraction, multiplication, division, square root and fused multiply-add (FMA). Each trial used sixteen prepared input triples. Before timing them we checked the output encodings against MPFR with nearest-even rounding, matching exponent bounds and gradual underflow. [Figure 12.1](#/chapter/performance/figure-public-binary-performance) shows the median of nine trials and their full range. For example, binary64 multiplication and addition favored FloatLib by factors of 2.4 and about 1.5, respectively. At 256 bits MPFR was 45.8 times faster at addition.

![Six panels, one for each operation, each with a FloatLib line and an MPFR line against encoded width from 32 to 4,096 bits. FloatLib is at or below MPFR at 32 and 64 bits in most panels, climbs steeply between 128 and 256 bits, and stays above MPFR from there on](assets/public-binary-performance.png "Time per call of FloatLib's public binary operations and of MPFR 4.1.0 at the same precision and exponent bounds, from 32 to 4,096 bits. Markers are medians of nine trials in nanoseconds, and whiskers run from the fastest to the slowest trial, so they are not confidence intervals. Both axes are logarithmic, and lower is faster. Measured on 2026-10-31 on one pinned core of an Intel Xeon Platinum 8275CL with Lean 4.35.0.")

At smaller widths the layout matters. FloatLib was faster at five of six operations in binary16, bfloat16 and nine-bit E4M4. MPFR was faster at division in all three. At seven and eight bits, a square-root table did well, while several arithmetic operations were slower than their nine-bit counterparts. For FMA an exhaustive table needs three indices. It would take 16 MiB at eight bits, above the default 1 MiB limit, so FloatLib used the exact baseline. The other slowdowns at these widths haven't been isolated. [Figure 12.2](#/chapter/performance/figure-public-binary-low-precision) shows the results by operation.

![Six panels, one for each operation, with a FloatLib marker and an MPFR marker for each of six formats: E3M3, E4M3, E5M2, E4M4, binary16 and bfloat16. MPFR is between about 25 and 45 ns everywhere. FloatLib is below it for E4M4, binary16 and bfloat16 except in division, and far above it, at 120 to 1,200 ns, for the three smallest formats except in square root](assets/public-binary-low-precision.png "The same comparison below 32 bits: binary16, bfloat16 and four IEEE-style layouts, E3M3 with 7 bits, E4M3 and E5M2 with 8, and E4M4 with 9. Markers are medians of nine trials in nanoseconds, and whiskers run from the fastest to the slowest trial. The vertical axis is logarithmic, and lower is faster. Measured on 2026-10-31 on one pinned core of an Intel Xeon Platinum 8275CL with Lean 4.35.0.")

Across binary16, bfloat16, binary32 and binary64, FloatLib had the lower median in 17 of 24 pairs. Across all widths tested, from 7 through 4,096 bits, it had the lower median in 25 of 84. The [measurements and fixtures](#/chapter/performance/public-binary-measurement-record) include the individual trials.

## Comparisons with other libraries

### How does FloatLib compare with Flocq?

We extracted the arithmetic of Flocq 4.2.2 [@boldoMelquiond2011] into OCaml and compared it with FloatLib and MPFR on eleven matching binary formats. This loop calls FloatLib's configured word kernels directly at binary32 and binary64 and uses its throughput policy elsewhere. Each implementation allocates and exposes its result in its own representation. We checked the [values on common inputs](#/chapter/external-validation/how-floatlib-compares-with-flocq-and-mpfr) before timing.

FloatLib was faster than extracted Flocq in 65 of 66 entries, by a median factor of 52. Flocq was faster at eight-bit FMA. MPFR was fastest in every entry of this particular loop. [Figure 12.3](#/chapter/performance/figure-flocq-matched) gives the results from 6 to 4,096 bits. The [Flocq wrapper](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/rocq/FlocqKernel.v) and [experiment record](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/flocq-matched/README.md) specify the extracted operations and compilers.

![Six panels, one per arithmetic operation: time per operation against format width, both on logarithmic axes, with one line each for FloatLib, extracted Flocq and MPFR at eleven matching binary formats from 6 to 4,096 bits](assets/flocq-matched.png "Time of one arithmetic operation in FloatLib, in Flocq 4.2.2 extracted to OCaml and in MPFR, at eleven matching binary formats from 6 to 4,096 bits. A point is the median over nine trials of the time per operation in nanoseconds, with the precision and the exponent bounds matched across the three; square root at 1,024 bits and above is timed over complete blocks of sixteen inputs. Both axes are logarithmic, and lower is faster. Measured on 2026-10-31 on an Intel Xeon Platinum 8275CL with Lean 4.35.0.")

### How does FloatLib compare with FLoPS?

FLoPS [@flopsArtifact] implements P3109 arithmetic in Lean. The two libraries agreed bit for bit in [529,152 arithmetic cases](#/chapter/external-validation/how-floatlib-compares-with-flops) with nearest-even rounding and no saturation. We then timed add, multiply, divide and FMA on `Binary4p2sf`, `Binary8p4se` and `Binary8p3se`. Each operation depended on the previous result. FloatLib had the lower median in 11 of 12 pairs. For example, `Binary8p4se` division took 4.52 µs against 7.25 µs, while four-bit FMA took 5.38 µs against 5.22 µs. Each library used its own pinned Lean and Clang toolchains. [All twelve timing pairs](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/p3109-flops/results.json).

### How fast are conversions between formats?

TensorLib [@tensorLib] specializes conversions to and from `Float32`. FloatLib's `Model.cast` accepts the format as a parameter, decodes its input exactly and rounds to the destination format. On sixteen normal inputs in each direction, TensorLib was faster in all eight comparisons across FP16, BF16, E4M3 and E5M2. For FP16, encoding took 282 ns in TensorLib and 2,035 ns in FloatLib. Decoding took 273 ns and 2,103 ns, respectively. All 128 timing fixtures agreed bit for bit. The [timing record](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/tensorlib/results.json) and [conversion checks](#/chapter/external-validation/how-floatlib-compares-with-tensorlib) cover the duration and the results separately.

### Host arithmetic as a reference

We compared six operations at widths up to 4,096 bits. Each result selects the next input, so the timings include that lookup. At 32 and 64 bits we called FloatLib's fixed-word kernels directly. [Figure 12.4](#/chapter/performance/figure-compiled-precision) also shows the public interface at those widths. We timed those calls separately, cycling through 16 inputs in a fixed order. Binary32 multiplication took 97.2 ns in the first loop and 20.7 ns in the second.

![Six panels of lines, one per arithmetic operation: compiled time per operation against format width for FloatLib and MPFR up to 4,096 bits, with SoftFloat, the host processor and FloatLib's public calls as short series at 32 and 64 bits, where the public calls lie below the FloatLib line in every panel.](assets/compiled-precision.png "Time per operation against format width, both on logarithmic scales. In the comparison with MPFR, SoftFloat and the host processor, each result selects the next input. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20). The open circles show public FloatLib calls at 32 and 64 bits, timed on a fixed cycle of inputs (median of nine trials on one pinned core, Lean 4.35.0, 2026-10-31).")

| Binary64 implementation | Multiply (ns) | Divide (ns) | Square root (ns) |
| --- | ---: | ---: | ---: |
| FloatLib, named word kernel | 321.9 | 398.3 | 162.5 |
| Berkeley SoftFloat | 17.7 | 33.5 | 27.5 |
| MPFR | 32.3 | 35.3 | 44.3 |
| Native C | 8.3 | 11.5 | 12.6 |

Berkeley SoftFloat was about 3 to 18 times faster than FloatLib's named kernels across all six binary32 and binary64 operations. The native C rows measure the processor's `float` and `double` arithmetic. Lean's wrappers and FloatLib's optional `NativeFPU.Unchecked` calls were outside this experiment. The [backend comparison](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/backends/README.md) includes all six operations and the rational inputs.

The same harness timed FloatLib's posit operations. At eight bits, addition, subtraction, multiplication and division took 21 to 24 ns using exhaustive tables. FMA took 121 ns. At 4,096 bits, addition took 6.3 µs and division 12.0 µs. Our [SoftPosit comparison](#/chapter/external-validation/why-did-softposit-disagree-with-floatlib) checked result bits. It supplies no comparative speed measurement.

## How the planner selects a kernel

An eight-bit value has 256 encodings. To add two of them, FloatLib can compute the result or read it from a 65,536-entry byte table. Filling the table makes the first call more expensive, so the choice depends on how many calls you expect to make.

Each candidate supplies an executable function and a proof that the function implements the specification. The planner starts from the exact baseline, filters alternatives by their estimated memory requirements and minimizes `expectedCalls × warmCost + coldCost`. For IEEE E4M3 addition, the default policy expects 100,000 calls and picks the word kernel. The throughput policy expects five million and picks the table. The bars in [Figure 12.5](#/chapter/performance/figure-ch09-backend-ladder) show the planner's own cost units. Actual elapsed times depend on the machine. [Selection policy](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/Selection/Policy.lean) · [Scoring rules](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/Selection/Scoring.lean).

![Three horizontal bars of estimated cost: the word kernel at 1,500,000, drawn solid as the selected one, the table at 1,742,848 and the baseline at 2,100,000, both hatched](assets/ch09-backend-ladder.png "The planner's estimated cost of three implementations of E4M3 addition with UInt8 storage, under the default policy of 100,000 expected calls. An estimate is 100,000 warm costs plus one cold cost, in the planner's own units and not a measured time. The 64 KiB table fits the 1 MiB limit, so the table and the word kernel are eligible beside the baseline, and the planner selects the lowest estimate. Every candidate is already proved equal to the specification.")

To look up the selected implementation, use the format's family and the operation you want.

```lean
open FloatLib.Floats

#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.nativeWord

section
open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.exhaustiveTable
end
```

The `PlanningLatency` scope favors a single call. A local [[FloatLib.Floats.ExecFloat.Backend.PolicyFor]] instance sets a custom workload and memory budget. The baseline remains available if every alternative is ineligible. [[FloatLib.Floats.ExecFloat.Backend.selectCertified_run_eq_spec]] proves that whichever candidate wins implements the same operation. [Chapter 3](#/chapter/the-numerical-models/how-do-we-know-the-fast-code-is-right) follows the public addition call through its refinement proof.

| Representation | Available implementations |
| --- | --- |
| Byte, at most eight encoded bits | Exhaustive value tables where the policy can accommodate them |
| IEEE layout fitting in 64 bits | Word kernels subject to operation-specific bounds, with dedicated software kernels for binary32 and binary64 |
| IEEE layout with more than 64 fraction bits and at most 128 encoded bits | Two-word kernels |
| IEEE layout above 128 bits, with at most 32 exponent bits and limb storage | Wide-limb kernels |
| Every descriptor | Exact baseline, including fallback for inputs a specialized kernel declines |

Different representations of the same format can have different costs. For the 256-bit IEEE format with 19 exponent bits and 236 fraction bits, the default carrier uses the baseline. `ExecFloat.BinaryLimbs (exponentBits := 19) (fractionBits := 236)` keeps the value in an array of 32-bit words between operations and makes the wide-limb kernels available. Both carriers implement the same format and rounding rules.

### Division, rounding and limb arithmetic

For a small example of a word kernel, start the division of 4 by 3 with quotient 1 and remainder 1. Double the remainder and compare it with 3. A remainder smaller than 3 gives the next bit 0. Otherwise subtract 3 and append 1. After four steps the quotient is 21 and the remainder is 1, satisfying $21 \cdot 3 + 1 = 4 \cdot 2^4$. [Figure 12.6](#/chapter/performance/figure-ch08-restoring-division) shows the four steps. The [division proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Quotient/Proof.lean) establishes this relation for any number of steps.

![A table with a row for the start and a row for each of four steps. Each step draws twice the remainder as a bar against a line at the divisor 3. In steps 1 and 3 the bar, 2, stays short of the line and the bit is 0. In steps 2 and 4 the bar, 4, passes the line, the divisor is subtracted and the bit is 1. The quotient goes from 1 to 2, 5, 10 and 21, and the remainder alternates between 2 and 1](assets/ch08-restoring-division.png "Restoring division of 4 by 3, one quotient bit for each step. It starts from 4 = 1 × 3 + 1, so q = 1 and r = 1. A step doubles r and compares it with 3: it keeps 2r and appends 0, or subtracts 3 and appends 1, so that q × 3 + r = 4 × 2^n and 0 ≤ r < 3 hold after n steps. After four steps, 21 × 3 + 1 = 64.")

The checked division kernel can instead propose a quotient using Knuth's Algorithm D [@knuth1997]. Multiplying back and checking the remainder proves whether the candidate is correct. Failure sends the input to restoring division. [[FloatLib.Numerics.FixedWord.CertifiedDivision.certificate_sound]] proves the check is sufficient. The [binary64 square-root kernel](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Compiled/Word/Full/Sqrt/Runtime.lean) likewise checks a fast guess exactly before accepting it.

Rounding to nearest even after a right shift needs three bits of information. The highest discarded bit says whether we have reached halfway. A sticky bit records whether any lower discarded bit was set. At an exact tie the lowest retained bit decides which neighbor is even. [[FloatLib.Numerics.roundShiftRightEven_eq_guard_sticky]] proves this rule. When exponents differ greatly, [bounded alignment](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/ShiftRightJam/Proof.lean) preserves the final rounding while discarding low bits early.

A limb array stores an integer in base $2^{32}$, lowest digit first. Adding one to $2^{96}-1$ sends a carry through three full limbs and produces `[0, 0, 0, 1]`, as [Figure 12.7](#/chapter/performance/figure-ch08-limb-arrays) shows. Multiplication also fits a limb product, an accumulated digit and a carry in one 64-bit word, since $(2^{32}-1)^2+2(2^{32}-1)=2^{64}-1$. The [limb implementation and proofs](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels/LimbArray) relate these operations to arithmetic on natural numbers.

![Four boxes in a row, limb 0 to limb 3, joined by arrows labelled carry 1. In each of the first three, (B − 1) + 1 = B and the limb stores 0. Limb 3 holds 1](assets/ch08-limb-arrays.png "Adding 1 to 2^96 − 1, stored as three limbs in base B = 2^32 with the lowest limb first. Every limb holds B − 1, so every sum is B: the limb stores 0 and passes a carry of 1 to the next. The last carry fills the extra limb that addition reserves, and the result [0, 0, 0, 1] is B^3 = 2^96.")

## Independent benchmark suites

### FPBench roundoff bounds

[FPBench](https://fpbench.org) supplies 136 programs in twelve suites. Running each in binary32 and binary64 gave 272 cases. The translator handled 188, with loops, tensors and unsupported operators accounting for the remaining 84. On the translated cases, `roundoff` proved 184 conditional forward bounds, 180 conditional closed forms and 22 conditional backward bounds within 60 seconds each. It discharged the range and no-overflow premises to produce numerical results for 33 forward bounds and 18 closed forms.

[Figure 12.8](#/chapter/performance/figure-suites-fpbench) also compares bound sizes where both tools returned a number. For 15 of 23 common FPTaylor cases, FloatLib's bound was 2.1 to 3.2 times as large. The other eight had larger ratios. For 14 common Gappa cases the ratios ranged from 1.04 to 1.94.

![Two panels. Left: five stacked horizontal bars, one per kind of theorem, split into programs proved, not proved and not translated. Right: three rows of dots on a logarithmic axis, one dot per program for the ratio of FloatLib's bound to another tool's, with a tick at the median of a row that has three ratios or more, and a vertical line at ratio one.](assets/suites-fpbench.png "FPBench: what FloatLib's roundoff tactic proves, and its proved bounds against FPTaylor and Gappa. Panel (a) counts the 136 programs of twelve FPBench suite files, each in binary32 and in binary64, by outcome for each kind of theorem; panel (b) is FloatLib's proved numerical bound divided by the other tool's bound on the same program, on a logarithmic axis where 1 is equal and above 1 is looser. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20).")

### Real inequalities

The [MetiTarski](https://bitbucket.org/lcpaulson/metitarski-git/) collection has 948 inequalities and [Flyspeck](https://github.com/flyspeck/flyspeck) supplied 164 records. The translator handled 798 and 20, respectively. With twenty seconds per goal, `interval` alone closed 124 MetiTarski and three Flyspeck goals. Enabling the constraint engine closed 340 and six, every goal of the first route among them. With the constraint engine 64 MetiTarski goals ran out of time, and none without it. [Figure 12.9](#/chapter/performance/figure-suites-inequalities) gives the outcomes and times.

![Two panels with the same four rows, MetiTarski and Flyspeck each with interval alone and with the constraint engine. Left: stacked horizontal bars of goals proved, not proved and not translated. Right: one dot per proved goal on a logarithmic time axis, with a tick at the median of a row that has three goals or more.](assets/suites-inequalities.png "MetiTarski and Flyspeck inequalities given to FloatLib's interval tactic, alone and with the constraint engine. Panel (a) counts the goals by outcome (948 MetiTarski goals and 164 Flyspeck records, one tactic call each); panel (b) is the time Lean took to elaborate each proved goal, without the imports of its file, on a logarithmic axis where lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20).")

Four smaller test collections written for FloatLib, Mathlib, SymLean and the IEANTN examples supplied another 169 goals. In a single tactic call per goal, `interval` closed 161. [Figure 12.10](#/chapter/performance/figure-interval-corpora) shows the outcomes for three tactics. [Chapter 11](#/chapter/proving-numerical-bounds/how-much-does-interval-prove-on-other-projects-goals) describes the goals in each corpus.

![Four groups of three horizontal bars, one group per test corpus and one bar per tactic, on an axis from 0 to 100 percent; each bar ends in its count of closed goals out of the goals of the corpus.](assets/interval-corpora.png "Goals closed on four test corpora (169 goals) by FloatLib's interval tactic, by Mathlib's dyadic_interval and by SymLean's cega. A bar is the share of a corpus that one tactic call per goal closes, with the count at its end; a count says what a tactic did on that corpus, not what it does on all goals. Recorded on 2026-11-16 with Lean 4.35.0, and not run again by the timing mode.")

### Correct rounding on hard inputs

The hard cases for functions such as `exp` and `log` lie close to a rounding boundary. We tested `exp`, `expm1`, `log` and `log1p` on 107,215 published binary32 and binary64 cases. FloatLib matched MPFR on all 107,199 representable real cases. For complex inputs of the form $x+i x$, all 214,396 compared components matched GNU MPC. The [case record](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/suites/correct-rounding.csv) lists excluded inputs. Median real-call times across the experiments were 70 to 155 µs for FloatLib, 1.5 to 6.4 µs for MPFR and under 0.4 µs for CORE-MATH. [Figure 12.11](#/chapter/performance/figure-suites-hard-cases) breaks these out by function, format and input source.

![Two panels with the same 24 rows, one per function, format and source of inputs. Left: horizontal bars of the number of inputs whose result equals the reference. Right: the median time per call on a logarithmic axis, a filled circle for FloatLib, a diamond for MPFR and a grey cross for CORE-MATH; the complex rows have the FloatLib mark only.](assets/suites-hard-cases.png "Hard-to-round inputs of exp, expm1, log and log1p: the results of FloatLib against MPFR, CORE-MATH and GNU MPC, and the time per call. Panel (a) counts the inputs whose result word from FloatLib equals the reference (107,199 real results and 214,396 parts of complex results, a complex input counting once per part); panel (b) is the median time of one compiled call, on a logarithmic axis where lower is faster. These are tests on listed inputs, not proofs. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-17).")

A separate sweep measured 34 real and 18 complex correctly rounded functions at widths up to 4,096 bits. The binary64 real functions took 0.04 to 11 ms per call, with a median across functions of about 0.7 ms. At 4,096 bits the range was 3 ms to 94 seconds, with a median of 19 seconds. [Figure 12.12](#/chapter/performance/figure-correctly-rounded) shows how the individual functions scale. The [elementary functions chapter](#/chapter/elementary-functions) describes their evaluation and rounding guarantees.

![Two panels of lines, real functions and complex functions: compiled time per call against format width, with one thin line per function and a thick line with markers for their median.](assets/correctly-rounded.png "Compiled time of one call of each correctly rounded function of FloatLib by format width: 34 real functions and 18 complex functions. A thin line is one function, rounded to nearest even, and the thick line is the median over the functions. Both axes are logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20); the complex times were recorded on 2026-11-16 with Lean 4.35.0.")

### IEEE operations and status flags

[Berkeley TestFloat](https://github.com/ucb-bar/berkeley-testfloat-3) exercised arithmetic and comparisons in binary16, binary32, binary64 and binary128, and conversions between formats, including bfloat16 and binary32. The matrix used five rounding modes where the operation depends on the mode. Across 210 level-1 campaigns, every one of the 127,741,704 vectors matched in both value and status flags. FMA accounted for 122,664,960 of those vectors. [Figure 12.13](#/chapter/performance/figure-suites-testfloat) gives the distribution by format. The [validation chapter](#/chapter/external-validation) describes how the reference comparisons handle exceptional values.

![Two panels of horizontal bars with one row per format (binary16, binary32, binary64, binary128, bfloat16). Left: the number of TestFloat campaigns, all in the colour of a campaign in which every vector matches. Right: the number of vectors checked, in millions.](assets/suites-testfloat.png "Berkeley TestFloat, level 1: the campaigns FloatLib matches and the vectors they check, by format. Panel (a) counts the 210 campaigns, one per operation and rounding direction in each format, of which 210 match on every vector in value and in status flags; panel (b) is the number of vectors of those campaigns, 127,741,704 in all with 0 mismatches. A finite campaign is not a proof. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-17).")

## Reproducing the measurements

<a id="public-binary-measurement-record"></a>

The public-call run used one pinned core of a Xeon Platinum 8275CL with Lean 4.35.0, MPFR 4.1.0-p13 and GMP 6.2.1. The [trial data](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/public-binary/measurements.csv), [build metadata](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/public-binary/metadata.json), [input fixtures](assets/public-binary-fixtures.zip) and [benchmark bundle](assets/public-binary-benchmark.tar.gz) are available for repeating that comparison.

The SoftFloat, MPFR and native C comparison used Lean 4.36.0 on the same model of processor, with one calibrated timing interval per cell. The [benchmark method](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/docs/Comparison.md) documents the adapters, result-dependent loops and compiler options. The [figure index](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/FIGURES.md) identifies the source data behind each plot.

To rerun the four standard suites from a checkout, use the command below. The [suite results](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/suites/README.md) record per-case outcomes, time and memory limits, and the external tool versions.

```sh
bash benchmarks/suites/run.sh fpbench inequalities correct-rounding testfloat
```
