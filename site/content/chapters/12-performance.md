---
number: "12"
slug: performance
title: "How fast is FloatLib, and why"
summary: "How fast FloatLib's proved arithmetic runs next to MPFR, SoftFloat, Flocq and other libraries, how it picks the code that runs for your format, and why a bad pick can only cost speed."
phases: [kernels, backends, planner-and-configured, execution, trust]
---

This chapter compares the performance of FloatLib's public arithmetic operations with other implementations and explains how its planner selects a backend. In the public-call benchmark, binary64 multiplication takes 11.2 nanoseconds (ns) in FloatLib and 27.0 ns in MPFR at the same precision and exponent range, a factor of about 2.4. The sections below describe the measured workloads, the faster and slower cases, and the limits of these comparisons.

## How fast is FloatLib?

Across binary16, bfloat16, binary32 and binary64, FloatLib has lower measured times than MPFR in 17 of the 24 format-operation pairs. Binary64 addition and subtraction are about 1.5 times faster. The comparisons with other proved implementations show lower times than extracted Flocq in 65 of 66 entries, by a median factor of 52, and lower times than FLoPS in 11 of 12 P3109 pairs.

Across all 84 public-call pairs, from 7 to 4,096 bits, FloatLib is faster than MPFR in 25. MPFR is faster in every measured pair above 64 bits. Berkeley SoftFloat, a C library of software IEEE arithmetic, was 2 to 6 times faster on all six operations in the October binary128 benchmark. TensorLib, a Lean tensor library, was faster in all eight measured conversions. The following sections examine the implementation costs behind these results.

We measured the FloatLib 2.0.0 release on 2026-10-31, on an Intel Xeon Platinum 8275CL. We haven't timed 3.0.0 itself, but comparing the code Lean generates for the two releases shows the same arithmetic on every path we time against MPFR, Flocq, SoftFloat, Universal, FLoPS and TensorLib. None of the times includes proof checking, because Lean erases proof terms during compilation [@leanReference].

<a id="timing-results"></a>

## How fast are the calls you write yourself?

These are calls like `x * y` on two `Binary64` values, timed against MPFR with the same precision, exponent bounds, nearest-even rounding and gradual underflow. The whiskers span the fastest and slowest of nine trials, so small gaps between markers don't tell you much, and each reported ratio is the median of the nine within-trial ratios.

| Campaign | Public calls against MPFR |
| --- | --- |
| Machine | one pinned CPU of an Intel Xeon Platinum 8275CL, shared with other work |
| Timed calls | FloatLib's public binary operations, and MPFR 4.1.0-p13 with the same precision and exponent bounds |
| Inputs | sixteen prepared input triples per point, full encodings checked before timing |
| Statistic | median of nine trials, whiskers at the observed minimum and maximum |
| Recorded | 2026-10-31, on the 2.0.0 release |
| Record | [measurements, metadata, and fixtures](#/chapter/performance/public-binary-measurement-record) |

![FloatLib and MPFR for six public binary operations at encoded widths 32 through 4096](assets/public-binary-performance.png "Median nanoseconds per operation across nine trials, with whiskers at the observed minimum and maximum, which aren't confidence intervals. Both axes are logarithmic, and lower is faster.")

In [Figure 12.1](#/chapter/performance/figure-public-binary-performance), at 32 and 64 bits, FloatLib's marker sits below MPFR's in most panels. At binary32, multiplication, square root and fused multiply-add (FMA, $x \cdot y + z$ with one rounding) won, and addition lost narrowly. MPFR won division at both widths and binary64 square root and FMA. From 256 bits up, where every operation runs the exact baseline (FloatLib's general fallback that computes with arbitrary-precision integers), MPFR pulls furthest ahead, 45.8 times for 256-bit addition.

![FloatLib and MPFR for six public binary operations below 32 bits](assets/public-binary-low-precision.png "Median nanoseconds per operation across nine trials, with whiskers at the observed minimum and maximum. The vertical axis is logarithmic, and lower is faster.")

Below 32 bits, [Figure 12.2](#/chapter/performance/figure-public-binary-low-precision) adds binary16, bfloat16 and four IEEE-style layouts from 7 to 9 bits. This is FloatLib's best stretch: in binary16, bfloat16 and the 9-bit E4M4 layout (four exponent and four fraction bits) it beat MPFR in every operation but division, and binary16 multiplication was about 2.3 times faster.

The 7-bit and 8-bit formats behave oddly. Square root reads an exhaustive table, one stored answer per input, and edged out MPFR, but addition, subtraction, multiplication and division took 122 to 618 ns, the slowest points in the figure, against MPFR's 23 to 33 ns and 11 to 54 ns for the 9-bit layout's native-word kernels. (A *kernel* is a specialized integer routine for one operation, here one that keeps every field in a machine word.) These layouts store each value in one byte instead of a 16-bit word, but we haven't pinned down what causes the gap. FMA would need a 2 MiB table at 7 bits and 16 MiB at 8, over the planner's default 1 MiB limit, so it runs the exact baseline at about 1.2 µs (a µs is a thousand ns).

<details>
<summary>The public operation and its theorem</summary>

### Is the timed code the proved code?

Yes. `sum64` below is ordinary binary64 addition, the call we time, and `ExecFloat.Proof.add_eq_spec` says this very expression returns the result `ExecFloat.Spec.add` specifies for every pair of inputs, rounding included.

```lean
open FloatLib.Floats

def sum64 (x y : Binary64) : Binary64 := x + y

example (x y : Binary64) : sum64 x y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y

#eval sum64 1 2
-- 3
```

</details>

## What made FloatLib faster in October 2026?

The 2.0.0 code includes three changes from October 2026. About 95% of each binary128 operation had gone into splitting and joining GMP numbers (big integers), so we stored binary128 as two native words with kernels of its own. We specialized the operations that run on the general format model to their format. And we cached the constants of elementary functions such as sine, which had been regenerated on every call.

| Campaign | October 2026 before-and-after timings |
| --- | --- |
| Machine | Intel Xeon Platinum 8275CL |
| Timed rows | binary128 arithmetic, binary64 model-path operations, and sine |
| Inputs | 100,000 mixed operands for binary128 arithmetic, with a separate set for square root, and benchmark cells for the other rows |
| Statistic | best of several rounds for binary128 arithmetic, minimum of interleaved before-and-after rounds for the other rows |
| Compare with | each row's own before time, not the public-call figures |

| Operation | Change | Before | After |
| --- | --- | ---: | ---: |
| binary128 `add` | two-word storage and kernels | 2,161 ns | 107 ns |
| binary128 `sub` | two-word storage and kernels | 2,234 ns | 110 ns |
| binary128 `mul` | two-word storage and kernels | 927 ns | 48 ns |
| binary128 `div` | two-word storage and kernels | 1,812 ns | 209 ns |
| binary128 `sqrt` | two-word storage and kernels | 1,649 ns | 223 ns |
| binary128 `fma` | two-word storage and kernels | 2,631 ns | 154 ns |
| binary64 `roundToIntegral` | specialized model path | 3,691 ns | 838 ns |
| binary64 `scale` (scaleB) | specialized model path | 3,781 ns | 814 ns |
| binary64 `binaryExponent` (logB) | specialized model path | 4,141 ns | 981 ns |
| binary64 `parse` | specialized model path | 10,954 ns | 7,061 ns |
| binary64 `sqrt (status := true)` | specialized model path | 1,964 ns | 824 ns |
| binary64 `sin` | cached constants | 658 µs | 43 µs |
| binary64 `sin` | Payne-Hanek reduction | 29.4 µs | 20.7 µs |
| binary128 `sin` | cached constants | 6.2 ms | 140 µs |
| binary128 `sin` | Payne-Hanek reduction | 72.6 µs | 33.8 µs |

SoftFloat stayed ahead at binary128 even so. The model-path rows gain from format specialization, from value-only calls that skip the status flags and MPFR's ternary value (its report of whether a result was rounded down, up or not at all), and from one comparison per rounding for both the ternary value and the inexact flag.

## How does FloatLib compare with other proved libraries?

### How does FloatLib compare with Flocq?

Flocq is a proved floating-point library for the Coq proof assistant [@boldoMelquiond2011], whose operations can be extracted into a runnable program. We timed that program, extracted with Coq 8.20.1 and compiled with OCaml 4.13.1 and Zarith, with allocation and observing the result included, and MPFR at matching formats, after [numerical checks](#/chapter/external-validation/how-floatlib-compares-with-flocq-and-mpfr) compared complete values on the same rational inputs. On the FloatLib side the loop calls word kernels by name at binary32/64 and public operations under `PlanningThroughput` elsewhere.

![FloatLib, extracted Flocq, and MPFR across eleven matching binary formats and six operations](assets/flocq-matched.png "Median nanoseconds per operation across nine trials at matching binary precision and exponent bounds. Both axes are logarithmic, and lower is faster. Measurements ran on an Intel Xeon Platinum 8275CL.")

FloatLib beat extracted Flocq in 65 of the 66 entries of [Figure 12.3](#/chapter/performance/figure-flocq-matched), from 6 to 4,096 bits, by a median factor of 52. The one loss, 8-bit FMA, runs the exact baseline for lack of a table. MPFR was faster than FloatLib at every point, by a median factor of 6.3.

<details>
<summary>Extraction, inputs, and the timed Flocq loop</summary>

### Which Flocq program did we time?

Our [Flocq wrapper](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/rocq/FlocqKernel.v) runs the `IEEE754.BinarySingleNaN` operations of Flocq 4.2.2. Flocq requires `0 < precision < emax`, which rules out the custom 4-, 5- and 7-bit layouts. The [result README](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/flocq-matched/README.md) has the data, environment details and commands.

</details>

### How does FloatLib compare with FLoPS?

FLoPS is another executable Lean implementation with refinement proofs [@flopsArtifact], proofs that its running code matches its specification, so this race is Lean against Lean. With nearest-even rounding and no saturation, all 529,152 arithmetic cases in three machine-learning formats of the IEEE P3109 working group and the 192 timing fixtures agreed bit for bit ([input coverage](#/chapter/external-validation/how-floatlib-compares-with-flops)). The [experiment](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/p3109-flops/results.json) reports median microseconds over nine pairs of fresh processes running a dependent loop, each operation waiting for the one before.

| Format | Implementation | Add | Multiply | Divide | FMA |
| --- | --- | ---: | ---: | ---: | ---: |
| Binary4p2sf | FloatLib | 3.93 | 4.00 | 3.96 | 5.38 |
| Binary4p2sf | FLoPS | 4.29 | 4.24 | 5.77 | 5.22 |
| Binary8p4se | FloatLib | 4.44 | 4.49 | 4.52 | 6.03 |
| Binary8p4se | FLoPS | 5.59 | 5.53 | 7.25 | 6.68 |
| Binary8p3se | FloatLib | 4.37 | 4.54 | 4.49 | 5.84 |
| Binary8p3se | FLoPS | 5.46 | 5.33 | 7.12 | 6.51 |

FloatLib had the lower median in 11 of the 12 pairs. The one loss, four-bit FMA, is as consistent as the wins, since no pair's 5th to 95th percentile ranges overlap. Neither library uses the processor's floating-point unit (FPU) here, and each was built with its own pinned Lean and Clang, so the times include compiler effects.

## How fast are conversions between formats?

Conversion is a plain loss for us. We timed TensorLib's specialized `Float32` conversions [@tensorLib] against FloatLib's general `Model.cast` on four formats, after all 128 timing fixtures agreed exactly ([broader conversion checks](#/chapter/external-validation/how-floatlib-compares-with-tensorlib) cover rounding boundaries and exceptional values). The [results](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/tensorlib/results.json) are median nanoseconds over nine paired trials of a dependent loop on sixteen normal inputs, where “encode” converts Float32 to the small format and “decode” converts back.

| Format | FloatLib encode | TensorLib encode | FloatLib decode | TensorLib decode |
| --- | ---: | ---: | ---: | ---: |
| FP16 | 2,034.5 | 281.8 | 2,103.4 | 272.9 |
| BF16 | 2,033.1 | 268.9 | 1,087.8 | 274.4 |
| E4M3FN | 3,555.5 | 284.2 | 2,226.7 | 278.2 |
| E5M2 | 2,075.1 | 282.6 | 2,106.9 | 276.2 |

TensorLib was faster in all eight, a specialist against a generalist: it works on the fixed-format fields directly, while FloatLib's cast takes the format as a parameter, decodes the value exactly and then rounds. On these normal inputs TensorLib's casts use integer shifts, masks and rounding, so the speedup isn't evidence of an FPU advantage. Its FP16 and FP8 subnormal decoders do use `Float32` multiplication, outside this timed workload. Its tensor arithmetic does use native operations, as [the validation chapter](#/chapter/external-validation/how-floatlib-compares-with-tensorlib) explains, and converting many independent elements in a tensor kernel would be a different workload.

## How does FloatLib compare with SoftFloat, MPFR and native C?

Our biggest comparison, the nine-trial software comparison, runs FloatLib, SoftFloat, MPFR, native C (the processor's own arithmetic, called from C), CPython (the standard Python interpreter) and Universal (Stillwater's software posit library) through one dependent loop. One catch: this loop calls FloatLib the way the Flocq loop does, while public binary64 calls try direct word kernels first, so binary32 multiplication took 100.6 ns here against 20.7 ns in the public calls. For binary32 and binary64 speed, read the public-call figures.

| Campaign | Nine-trial software comparison |
| --- | --- |
| Machine | one logical CPU of an Intel Xeon Platinum 8275CL, shared with other work |
| Timed calls | FloatLib's configured word kernels by name at binary32/64 and public operations at other widths, against SoftFloat, MPFR, native C, CPython, and Universal |
| Inputs | sixteen rational input sets, each result choosing the next set |
| Statistic | median of nine trials, bands at the 5th and 95th percentiles |
| Recorded | 2026-10-31, on the 2.0.0 release |
| Record | [results](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/main/README.md) |

### Binary32

Binary32 is a clean loss here: SoftFloat, MPFR and native C each beat FloatLib's named word kernels on all six operations. Times are median ns per operation.

| Implementation | Add | Subtract | Multiply | Divide | Square root | FMA |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| FloatLib | 162.2 | 143.0 | 100.6 | 150.3 | 87.2 | 150.6 |
| Berkeley SoftFloat | 23.0 | 22.8 | 17.6 | 25.1 | 25.7 | 27.0 |
| MPFR | 34.0 | 35.7 | 34.9 | 36.5 | 40.9 | 55.5 |
| Native C | 8.5 | 8.5 | 8.5 | 10.4 | 10.6 | 8.8 |

### Binary64

At binary64 FloatLib beat CPython on all five operations it provides, though Python's timings include its runtime, and the version we measured has no `math.fma`.

| Implementation | Add | Subtract | Multiply | Divide | Square root | FMA |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| FloatLib | 389.4 | 346.3 | 332.3 | 400.3 | 167.1 | 494.5 |
| Berkeley SoftFloat | 22.1 | 21.6 | 17.8 | 33.5 | 27.6 | 27.2 |
| MPFR | 37.4 | 36.2 | 32.6 | 34.3 | 46.0 | 60.6 |
| Native C | 8.3 | 8.3 | 8.4 | 11.3 | 12.5 | 8.6 |
| CPython | 1,493.5 | 1,503.9 | 1,482.8 | 1,728.6 | 1,493.0 | n/a |

### Posits

Posits, a format whose precision varies with the size of the value, go much better against Universal (a different library from SoftPosit). FloatLib won all five operations at 32 and 64 bits and 56 of the 65 cells overall, and from 5 to 8 bits its exhaustive tables ran 1.9 to 4.8 times faster for every operation but FMA.

| Width | Implementation | Add | Subtract | Multiply | Divide | FMA |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| 32 | FloatLib | 121.3 | 152.4 | 114.7 | 274.7 | 141.6 |
| 32 | Universal | 289.7 | 298.6 | 331.4 | 629.5 | 473.0 |
| 64 | FloatLib | 123.5 | 126.9 | 162.8 | 362.3 | 244.2 |
| 64 | Universal | 633.4 | 905.4 | 842.7 | 2,010.8 | 1,154.1 |
| 4,096 | FloatLib | 6,341.8 | 5,953.6 | 8,086.1 | 12,165.1 | 10,024.4 |
| 4,096 | Universal | 41,296.8 | 42,112.2 | 985,340.8 | 13,222,078.2 | 1,052,650.8 |

Universal won the other nine: FMA at 5 to 8 bits, where the planner's cost estimate chose packed-word fused accumulation over three-input tables, 256-bit addition and subtraction and 512-bit addition, where FloatLib's exact sum took 4.4 to 5.4 µs, and 16-bit division and 128-bit FMA. Its square root, which goes through binary64 and the host square root and so has its own series in the plot, won at 16 and 32 bits.

<a id="comparing-with-leans-native-floats"></a>

### Host arithmetic as a reference

The native C column is the processor's own `float` and `double` arithmetic, measured from C, and FloatLib's named word kernels are 8.2 to 57.2 times slower, as [Figure 12.9](#/chapter/performance/figure-ch17-host-vs-software) labels. We haven't timed Lean's `Float32` and `Float` wrappers or FloatLib's `NativeFPU.Unchecked` functions, whose guards and bit conversions add work of their own.

## More views of the nine-trial comparison

<details>
<summary>Overview, ratios, small formats, wide operations, and host comparison</summary>

### Overview across encoded widths

A missing marker in [Figure 12.4](#/chapter/performance/figure-format-comparison-main) means the comparison was unavailable or excluded, and the [validation chapter](#/chapter/external-validation/why-are-some-posit-timings-missing) says why.

![Six arithmetic operations across encoded widths from 2 to 4,096 bits, as median nanoseconds per operation with 5th to 95th percentile bands](assets/format-comparison-main.png "Median nanoseconds per operation across encoded widths, with 5th to 95th percentile bands. Both axes are logarithmic, and lower is faster. Missing markers denote unavailable or excluded comparisons.")

### How to read a time ratio

The ratios below compare formats of the same width, and equal encoded width means equal storage and nothing more. A binary format has a fixed precision, a posit's precision varies with its value, and MPFR uses the precision of the binary companion, the binary format with the same storage, so equal width doesn't imply equal accuracy or range.

![FloatLib time divided by the external implementation's time for addition, multiplication, and division, at equal encoded widths](assets/ch10-external-ratios.png "FloatLib time divided by the comparison library’s time at equal encoded width. Lower is faster for FloatLib relative to that library, and 1 means equal times. Different formats have different numerical contracts.")

[Figure 12.5](#/chapter/performance/figure-ch10-external-ratios) divides FloatLib's time by the other library's, so 1 means equal median time. Each ratio compares whole loops with different algorithms, representations and adapters, so none of them isolates a cost that comes from verification.

### Why can a wider format be faster?

![All six operations from 2 to 16 bits, with each measured width labelled, including 5, 6, and 7 bits](assets/format-comparison-low-width.png "Median nanoseconds per operation at widths 2 to 16, with percentile bands and logarithmic axes. Lower is faster, and only measured widths have markers.")

In this loop binary addition took 389.4 ns at 64 bits but 83.4 ns at 128, where the planner selects the two-word kernels and the loop reads the low word, while 64 bits takes the named-kernel path with its normalization. Timing alone can't separate the costs of dispatch (choosing which code runs), arithmetic and representation. [Figure 12.6](#/chapter/performance/figure-format-comparison-low-width) zooms in on the left edge.

### Multiplication, fused operations, and wide arithmetic

![Multiplication and fused multiply-add, with median ns/op and percentile bands across encoded widths](assets/format-comparison-mul-fma.png "Multiplication and fused multiply-add timings across encoded widths. Both axes are logarithmic, bands show the 5th to 95th percentiles, and lower is faster.")

FMA rounds once, so its intermediate product can be wider than a multiplication's rounded result. Watch how that plays out in [Figure 12.7](#/chapter/performance/figure-format-comparison-mul-fma) as the width grows.

![Division and square root, with median ns/op and percentile bands across encoded widths](assets/format-comparison-div-sqrt.png "Division and square-root timings across encoded widths. Both axes are logarithmic, and lower is faster. Universal square roots that disagreed on the benchmark inputs are excluded.")

[Figure 12.8](#/chapter/performance/figure-format-comparison-div-sqrt) shows division and square root. Here's what the planner selects for binary32 and the 256-bit layout:

```lean
#eval (ExecFloat.Div.selectedCandidate (F := ExecFloat.Binary.Family 8 23)).name
-- "binary-interchange division fixed-format kernel"
#eval (ExecFloat.Div.selectedCandidate (F := ExecFloat.Binary.Family 19 236)).name
-- "binary-interchange division exact baseline"
#eval (ExecFloat.Sqrt.selectedCandidate (F := ExecFloat.Binary.Family 19 236)).name
-- "binary-interchange square root exact baseline"
```

The [limb carrier](#/chapter/performance/how-to-store-wide-numbers-as-limbs) offers other division and square-root candidates. In the generic path, [bounded alignment](#/chapter/performance/how-to-round-by-reading-three-bits) limits intermediates for well-separated add/sub/FMA operands and [increasing-precision square root](#/chapter/performance/how-to-take-a-square-root-two-bits-at-a-time) starts on a leading portion of the radicand, the number under the root. Neither changes the specified result, and what they save depends on the operands.

### Host arithmetic and software

![Native C and FloatLib proved software at binary32 and binary64, with bars at median ns/op and labels giving FloatLib/native time ratios](assets/ch17-host-vs-software.png "Median nanoseconds per operation for native C arithmetic and FloatLib software at binary32 and binary64. Lower is faster, and annotations give the software/native time ratio.")

</details>

## How does FloatLib pick the code that runs?

For each call to `x+y`, the planner selects an addition implementation. An eight-bit format has 256 encodings and 65,536 ordered operand pairs, so all results can be stored in a 64 KiB lookup table. Building the table has an initial cost that must be compared with the saving per call. The policy supplies the expected number of calls for this comparison. For IEEE E4M3 addition, the default policy expects 100,000 calls and selects a word kernel; the throughput policy expects five million calls and selects the table.

So one addition can have three implementations: the table, a word kernel and the exact baseline. The planner picks among those that exist for your format, operation and storage, its *candidates*. Every candidate carries a proof that its `run` equals the same specification, and the winner keeps its proof, so a bad cost estimate can pick slow code but never wrong code.

## How to steer the planner

The planner never times anything on your machine and learns nothing from benchmark results. It ranks certified kernels by declared cost estimates, so the workload you tell it to expect is all it has to go on:

| Choice | How to request it | What changes |
| --- | --- | --- |
| Favor a few calls | Open the `PlanningLatency` scope | Avoids setup that may not pay back |
| Favor repeated calls | Open the `PlanningThroughput` scope | Amortizes setup over more calls and allows larger tables |
| Set your own workload and memory limits | Supply a local `Backend.PolicyFor` instance | Changes the scores and which candidates fit the limits |
| Store wide binary values as limbs | Use `ExecFloat.BinaryLimbs` | Makes eligible wide-limb kernels available |
| Use direct host FPU operations at 32 or 64 bits | Import `NativeFPU.Unchecked` and call its named functions | Uses guarded host arithmetic without a FloatLib refinement certificate |

Binary32 and binary64 always get their fixed-format software kernels, which beat the baseline under every policy. Some quotient and square-root kernels use the host's floating-point operations, but only for a guess that exact integer arithmetic checks, and their refinement proofs cover both paths without assuming the guess was any good. SoftFloat, MPFR and Universal are comparisons, not backends you can select.

## What can the planner choose from?

The exact baseline handles every width, and it pays for that. It computes on `Nat` significands (a significand holds a number's significant digits, and `Nat` is Lean's natural number of any size) with wide intermediates on the heap, about 4.1 microseconds for addition at 256 bits in our [calibrated cost model](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Descriptor/Plan/Estimates.lean). The kernels avoid that, and for addition each proves agreement with the same reference function, `ExecFloat.Spec.add`.

Which kernels a format can use depends on its layout and storage. Tables store values only, so their lookup certificates don't supply an exception-status word, the flags that report events such as overflow. Word and limb kernels have guards, conditions under which they run, that differ by operation.

| Candidate | Format and storage requirements |
| --- | --- |
| Exhaustive table | At most eight encoded bits, stored as a byte; the policy must admit its memory use |
| Word kernel | IEEE encoding fitting in 64 bits, with per-operation bounds on the intermediates |
| Fixed-format kernel | Exactly the binary32 or binary64 layout |
| Two-limb `NativePair` | IEEE encoding, more than 64 fraction bits, at most 128 encoded bits |
| Wide-limb kernel | IEEE encoding wider than 128 bits, at most 32 exponent bits, stored as a limb array |
| Exact baseline | Every descriptor; also supplies the fallback when a specialized kernel declines a call |

<details>
<summary>Kernel algorithms, capacity bounds, and refinement declarations</summary>

The [byte tables](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/ByteTable) are filled on first use by running the reference operation, and [[FloatLib.Floats.Formats.BinaryInterchange.Configured.ByteTable.runBinary_eq_lift]] and its unary and ternary versions say each entry is the reference result for every encoded operand, signed zeros, infinities and NaNs included.

The [word kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/Small) take up to 30 exponent bits and 61 fraction bits for addition and subtraction, 31 fraction bits for multiplication, or up to 61 with the exact `64 x 64 -> 128` product of the [two-word multiplication kernel](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Word/TwoWordMul), and any IEEE encoding of at most 64 bits for division. Calls that fail a normal-input or normal-result check go to the exact baseline.

The [two-limb `NativePair` kernel](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/FixedLimb/Pair) covers binary128 and every `ExecFloat.Binary e f` with $65 \le f$ and $e + f \le 127$, for all six operations, though its square root sends fractions wider than 124 bits and exponent biases that don't exceed the fraction width to the baseline.

Above 128 bits the carrier, the runtime representation a value is stored in, decides. `ExecFloat.Binary` gets no specialized kernel, while `ExecFloat.BinaryLimbs` adds the [wide-limb backend](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/WideLimb) for eligible descriptors, behind normal-input and normal-result guards for addition, subtraction, multiplication and FMA ([details](#/chapter/performance/how-limb-arrays-hold-wider-numbers) for division and square root), with [[FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb.toModel_add]] through [[FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb.toModel_fma]] covering both paths. The [generic baseline](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/Generic) catches whatever a kernel declines.

</details>

Let's name a small format, `E4M3IEEE`, with four exponent bits, three fraction bits and the IEEE encoding, so unlike the OCP format E4M3FN from [the machine-learning formats chapter](#/chapter/low-precision-formats-for-machine-learning) it has infinities. If you add the same two numbers in it and in binary128:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

abbrev E4M3IEEE := ExecFloat.Binary (exponentBits := 4) (fractionBits := 3)

#eval (1.5 : E4M3IEEE) + 2.25
-- 3.75
#eval (1.5 : Binary128) + 2.25
-- 3.75
```

you get the same answer from two different kernels under the default policy, a machine-word kernel for the 8-bit addition and a two-limb kernel for binary128. Neither call rounds, since the inputs and the exact sum fit both formats.

## Which kernels can your format use?

A kernel looks only at the descriptor, FloatLib's description of a format by its field widths and encoding, so a custom `ExecFloat.Binary` with a standard layout gets that layout's kernel. Each kernel's requirements are a decidable proposition, one whose truth Lean can compute, such as [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeSmallWordAdd.Eligible]] or [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair.Eligible]], so `by decide` checks them:

```lean
example : Model.NativeSmallWord.StorageEligible FloatFormat.binary16 := by decide
example : Model.NativeSmallWordAdd.Eligible FloatFormat.binary64 := by decide
example : ¬ Model.NativeSmallWord.Eligible FloatFormat.binary64 := by decide
example : Model.NativeTwoWordMul.Eligible FloatFormat.binary64 := by decide
example : Model.NativePair.Eligible FloatFormat.binary128 := by decide
example : ¬ Model.NativePair.Eligible (FloatFormat.ieee 15 64) := by decide
example : Model.WideLimb.Eligible (FloatFormat.ieee 19 236) := by decide
example : ¬ Model.WideLimb.Eligible FloatFormat.binary128 := by decide
```

The 80-bit layout `FloatFormat.ieee 15 64` is smaller than binary128 and still fails: its 64-bit fraction fills the low word, while the pair kernel expects the sign, the exponent and the top of the fraction in the high word.

<details>
<summary>Inspecting structural candidates before selection</summary>

[[FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.structuralRoute?]] shows the route before selection, at most one of three kernel types per operation (fixed format, machine word or fixed limbs), and the storage plan and policy decide whether it runs.

```lean
#eval Descriptor.Plan.structuralRoute? (FloatFormat.ieee 4 3) .add
-- some (FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.StructuralRoute.nativeWord)
#eval Descriptor.Plan.structuralRoute? FloatFormat.binary32 .add
-- some (FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.StructuralRoute.fixedFormat)
#eval Descriptor.Plan.structuralRoute? (FloatFormat.ieee 11 40) .add
-- some (FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.StructuralRoute.nativeWord)
#eval Descriptor.Plan.structuralRoute? (FloatFormat.ieee 11 40) .mul
-- some (FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.StructuralRoute.fixedLimbs)
#eval Descriptor.Plan.structuralRoute? FloatFormat.binary128 .add
-- some (FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.StructuralRoute.fixedLimbs)
#eval Descriptor.Plan.structuralRoute? (FloatFormat.ieee 19 236) .add
-- none
```

The 52-bit layout with 40 fraction bits adds in one word, but its products of up to 82 bits need the two-word multiply, which counts as fixed-limb code. A `none` leaves the baseline or, on a limb carrier, a wide-limb candidate.

</details>

## How does the planner choose?

Each [[FloatLib.Floats.ExecFloat.Backend.Candidate]] record names its [[FloatLib.Floats.ExecFloat.Backend.KernelClass]] and estimates its one-time and per-call costs. A [[FloatLib.Floats.ExecFloat.Backend.Policy]] sets the expected workload and the memory limits. `latency` expects one call, the balanced profile [[FloatLib.Floats.ExecFloat.Backend.Policy.default]] 100,000 and `throughput` 5,000,000. Latency and balanced allow 1 MiB of resident memory per candidate and throughput 16 MiB, and all three allow 64 MiB of temporary memory. The weights live in the [policy](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Selection/Policy.lean).

The [scoring function](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Selection/Scoring.lean) adds a warm cost, paid on every call, to a cold cost, paid once for setup and resident memory. In transit terms the cold cost is the pass and the warm cost is the fare:

$$\mathrm{score} = \mathrm{expectedCalls} \cdot \mathrm{warmCost} + \mathrm{coldCost}.$$

Before scoring, `admissible` throws out alternatives whose estimated resident or temporary bytes go over the policy's limits, and `consider_rejects_excess_residency` proves such a candidate can't replace the current choice. [Figure 12.10](#/chapter/performance/figure-ch09-backend-ladder) works through E4M3 addition with `UInt8` storage.

![Three eligible implementations of E4M3 addition, with estimated total costs of 1,500,000 for the word kernel, 1,742,848 for the table, and 2,100,000 for the baseline](assets/ch09-backend-ladder.png "The planner selects the lowest estimated cost among eligible alternatives. These are relative cost units for 100,000 calls, not measured execution times.")

The choice is a fold: [[FloatLib.Floats.ExecFloat.Backend.selectCertified]] starts from the baseline and keeps whichever alternative scores lower. The baseline stays available even when its own estimated memory goes over the limits, so selection always has an answer, and the limits filter alternatives without capping the winner's memory.

### Why can a bad estimate only cost speed?

Correctness comes from what the fold runs over, a [[FloatLib.Floats.ExecFloat.Backend.CandidateSet]] of [[FloatLib.Floats.ExecFloat.Backend.Certified]] values. A `Certified spec` holds an executable `run`, the estimate and a proof `run_eq_spec : run = spec`, and you can't build one without the proof. [[FloatLib.Floats.ExecFloat.Backend.selectCertified_estimate]] says folding over the estimates alone gives the same answer, so a tool can report the plan without running a kernel. And [[FloatLib.Floats.ExecFloat.Backend.selectCertified_run_eq_spec]] says whatever the fold returns satisfies `run = spec`, however badly the estimates predict runtime. Look at its statement: any policy, any candidate set, not a word about the estimates.

```lean
open FloatLib.Floats.ExecFloat.Backend in
example {α : Type} {spec : α} (policy : Policy) (candidates : CandidateSet (Certified spec)) :
    (selectCertified policy candidates).run = spec :=
  selectCertified_run_eq_spec policy candidates
```

## How to see which kernel runs

You can ask the planner what it picked: `selectedCandidate` shows the selected certificate's estimate, and `selected_eq_planner` says it's the planner's answer. Name the format by its family, `ExecFloat.Binary.Family` with exponent and fraction widths or `ExecFloat.Binary.LimbFamily` for the limb carrier.

<details>
<summary>Selected kernels across standard and custom widths</summary>

```lean
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 5 10)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.nativeWord
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 8 23)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.fixedFormat
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 11 52)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.fixedFormat
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 15 80)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.fixedLimbs
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 15 112)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.fixedLimbs
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 15 64)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
```

</details>

The 80-bit layout comes out `generic`, as its pair predicate said. On the 8-bit format, different operations pick different winners:

```lean
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.nativeWord
#eval (ExecFloat.Sqrt.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.exhaustiveTable
#eval (ExecFloat.Fma.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
```

`#float_info` reads off the selected candidate for all six operations under the planning policy it names, and `#float_info!` also shows every score:

```lean
#float_info E4M3IEEE
-- Execution:
--   planning policy: balanced
--   backends: add, sub, mul, div = machine-word kernel (UInt8); sqrt = exhaustive encoded-value table (UInt8); fma = exact baseline (UInt8)
#float_info Binary32
-- Execution:
--   planning policy: balanced
--   backends: add, sub, mul, div, sqrt, fma = fixed-format word kernel (UInt32)
```

`breakEvenCalls` answers the transit-pass question: after how many calls does one candidate earn back its setup cost against another? Both calls use the byte storage plan that `e4m3_byte` certifies:

```lean
theorem e4m3_byte : (FloatFormat.ieee 4 3).bitWidth ≤ 8 := by decide

open FloatLib.Floats.ExecFloat.Backend in
#eval Candidate.breakEvenCalls Policy.default
  (Configured.Plan.directByteEstimate (FloatFormat.ieee 4 3) .sqrt)
  (Configured.Plan.structuralEstimate (.byte e4m3_byte) .sqrt .nativeWord)
-- some 205
open FloatLib.Floats.ExecFloat.Backend in
#eval Candidate.breakEvenCalls Policy.default
  (Configured.Plan.directByteEstimate (FloatFormat.ieee 4 3) .add)
  (Configured.Plan.structuralEstimate (.byte e4m3_byte) .add .nativeWord)
-- some 120238
#eval (Configured.Plan.directByteEstimate (FloatFormat.ieee 4 3) .fma).residentBytes
-- 16777216
```

Square root's 256-entry table earns back its setup against the word kernel after 205 calls. Addition's 64 KiB table saves only 12 units a call, so it needs 120238 calls, more than the 100,000 the default policy expects, and the word kernel wins.

Memory explains FMA. Unary and binary byte-result tables fit under 1 MiB up to eight encoded bits, but ternary ones only up to six, and an eight-bit FMA table needs $2^{24}$ bytes, 16 MiB, so the balanced policy turns it away before scoring. All of this is the declared cost model, not measured time.

## How to change the expected workload

Policies come from a type class, [[FloatLib.Floats.ExecFloat.Backend.PolicyFor]]. A type class lets Lean find a value from a type, here the policy for a format family, and each value it can find is an *instance*. The low-priority default instance is the balanced profile, and the scoped instances `PlanningLatency.policy` and `PlanningThroughput.policy` switch every format at once:

```lean
section FirstCall
open scoped FloatLib.Floats.ExecFloat.Backend.PlanningLatency
#eval (ExecFloat.Sqrt.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
end FirstCall

section Sustained
open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.exhaustiveTable
#eval (ExecFloat.Fma.selectedCandidate (F := ExecFloat.Binary.Family 4 3)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
end Sustained
```

For a single call, even the 256-entry square-root table isn't worth building. Under throughput the 16 MiB ceiling lets the FMA table in, but its setup doesn't pay off over five million calls, while addition moves to its table. Only the plan changes, never the value type or the reference operation.

## How an ordinary addition reaches its kernel

Let's follow `(1.5 : E4M3IEEE) + 2.25` down to its kernel. The call reaches addition's [[FloatLib.Floats.ExecFloat.Capability]], which holds the specification, the candidates and the selected certificate, chosen once and then remembered.

From the [public dispatch](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Dispatch.lean) down it's a chain of equalities: the code that runs is the stored certificate's `run`, that `run` is the specification, [[FloatLib.Floats.ExecFloat.Capability.run_eq_spec]] joins the two, and [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] puts the result under the public operation's name. Another field proves the stored certificate is the planner's winner.

```lean
example (x y : E4M3IEEE) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y

example (x y : Binary256) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

The equation covers every pair of operands, guarded fallbacks included, so it holds just as well for `Binary256`, whose carrier selects the baseline, and when the descriptor or policy varies at runtime.

## How to store wide numbers as limbs

The wide-limb kernel needs `ExecFloat.BinaryLimbs`, which keeps a wide value between calls in an array of 32-bit limbs, the machine-word digits of a big number. Literals, arithmetic and the public equations work on it too:

```lean
abbrev Limb256 := ExecFloat.BinaryLimbs (exponentBits := 19) (fractionBits := 236)

#eval (1.5 : Limb256) + 2.25
-- 3.75

example (x y : Limb256) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

For this 256-bit descriptor the default policy picks wide-limb candidates for all six operations, three of them here:

```lean
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.LimbFamily 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
#eval (ExecFloat.Div.selectedCandidate (F := ExecFloat.Binary.LimbFamily 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
#eval (ExecFloat.Sqrt.selectedCandidate (F := ExecFloat.Binary.LimbFamily 19 236)).kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
```

`Binary256` and `Limb256` are the same numbers in different boxes. `.wide` stores `Model format` and is the default for this layout, while `.limbs` stores `Model.WideLimb.Value format` and needs a proof that the encoded width is over 128 bits. Same descriptor, different candidate sets:

<details>
<summary>The candidate fold for limb and proof-model storage</summary>

```lean
abbrev B256 : FloatFormat := FloatFormat.ieee 19 236
theorem b256_wide : 128 < B256.bitWidth := by decide

open FloatLib.Floats.ExecFloat.Backend in
#eval (selectCertified Policy.default
  (Configured.Plan.automaticAddCandidates B256 (.limbs b256_wide))).estimate.kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
open FloatLib.Floats.ExecFloat.Backend in
#eval (selectCertified Policy.default
  (Configured.Plan.automaticDivCandidates B256 (.limbs b256_wide))).estimate.kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.wideLimbs
open FloatLib.Floats.ExecFloat.Backend in
#eval (selectCertified Policy.default
  (Configured.Plan.automaticAddCandidates B256 .wide)).estimate.kind
-- FloatLib.Floats.ExecFloat.Backend.KernelClass.generic
```

</details>

[[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.wideLimbAdd?]] and its siblings offer limb kernels only for eligible descriptors. For division and square root both candidates are charged the same integer work, so only the baseline's estimated cost of converting between the limb carrier and the proof model makes the direct one win. This is a planning estimate rather than a measured speedup.

## Why isn't the host FPU a candidate?

Lean's `Float` and `Float32` reach the processor's faster arithmetic for binary32 and binary64. But a planner candidate needs a `Backend.Certified` value, and its `run_eq_spec : run = spec` would demand exact packed-word equality on every guarded finite input, overflow, underflow and signed zeros included. We have those equalities for Lean's logical model on finite operands, and for square root on every input ([Lean's native floats](#/chapter/lean-native-floats/what-is-proved-about-leans-arithmetic)), but the compiled operations are `@[extern]` C calls, and no Lean theorem says what the processor returns for them or that the process rounds to nearest even with gradual underflow.

So trusting the host is your decision, made where you call it. Import the unchecked module and name the operation, and ordinary `+` stays on the certified software path:

```
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange.Configured

def hostAdd32 (x y : Binary32) : Binary32 :=
  NativeFPU.Unchecked.add32 x y
```

Its ten named functions cover addition, subtraction, multiplication, division and square root at both host widths, with no unchecked FMA and no `@[implemented_by]` swap behind the certified operations. Guards, NaN payloads and process settings are in the [native-floats chapter](#/chapter/lean-native-floats/how-to-use-the-processors-own-arithmetic).

## How to check the planner's work

<details>
<summary>Why binary32 and binary64 always get their own kernel</summary>

For binary32 and binary64 the [fixed-format dispatch](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeDispatch.lean) names the fixed-format certificate, and [[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.selectCertified_binary32AddCandidates]] and its eleven siblings prove by cost dominance that the planner picks it under every policy:

```lean
open FloatLib.Floats.ExecFloat.Backend in
theorem binary32_add_selects_software (policy : Policy)
    (h : FloatFormat.binary32.bitWidth ≤ 32) :
    selectCertified policy (Configured.Plan.binary32AddCandidates h) =
      Configured.Plan.softwareAdd32Certified h :=
  Configured.Plan.selectCertified_binary32AddCandidates policy h
```

Hypothesis `h` says the layout fits the `word32` storage plan, which `StoragePlan.forKnownWidth` supplies for a 32-bit width. It puts no restriction on the operands.

</details>

<details>
<summary>Public equations and their axiom dependencies</summary>

The six public equations, [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] through [[FloatLib.Floats.ExecFloat.Proof.fma_eq_spec]], are stated against [[FloatLib.Floats.ExecFloat.Spec.add]] and its siblings, and [[FloatLib.Floats.ExecFloat.Proof.fullArithmeticCertificate]] collects them. Here's what the addition equation and the real-number theorem rest on:

```lean
open FloatLib.Floats

example (x y : Binary32) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y

#print axioms FloatLib.Floats.ExecFloat.Proof.add_eq_spec
-- 'FloatLib.Floats.ExecFloat.Proof.add_eq_spec' does not depend on any axioms

#print axioms FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt
-- 'FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt' depends on axioms: [propext,
--  Classical.choice,
--  Quot.sound]
```

The `example` type-checks because `+` on `Binary32` unfolds to [[FloatLib.Floats.ExecFloat.add]], the certified dispatch. The public equation needs no axioms, since it's a projection out of a certificate. The real-number theorem inherits the three axioms under Mathlib's construction of the reals: propositional extensionality, quotient soundness and choice.

</details>

## What is inside a kernel?

A kernel is an integer algorithm plus a theorem that says which natural number its returned words stand for (`toNat`), so a backend can run it instead of the big-integer reference operation. It works on a `UInt64`, two words ([[FloatLib.Numerics.FixedWord.UInt128]]), four words (a `UInt256`) or an `Array UInt32` of limbs.

### How to multiply in machine words

The exact product of two binary64 significands can need 106 bits, so [[FloatLib.Numerics.FixedWord.mul64]] returns two words, multiplying 32-bit halves grade-school style [@warrenHackersDelight2013]. [[FloatLib.Numerics.FixedWord.mul64_toNat]] says the pair, read as

$$\mathrm{toNat}(\langle hi, lo\rangle) = lo + hi \cdot 2^{64},$$

is the natural-number product, and `add128_toNat` keeps the carry.

```lean
section
open FloatLib.Numerics.FixedWord

#eval mul64 0xffffffffffffffff 0xffffffffffffffff
-- { hi := 18446744073709551614, lo := 1 }

example (x y : UInt64) : (mul64 x y).toNat = x.toNat * y.toNat :=
  mul64_toNat x y

#eval add128 ⟨0xffffffffffffffff, 0xffffffffffffffff⟩ ⟨0, 1⟩
-- { value := { hi := 0, lo := 0 }, carry := 1 }
end
```

Since $(2^{64}-1)^2 = 2^{128} - 2^{65} + 1$, the high word is $2^{64} - 2$ and the low word is 1. The addition rolls over like an odometer into its carry.

### How to round by reading three bits

To round $v$ to nearest even after dropping $s$ low bits, you keep the quotient if the dropped part is below half, add one if it's above, and take the even neighbour on a tie. That decision needs only three bits. [[FloatLib.Numerics.roundShiftRightEven_eq_guard_sticky]], in the [shift-rounding module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Quantization/Deterministic/ShiftRight.lean), proves that for $s > 0$

$$\mathrm{round}(v, s) = \lfloor v / 2^s \rfloor + \begin{cases} 1 & \text{if } g \wedge (t \vee p) \\ 0 & \text{otherwise,} \end{cases}$$

where the guard bit $g$ is bit $s-1$ of $v$, the sticky bit $t$ says whether any lower bit is set, and the parity bit $p$ is bit $s$. The word version agrees with [[FloatLib.Numerics.roundShiftRightEven]] for every value and shift (`roundShiftRightEven_toNat`). `shiftRightJam` drops $j$ bits early, leaving a one in the low bit if anything nonzero fell off, and [[FloatLib.Numerics.roundShiftRightEven_shiftRightJam]] ([proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/ShiftRightJam/Proof.lean)) says the final rounding is unchanged when $j + 2 \le s$:

```lean
section
open FloatLib.Numerics.FixedWord

-- 21 / 8 = 2.625: guard set and sticky set, so round up.
#eval roundShiftRightEven 0b10101 3
-- 3

-- 20 / 8 = 2.5: a tie, and the quotient 2 is even, so keep it.
#eval roundShiftRightEven 0b10100 3
-- 2

-- 28 / 8 = 3.5: a tie, and the quotient 3 is odd, so round up.
#eval roundShiftRightEven 0b11100 3
-- 4

-- 100 / 16 = 6.25: the jam records the discarded 0.25 as a low one bit.
#eval UInt256.shiftRightJam128 ⟨0, 0, 0, 0b1100100⟩ 4
-- { hi := 0, lo := 7 }

example (value : UInt64) (shift : Nat) :
    (roundShiftRightEven value shift).toNat =
      FloatLib.Numerics.roundShiftRightEven value.toNat shift :=
  roundShiftRightEven_toNat value shift
end
```

The jammed seven is six plus a one saying something fell off. Jamming lets the generic addition, subtraction and FMA path, [`FiniteScaleAdd.roundAligned`](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Generic/ScaleAdd/Runtime.lean), skip complete alignment when one operand is far smaller, and [`FiniteProductRound.round_shiftRightJam`](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Generic/ProductRound/Proof.lean) and `roundSum_eq` prove the result is still exact addition followed by one rounding, normal or subnormal.

### How to divide one bit at a time

Restoring division is school long division in base two, one quotient bit per step. Let's look at the step from the [restoring-division proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Quotient/Proof.lean), checked by `rfl`:

```lean
open FloatLib.Numerics.FixedWord.RestoringQuotient in
def natQuotientStep (den : Nat) (state : QuotientState Nat) :
    QuotientState Nat :=
  let doubledRemainder := 2 * state.remainder
  if doubledRemainder < den then
    { quotient := 2 * state.quotient
      remainder := doubledRemainder }
  else
    { quotient := 2 * state.quotient + 1
      remainder := doubledRemainder - den }

example :
    natQuotientStep =
      FloatLib.Numerics.FixedWord.RestoringQuotient.natQuotientStep := rfl
```

After $n$ steps from a remainder below the divisor, the invariant `natQuotientSteps_spec` gives

$$q' \cdot d + r' = (q \cdot d + r) \cdot 2^n, \qquad r' < d, \qquad q \le q',$$

so the quotient is the true floor (`natQuotientSteps_div_mod`). On machine words the loop needs a divisor and quotient prefix below $2^{63}$, so that no doubling wraps, and [[FloatLib.Numerics.FixedWord.RestoringQuotient.roundScaledQuotient_toNat]] proves that `roundScaledQuotient` rounds the scaled quotient to nearest even. Compiled code may first try a floating-point estimate, and the [`roundScaledQuotient_eq_internal` compiler equation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Quotient/Compiler.lean) proves equality whatever the guess.

```lean
section
open FloatLib.Numerics.FixedWord.RestoringQuotient

-- Start from 4 = 1 * 3 + 1 and generate four more quotient bits:
-- 4 * 2^4 = 64 = 21 * 3 + 1.
#eval quotientSteps 3 4 { quotient := 1, remainder := 1 }
-- { quotient := 21, remainder := 1 }

-- (1 / 3) * 2^52 rounded to nearest even, in native words ...
#eval roundScaledQuotient 1 3 52
-- 1501199875790165

-- ... and by the arbitrary-precision definition it refines.
#eval FloatLib.Numerics.roundQuotientEven (1 <<< 52) 3
-- 1501199875790165

example (den n : Nat) (state : QuotientState Nat) (h : state.remainder < den) :
    (natQuotientSteps den n state).quotient =
      ((state.quotient * den + state.remainder) * 2 ^ n) / den :=
  (natQuotientSteps_div_mod den n state h).1
end
```

[Figure 12.11](#/chapter/performance/figure-ch08-restoring-division) follows the first `#eval` step by step.

![Restoring division of 4 by 3: four steps double the remainder and compare it with 3, keeping it and appending 0 or subtracting 3 and appending 1, to reach quotient 21 and remainder 1](assets/ch08-restoring-division.png "Each step appends one quotient bit and preserves the exact quotient-and-remainder identity.")

### How to take a square root two bits at a time

Square root brings digits down in pairs, like the pencil-and-paper method.

The invariant $r^2 + m = x$ with $m \le 2r$ makes $r$ equal to $\lfloor\sqrt{x}\rfloor$. [[FloatLib.Numerics.FixedWord.RestoringSquareRoot.rootAndRemainder_spec]] holds for any digit count up to 125 and any radicand below $2^{2 \cdot \mathrm{steps}}$, and the binary128 backend uses 113 digits. No integer radicand sits on a midpoint, so `roundRoot` rounds up exactly when $m > r$, and `roundRoot_toNat` proves it gives the nearest integer root under the same hypotheses:

```lean
section
open FloatLib.Numerics.FixedWord.RestoringSquareRoot

-- 1000 = 31^2 + 39
#eval rootAndRemainder ⟨0, 0, 0, 1000⟩ 64
-- { root := { hi := 0, lo := 31 }, remainder := { hi := 0, lo := 39 } }

-- 39 > 31, so the nearest integer root is 32 (sqrt 1000 = 31.62...).
#eval roundRoot (rootAndRemainder ⟨0, 0, 0, 1000⟩ 64)
-- { hi := 0, lo := 32 }

-- 980 = 31^2 + 19 and 19 <= 31, so it stays at 31 (sqrt 980 = 31.30...).
#eval roundRoot (rootAndRemainder ⟨0, 0, 0, 980⟩ 64)
-- { hi := 0, lo := 31 }
end
```

The [binary64 square root](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Full/Sqrt/Runtime.lean), which covers every input bit pattern, NaN, infinities, signed zeros and negatives included, and the binary128 [checked square-root kernel](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/CheckedSqrt/Runtime.lean) both start from a fast guess that an exact check accepts or rejects, and their proofs show the result matches the restoring loop either way. [`IntegerSquareRoot.sqrtNat`](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/IntegerSquareRoot/Runtime.lean), after [CPython 3.13's integer-square-root algorithm](https://github.com/python/cpython/blob/v3.13.0/Modules/mathmodule.c#L1494), handles radicands of any width, with an increasing-precision candidate for large ones, and returns the floor root. [`checkRoot?_eq` and `sqrtRem_eq`](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/IntegerSquareRoot/Proof.lean) prove that `sqrtRem` returns $(\lfloor\sqrt n\rfloor,\ n-\lfloor\sqrt n\rfloor^2)$, however good the candidate was.

### How to check a division answer instead of trusting it

Restoring division pays one iteration per bit, while Knuth's Algorithm D [@knuth1997] needs four digit steps for a 128-bit quotient. We haven't proved that search, and we don't have to: [[FloatLib.Numerics.FixedWord.CertifiedDivision.candidate]] runs it, and [[FloatLib.Numerics.FixedWord.CertifiedDivision.certificate]] multiplies back to check the answer (namespaces shortened):

```
sum.carry == 0 &&
  sum.value == UInt256.ofUInt128ShiftedLeft num (shift.toNat precision) &&
  UInt128.less remainder den
```

The tests say that quotient times divisor plus remainder doesn't carry out of 256 bits, equals the scaled numerator, and leaves a remainder below the divisor, so by [[FloatLib.Numerics.FixedWord.CertifiedDivision.certificate_sound]] a passing candidate is the unique correct quotient and remainder, however it was produced, and `roundQuotient_toNat` covers the final rounding. A failed check falls back to the restoring loop in [[FloatLib.Numerics.FixedWord.CertifiedDivision.checkedCandidate]], and backends use [[FloatLib.Numerics.FixedWord.CertifiedDivision.checkedCandidate_sound]], for normalized significands of $p + 1$ bits with $65 \le p \le 126$ and either numerator shift. Here is one divided by one and a half in binary128:

```lean
section
open FloatLib.Numerics.FixedWord
open FloatLib.Numerics.FixedWord.CertifiedDivision

-- binary128 significands have 113 bits: 1.0 divided by 1.5.
-- The numerator is smaller, so the extra shift scales it by 2^113.
#eval (checkedCandidate 112 (UInt128.ofNat (2 ^ 112)) (UInt128.ofNat (3 * 2 ^ 111)) .extra).quotient.toNat
-- 6923062478046436838040661772293461

#eval (2 ^ 225 : Nat) / (3 * 2 ^ 111)
-- 6923062478046436838040661772293461

-- The certificate accepts the true quotient and rejects its predecessor.
#eval certificate 112 (UInt128.ofNat (2 ^ 112)) (UInt128.ofNat (3 * 2 ^ 111)) .extra
  (UInt128.ofNat 6923062478046436838040661772293461) (UInt128.ofNat (2 ^ 111))
-- true

#eval certificate 112 (UInt128.ofNat (2 ^ 112)) (UInt128.ofNat (3 * 2 ^ 111)) .extra
  (UInt128.ofNat 6923062478046436838040661772293460) (UInt128.ofNat (2 ^ 111))
-- false
end
```

Soundness rests on the check alone, so we're free to change the search in the [certified-division implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/CertifiedDivision/Runtime.lean).

### How slow definitions get swapped for fast ones

A `@[csimp]` equation ([the chapter on running code and proofs](#/chapter/the-numerical-models)) is a checked proof that two functions are equal, and the compiler then calls the fast one wherever code calls the slow one. Here the logical [[FloatLib.Numerics.roundShiftRightEven]] gets `roundShiftRightEvenNat`, quoted as a checked copy:

```lean
def roundShiftRightEvenNat (value shift : Nat) : Nat :=
  if _hvalue : value < 2 ^ 64 then
    (FloatLib.Numerics.FixedWord.roundShiftRightEven (UInt64.ofNat value) shift).toNat
  else if shift == 0 then
    value
  else
    let amount := shift - 1
    let retained := Nat.shiftRight value amount
    let quotient := Nat.shiftRight retained 1
    let lowByte := UInt8.ofNat retained
    if (lowByte &&& 1) != 0 then
      if ((lowByte >>> 1) &&& 1) != 0 || Nat.shiftLeft retained amount != value then
        quotient + 1
      else
        quotient
    else
      quotient

example :
    roundShiftRightEvenNat =
      FloatLib.Numerics.FixedWord.roundShiftRightEvenNat := rfl

example :
    FloatLib.Numerics.roundShiftRightEven =
      FloatLib.Numerics.FixedWord.roundShiftRightEvenNat :=
  FloatLib.Numerics.FixedWord.roundShiftRightEven_eq_roundShiftRightEvenNat

#eval FloatLib.Numerics.roundShiftRightEven 0b10101 3
-- 3
```

The second `example` is the `@[csimp]` theorem, [[FloatLib.Numerics.FixedWord.roundShiftRightEven_eq_roundShiftRightEvenNat]]. Once you import its module, newly compiled code and `#eval` use the fast version, but functions compiled before the import don't change, so their modules need the theorem when they're compiled. Theorems about the logical definition keep applying. Similar equations cover `roundQuotientEven` ([rounding proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Core/Proof/Rounding.lean)) and `Nat.sqrt` ([integer-square-root proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/IntegerSquareRoot/Proof.lean)), so any program importing `FloatLib.Kernels` compiles its `Nat.sqrt` calls through [[FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat]], floating point or not.

<details>
<summary>The two compiler-certificate signatures</summary>

On the left is the logical definition, and on the right the executable dispatcher:

```lean
#check @FloatLib.Numerics.FixedWord.roundShiftRightEven_eq_roundShiftRightEvenNat
-- FloatLib.Numerics.FixedWord.roundShiftRightEven_eq_roundShiftRightEvenNat : FloatLib.Numerics.roundShiftRightEven =
--   FloatLib.Numerics.FixedWord.roundShiftRightEvenNat

#check @FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat
-- FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat : Nat.sqrt =
--   FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrtNat
```

</details>

The [division](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Quotient/Compiler.lean) and [square-root](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/RestoringSqrt/Compiler.lean) compiler proofs replace whole loops the same way, with equalities such as [[FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128_eq_internal]] that hold for every input, even where words wrap. Import their compiler modules when a consumer is compiled.

**Note:** These equalities are about Lean's logical operations. `mul64_toNat`, for example, relates the `UInt64` operations in Lean's model to natural-number multiplication. Running the proved algorithms also relies on the compiler applying the substitutions correctly, and on the compiler, runtime and CPU implementing those word operations correctly.

### How limb arrays hold wider numbers

Wider formats use [[FloatLib.Numerics.LimbArray]] from the [limb-array implementation](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels/LimbArray), a natural number stored as an `Array UInt32` with limb $i$ worth $2^{32 i}$, digits in base $2^{32}$ from the ones place up. [[FloatLib.Numerics.LimbArray.toNat]] reads the value, and the [limb-arithmetic proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/LimbArray/Arithmetic/Proof.lean) specifies each operation by its effect on it, from [[FloatLib.Numerics.LimbArray.toNat_add]] and [[FloatLib.Numerics.LimbArray.toNat_mul]] to [[FloatLib.Numerics.LimbArray.toNat_roundShiftRightEven]]. A 32-bit limb leaves room for a product plus two addends in one `UInt64`:

$$(2^{32}-1)^2 + 2(2^{32}-1) = 2^{64} - 1.$$

`add` returns one limb more than the wider operand, so `toNat_add` has no side condition, while `sub` assumes its result is nonnegative (`toNat_sub`). [[FloatLib.Numerics.LimbArray.mul]] is the schoolbook product, and [[FloatLib.Numerics.LimbArray.roundShiftRightEven]] applies the guard-and-sticky rule:

```lean
open FloatLib.Numerics in
def roundShiftRightEven (v : LimbArray) (shift : Nat) : LimbArray :=
  if shift == 0 then
    v
  else
    let quotient := v.shiftRight shift
    if v.testBit (shift - 1) && (v.anyBelow (shift - 1) || v.testBit shift) then
      quotient.addAt 0 1
    else
      quotient

example : roundShiftRightEven = FloatLib.Numerics.LimbArray.roundShiftRightEven := rfl
```

Arrays print lowest limb first, and on a nonempty array `orLowBit` is the jam (`toNat_orLowBit`):

```lean
section
open FloatLib.Numerics

#eval LimbArray.ofNat (2 ^ 70 + 5) 3
-- { limbs := #[5, 0, 64] }

-- Three limbs times two limbs gives five, and the value is the product.
#eval LimbArray.mul (LimbArray.ofNat (2 ^ 70 + 5) 3) (LimbArray.ofNat (2 ^ 40 + 1) 2)
-- { limbs := #[5, 1280, 64, 16384, 0] }

#eval (LimbArray.mul (LimbArray.ofNat (2 ^ 70 + 5) 3) (LimbArray.ofNat (2 ^ 40 + 1) 2)).toNat ==
  (2 ^ 70 + 5) * (2 ^ 40 + 1)
-- true

-- The sum gets one limb more than the wider operand, so the carry has somewhere to go.
#eval LimbArray.add (LimbArray.ofNat (2 ^ 96 - 1) 3) (LimbArray.ofNat 1 1)
-- { limbs := #[0, 0, 0, 1] }

-- 100 = 0b1100100: nothing below bit 2, something below bit 4.
#eval (LimbArray.ofNat 100 1).anyBelow 2
-- false
#eval (LimbArray.ofNat 100 1).anyBelow 4
-- true

-- Shift right by four and jam the discarded bits into the low bit: 6 becomes 7.
#eval ((LimbArray.ofNat 100 1).shiftRight 4).orLowBit true
-- { limbs := #[7] }

example (a b : LimbArray) : (LimbArray.mul a b).toNat = a.toNat * b.toNat :=
  LimbArray.toNat_mul a b

example (v : LimbArray) (shift : Nat) :
    (LimbArray.roundShiftRightEven v shift).toNat =
      FloatLib.Numerics.roundShiftRightEven v.toNat shift :=
  LimbArray.toNat_roundShiftRightEven v shift
end
```

$$
(2^{70}+5)(2^{40}+1)=2^{110}+2^{70}+5\cdot2^{40}+5.
$$

Expanding the product gives its limbs: five, $5\cdot2^{40}=1280\cdot2^{32}$, $2^{70}=64\cdot2^{64}$, $2^{110}=16384\cdot2^{96}$, and a zero, since multiplication reserves the sum of the operand lengths. [Figure 12.12](#/chapter/performance/figure-ch08-limb-arrays) follows the sum, a carry rippling through three full limbs the way 999 plus one rolls over into 1000.

![Adding 1 to 2^96 - 1 in base 2^32: each of three saturated limbs stores zero and passes a carry of one, producing four limbs (0, 0, 0, 1), lowest limb first](assets/ch08-limb-arrays.png "The final carry occupies the extra limb reserved by addition.")

The [wide-limb backend](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/WideLimb) runs on these arrays, though its division and square root compute with arbitrary-precision integers decoded from the stored limb fields. Its [division](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/WideLimb/Division/Runtime.lean) handles finite operands, zeros and subnormals included, through the shared [quotient rounder](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Generic/QuotientRound/Runtime.lean), and its [square root](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/WideLimb/Sqrt/Runtime.lean) handles positive normal operands. Everything else goes to the reference operation, and [`toModel_div`](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/WideLimb/Division/Proof.lean) and [`toModel_sqrt`](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/WideLimb/Sqrt/Proof.lean) cover the complete operations, fallback branches included.

### What are the capacity bounds?

Several certificates have capacity hypotheses: a divisor below $2^{63}$ for the word division loop, a radicand below $2^{226}$ for the two-word square root at 113 digits, and a fraction-width parameter from 65 to 126 for certified division. Backends prove these from their field widths. Outside the bounds a kernel still returns words, the same ones the logical loops return, but the theorem says nothing about what they mean, so the dispatcher uses these certificates only where their hypotheses hold, with a proved fallback elsewhere.

## How we measured the nine-trial comparison

<details>
<summary>Timed work, toolchains, adapters, and input agreement</summary>

### What one timed operation includes

The sixteen input sets are rationals that each adapter converts before timing, and MPFR converts them itself, so no earlier binary64 rounding gets in.

The workload uses sixteen fixed input entries. Each result selects the next entry, making each operation depend on the previous result. The selected entry supplies the next operands, so repeated operations do not change the numerical input distribution. Each reported ns/op includes lookup, adapter work, the arithmetic call and observation of the result. Native C's 8.33 ns addition therefore measures more than one addition instruction. Independent operations, vectorized kernels and workloads concentrated on subnormal inputs may give different comparisons. uops.info [@abelUopsInfo2019] distinguishes dependent instruction chains from independent operations.

Before timing MPFR, SoftFloat, native C and Python, we compare 256 operations per format with FloatLib through two checksums, over the results and over the chosen inputs, since one rounding difference can send the loop to another page. That's evidence of agreement on these inputs, not a proof about every intermediate result.

### How we ran the external implementations

Each library runs through an adapter in its own representation, and that cost stays inside the measured loop, MPFR reusing a destination object and Python creating Python result objects. Our [MPFR adapter](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/c/exact_format_mpfr.c), on MPFR 4.1.0 [@fousseMpfr2007], sets the binary companion's precision and exponent range at each width and calls `mpfr_subnormalize` after every operation, since precision alone would miss the tiny formats' overflow and gradual underflow.

SoftFloat runs at revision `a0c6494`, built with the configuration our [benchmark driver](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/scripts/format-comparison.sh) selects, through the [SoftFloat adapter](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/c/softfloat_ieee.c), with nearest-even rounding and tininess detected after rounding. The native adapter uses C `float` and `double` without `-ffast-math` and checks the host representation and rounding mode first, though no check in the benchmark record targets flush-to-zero. The measured interpreter was CPython 3.12.13, which has no `math.fma`.

We used Stillwater Universal [@stillwaterUniversal] at revision `26e69f5` with `posit<width, 2, uint64_t>`, and timed an operation only when all sixteen results agreed with FloatLib's. Of 78 operation-and-width combinations 71 agreed, square root differing at every width from 64 through 4,096 bits, and widths below five are out because of Universal's generic `es=2` FMA constraint. Agreement here is evidence for this workload, not an exhaustive posit conformance result.

</details>

<a id="which-libraries-did-we-time"></a>

## Which comparisons check answers but not speed?

SoftPosit is a correctness comparison, not a race: we compared its result bits only, and that run's time includes preparing inputs and comparing answers. Berkeley's tools split the same way, TestFloat for correctness tests and SoftFloat for arithmetic, and the ONNX and P3109 table checks compare encodings. The [validation chapter](#/chapter/external-validation) explains those checks and works through [the seven SoftPosit inputs](#/chapter/external-validation/why-did-softposit-disagree-with-floatlib) behind the reported differences.

## How to reproduce the measurements

To rerun the nine-trial loop, start from the [benchmark method](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/docs/Comparison.md) and [results](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/main/README.md), which give the commands, toolchains and raw trials. The public-call record below has its own data and instructions.

<a id="public-binary-measurement-record"></a>

<details>
<summary>Public binary measurement record</summary>

The public-call [measurements](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/public-binary/measurements.csv) and [metadata](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/public-binary/metadata.json) keep every trial and the build: Lean 4.35.0 and Mathlib `56a00585`, against MPFR 4.1.0-p13 with GMP 6.2.1. Calibration aimed at 40 ms per interval, but 99 of the 1,512 timed intervals came in under 36 ms, the shortest at 22.2 ms, and recorded CPU-quota throttling was zero. The [fixture archive](assets/public-binary-fixtures.zip) holds the inputs, expected outputs and agreement reports for the 84 plotted cases, the [benchmark bundle](assets/public-binary-benchmark.tar.gz) lets you compare a FloatLib checkout with MPFR yourself, and the [figure script](https://github.com/lean-dojo/FloatLib/blob/main/site/content/assets/figures/ch15_public_binary.py) regenerates both PNGs from the retained data without rerunning the benchmark:

```bash
python3 site/content/assets/figures/ch15_public_binary.py
```

</details>
