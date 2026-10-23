---
number: "17"
slug: performance
title: "Performance"
summary: "Measure ordinary public binary arithmetic against MPFR, then compare other libraries on their separate workloads."
phases: [trust]
---

Our performance goal is to reach MPFR's speed with proved arithmetic. In the recorded public-call experiment, binary32 multiplication took 17.9 ns in FloatLib and 27.5 ns in MPFR. That's one of our better results, but binary64 and binary128 were slower on all six operations. These measurements predate the October 2026 changes described below; the later before-and-after timings measure those changes on different workloads.

Lean erases proof terms during compilation [@leanReference]. The timed program executes arithmetic, representation conversions, and dispatch. These are the costs we need to improve to make the proved operations faster.

<a id="timing-results"></a>

## Public binary arithmetic

We time ordinary public `ExecFloat.Binary` calls, including the configured representation and the
selected software kernel. MPFR gets the same precision, exponent bounds, and nearest-even rounding
with gradual underflow. Each point
cycles through sixteen prepared input triples, and we check their full encodings before timing
starts. Inside the loop we call the operation and checksum the low 64 result bits, and that checksum
never picks the next input.

We ran three trials one after another on the same pinned CPU of an Intel
Xeon Platinum 8275CL, a machine shared with other work. Each plotted time is that arm's median, and
each ratio is the median of the within-trial FloatLib/MPFR ratios. The whiskers show the observed
minimum and maximum. They aren't confidence intervals, so we wouldn't read much into small
differences.

| Campaign | Public calls against MPFR |
| --- | --- |
| Machine | one pinned CPU of an Intel Xeon Platinum 8275CL, shared with other work |
| Timed calls | FloatLib's public binary operations, and MPFR 4.1.0-p13 with the same precision and exponent bounds |
| Inputs | sixteen prepared input triples per point, full encodings checked before timing |
| Statistic | median of three trials, whiskers at the observed minimum and maximum |
| Recorded | before the October 2026 changes |
| Record | [measurements, metadata, and fixtures](#/chapter/performance/public-binary-measurement-record) |

![FloatLib and MPFR for six public binary operations at encoded widths 32 through 4096](assets/public-binary-performance.png "Median nanoseconds per operation across three trials; whiskers show the observed minimum and maximum, not confidence intervals. Both axes are logarithmic; lower is faster.")

In [Figure 17.1](#/chapter/performance/figure-public-binary-performance), look at the 32-bit points
in the mul and fma panels, where FloatLib's marker sits below MPFR's. Multiplication there is the
17.9 ns result above, and binary32 FMA took 33.2 ns in FloatLib against 43.1 ns in MPFR in this
recorded workload. Subtraction was close. Addition, division, and square root took longer than in
MPFR. In the wider formats we were mostly behind :)

At binary64 and binary128, FloatLib was slower
on all six operations. Binary64 multiplication took 239 ns, about 8.82 times MPFR's time, and
binary64 square root took 1.34 µs, about 45.5 times MPFR's time.

At 4,096 bits, division took 4.57
µs, about 2.12 times MPFR's time, while multiplication took about 3.26 times MPFR's time and FMA
about 2.77 times. Addition and square root left larger gaps, at about 21.2 and 8.10 times MPFR's
time respectively.

![FloatLib and MPFR for six public binary operations below 32 bits](assets/public-binary-low-precision.png "Median nanoseconds per operation across three trials; whiskers show the observed minimum and maximum. The vertical axis is logarithmic; lower is faster.")

Below 32 bits, [Figure 17.2](#/chapter/performance/figure-public-binary-low-precision) adds
binary16, bfloat16, and four layouts from 7 to 9 bits, which use IEEE-style encodings with
infinities and NaNs. Here multiplication did better. Binary16 multiplication took 11.0 ns versus
28.4 ns for MPFR, about 2.58 times faster, and bfloat16 multiplication took 12.1 ns versus 27.5 ns,
about 2.26 times faster. Addition and subtraction were faster in these two formats too, but
division, square root, and FMA were slower.

Which kernel gets selected matters as much as the width,
and square root is a good example. In the 7-bit and 8-bit formats, square root used exhaustive
tables and took about 23 ns, while binary16 and bfloat16 selected word kernels and took about 1.3 µs
for square root, against 30 to 33 ns for MPFR. Most other 7-bit and 8-bit operations were also
slower than MPFR on these inputs.

You'll find the complete loop in the [benchmark instructions and
data](#/chapter/performance/public-binary-measurement-record). Every experiment after this one has
its own workload, so each gets its own section below.

<details>
<summary>The public operation and its theorem</summary>

### Running the code we proved

One small definition shows how the code and the theorem fit together. Say we write `sum64` with
ordinary binary64 addition. The theorem then says that this same expression returns the result
specified by `ExecFloat.Spec.add`.

```lean
open FloatLib.Floats

def sum64 (x y : Binary64) : Binary64 := x + y

example (x y : Binary64) : sum64 x y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y

#eval sum64 1 2
-- 3
```

The theorem covers every pair of binary64 inputs, rounding included. Its right-hand side specifies
a floating-point operation, so it keeps the rounding that replacing addition by a real sum would
lose. The [planner walkthrough](#/chapter/backends-and-the-planner/following-a-public-arithmetic-call)
identifies the software kernel reached by this expression.

</details>

## Speed work in October 2026

In October 2026 we made three changes, and we haven't rerun the earlier recorded campaign behind the
public-binary figures above since then. We stored binary128 values as two native words and gave its
six operations kernels that work on those words. We also specialized the model-path operations to
their format, and we cached the constants of the elementary functions.

| Campaign | October 2026 before-and-after timings |
| --- | --- |
| Machine | Intel Xeon Platinum 8275CL |
| Timed rows | binary128 arithmetic, binary64 model-path operations, and sine |
| Inputs | 100,000 mixed operands for binary128 arithmetic, with a separate set for square root, and benchmark cells for the other rows |
| Statistic | best of several rounds for binary128 arithmetic, minimum of interleaved before-and-after rounds for the other rows |
| Compare with | each row's own before time, not the public-call figures |

Each row of the table below gives the time per operation before and after a change, and the binary64
model-path rows and the sine rows are cells of the `execFloatTimeOps` benchmark.

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

Binary128 got much faster, but it didn't catch up. Even after the change, binary128 was 2 to 6 times
slower than SoftFloat, which took 22 to 54 ns for these six operations, and MPFR at 113 bits took 31
to 80 ns.

We timed the smaller formats in the binary128 comparison as well. Square root in binary16
and bfloat16 went from 1,300.8 and 1,279.8 ns down to 24.4 and 22.1 ns, and those starting times
match the 1.3 µs reported above. Binary64 FMA went from 1,028.9 and 2,551.4 ns to 119.4 and 145.8 ns
on its two operand sets.

On the model path the gains come from three things. Integral rounding,
scaling, `binaryExponent`, and square root are now specialized to their format. Value-only calls
compute no flags or ternary value, and a single comparison per rounding gives both the ternary value
and the inexact flag. For sine, each format's two rows come from two different comparisons, each
against the tree just before that change.

## Matched binary arithmetic with Flocq and MPFR

We also timed FloatLib against extracted Flocq and MPFR, with matching significand precision,
exponent bounds, and nearest-even rounding. Each adapter rounds the same exact rational inputs once,
and before any of these inputs is used for timing, the [numerical
checks](#/chapter/external-validation/binary-arithmetic-with-flocq-and-mpfr) compare the complete
values.

![FloatLib, extracted Flocq, and MPFR across eleven matching binary formats and six operations](assets/flocq-matched.png "Nanoseconds per operation at matching binary precision and exponent bounds. Both axes are logarithmic; lower is faster. Measurements ran on an Intel Xeon Platinum 8275CL.")

The measured widths in [Figure 17.3](#/chapter/performance/figure-flocq-matched) run from 6 to 4,096
bits, and FloatLib beat the extracted Flocq program everywhere except 8-bit FMA, where Flocq took
846 ns and FloatLib took 1,601 ns. For binary64 multiplication, FloatLib took 330 ns and Flocq took
10,575 ns, while MPFR took 32 ns there. MPFR was faster than FloatLib at every point in this
comparison. During timing, each operation and width drew from sixteen input sets.

We ran it on an
Intel Xeon Platinum 8275CL with one calibrated trial per entry, so there's no estimate of timing
variability. These dependent scalar loops include input selection, allocation, and observing the
result. They also call FloatLib differently from the ordinary public calls above, because at
binary32/64 FloatLib calls proved word kernels by name, and at other widths it uses public
operations under `PlanningThroughput`.

<details>
<summary>Extraction, inputs, and the timed Flocq loop</summary>

### The Flocq program we timed

Our [Flocq wrapper](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/rocq/FlocqKernel.v)
uses Flocq 4.2.2 [@boldoMelquiond2011] and exposes `Bplus`, `Bminus`, `Bmult`, `Bdiv`, `Bsqrt`, and
`Bfma` from `IEEE754.BinarySingleNaN`. To convert an input it uses the proved `Bdiv_correct_aux`
helper, which rounds an exact integer quotient once. Precision and exponent bounds match the
FloatLib descriptor, and all three implementations use nearest-even rounding and gradual underflow.
Flocq requires `0 < precision < emax`, which rules out the custom 4-, 5-, and 7-bit layouts, so
they're absent from all three curves. We extracted the wrapper with Coq 8.20.1 and compiled it with
OCaml 4.13.1 and Zarith. The MPFR adapter used MPFR 4.1.0 and GCC 11.5.0, and every timing process
in this experiment ran on the same logical CPU. In the main loop each result picks the next of
sixteen prepared input sets and goes into a checksum, but it never becomes the next operand. Square
root at 1,024, 2,048, and 4,096 bits works differently, for all three implementations. It runs
complete blocks of sixteen inputs, where each result affects their order and each block visits every
input once, so even the slowest wide square roots get timed on the full input set. Every other point
uses the original chain, whose calibrated length differs between implementations. Inside the timer
are the arithmetic, value allocation, normalization for the fingerprint, and checksum work, while
input construction, warmup, proof checking, and compilation all happen before it starts. If you want
to reproduce the figure, the [result
README](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/flocq-matched/README.md)
has the data, environment details, and commands.

</details>

## Other measured workloads

### P3109 arithmetic with FLoPS

FLoPS is another executable Lean implementation with refinement proofs [@flopsArtifact], and we like
this comparison because it's Lean against Lean. We compared three P3109 formats with it, using
nearest-even rounding and no saturation, and all 529,152 arithmetic cases and the 192 exact timing
fixtures agreed bit for bit. [The validation
chapter](#/chapter/external-validation/p3109-arithmetic-with-flops) describes the input coverage.
The
[experiment](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/p3109-flops/results.json)
ran on an Intel Xeon Platinum 8275CL, and the entries below are median microseconds per operation
across nine pairs of fresh processes on one logical CPU. Both libraries run the same loop over 16
finite input triples, and each returned code decides the next input. We time input selection, the
operation, and the checksum, and input construction and process startup happen outside the timer.

| Format | Implementation | Add | Multiply | Divide | FMA |
| --- | --- | ---: | ---: | ---: | ---: |
| Binary4p2sf | FloatLib | 4.37 | 4.47 | 4.32 | 5.86 |
| Binary4p2sf | FLoPS | 4.29 | 4.13 | 5.71 | 5.16 |
| Binary8p4se | FloatLib | 4.89 | 4.96 | 4.94 | 6.40 |
| Binary8p4se | FLoPS | 5.57 | 5.42 | 7.24 | 6.66 |
| Binary8p3se | FloatLib | 4.79 | 4.99 | 4.91 | 6.31 |
| Binary8p3se | FLoPS | 5.43 | 5.29 | 7.00 | 6.40 |

FloatLib had the lower median in 9 of the 12 format/operation pairs, and its division was about 1.32
to 1.46 times faster on these fixtures. FLoPS had lower medians for four-bit addition,
multiplication, and FMA. Eight-bit FMA was close. For Binary8p3se the 5th to 95th percentile ranges
were 6.29 to 6.47 µs for FloatLib and 6.37 to 6.54 µs for FLoPS, so we wouldn't make much of the
small gap between the medians. Both libraries run software arithmetic with refinement proofs, and
neither hands these operations to a host FPU. FloatLib uses its exact rational P3109 arithmetic,
while FLoPS keeps integer significands and exponents through its dyadic operations, with a
quotient/remainder rounding kernel for division. We built each one with its pinned toolchain, so the
times compare the compiled libraries and their adapters, compiler effects included. FloatLib used
Lean 4.33.1 and Clang 22.1.4, and FLoPS used Lean 4.28.0 and Clang 19.1.2. The retained nine-trial
IEEE and posit tables below use different formats and a different machine.

### Scalar conversions with TensorLib

TensorLib supplies specialized `Float32` conversions [@tensorLib], and we compare them with
FloatLib's general `Model.cast` on four formats. All 128 input/output timing fixtures agree exactly,
and the [broader conversion checks](#/chapter/external-validation/scalar-conversions-with-tensorlib)
cover rounding boundaries and exceptional values too. The entries in the
[results](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/tensorlib/results.json)
are median nanoseconds per conversion across nine paired trials on one logical CPU of the Intel Xeon
Platinum 8275CL. “Encode” converts Float32 to the small format and “decode” converts back.

| Format | FloatLib encode | TensorLib encode | FloatLib decode | TensorLib decode |
| --- | ---: | ---: | ---: | ---: |
| FP16 | 2,201.0 | 265.3 | 2,098.2 | 268.9 |
| BF16 | 2,219.9 | 252.6 | 1,590.0 | 268.3 |
| E4M3FN | 3,642.9 | 279.7 | 2,187.5 | 272.9 |
| E5M2 | 2,248.1 | 267.9 | 2,083.1 | 270.5 |

TensorLib was faster in all eight conversions, by about 5.9 to 13.0 times, so this one is simply a
loss for us :) TensorLib works on the fixed-format fields themselves, while FloatLib's descriptor
cast handles format parameters and uses exact dyadic decoding and rounding. Our timings here use
FloatLib's field-copy widening path, and compatible widenings now go through a [proved word
shift](#/chapter/ieee-binary-formats/casting-between-widths), which this table doesn't measure. For
the normal inputs timed here, TensorLib's casts use integer shifts, masks, and rounding. Its FP16
and FP8 subnormal decoders do use `Float32` multiplication, but this workload never reaches those
branches, so the speedup isn't evidence of an FPU advantage. TensorLib's floating tensor arithmetic
does use native operations, and [the validation
chapter](#/chapter/external-validation/symbolic-arithmetic-and-tensors) explains that execution
choice and FloatLib's optional hardware path. As for the method, both adapters run the same loop
over sixteen normal finite inputs from $-4$ to $4$, excluding zero. Each output picks the next input
and goes into a checksum that we check. We build the input values before timing, and lookup,
conversion, result bits, and checksum bookkeeping are all inside the timer.

Each pair alternates
which library runs first, after 256 warmup iterations. FloatLib used Lean 4.33.1 and TensorLib used
Lean 4.33.0, both with Clang 22.1.4. These are scalar dependent-call timings, and a tensor kernel
that converts many independent elements would be a different workload.

## The nine-trial software comparison

These tables and the optional plots come from an older experiment on an Intel Xeon Platinum 8488C.
It used sixteen rational input sets, and each result chose the next set without becoming the next
operand. Medians are across nine trials pinned to one logical CPU, and the bands show the 5th to
95th percentiles, which aren't confidence intervals. Each timing includes input selection,
representation, adapter work, and checksums. As in the Flocq comparison, FloatLib called proved word
kernels by name at binary32/64 and used public operations under `PlanningThroughput` at other
widths. Its planner ranks certified candidates by configured costs, which isn't the same as picking
the fastest line in a plot. This run used different calling paths, inputs, and toolchains from the
public-call experiment above, so its results describe the version of the library we measured then.
Don't be surprised, then, that binary32 multiplication took 102.0 ns here, on the 8488C, and 17.9 ns
in the public-call experiment on the 8275CL.

| Campaign | Nine-trial software comparison |
| --- | --- |
| Machine | one logical CPU of an Intel Xeon Platinum 8488C |
| Timed calls | FloatLib proved word kernels by name at binary32/64 and public operations at other widths, against SoftFloat, MPFR, native C, CPython, and Universal |
| Inputs | sixteen rational input sets, each result choosing the next set |
| Statistic | median of nine trials, bands at the 5th and 95th percentiles |
| Recorded | September 2026 |
| Record | [results](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/main/README.md) |

### Binary32

All tables report median nanoseconds per operation, and
[Figure 17.4](#/chapter/performance/figure-format-comparison-main) adds the intermediate and wider
formats.

| Implementation | Add | Subtract | Multiply | Divide | Square root | FMA |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| FloatLib | 138.6 | 128.3 | 102.0 | 123.7 | 93.0 | 140.5 |
| Berkeley SoftFloat | 22.9 | 23.1 | 18.2 | 19.6 | 27.8 | 29.2 |
| MPFR | 34.1 | 34.9 | 31.8 | 33.3 | 45.5 | 47.6 |
| Native C | 8.4 | 8.4 | 8.7 | 10.7 | 11.4 | 10.9 |

SoftFloat, MPFR, and native C were each faster than FloatLib on all six operations here. Native C
uses the processor's floating point unit.

### Binary64

| Implementation | Add | Subtract | Multiply | Divide | Square root | FMA |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| FloatLib | 312.8 | 293.5 | 250.7 | 1,447.3 | 1,271.3 | 1,277.2 |
| Berkeley SoftFloat | 23.3 | 23.1 | 18.3 | 29.5 | 30.6 | 29.0 |
| MPFR | 36.7 | 35.4 | 31.9 | 31.3 | 49.2 | 49.4 |
| Native C | 8.2 | 8.2 | 8.5 | 11.6 | 13.1 | 10.7 |
| CPython | 801.3 | 827.3 | 826.0 | 821.9 | 800.1 | n/a |

Against CPython, FloatLib won addition, subtraction, and multiplication but took longer for
division and square root. Python's timings include its runtime, and the version we measured has no
`math.fma`.

### Posits

For posits we compare with Stillwater Universal, which is a different library from
SoftPosit. These are software arithmetic times, again in ns/op.

| Width | Implementation | Add | Subtract | Multiply | Divide | FMA |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| 32 | FloatLib | 311.7 | 284.4 | 288.9 | 482.0 | 352.3 |
| 32 | Universal | 229.1 | 235.7 | 266.5 | 474.2 | 412.4 |
| 64 | FloatLib | 374.2 | 353.8 | 305.1 | 677.8 | 438.6 |
| 64 | Universal | 557.5 | 557.3 | 684.9 | 1,432.1 | 988.5 |
| 4,096 | FloatLib | 5,377.6 | 4,937.7 | 7,254.4 | 11,889.5 | 8,803.7 |
| 4,096 | Universal | 41,447.9 | 41,509.3 | 839,625.2 | 9,757,303.8 | 908,847.7 |

Division was close at 32 bits, where FloatLib took about 1.7% longer. At 64 bits FloatLib was faster
on all five operations shown, and at 4,096 bits multiplication took 7.25 µs versus 839.63 µs, about
116 times faster on these inputs. Universal won at some widths too, as the full curves show. Square
root is a different story. Universal's measured posit square root calls the host square root, so it
gets its own series in the plot to mark that different execution path, and at 32 bits it took 156.0
ns, against FloatLib's 2,489.7 ns for the proved software operation.

<a id="comparing-with-leans-native-floats"></a>

### Host arithmetic as a reference

In the native C column, the host's `float` and `double` arithmetic runs through the same nine-trial
loop. Binary32 addition took 8.36 ns there, against 138.6 ns for FloatLib. At binary64 the times
were 8.20 ns and 312.8 ns, so for addition software was 16.6 and 38.2 times slower than native. That
ratio varied by operation, from 8.1 for binary32 square root to 124.6 for binary64 division, and
[Figure 17.9](#/chapter/performance/figure-ch17-host-vs-software) labels each operation with its
software/native ratio. All of this is measured from C, though. Lean's `Float32` and `Float` wrappers
would need timings of their own, and so would FloatLib's `NativeFPU.Unchecked` functions with their
guards and bit conversions. The [native-floats chapter](#/chapter/lean-native-floats) follows those
interfaces through finite rounding, NaN payloads, and the conditions on a guarded host call.

## More views of the nine-trial comparison

The optional views below show how the same nine-trial times change with operation and width, and
they don't mix in the current public-call or matched Flocq measurements.

<details>
<summary>Overview, ratios, small formats, wide operations, and host comparison</summary>

### Overview across encoded widths

In [Figure 17.4](#/chapter/performance/figure-format-comparison-main), blue squares are FloatLib
binary and green circles are FloatLib posits, both running proved software. Lower is faster, and
both axes are logarithmic. Each marker is a measured encoded width, and the lines connect markers
across kernel changes, with posits starting at 2 bits and binary at 4 bits. We stopped measuring at
4,096 bits, but the library has no limit there. A missing marker means the comparison was
unavailable or excluded, and the [validation
chapter](#/chapter/external-validation/why-some-performance-markers-are-missing) says why.

![Six arithmetic operations across encoded widths from 2 to 4,096 bits; median nanoseconds per operation with 5th to 95th percentile bands](assets/format-comparison-main.png "Median nanoseconds per operation across encoded widths, with 5th to 95th percentile bands. Both axes are logarithmic; lower is faster. Missing markers denote unavailable or excluded comparisons.")

### Comparing relative times

Equal encoded width only means equal storage. A binary format has a fixed significand precision,
while a posit's precision varies with its value, and MPFR uses the binary companion's precision. So
a posit timing and a binary timing at the same width don't imply equal accuracy or equal dynamic
range. The 8-bit binary point, for example, uses an E4M3 layout, and the 4,096-bit point is a
custom binary layout with 19 exponent bits.

![FloatLib time divided by the external implementation's time for addition, multiplication, and division, at equal encoded widths](assets/ch10-external-ratios.png "FloatLib time divided by the comparison library’s time at equal encoded width. Lower is faster for FloatLib relative to that library; 1 means equal times. Different formats still have different numerical contracts.")

[Figure 17.5](#/chapter/performance/figure-ch10-external-ratios) divides FloatLib's time by the
other library's time at equal encoded width, and its horizontal line marks equal time. A ratio of 1
means equal median time, and 10 means FloatLib took ten times as long. Let's compute one point by
hand, say MPFR for binary64 addition, from the two measured medians:

$$
\rho_{\mathrm{MPFR}}
= \frac{312.7723\ \mathrm{ns/op}}{36.6719\ \mathrm{ns/op}}
\approx 8.53.
$$

This experiment divides two medians computed on their own, whereas the public-call experiment takes
the median of within-trial ratios. On the logarithmic axis, equal vertical distances are equal
multiplicative changes. Each ratio compares complete timed loops with different algorithms,
representations, and adapters, so none of them can isolate a cost that comes from verification.

### Why a wider format can be faster

![All six operations from 2 to 16 bits, with each measured width labelled, including 5, 6, and 7 bits](assets/format-comparison-low-width.png "Median nanoseconds per operation at widths 2 to 16, with percentile bands and logarithmic axes. Lower is faster; only measured widths have markers.")

[Figure 17.6](#/chapter/performance/figure-format-comparison-low-width) zooms in on the crowded left
edge of the overview, where 5, 6, and 7 bits each get their own measurement. At these widths table
lookup can be a small part of the total time, because input selection, function calls, and the
checksum still run on every iteration. So the nearly flat stretches of these curves don't mean the
underlying arithmetic has constant cost. Time doesn't grow steadily with width, and square root is
the odd case here. In the binary measurements it took 999.8 ns at 16 bits and 93.0 ns at 32 bits,
where the format has a specialized fixed-format route. A wider format can be faster when the extra
width changes the algorithm and calling path. The timing alone doesn't separate the costs of
dispatch, arithmetic, and representation. FloatLib can use exhaustive
tables, native-word kernels, monomorphic binary32 and binary64 operations, eligible fixed-limb
kernels, or an exact general engine, and which ones are available depends on the operation and
layout as well as on the encoded width. You can ask the current API which implementation it selects.
Its answers describe today's source, though, and don't reconstruct the historical executable we ran
in the nine-trial comparison:

```lean
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 5 10)).name
-- "binary-interchange addition native-word kernel"
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 8 23)).name
-- "binary-interchange addition fixed-format kernel"
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 15 112)).name
-- "binary-interchange addition fixed-limb kernel"
#eval (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 19 236)).name
-- "binary-interchange addition exact baseline"
```

Whichever candidate comes back, [[FloatLib.Floats.ExecFloat.Backend.selectCertified_run_eq_spec]]
ties the selected candidate's result to the specification, and the [planner
walkthrough](#/chapter/backends-and-the-planner/following-a-public-arithmetic-call) follows that
certificate into an ordinary `x + y` call.

### Multiplication, fused operations, and wide arithmetic

![Multiplication and fused multiply-add, with median ns/op and percentile bands across encoded widths](assets/format-comparison-mul-fma.png "Multiplication and fused multiply-add timings across encoded widths. Both axes are logarithmic; bands show the 5th to 95th percentiles and lower is faster.")

Fused multiply-add rounds the exact product-plus-addend once, so its intermediate product can be
wider than the rounded result of an ordinary multiplication.
[Figure 17.7](#/chapter/performance/figure-format-comparison-mul-fma) spreads out the width
dependence you can see in the binary32 and binary64 FMA table entries. CPython 3.11.2 has no
`math.fma` and so no FMA point.

![Division and square root, with median ns/op and percentile bands across encoded widths](assets/format-comparison-div-sqrt.png "Division and square-root timings across encoded widths. Both axes are logarithmic; lower is faster. Universal square roots that disagreed on the benchmark inputs are excluded.")

Look at the right edge of [Figure 17.8](#/chapter/performance/figure-format-comparison-div-sqrt). At
4,096 bits in this nine-trial workload, FloatLib binary division took 10.41 µs against 2.37 µs for
MPFR, a ratio of 4.39, and square root took 40.71 µs against 1.69 µs for MPFR, a ratio of 24.07.
Addition at the same width took 4.26 µs, so wide operations have costs of their own even when they
share the same public representation. On the proved software path, multiword arithmetic is built out
of ordinary machine words, and the generic engine also allocates arbitrary-precision integers. A
planner label doesn't tell you about all of that work. At 256 bits, for instance, the
`ExecFloat.Binary` family selects the exact baseline for both division and square root, but inside
that baseline square root goes through the shared integer-root dispatcher. Here are the selected
candidates:

```lean
#eval (ExecFloat.Div.selectedCandidate (F := ExecFloat.Binary.Family 8 23)).name
-- "binary-interchange division fixed-format kernel"
#eval (ExecFloat.Div.selectedCandidate (F := ExecFloat.Binary.Family 19 236)).name
-- "binary-interchange division exact baseline"
#eval (ExecFloat.Sqrt.selectedCandidate (F := ExecFloat.Binary.Family 19 236)).name
-- "binary-interchange square root exact baseline"
```

Binary32 division has a fixed-format candidate, and both queries at 256 bits report the exact
baseline. If you choose `ExecFloat.BinaryLimbs`, limb-carrier division and square-root candidates
become available, as [chapter 16](#/chapter/backends-and-the-planner/choosing-the-limb-carrier)
shows, though they use a different public representation from the `Binary` queries above. Inside the
generic IEEE path, [bounded
alignment](#/chapter/kernels-fixed-word-algorithms/bounded-alignment-in-generic-addition) limits the
intermediates for well-separated add/sub/FMA operands, and [increasing-precision square
root](#/chapter/kernels-fixed-word-algorithms/increasing-precision-for-arbitrary-precision-square-root)
starts its refinements on a leading portion of the radicand. Neither changes the specified result.
How much time they save depends on the operands, and it has to be measured through the public call,
with decoding, rounding, and result observation included.

### Host arithmetic and software

![Native C and FloatLib proved software at binary32 and binary64; bars show median ns/op and labels show FloatLib/native time ratios](assets/ch17-host-vs-software.png "Median nanoseconds per operation for native C arithmetic and FloatLib software at binary32 and binary64. Lower is faster; annotations give the software/native time ratio.")

</details>

## Method for the nine-trial comparison

<details>
<summary>Timed work, toolchains, adapters, and input agreement</summary>

### What one timed operation includes

We start from sixteen sets of rational inputs, which the adapters convert before timing. Each
arithmetic result picks the next set and goes into a checksum, so later work depends on the
operation being measured. That way the loop can't keep computing a constant, and multiplication or
division can't collapse into a stream of zeros or infinities. Take, say, the first pair in the
[exact
workload](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/lean/FloatLibBenchmarks/Support/ExactWorkload.lean),
$-9/8$ and $-69/35$. At ordinary IEEE widths the first is exactly representable in binary and the
second needs rounding. MPFR converts the rationals themselves, so no earlier binary64 rounding error
gets in, and Universal imports the posit encodings that FloatLib generated from these inputs. All of
this setup happens before the clock starts.

Now let's follow one addition iteration. The loop loads
an already-converted pair, adds it, observes the result, and uses that result to choose the pair for
the next iteration. So the dependency runs through the choice of inputs, since the next operation
can't know which pair to use until the previous result is available, but the result itself never
becomes the next operand. We chose that so the loop keeps drawing from the same sixteen sets,
because otherwise it would drift to a different numerical workload as repeated multiplication grows
a value or repeated division shrinks it.

Each reported ns/op covers input lookup, representation and adapter work, the arithmetic call, and
result observation, and each operation waits for the result before it. So native C's 8.36 ns
addition is more than a hardware add instruction. A loop of independent operations, a vectorized
array kernel, or a workload dominated by subnormals or exceptional values could all compare
differently, and instruction-measurement work such as uops.info [@abelUopsInfo2019] draws the same
line between dependent chains and independent operations. Before timing MPFR, SoftFloat, native C,
and Python, we run 256 operations at each supported binary format and compare checksums with
FloatLib. There are two checksums, one over the results and one over the chosen inputs. We need
both, because a rounding difference can change which input comes next, and two loops that look alike
could end up doing different work. Matching checksums are evidence of agreement on these inputs, but
they don't prove anything about every intermediate result. In the Flocq comparison we go further and
compare complete numerical values.

A fast implementation and a slow one need different loop lengths to give useful measurements, so a
short preliminary run estimates how many iterations will take about 200 ms, and every reported trial
lasts at least 50 ms. We shuffle and rotate the order across nine trials, so the same implementation
doesn't always run first. We report the median and show the 5th to 95th percentiles, and the
underlying data also has quartiles, standard deviation, and median absolute deviation. Most adapters
warm up for 256 iterations. We ran the timing loops one at a time on the same logical CPU, which
rules out migration between CPUs, though other work on the machine can still affect caches and clock
speed.

For the C adapters the compiler was GCC 12.2.0 with `-O3 -march=native`, and FloatLib used
Lean 4.33.1. The external builds are described below. Compilation, process startup, input
construction, warmup, and CSV output happen outside the measured interval, but any allocation or
garbage collection inside the loop counts toward the reported time.

### How we ran the external implementations

Each adapter runs the dependent loop in its library's own representation. MPFR reuses a destination
object, Python creates and observes Python objects, and the Flocq experiment returns structured
values. Whatever that allocation and observation costs stays inside each experiment's measured
loop.

#### MPFR: matching precision and exponent range

GMP, the GNU Multiple Precision Arithmetic Library, provides exact integer and rational arithmetic.
It has `mpf` floating-point numbers too, but those round the requested precision up to whole machine
limbs and truncate final results. MPFR builds on GMP and specifies correctly rounded floating-point
operations, where each result is the exact result rounded to the chosen bit precision and rounding
direction. So MPFR is the closer comparison for FloatLib's floating-point arithmetic
[@gmpFloatingPointManual] [@mpfrManual]. Our MPFR adapter uses MPFR 4.2.0 [@fousseMpfr2007], linked
through `pkg-config`, and its C wrapper was compiled with GCC 12.2.0 and
`-O3 -march=native -std=c11 -Wall -Wextra -Werror`. Those are the wrapper's flags, and they say
nothing about how the installed MPFR and GMP libraries were compiled.

At each width the [MPFR
adapter](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/c/exact_format_mpfr.c) selects
the binary companion's precision and exponent range, so binary32 gets 24 significand bits and
binary64 gets 53. Each input starts as an exact GMP rational and is imported with `mpfr_set_q` under
nearest-even rounding. After conversion and after each arithmetic call, `mpfr_subnormalize` handles
the destination's subnormal range. Precision alone isn't enough, because setting only the precision
would miss the tiny formats' overflow and gradual underflow behavior, which can change which inputs
the loop visits next.

Each timed call is one of `mpfr_add`, `mpfr_sub`, `mpfr_mul`, `mpfr_div`,
`mpfr_sqrt`, or `mpfr_fma`, followed by subnormal handling and a checksum update. We initialize a
result object once per loop invocation and reuse it across iterations. The adapter runs the
256-operation comparison at every measured binary width, and the broader arithmetic checks are in
the validation chapter.

#### SoftFloat, native C, and Python

We used Berkeley SoftFloat at revision `a0c6494`, built `softfloat.a` with the upstream Linux/x86-64
GCC recipe that our [benchmark
driver](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/scripts/format-comparison.sh)
selects, and then linked the [SoftFloat
adapter](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/c/softfloat_ieee.c) with the
same C wrapper flags as MPFR. The library build itself uses the `8086-SSE` specialization and GCC
`-O2`, and the wrapper's `-O3` flag doesn't change that. We time SoftFloat's `f32_*` and `f64_*`
functions, fused `mulAdd` included, with nearest-even rounding and tininess detected after rounding.
Input conversion happens before timing, and the 256-operation comparison covers both binary32 and
binary64.

Our native adapter uses C `float` and `double`, with `sqrtf`/`sqrt` and `fmaf`/`fma` for
the corresponding operations. It's built with the same GCC wrapper flags, without `-ffast-math`, and
joins the same agreement check. It measures the host arithmetic through a C loop, which leaves out
Lean's native-float wrapper and FloatLib's guarded host API. Before timing, it checks the host
representation and nearest-even rounding mode, and it compares all sixteen input results with MPFR.
No check in the benchmark record targets the host's flush-to-zero controls.

For Python we use
CPython 3.11.2 at binary64. Its timer wraps the Python loop, so interpreter dispatch, object
handling, input selection, and checksum work all count, and the inputs are prepared first. This
interpreter has no `math.fma`, so there's no FMA point, and writing `x * y + z` instead would round
twice. Its other five operations join the binary64 agreement check.

#### Universal: checking the posit inputs before timing

We used Stillwater Universal [@stillwaterUniversal] at revision `26e69f5`, compiling a C++20 adapter
for each width with GCC 12.2.0 and `-O3 -march=native -Wall -Wextra -Werror`. Before it times an
operation at a given width, the adapter compares all sixteen results with the result words FloatLib
generated. It imports the input words into `posit<width, 2, uint64_t>` as they are, without routing
them through a host float. Only when all sixteen results agree do we time it.

Of the 78
operation-and-width combinations, 71 agreed, and square root differed at every measured width from
64 through 4,096 bits. We left out widths below five because of Universal's generic `es=2` FMA
constraint. The [validation chapter](#/chapter/external-validation) lists the accepted and differing
results, so every missing marker has an explanation: an unsupported width or a numerical
disagreement, never zero time. Universal's configurations that convert through binary64 for host
square root get their own series, apart from its software arithmetic. Agreement on these inputs is
evidence for this workload, but it isn't an exhaustive posit conformance result.

</details>

<a id="which-libraries-did-we-time"></a>

## Correctness comparisons without timings

For SoftPosit we only compared result bits and never timed the arithmetic of either library on its
own. That comparison's total runtime includes preparing the inputs, running both libraries, and
comparing their answers, so dividing it by the case count wouldn't tell you which library was
faster. Berkeley's tools need the same distinction: TestFloat generates correctness tests, and
SoftFloat is the arithmetic library timed above. The ONNX and P3109 table checks compare encodings,
while the P3109 arithmetic timings use FLoPS's executable kernel. Those checks are explained in the
[validation chapter](#/chapter/external-validation), and the [posit
chapter](#/chapter/posits-and-the-quire/cross-checks-against-universal-and-softposit) works through
the seven distinct SoftPosit inputs behind the reported differences.

## Reproducing the measurements

If you'd like to reproduce the retained nine-trial measurements, the [benchmark
method](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/docs/Comparison.md) and
[results](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/main/README.md) give
you the commands, toolchains, measured sources, and raw trials. The Flocq, P3109, and TensorLib
sections each link their own records, and the current public-call record comes next.

<a id="public-binary-measurement-record"></a>

<details>
<summary>Public binary measurement record</summary>

For the public-call runs, the
[measurements](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/public-binary/measurements.csv)
keep each trial, its execution order, iteration count, elapsed nanoseconds, and the checked
warmup/result sinks, and a compact
[metadata](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/public-binary/metadata.json)
file records the measured build, format layouts, and CPU affinity. On the external arm we use MPFR
4.1.0-p13 with GMP 6.2.1. Width means encoded storage, so the wide plot's significand precisions are
24, 53, 113, 237, 493, 1,005, 2,029, and 4,077 bits, while binary16 has 11 significand bits and
bfloat16 has 8. The smaller layouts are labelled by their stored exponent and fraction widths, and
in every case MPFR matches the format's precision and exponent range. We calibrate iteration counts
per arm toward 40 ms and then hold them fixed across three trials, with 512 warmup calls. Each timed
count covers whole sixteen-input cycles. None of the plotted trials is shorter than 36.2 ms, and
recorded CPU-quota throttling is zero. Parsing, input construction, full-encoding checks, warmup,
and process startup all come before timing, while allocation and result observation inside the loop
are included. Speed ratios use the median of paired trial ratios, and plotted times use each arm's
median.

For the 84 plotted format/operation cases, the [fixture archive](assets/public-binary-fixtures.zip)
holds the exact encoded input triples, the expected complete outputs, and the retained full-encoding
agreement receipts. To compare a FloatLib checkout with MPFR yourself, use the [benchmark
bundle](assets/public-binary-benchmark.tar.gz), which has the driver, prepared inputs, and
instructions. Its broader encoding checks also cover custom widths, rounding boundaries, large
exponent gaps, and limb storage. Running the [figure
script](https://github.com/lean-dojo/FloatLib/blob/main/site/content/assets/figures/ch15_public_binary.py)
checks the retained data and regenerates both PNGs:

```bash
python3 site/content/assets/figures/ch15_public_binary.py
```

That command rebuilds the figures from the recorded measurements, but it doesn't rerun the
benchmark.

</details>
