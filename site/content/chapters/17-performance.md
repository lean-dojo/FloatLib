---
number: "17"
slug: performance
title: "Performance"
summary: "Measure ordinary public binary arithmetic against MPFR, then compare other libraries on their separate workloads."
phases: [trust]
---

On ordinary public calls, binary64 multiplication takes 11.2 ns in FloatLib and 27.0 ns in MPFR at the same precision and exponent range, so the proved software is about 2.4 times faster. Binary64 addition and subtraction are about 1.5 times faster too, and of the 84 format and operation pairs we time from 7 to 4,096 bits, FloatLib is faster in 25. We measured the FloatLib 2.0.0 release on 2026-10-31, after the October 2026 speed work described below. We haven't timed FloatLib 3.0.0 itself. Comparing the code Lean generates for both releases, we found the same arithmetic on every path that the comparisons with MPFR, Flocq, SoftFloat, Universal, FLoPS, and TensorLib time. The changes there are erased proof arguments, renamed parameters, and documentation, and the compiled code differs in small details such as instruction order.

Lean erases proof terms during compilation [@leanReference], so the timed program executes arithmetic, representation conversions, and dispatch, and none of the times below includes proof checking.

<a id="timing-results"></a>

## Public binary arithmetic

We time ordinary public `ExecFloat.Binary` calls, including the configured representation and the
selected software kernel. MPFR gets the same precision, exponent bounds, and nearest-even rounding
with gradual underflow. Each point
cycles through sixteen prepared input triples, and we check their full encodings before timing
starts. Inside the loop we call the operation and checksum the low 64 result bits, and that checksum
never picks the next input.

We ran nine trials one after another on the same pinned CPU of an Intel Xeon Platinum 8275CL, a
machine shared with other work, and alternated which library ran first. Each plotted time is that
arm's median, and each ratio is the median of the nine within-trial FloatLib/MPFR ratios. The
whiskers show the observed minimum and maximum. They aren't confidence intervals, so we wouldn't
read much into small differences.

| Campaign | Public calls against MPFR |
| --- | --- |
| Machine | one pinned CPU of an Intel Xeon Platinum 8275CL, shared with other work |
| Timed calls | FloatLib's public binary operations, and MPFR 4.1.0-p13 with the same precision and exponent bounds |
| Inputs | sixteen prepared input triples per point, full encodings checked before timing |
| Statistic | median of nine trials, whiskers at the observed minimum and maximum |
| Recorded | 2026-10-31, on the 2.0.0 release |
| Record | [measurements, metadata, and fixtures](#/chapter/performance/public-binary-measurement-record) |

![FloatLib and MPFR for six public binary operations at encoded widths 32 through 4096](assets/public-binary-performance.png "Median nanoseconds per operation across nine trials, with whiskers at the observed minimum and maximum, which aren't confidence intervals. Both axes are logarithmic, and lower is faster.")

In [Figure 17.1](#/chapter/performance/figure-public-binary-performance), look at the 32-bit and
64-bit points, where FloatLib's marker sits below MPFR's in most panels. Binary64 addition took
17.1 ns against 25.5 ns in MPFR, subtraction 17.0 against 25.9 ns, and multiplication 11.2 against
27.0 ns. At binary32, multiplication took 20.7 ns against 27.5 ns, square root 17.7 against 30.4
ns, and FMA 33.4 against 43.4 ns, and subtraction was slightly faster too. Binary32 addition was
close, at 1.07 times MPFR's time.

MPFR keeps its lead in division at both widths, where FloatLib took 1.38 times MPFR's time for
binary32 and 1.83 times for binary64. Binary64 square root and FMA took 94.9 and 113.4 ns, 3.21 and 2.40 times
MPFR's time. Binary128 stores each value in two machine words, and its multiplication took 38.8 ns
against 31.2 ns in MPFR, about 1.25 times MPFR's time. Its FMA took 1.78 times MPFR's time, and its
addition, subtraction, division, and square root 2.5 to 5.7 times.

From 256 bits up every operation selects the exact baseline, which computes with
arbitrary-precision integers, and the gaps are largest there. At 256 bits addition took 45.8 times
MPFR's time and multiplication 29.0 times. At 4,096 bits, division took 4.58 µs, about 2.15
times MPFR's time, while multiplication took about 3.27 times MPFR's time and FMA about 2.74 times.
Addition and square root left larger gaps, at about 20.7 and 7.89 times MPFR's time respectively.

![FloatLib and MPFR for six public binary operations below 32 bits](assets/public-binary-low-precision.png "Median nanoseconds per operation across nine trials, with whiskers at the observed minimum and maximum. The vertical axis is logarithmic, and lower is faster.")

Below 32 bits, [Figure 17.2](#/chapter/performance/figure-public-binary-low-precision) adds
binary16, bfloat16, and four layouts from 7 to 9 bits, which use IEEE-style encodings with
infinities and NaNs. Binary16, bfloat16, and the 9-bit E4M4 layout are where FloatLib does best,
and each was faster than MPFR in five of the six operations. Binary16 multiplication took 12.3 ns
versus 28.7 ns for MPFR, about 2.3 times faster, and binary16 FMA took 21.2 ns versus 43.7 ns.
Bfloat16 multiplication took 11.5 ns versus 27.4 ns. Division was the exception in these three
formats, at 1.66 to 1.74 times MPFR's time.

Which kernel gets selected matters as much as the width. Square root in the 7-bit and 8-bit
formats uses exhaustive tables and took 23 to 26 ns, a little faster than MPFR's 28 to 30 ns. The
other operations in those formats are the slowest points in the figure. Addition, subtraction,
multiplication, and division took 122 to 618 ns, against 23 to 33 ns for MPFR. The 8-bit layouts
select kernels with the same names as the 9-bit layout's native-word kernels, which take 11 to 54
ns there, but they store each value in one byte instead of a 16-bit word. We haven't established what causes
that gap. FMA has no table at these
widths, because a table of every input triple would need 2 MiB at 7 bits and 16 MiB at 8 bits,
above the default policy's 1 MiB limit. So FMA runs the exact baseline and took about 1.2 µs.

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

In October 2026 we made three changes, and the 2.0.0 code measured above includes all of them. We
stored binary128 values as two native words and gave its six operations kernels that work on those
words. We also specialized the model-path operations to their format, and we cached the constants
of the elementary functions.

We had run the public-call experiment once before, on the same CPU model with the same fixtures and
the same MPFR version. MPFR's times agree between the two runs, with a median ratio of 1.003, so the
differences are FloatLib's, and they're large. Binary128 addition went from 1,907.5 ns to 75.5 ns,
multiplication from 899.1 to 38.8 ns, and FMA from 2,364.1 to 138.0 ns. Part of that binary128 gain
is in observing the result, because the driver now reads the low storage word where it used to
convert the proof model to bits. Binary64 multiplication
went from 239.2 to 11.2 ns, binary64 square root from 1,338.2 to 94.9 ns, and binary16 square root
from 1,291.7 to 26.1 ns. FloatLib was faster than MPFR in 14 of the 84 pairs in the earlier run and
is in 25 now. Those differences include every change between the two runs, the move from Lean
4.34.0 to 4.35.0 among them, so the table below times the October changes on their own workloads,
each against the tree just before it.

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
and bfloat16 went from 1,300.8 and 1,279.8 ns down to 24.4 and 22.1 ns, close to the 26.1 and 22.9
ns of the public calls above. Binary64 FMA went from 1,028.9 and 2,551.4 ns to 119.4 and 145.8 ns
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

![FloatLib, extracted Flocq, and MPFR across eleven matching binary formats and six operations](assets/flocq-matched.png "Median nanoseconds per operation across nine trials at matching binary precision and exponent bounds. Both axes are logarithmic, and lower is faster. Measurements ran on an Intel Xeon Platinum 8275CL.")

The measured widths in [Figure 17.3](#/chapter/performance/figure-flocq-matched) run from 6 to 4,096
bits, and FloatLib beat the extracted Flocq program in 65 of the 66 entries, by a median factor of
52. The gap grows with width. For binary64 multiplication, FloatLib took 328 ns and Flocq took
10,735 ns, and at 4,096 bits square root took 14.1 µs in FloatLib and 1.37 s in Flocq. The one loss
is 8-bit FMA, where Flocq took 886 ns and FloatLib took 1,335 ns, because FMA has no table at 8
bits and runs the exact baseline. MPFR was faster than FloatLib at every point in this comparison,
by a median factor of 6.3, and came closest at binary128 multiplication, with 37.1 ns against 43.3
ns. During timing, each operation and width drew from sixteen input sets.

We ran it on an Intel Xeon Platinum 8275CL with nine trials per entry, and each plotted time is the
median of the nine. These dependent scalar loops include input selection, allocation, and
observing the result. They also call FloatLib differently from the ordinary public calls above,
because at binary32/64 FloatLib calls the configured word kernels by name, and at other widths it
uses public operations under `PlanningThroughput`. Up to 64 bits the loop also normalizes each
result into a fingerprint, while wider results contribute their low word. Both differences favor
the wider format here, and binary128 multiplication took 43.3 ns against 328 ns at binary64.

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
| Binary4p2sf | FloatLib | 3.93 | 4.00 | 3.96 | 5.38 |
| Binary4p2sf | FLoPS | 4.29 | 4.24 | 5.77 | 5.22 |
| Binary8p4se | FloatLib | 4.44 | 4.49 | 4.52 | 6.03 |
| Binary8p4se | FLoPS | 5.59 | 5.53 | 7.25 | 6.68 |
| Binary8p3se | FloatLib | 4.37 | 4.54 | 4.49 | 5.84 |
| Binary8p3se | FLoPS | 5.46 | 5.33 | 7.12 | 6.51 |

FloatLib had the lower median in 11 of the 12 format/operation pairs, and its division was about
1.46 to 1.60 times faster on these fixtures. The one loss is four-bit FMA, where FloatLib took 5.38
µs and FLoPS 5.22 µs. The 5th to 95th percentile ranges of FloatLib and FLoPS don't overlap in any
of the twelve pairs, so the small four-bit FMA gap is as consistent as the wins. Both libraries run
software arithmetic with refinement proofs, and neither hands these operations to a host FPU.
FloatLib uses its exact rational P3109 arithmetic, while FLoPS keeps integer significands and
exponents through its dyadic operations, with a quotient/remainder rounding kernel for division. We
built each one with its pinned toolchain, so the times compare the compiled libraries and their
adapters, compiler effects included. FloatLib used Lean 4.35.0 and Clang 23.1.0, and FLoPS used
Lean 4.28.0 and Clang 19.1.2. The nine-trial IEEE and posit tables below use different formats and
a different loop.

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
| FP16 | 2,034.5 | 281.8 | 2,103.4 | 272.9 |
| BF16 | 2,033.1 | 268.9 | 1,087.8 | 274.4 |
| E4M3FN | 3,555.5 | 284.2 | 2,226.7 | 278.2 |
| E5M2 | 2,075.1 | 282.6 | 2,106.9 | 276.2 |

TensorLib was faster in all eight conversions, by about 4.0 to 12.5 times, so this one is simply a
loss for us :) TensorLib works on the fixed-format fields themselves, while FloatLib's descriptor
cast handles format parameters and uses exact dyadic decoding and rounding. Decoding BF16 is a
compatible widening, which goes through a [proved word
shift](#/chapter/ieee-binary-formats/casting-between-widths), and at 1,087.8 ns it's FloatLib's
fastest conversion here, about four times TensorLib's 274.4 ns. For
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
which library runs first, after 256 warmup iterations. FloatLib used Lean 4.35.0 with Clang 23.1.0,
and TensorLib used Lean 4.33.0 with Clang 22.1.4. These are scalar dependent-call timings, and a tensor kernel
that converts many independent elements would be a different workload.

## The nine-trial software comparison

These tables and the optional plots come from a second experiment on the same CPU model, an Intel
Xeon Platinum 8275CL, which we also ran on the 2.0.0 release on 2026-10-31. It used sixteen
rational input sets, and each result chose the next set without becoming the next operand. Medians
are across nine trials pinned to one logical CPU, and the bands show the 5th to 95th percentiles,
which aren't confidence intervals. Each timing includes input selection, representation, adapter
work, and checksums. As in the Flocq comparison, FloatLib called the configured word kernels by name
at binary32/64 and used public operations under `PlanningThroughput` at other widths. Its planner
ranks certified candidates by configured costs, which isn't the same as picking the fastest line in
a plot. Public binary64 calls try direct word kernels before those named kernels, and up to 64 bits
this loop also normalizes every binary result into a fingerprint. So binary32 multiplication took
100.6 ns here and 20.7 ns in the public-call experiment on the same CPU model, and the public-call
figures are the ones to use for binary32 and binary64 speed.

| Campaign | Nine-trial software comparison |
| --- | --- |
| Machine | one logical CPU of an Intel Xeon Platinum 8275CL, shared with other work |
| Timed calls | FloatLib's configured word kernels by name at binary32/64 and public operations at other widths, against SoftFloat, MPFR, native C, CPython, and Universal |
| Inputs | sixteen rational input sets, each result choosing the next set |
| Statistic | median of nine trials, bands at the 5th and 95th percentiles |
| Recorded | 2026-10-31, on the 2.0.0 release |
| Record | [results](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/main/README.md) |

### Binary32

All tables report median nanoseconds per operation, and
[Figure 17.4](#/chapter/performance/figure-format-comparison-main) adds the intermediate and wider
formats.

| Implementation | Add | Subtract | Multiply | Divide | Square root | FMA |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| FloatLib | 162.2 | 143.0 | 100.6 | 150.3 | 87.2 | 150.6 |
| Berkeley SoftFloat | 23.0 | 22.8 | 17.6 | 25.1 | 25.7 | 27.0 |
| MPFR | 34.0 | 35.7 | 34.9 | 36.5 | 40.9 | 55.5 |
| Native C | 8.5 | 8.5 | 8.5 | 10.4 | 10.6 | 8.8 |

SoftFloat, MPFR, and native C were each faster than FloatLib's named word kernels on all six
operations in this loop. Native C uses the processor's floating point unit.

### Binary64

| Implementation | Add | Subtract | Multiply | Divide | Square root | FMA |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| FloatLib | 389.4 | 346.3 | 332.3 | 400.3 | 167.1 | 494.5 |
| Berkeley SoftFloat | 22.1 | 21.6 | 17.8 | 33.5 | 27.6 | 27.2 |
| MPFR | 37.4 | 36.2 | 32.6 | 34.3 | 46.0 | 60.6 |
| Native C | 8.3 | 8.3 | 8.4 | 11.3 | 12.5 | 8.6 |
| CPython | 1,493.5 | 1,503.9 | 1,482.8 | 1,728.6 | 1,493.0 | n/a |

Against CPython, FloatLib won all five operations that CPython provides. Python's timings include
its runtime, and the version we measured has no `math.fma`.

### Posits

For posits we compare with Stillwater Universal, which is a different library from
SoftPosit. These are software arithmetic times, again in ns/op.

| Width | Implementation | Add | Subtract | Multiply | Divide | FMA |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| 32 | FloatLib | 121.3 | 152.4 | 114.7 | 274.7 | 141.6 |
| 32 | Universal | 289.7 | 298.6 | 331.4 | 629.5 | 473.0 |
| 64 | FloatLib | 123.5 | 126.9 | 162.8 | 362.3 | 244.2 |
| 64 | Universal | 633.4 | 905.4 | 842.7 | 2,010.8 | 1,154.1 |
| 4,096 | FloatLib | 6,341.8 | 5,953.6 | 8,086.1 | 12,165.1 | 10,024.4 |
| 4,096 | Universal | 41,296.8 | 42,112.2 | 985,340.8 | 13,222,078.2 | 1,052,650.8 |

FloatLib was faster on all five operations at 32 and 64 bits, and in 56 of the 65 software cells
overall. At 4,096 bits multiplication took 8.09 µs versus 985.34 µs, about 122 times faster on these
inputs, and division took 12.17 µs versus 13.22 ms, about 1,087 times faster. From 5 to 8 bits the
operations other than FMA use exhaustive tables at about 21 ns and run 1.9 to 4.8 times faster than
Universal. Universal won the other nine cells. Four are FMA at 5 to 8 bits, where the planner chose FloatLib's packed-word
fused accumulation over the available ternary tables by its cost estimate, and it took 113 to 130 ns
against 66 to 103 ns. Then come 16-bit division, at 276 against 167 ns, and 128-bit FMA, at 4.90 against 2.88 µs.
The last three are 256-bit addition and subtraction and 512-bit addition, where FloatLib's
exact-dyadic sum took 4.4 to 5.4 µs. Square root is a different story. Universal's measured posit
square root calls the host square root, so it gets its own series in the plot to mark that
different execution path. At 16 bits it took 88.7 ns against FloatLib's 212.8 ns, and at 32 bits
172.2 ns against 271.6 ns for the proved software operation, while from 5 to 8 bits FloatLib's
tables were 2.65 to 3.45 times faster.

<a id="comparing-with-leans-native-floats"></a>

### Host arithmetic as a reference

In the native C column, the host's `float` and `double` arithmetic runs through the same nine-trial
loop. Binary32 addition took 8.50 ns there, against 162.2 ns for FloatLib's named word kernel. At
binary64 the times were 8.33 ns and 389.4 ns, so for addition this loop ran software 19.1 and 46.7
times slower than native. That ratio varied by operation, from 8.2 for binary32 square root to 57.2
for binary64 FMA, and
[Figure 17.9](#/chapter/performance/figure-ch17-host-vs-software) labels each operation with its
software/native ratio. All of this is measured from C, though. We haven't timed Lean's `Float32` and `Float`
wrappers or FloatLib's `NativeFPU.Unchecked` functions, whose guards and bit conversions add work of
their own. The [native-floats chapter](#/chapter/lean-native-floats) follows those
interfaces through finite rounding, NaN payloads, and the conditions on a guarded host call.

## More views of the nine-trial comparison

The optional views below show how the same nine-trial times change with operation and width, and
they don't mix in the public-call or matched Flocq measurements.

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

![Six arithmetic operations across encoded widths from 2 to 4,096 bits, as median nanoseconds per operation with 5th to 95th percentile bands](assets/format-comparison-main.png "Median nanoseconds per operation across encoded widths, with 5th to 95th percentile bands. Both axes are logarithmic, and lower is faster. Missing markers denote unavailable or excluded comparisons.")

### Comparing relative times

Equal encoded width only means equal storage. A binary format has a fixed significand precision,
while a posit's precision varies with its value, and MPFR uses the binary companion's precision. So
a posit timing and a binary timing at the same width don't imply equal accuracy or equal dynamic
range. The 8-bit binary point, for example, uses an E4M3 layout, and the 4,096-bit point is a
custom binary layout with 19 exponent bits.

![FloatLib time divided by the external implementation's time for addition, multiplication, and division, at equal encoded widths](assets/ch10-external-ratios.png "FloatLib time divided by the comparison library’s time at equal encoded width. Lower is faster for FloatLib relative to that library, and 1 means equal times. Different formats have different numerical contracts.")

[Figure 17.5](#/chapter/performance/figure-ch10-external-ratios) divides FloatLib's time by the
other library's time at equal encoded width, and its horizontal line marks equal time. A ratio of 1
means equal median time, and 10 means FloatLib took ten times as long. Let's compute one point by
hand, say MPFR for binary64 addition, from the two measured medians:

$$
\rho_{\mathrm{MPFR}}
= \frac{389.4485\ \mathrm{ns/op}}{37.4140\ \mathrm{ns/op}}
\approx 10.41.
$$

This experiment divides two medians computed on their own, whereas the public-call experiment takes
the median of within-trial ratios. On the logarithmic axis, equal vertical distances are equal
multiplicative changes. Each ratio compares complete timed loops with different algorithms,
representations, and adapters, so none of them can isolate a cost that comes from verification.

### Why a wider format can be faster

![All six operations from 2 to 16 bits, with each measured width labelled, including 5, 6, and 7 bits](assets/format-comparison-low-width.png "Median nanoseconds per operation at widths 2 to 16, with percentile bands and logarithmic axes. Lower is faster, and only measured widths have markers.")

[Figure 17.6](#/chapter/performance/figure-format-comparison-low-width) zooms in on the crowded left
edge of the overview, where 5, 6, and 7 bits each get their own measurement. At these widths table
lookup can be a small part of the total time, because input selection, function calls, and the
checksum still run on every iteration. So the nearly flat stretches of these curves don't mean the
underlying arithmetic has constant cost. Time doesn't grow steadily with width either. In the
binary measurements addition took 389.4 ns at 64 bits and 83.4 ns at 128 bits. At 128 bits the
planner selects the two-word kernels and the loop reads the result's low word, while at 64 bits
this experiment calls the configured word kernel by name and normalizes the result. A wider format
can be faster when the extra width changes the algorithm and calling path. The timing alone doesn't separate the costs of
dispatch, arithmetic, and representation. FloatLib can use exhaustive
tables, native-word kernels, monomorphic binary32 and binary64 operations, eligible fixed-limb
kernels, or an exact general engine, and which ones are available depends on the operation and
layout as well as on the encoded width. You can ask the API which implementation it selects. At
binary32 and binary64 the nine-trial comparison bypasses that selection by naming its kernels, and
at the other widths below the answers match the backends it recorded:

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

![Multiplication and fused multiply-add, with median ns/op and percentile bands across encoded widths](assets/format-comparison-mul-fma.png "Multiplication and fused multiply-add timings across encoded widths. Both axes are logarithmic, bands show the 5th to 95th percentiles, and lower is faster.")

Fused multiply-add rounds the exact product-plus-addend once, so its intermediate product can be
wider than the rounded result of an ordinary multiplication.
[Figure 17.7](#/chapter/performance/figure-format-comparison-mul-fma) spreads out the width
dependence you can see in the binary32 and binary64 FMA table entries. CPython 3.12.13 has no
`math.fma` and so no FMA point.

![Division and square root, with median ns/op and percentile bands across encoded widths](assets/format-comparison-div-sqrt.png "Division and square-root timings across encoded widths. Both axes are logarithmic, and lower is faster. Universal square roots that disagreed on the benchmark inputs are excluded.")

Look at the right edge of [Figure 17.8](#/chapter/performance/figure-format-comparison-div-sqrt). At
4,096 bits in this nine-trial workload, FloatLib binary division took 4.45 µs against 2.41 µs for
MPFR, a ratio of 1.85, and square root took 13.94 µs against 1.91 µs for MPFR, a ratio of 7.30.
Addition at the same width took 2.36 µs, so wide operations have costs of their own even when they
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

![Native C and FloatLib proved software at binary32 and binary64, with bars at median ns/op and labels giving FloatLib/native time ratios](assets/ch17-host-vs-software.png "Median nanoseconds per operation for native C arithmetic and FloatLib software at binary32 and binary64. Lower is faster, and annotations give the software/native time ratio.")

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
result observation, and each operation waits for the result before it. So native C's 8.33 ns
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
lasts at least 50 ms. The one exception is MPFR's 1,024-bit addition, where the preliminary run
overestimated the cost per operation and four of the nine trials lasted 49.1 to 49.7 ms. We shuffle and rotate the order across nine trials, so the same implementation
doesn't always run first. We report the median and show the 5th to 95th percentiles, and the
underlying data also has quartiles, standard deviation, and median absolute deviation. Most adapters
warm up for 256 iterations. We ran the timing loops one at a time on the same logical CPU, which
rules out migration between CPUs, though other work on the machine can affect caches and clock
speed.

For the C adapters the compiler was GCC 11.5.0 with `-O3 -march=native`, and FloatLib used
Lean 4.35.0. The external builds are described below. Compilation, process startup, input
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
[@gmpFloatingPointManual] [@mpfrManual]. Our MPFR adapter uses MPFR 4.1.0 [@fousseMpfr2007], linked
through `pkg-config`, and its C wrapper was compiled with GCC 11.5.0 and
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
CPython 3.12.13 at binary64. Its timer wraps the Python loop, so interpreter dispatch, object
handling, input selection, and checksum work all count, and the inputs are prepared first. This
interpreter has no `math.fma`, so there's no FMA point, and writing `x * y + z` instead would round
twice. Its other five operations join the binary64 agreement check.

#### Universal: checking the posit inputs before timing

We used Stillwater Universal [@stillwaterUniversal] at revision `26e69f5`, compiling a C++20 adapter
for each width with GCC 11.5.0 and `-O3 -march=native -Wall -Wextra -Werror`. Before it times an
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
sections each link their own records, and the public-call record comes next.

<a id="public-binary-measurement-record"></a>

<details>
<summary>Public binary measurement record</summary>

For the public-call runs, the
[measurements](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/public-binary/measurements.csv)
keep each trial, its execution order, iteration count, elapsed nanoseconds, and the checked
warmup/result sinks, and a compact
[metadata](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/public-binary/metadata.json)
file records the measured build, format layouts, and CPU affinity. We built the 2.0.0 release with
Lean 4.35.0 and Mathlib `56a00585`, and on the external arm we use MPFR 4.1.0-p13 with GMP 6.2.1. Width means encoded storage, so the wide plot's significand precisions are
24, 53, 113, 237, 493, 1,005, 2,029, and 4,077 bits, while binary16 has 11 significand bits and
bfloat16 has 8. The smaller layouts are labelled by their stored exponent and fraction widths, and
in every case MPFR matches the format's precision and exponent range. We calibrate iteration counts
per arm toward 40 ms and then hold them fixed across nine trials, with 512 warmup calls. Each timed
count covers whole sixteen-input cycles. Some trials ran faster than their calibration, so 99 of
the 1,512 timed intervals are shorter than 36 ms. The shortest lasted 22.2 ms and the median 40.1
ms, and recorded CPU-quota throttling is zero. Parsing, input construction, full-encoding checks, warmup,
and process startup all come before timing, while allocation and result observation inside the loop
are included. Speed ratios use the median of paired trial ratios, and plotted times use each arm's
median.

For the 84 plotted format/operation cases, the [fixture archive](assets/public-binary-fixtures.zip)
holds the exact encoded input triples, the expected complete outputs, and the retained full-encoding
agreement receipts. To compare a FloatLib checkout with MPFR yourself, use the [benchmark
bundle](assets/public-binary-benchmark.tar.gz), which has the driver we ran, prepared inputs, and
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
