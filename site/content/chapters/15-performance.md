---
number: "15"
slug: performance
title: "Performance and native floats"
summary: "We time arithmetic from 2 to 4,096 bits and compare FloatLib with other software libraries and native floats."
phases: [trust]
---

Our performance goal is to reach MPFR's speed with proved arithmetic.

64-bit posit multiplication took **305 ns in FloatLib and 685 ns in Universal**.
That's a good result for our software kernels. Binary32 addition gives us more work to do:
138.6 ns in FloatLib, 22.9 ns in Berkeley SoftFloat, and 34.1 ns in MPFR.
Looking at the individual operations tells us much more than one score for the whole library.

Blue squares are FloatLib binary and green circles are FloatLib posits; the grey diamonds
are an extracted Flocq precision model. Lower means faster. Both FloatLib curves run proved software. Lean
erases proof terms during compilation [@leanReference], so a call executes the arithmetic
without checking the theorem again. The relative times reflect the algorithms, representations,
and calling paths. They do not measure the time needed to prove the operations.

These curves use FloatLib's default policy and carriers. Binary32 and binary64 already
run their fixed-format software kernels. The planner ranks certified candidates using
cost estimates; it does not choose the fastest line in this plot. MPFR and SoftFloat
are external comparisons, and the native C line measures the host FPU. Users can
[change the planning policy, choose limb storage, or explicitly call the host path](#/chapter/backends-and-the-planner/what-can-i-choose).

![Six arithmetic operations across encoded widths from 2 to 4,096 bits; median nanoseconds per operation with 5th to 95th percentile bands](assets/format-comparison-main.png "Median nanoseconds per operation across encoded widths, with 5th to 95th percentile bands. Both axes are logarithmic; lower is faster. Missing markers denote unavailable or excluded comparisons.")

Read [Figure 15.1](#/chapter/performance/figure-format-comparison-main) one operation at a time.
It shows nine trials for each operation and width on an **Intel Xeon Platinum 8488C**,
keeping the timing process on one logical CPU. Both axes are logarithmic. Each marker is a measured encoded
width; lines connect those markers, including transitions between FloatLib kernels. The bands
show the 5th to 95th percentiles across trials, not confidence intervals. FloatLib posit starts at
2 bits and binary at 4 bits. The measurements stop at 4,096 bits; that is the largest width measured
here, not a library limit.

The starred Flocq series needs particular care: our adapter matches significand precision,
but uses different exponent limits and can construct different inputs at small widths.
We did not check that it visited the same sequence of inputs as FloatLib. The
[external benchmark method](#/chapter/performance/how-we-ran-the-external-implementations)
below works through a concrete example and explains what each comparison measures.

<a id="the-times-behind-the-curves"></a>

## Timing results

Here are the ordinary 32-bit and 64-bit binary formats first. Every entry is a
**median in nanoseconds per operation** across nine trials. Lower is
faster. These times include the benchmark's input selection, representation, adapter,
and checksum work, as well as the arithmetic call.

### Binary32

| Implementation | Add | Subtract | Multiply | Divide | Square root | FMA |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| **FloatLib** | **138.6** | **128.3** | **102.0** | **123.7** | **93.0** | **140.5** |
| Berkeley SoftFloat | 22.9 | 23.1 | 18.2 | 19.6 | 27.8 | 29.2 |
| MPFR | 34.1 | 34.9 | 31.8 | 33.3 | 45.5 | 47.6 |
| Extracted Flocq\* | 1,128.0 | 1,108.1 | 1,709.7 | 1,427.0 | 7,485.3 | 2,615.3 |
| Native C | 8.4 | 8.4 | 8.7 | 10.7 | 11.4 | 10.9 |

FloatLib is faster than this extracted Flocq program on all six operations here;
SoftFloat, MPFR, and native C are faster than FloatLib on all six. The asterisk marks a
contextual comparison: Flocq's extracted
program models the significand precision, without reproducing all of binary32's
exponent limits and exceptional behavior. Native C uses the processor's floating
point unit.

### Binary64

| Implementation | Add | Subtract | Multiply | Divide | Square root | FMA |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| **FloatLib** | **312.8** | **293.5** | **250.7** | **1,447.3** | **1,271.3** | **1,277.2** |
| Berkeley SoftFloat | 23.3 | 23.1 | 18.3 | 29.5 | 30.6 | 29.0 |
| MPFR | 36.7 | 35.4 | 31.9 | 31.3 | 49.2 | 49.4 |
| Extracted Flocq\* | 2,201.0 | 2,155.7 | 6,617.5 | 3,037.4 | 34,460.3 | 10,113.8 |
| Native C | 8.2 | 8.2 | 8.5 | 11.6 | 13.1 | 10.7 |
| CPython | 801.3 | 827.3 | 826.0 | 821.9 | 800.1 | n/a |

Against CPython, FloatLib wins addition, subtraction, and multiplication, but takes
longer for division and square root. The Python timings include its runtime; the
version measured has no `math.fma`. The Flocq precision-model distinction also
applies at this width.

### Posits

The posit comparison is with **Stillwater Universal**, a different library from
SoftPosit. These are software arithmetic times, again in **ns/op**.

| Width | Implementation | Add | Subtract | Multiply | Divide | FMA |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| 32 | **FloatLib** | **311.7** | **284.4** | **288.9** | **482.0** | **352.3** |
| 32 | Universal | 229.1 | 235.7 | 266.5 | 474.2 | 412.4 |
| 64 | **FloatLib** | **374.2** | **353.8** | **305.1** | **677.8** | **438.6** |
| 64 | Universal | 557.5 | 557.3 | 684.9 | 1,432.1 | 988.5 |
| 4,096 | **FloatLib** | **5,377.6** | **4,937.7** | **7,254.4** | **11,889.5** | **8,803.7** |
| 4,096 | Universal | 41,447.9 | 41,509.3 | 839,625.2 | 9,757,303.8 | 908,847.7 |

At 32 bits, division is close: FloatLib takes about 1.7% longer. At 64 bits, FloatLib
is faster on all five operations shown. The wide posit results are especially
interesting: at 4,096 bits, multiplication takes **7.25 µs versus 839.63 µs**,
about **116 times faster** on these inputs. The full curves include widths where
Universal wins too.

Universal's measured posit square root uses the host square root, so it has its own
series in the plot. At 32 bits it took 156.0 ns, compared with FloatLib's 2,489.7 ns
for the proved software operation. It would be misleading to fold that measurement
into the software-only table.

### P3109 arithmetic with FLoPS

FLoPS gives us another executable Lean implementation with refinement proofs
[@flopsArtifact]. We compared three P3109 formats using nearest-even rounding and
no saturation. All **529,152 arithmetic cases** and the **192 exact timing fixtures**
agreed bit for bit; [chapter 16](#/chapter/external-validation/p3109-arithmetic-with-flops)
describes the input coverage.

This is a separate experiment on an **Intel Xeon Platinum 8275CL**. The entries below
are **median microseconds per operation** across nine pairs of fresh processes on one
logical CPU. Both libraries run the same loop over 16 finite input triples; each returned
code determines the next input. Input selection, the operation, and the checksum are
timed; input construction and process startup are outside the timer.

| Format | Implementation | Add | Multiply | Divide | FMA |
| --- | --- | ---: | ---: | ---: | ---: |
| Binary4p2sf | **FloatLib** | **4.37** | **4.47** | **4.32** | **5.86** |
| Binary4p2sf | FLoPS | 4.29 | 4.13 | 5.71 | 5.16 |
| Binary8p4se | **FloatLib** | **4.89** | **4.96** | **4.94** | **6.40** |
| Binary8p4se | FLoPS | 5.57 | 5.42 | 7.24 | 6.66 |
| Binary8p3se | **FloatLib** | **4.79** | **4.99** | **4.91** | **6.31** |
| Binary8p3se | FLoPS | 5.43 | 5.29 | 7.00 | 6.40 |

FloatLib has lower medians in **9 of the 12 format/operation pairs**, with division about
**1.32 to 1.46 times faster** on these fixtures. FLoPS has lower medians for four-bit
addition, multiplication, and FMA. The eight-bit FMA results are close: for Binary8p3se,
the 5th to 95th percentile ranges are 6.29 to 6.47 µs for FloatLib and 6.37 to 6.54 µs for
FLoPS, so the small difference in their medians deserves little weight.

Both implementations execute software arithmetic with refinement proofs; neither delegates
these operations to a host FPU. FloatLib uses its exact rational P3109 arithmetic. FLoPS
keeps integer significands and exponents through its dyadic operations and uses a
quotient/remainder rounding kernel for division. We built each with its pinned toolchain: Lean 4.33.1
and Clang 22.1.4 for FloatLib; Lean 4.28.0 and Clang 19.1.2 for FLoPS. The times
therefore compare the compiled libraries and their adapters, including compiler effects.
The IEEE and posit tables above use different formats and a different machine.

### Scalar conversions with TensorLib

TensorLib's small-format conversions are a useful performance comparison in their own
right [@tensorLib]. We time its specialized `Float32` conversion functions against
FloatLib's general `Model.cast` for the same four formats. All 128 input/output timing
fixtures agree exactly; the [broader conversion checks](#/chapter/external-validation/scalar-conversions-with-tensorlib)
cover rounding boundaries and exceptional values too.

These are **median nanoseconds per conversion** across nine paired trials on the
**Intel Xeon Platinum 8275CL**, using one logical CPU. “Encode” converts Float32 to the
small format; “decode” converts back.

| Format | FloatLib encode | TensorLib encode | FloatLib decode | TensorLib decode |
| --- | ---: | ---: | ---: | ---: |
| FP16 | 2,201.0 | 265.3 | 2,098.2 | 268.9 |
| BF16 | 2,219.9 | 252.6 | 1,590.0 | 268.3 |
| E4M3FN | 3,642.9 | 279.7 | 2,187.5 | 272.9 |
| E5M2 | 2,248.1 | 267.9 | 2,083.1 | 270.5 |

TensorLib is faster in all eight conversions, by about **5.9 to 13.0 times**.
That gives us a clear place to improve FloatLib. TensorLib manipulates the fixed-format
fields directly; FloatLib's descriptor cast handles format parameters and uses exact
dyadic decoding and rounding, with a field-copy shortcut for compatible widenings.
For the normal inputs timed here, TensorLib's casts use integer shifts, masks, and
rounding. Its FP16 and FP8 subnormal decoders do use `Float32` multiplication, but those
branches are outside this timing workload. The measured speedup therefore does not
establish an FPU advantage. TensorLib's floating tensor arithmetic does use native
operations; [chapter 16](#/chapter/external-validation/symbolic-arithmetic-and-tensors)
explains that execution choice and FloatLib's optional hardware path.

Both adapters use the same loop over sixteen normal finite inputs from $-4$ to $4$,
excluding zero. Each output selects the next input and contributes to a checked checksum.
Input values are constructed before timing; lookup, conversion, result bits, and checksum
bookkeeping are included. We alternate which library runs first in each pair and use
256 warmup iterations. FloatLib uses Lean 4.33.1 and TensorLib uses Lean 4.33.0, both
with Clang 22.1.4. These are scalar dependent-call timings; a tensor kernel that converts
many independent elements would measure a different workload.

<a id="what-the-independent-checks-tell-us-about-speed"></a>

### Which libraries did we time?

The SoftPosit comparison checked result bits; it did not measure separate arithmetic
times for FloatLib and SoftPosit. Its total runtime includes preparing the inputs,
running both libraries, and comparing their answers. Dividing that time by the case
count would not tell us which library was faster.

The same distinction matters for Berkeley's tools: **TestFloat generates correctness
tests; SoftFloat is the arithmetic library timed above**. The ONNX and P3109 table
checks compare encodings; the P3109 arithmetic timings use FLoPS's executable kernel. The
[validation chapter](#/chapter/external-validation) explains those
checks, and the [posit chapter](#/chapter/posits-and-the-quire/cross-checks-against-universal-and-softposit)
works through the seven distinct SoftPosit inputs behind the reported differences.

<a id="executing-the-operation-covered-by-the-theorem"></a>

## Running the code we proved

We can see how the code and theorem fit together in one small definition. `sum64` uses
ordinary binary64 addition; the theorem states that this same expression returns the result
specified by `ExecFloat.Spec.add`.

```lean
open FloatLib.Floats

abbrev Binary64 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

def sum64 (x y : Binary64) : Binary64 := x + y

example (x y : Binary64) : sum64 x y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y

#eval sum64 1 2
-- 3
```

We get 3 from the evaluation. The proof tells us more: the same addition agrees with the
specification for every pair of binary64 inputs, including the rounding step. How quickly it
runs depends on the selected kernel, generated C, compiler optimization, and the work around
the call.

The quantifiers matter here. Evaluating `sum64 1 2` checks one especially simple pair, whereas
`add_eq_spec` applies to arbitrary `x` and `y` of this type. Its right-hand side is a floating-point
specification, so the statement does not replace rounded addition with addition over the reals.
The theorem fixes the result the implementation must return; the benchmark measures how long
the call takes.

Try changing the operands in the `#eval` call while leaving the theorem alone. We can inspect
another result without narrowing what the proof covers.

## What one timed operation includes

The benchmark starts with sixteen sets of rational inputs. The adapters construct their
inputs before timing; the Flocq conversion differs in the way explained below.
An arithmetic result selects the next set of inputs and
contributes to a checksum, so later work depends on the operation being measured. This avoids a
loop that repeatedly computes a constant, and avoids letting multiplication or division collapse
into a stream of zeros or infinities.

For example, the first pair in the [exact workload](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/lean/FloatLibBenchmarks/Support/ExactWorkload.lean) is
$-9/8$ and $-69/35$. The first is exactly binary-representable at ordinary IEEE widths; the
second needs rounding. MPFR converts the rationals directly, without an earlier binary64
rounding error. Universal imports the posit encodings generated from these inputs by
FloatLib. This setup work happens before the clock starts.

Let's follow one addition iteration. The loop loads an already-converted pair, adds it, observes the
result, and uses the result to choose a pair for the next iteration. The dependency follows
the choice of inputs: the next operation cannot know which pair to use until the previous
result is available. The result itself does not become the next operand. That last choice keeps
the loop drawing from the same sixteen sets instead of gradually changing its numerical
workload as repeated multiplication grows or repeated division shrinks a value.

The reported ns/op includes input lookup, representation and adapter work, the arithmetic call,
and result observation. Each operation waits for the preceding result. Native C's 8.36 ns
addition therefore includes more than a hardware add instruction. A loop of independent
operations, a vectorized array kernel, and a workload dominated by subnormals or exceptional
values could give different comparisons. The dependent-chain distinction is also used in
instruction-measurement work such as uops.info [@abelUopsInfo2019].

Before timing MPFR, SoftFloat, native C, and Python, we run **256 operations** at each
supported binary format and compare checksums with FloatLib. One checksum follows the
results; another follows the chosen inputs. Both matter: a rounding difference can change
which input comes next, so two loops that look alike could end up doing different work.
Matching checksums are a useful check on these inputs, rather than a proof about every
intermediate result. Flocq's different treatment is explained below.

Fast and slow implementations need different loop lengths to get useful measurements.
A short preliminary run estimates how many iterations will take about 200 ms; every
reported trial lasts at least 50 ms. The order is shuffled and rotated across nine trials
so the same implementation does not always run first. We report the median and show
the 5th to 95th percentiles. The underlying data also includes quartiles, standard deviation,
and median absolute deviation.
Most adapters warm up for 256 iterations. Flocq's warmup is capped at 64 through 128 bits,
16 through 512 bits, four at 1,024 bits, and one at the two largest widths.

The timing loops ran one at a time on the same logical CPU. This avoids migration between
CPUs, though other work on the machine can still affect caches and clock speed.
The compiler was GCC 12.2.0 with
`-O3 -march=native` for the C adapters; FloatLib used Lean 4.33.1. The external builds are
described below. Compilation, process startup, input construction, warmup, and CSV output
happen outside the measured interval. Runtime allocation and garbage collection that occur
inside the loop contribute to the reported time.

## How we ran the external implementations

We call each library from a small program that follows the loop above: choose inputs,
perform one operation, observe the result, and use it to choose the next inputs.
This gives us a common way to measure the libraries while using their own representations.

That shared structure makes the timings useful, but the adapters still matter. An MPFR call
reuses a destination object; an extracted Flocq call returns a structured value; Python creates
and observes Python objects. The time spent moving through those representations is part of
the measurement. The reported times include the whole loop.

### MPFR: matching precision and exponent range

GMP, the GNU Multiple Precision Arithmetic Library, provides exact integer and rational
arithmetic. It also provides `mpf` floating-point numbers, but their requested precision is
rounded up to whole machine limbs and final results are truncated. MPFR builds on GMP and
specifies correctly rounded floating-point operations: compute the exact result, then round
to the chosen bit precision and rounding direction. That makes MPFR the closer comparison
for FloatLib's floating-point arithmetic. [@gmpFloatingPointManual] [@mpfrManual]

The MPFR adapter uses **MPFR 4.2.0** [@fousseMpfr2007], linked through `pkg-config`.
Its C wrapper was compiled with GCC 12.2.0 and
`-O3 -march=native -std=c11 -Wall -Wextra -Werror`. These are the wrapper's flags;
they do not describe how the installed MPFR and GMP libraries were compiled.

At each width, the [MPFR adapter](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/c/exact_format_mpfr.c) selects the binary companion's precision and exponent
range. Binary32 uses 24 significand bits; binary64 uses 53. Each input is constructed as
an exact GMP rational and imported with `mpfr_set_q`, using nearest-even rounding.
After conversion and each arithmetic call, `mpfr_subnormalize` handles the destination's
subnormal range. Setting precision alone would miss the tiny formats' overflow and gradual
underflow behavior, which can change which inputs the loop visits next.

The timed call uses `mpfr_add`, `mpfr_sub`, `mpfr_mul`, `mpfr_div`, `mpfr_sqrt`, or
`mpfr_fma`, followed by subnormal handling and a checksum update. A result object is
initialized once per loop invocation and reused across iterations. The adapter runs the
256-operation comparison at every measured binary width. Broader arithmetic checks appear
in the validation chapter.

### SoftFloat, native C, and Python

We used Berkeley SoftFloat at revision `a0c6494`, building `softfloat.a` with
the upstream Linux/x86-64 GCC recipe selected by our [benchmark driver](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/scripts/format-comparison.sh), then linked the [SoftFloat adapter](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/c/softfloat_ieee.c) with the same
C wrapper flags as MPFR. That build uses the `8086-SSE` specialization and
GCC `-O2` for the static library; the wrapper's `-O3` flag does not change that library build.
The measured arithmetic calls are SoftFloat's `f32_*` and `f64_*`
functions, including fused `mulAdd`, with nearest-even rounding and tininess detected
after rounding. Input conversion happens before timing. The 256-operation comparison
covers both binary32 and binary64.

The native adapter uses C `float` and `double`, with `sqrtf`/`sqrt` and `fmaf`/`fma`
for the corresponding operations. It uses the same GCC wrapper flags, without
`-ffast-math`, and joins the same agreement check. This measures the host arithmetic
through a C loop; it does not measure Lean's native-float wrapper or FloatLib's guarded
host API. Before timing, it checks the host representation and nearest-even rounding mode,
and compares all sixteen input results with MPFR. The benchmark does not record a separate
check of the host's flush-to-zero controls.

The Python adapter runs under **CPython 3.11.2** at binary64. Its timer surrounds the
Python loop, so interpreter dispatch, object handling, input selection, and checksum work
are included. The inputs are prepared first. This interpreter has no `math.fma`, so the FMA
point is absent; replacing it with `x * y + z` would perform two roundings. Its other five
operations join the binary64 agreement check.

<a id="flocq-exactly-which-extracted-program"></a>

### The Flocq program we timed

Our small [Flocq wrapper](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/rocq/FlocqKernel.v) uses **Flocq 4.2.2**
[@boldoMelquiond2011]. It exposes `Bplus`, `Bminus`, `Bmult`, `Bdiv`, `Bsqrt`, and `Bfma`
from `IEEE754.BinarySingleNaN`, with nearest-even rounding and `benchmark_emax = 16384`.
Significand precision follows the binary companion. The exponent range and single-NaN
representation do not reproduce every FloatLib descriptor.

The clock starts inside the program, after input construction and warmup; proof checking
and compilation happen beforehand. The measured loop includes extracted arithmetic,
value allocation, normalization for the fingerprint, and checksum work.

There is also a difference in how our wrapper constructs the inputs. `flocq_from_ratio` first rounds
the integer numerator and denominator at the destination precision, then divides them.
That can differ from rounding the rational once. For the first input at two bits of
significand precision, nearest-even rounding gives

$$
R_2(45)=48,\qquad R_2(40)=32.
$$

Here 40 is halfway between 32 and 48, and 32 has the even significand. The adapter therefore
constructs $R_2(-48/32)=-1.5$. Directly rounding the intended fraction gives
$R_2(-45/40)=R_2(-1.125)=-1$. This difference comes from our wrapper's input construction.
It is not evidence of an error in Flocq's arithmetic.

The Flocq program runs every plotted operation and width, but skips the 256-operation
comparison. Its grey curve therefore measures this particular extracted program with its
own input rounding.

### Universal: checking the posit inputs before timing

We used Stillwater Universal [@stillwaterUniversal] at revision `26e69f5`, compiling a
C++20 adapter for each width with GCC 12.2.0 and
`-O3 -march=native -Wall -Wextra -Werror`. Before timing an operation at a given width, it
compares all sixteen results with the result words generated by FloatLib.
It imports the input words directly into `posit<width, 2, uint64_t>`, without routing
them through a host float. We time it only when all sixteen results agree.

Of the 78 operation-and-width combinations, 71 agreed; square root differed at each measured
width from 64 through 4,096 bits. Widths below five were omitted because of Universal's
generic `es=2` FMA constraint. The
[validation chapter](#/chapter/external-validation) lists the accepted
and differing results, so a missing marker has an explanation. It can mean an unsupported
width or a numerical disagreement; it never means zero time. Universal's configurations that
convert through binary64 for host square root have a separate series from its software
arithmetic. Agreement on these inputs is useful evidence for this workload, not an
exhaustive posit conformance result.

<a id="reading-the-ratios"></a>

### Comparing relative times

Equal encoded width is a storage comparison. A binary format has a fixed significand precision;
a posit's precision varies with its value. MPFR and Flocq use the binary companion's precision.
Posit-versus-binary timings at the same width do not imply equal
accuracy or equal dynamic range. The 8-bit binary point, for example, uses an E4M3
layout, and the 4,096-bit point is a custom binary layout with 19 exponent bits.

![FloatLib time divided by the external implementation's time for addition, multiplication, and division, at equal encoded widths](assets/ch10-external-ratios.png "FloatLib time divided by the comparison library’s time at equal encoded width. Lower is faster for FloatLib relative to that library; 1 means equal times. Different formats still have different numerical contracts.")

In [Figure 15.2](#/chapter/performance/figure-ch10-external-ratios),
a ratio of 1 means equal median time; 10 means FloatLib took ten times as long. For binary64
addition, FloatLib/MPFR is **8.53**, while FloatLib/extracted-Flocq is **0.142**. The absolute times
are 312.8 ns, 36.7 ns, and 2,201.0 ns respectively. Those two comparisons describe the same
FloatLib measurement against two very different software implementations.

We can reconstruct the MPFR point directly from the two measured medians:

$$
\rho_{\mathrm{MPFR}}
= \frac{312.7723\ \mathrm{ns/op}}{36.6719\ \mathrm{ns/op}}
\approx 8.53.
$$

The units cancel. FloatLib needed about 8.53 times the elapsed time per operation in this
workload. Replacing the denominator with Flocq's 2,201.0 ns gives 0.142, putting that point below
the equality line. This is a ratio of separately computed medians, rather than the median of
nine trial-by-trial ratios. On the logarithmic axis, equal vertical distances represent equal
multiplicative changes.

We cannot read either ratio as a “cost of proof.” The timed implementations use different arithmetic
algorithms, representations, allocation patterns, and adapters. A proof certifies FloatLib's
result; it does not explain which of those implementation choices accounts for the gap.
On this workload, FloatLib's binary64 addition was slower than the MPFR adapter and faster
than the extracted Flocq adapter.

The posit comparison also changes with width. At 32 bits, addition took 311.7 ns in FloatLib and
229.1 ns in Universal. At 64 bits, the corresponding times were 374.2 ns and 557.5 ns. At 4,096
bits, they were 5.38 µs and 41.45 µs. Those timings describe the benchmark's sixteen input sets.
An application with different inputs or a different mix of operations may give a different comparison.

<a id="small-formats-and-changes-of-kernel"></a>

## Why a wider format can be faster

![All six operations from 2 to 16 bits, with each measured width labelled, including 5, 6, and 7 bits](assets/format-comparison-low-width.png "Median nanoseconds per operation at widths 2 to 16, with percentile bands and logarithmic axes. Lower is faster; only measured widths have markers.")

We can separate the small-width points in [Figure 15.3](#/chapter/performance/figure-format-comparison-low-width),
which expands the crowded left edge of the main plot. Each of 5, 6, and 7 bits
has its own measurement. Table lookup can be a small part of the total time at these widths:
input selection, function calls, and the checksum still run on every iteration. A nearly flat
region therefore does not establish that the underlying arithmetic has constant cost.

The curve is not monotone in width. In the binary measurements, square root took 999.8 ns at
16 bits and 93.0 ns at 32 bits. The 32-bit format has a specialized fixed-format route. Increasing
the width can thus reduce time when it changes the algorithm and calling path. The timing alone
does not isolate how much of the difference comes from dispatch, arithmetic, or representation.

FloatLib can use exhaustive tables, native-word kernels, monomorphic binary32 and binary64
operations, eligible fixed-limb kernels, or an exact general engine. Availability depends on the
operation and layout as well as the encoded width. We can ask which implementation the
current API selects:

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

A candidate carries a theorem connecting its implementation to the specification.
[[FloatLib.Floats.ExecFloat.Backend.selectCertified_run_eq_spec]] proves that the selected
candidate's run has that result. To follow an ordinary `x + y` call all the way to that
kernel, we also check the dispatch theorem and the generated code.

## Multiplication, fused operations, and wide arithmetic

![Multiplication and fused multiply-add, with median ns/op and percentile bands across encoded widths](assets/format-comparison-mul-fma.png "Multiplication and fused multiply-add timings across encoded widths. Both axes are logarithmic; bands show the 5th to 95th percentiles and lower is faster.")

Fused multiply-add computes the exact product and sum before one final rounding. It can therefore
need a wider intermediate than an ordinary multiplication. In [Figure 15.4](#/chapter/performance/figure-format-comparison-mul-fma), binary32 FMA took
140.5 ns, while binary64 FMA took 1,277.2 ns. These particular implementations and inputs give that gap. The CPython FMA point is absent
because CPython 3.11.2 does not expose that operation.

![Division and square root, with median ns/op and percentile bands across encoded widths](assets/format-comparison-div-sqrt.png "Division and square-root timings across encoded widths. Both axes are logarithmic; lower is faster. Universal square roots that disagreed on the benchmark inputs are excluded.")

At 4,096 bits in [Figure 15.5](#/chapter/performance/figure-format-comparison-div-sqrt),
FloatLib binary division took **10.41 µs**, compared with **2.37 µs** for MPFR.
Square root took **40.71 µs**, compared with **1.69 µs** for MPFR. The ratio is 4.39 for division
and 24.07 for square root. Addition at the same width took 4.26 µs. Wide operations have distinct
costs even when they share the same public representation.

The proved software path builds multiword arithmetic from ordinary machine words. The general
engine also allocates arbitrary-precision integers. Those choices leave room for lower-level
limb engineering and less allocation; MPFR is an important comparison because it already does
that work efficiently. Division and square root have fewer specialized wide routes than
addition, subtraction, multiplication, and FMA. For example, the 256-bit binary family selects
the exact baseline for both division and square root. The selected-candidate queries make the
operation-specific difference explicit:

```lean
#eval (ExecFloat.Div.selectedCandidate (F := ExecFloat.Binary.Family 8 23)).name
-- "binary-interchange division fixed-format kernel"
#eval (ExecFloat.Div.selectedCandidate (F := ExecFloat.Binary.Family 19 236)).name
-- "binary-interchange division exact baseline"
#eval (ExecFloat.Sqrt.selectedCandidate (F := ExecFloat.Binary.Family 19 236)).name
-- "binary-interchange square root exact baseline"
```

Binary32 division has a fixed-format candidate, while both queries at 256 bits report the exact
baseline. The arithmetic specification is unchanged by that selection.

## Comparing with Lean's native floats

At binary32 and binary64, the host provides arithmetic directly. Lean's `Float32` and `Float` call its `float` and `double` operations, while FloatLib's certified operations execute software kernels. We can compare the software times with native C in [Figure 15.6](#/chapter/performance/figure-ch17-host-vs-software), a detail of the same benchmark.

![Native C and FloatLib proved software at binary32 and binary64; bars show median ns/op and labels show FloatLib/native time ratios](assets/ch17-host-vs-software.png "Median nanoseconds per operation for native C arithmetic and FloatLib software at binary32 and binary64. Lower is faster; annotations give the software/native time ratio.")

At binary32, addition took **138.6 ns/op** in FloatLib and **8.36 ns/op** in native C, a ratio of
16.6. At binary64, the corresponding times were **312.8 ns/op** and **8.20 ns/op**, a ratio of
38.2. Division shows a larger binary64 gap: **1,447.3 ns/op** for FloatLib and **11.62 ns/op** for
native C. The ratios are operation-specific; the binary32 square-root ratio is 8.1, while the
binary64 division ratio is 124.6.

For addition, the binary64 software bar is about 2.26 times the binary32 software bar, while
the two native bars are nearly equal. Thus the change from 16.6 to 38.2 in the ratios comes
mostly from the software times in these measurements. To understand the gap, we need to look at several differences: significand width, arithmetic
algorithm, representation, and calling path all differ between the two software kernels.

These are the same nine-trial measurements shown above, enlarged for the two common
binary formats. The [timing method](#/chapter/performance/what-one-timed-operation-includes)
explains the work included in each operation.

The native bars time **C arithmetic**. Lean's `Float32` and `Float`, and FloatLib's
`NativeFPU.Unchecked` functions, have their own calling costs. The unchecked functions also
add guards and bit conversions. We would need to time those interfaces separately before
assigning them the same numbers.

## Lean's model and its compiled operations

We're glad to see Lean exposing more of its floating-point model for proofs.
Lean 4.33 introduced the logical models; **Lean 4.34** connects the signed integer
conversions to them and exposes integer constructors and named `nan` and `inf` constants
[@lean434Release]. We use them to connect ordinary signed casts to the rounding and conversion
specifications already used by FloatLib.

In Lean 4.34, `Float32` contains a `Float32.Model`, which holds a `UInt32`
word and a validity proof. Its NaN representation is canonical: different NaN payloads do not
remain distinct model values. `Float` has the corresponding structure over `UInt64`.

The logical definitions unpack sign, significand, and exponent, perform arithmetic, round to
nearest even, and pack a result. For example, addition is defined by applying model addition
and then `ofModel`. The runtime-facing definitions carry `@[extern]` attributes: compiled
`Float32.add` uses C floating-point addition, and `Float32.sqrt` uses `sqrtf`. The logical model
and the external implementation therefore have a boundary that a proof about the model alone
does not verify.

To compare the stored words ourselves, we'll print them in hexadecimal at both widths.
The three `rfl` examples expose the logical definitions of
addition, multiplication, and the bit cast without making a claim about generated machine code.
The last evaluation shows the canonical NaN returned by the native bit-conversion API.

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

abbrev Binary16 := ExecFloat.Binary (exponentBits := 5) (fractionBits := 10)
abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

/-- Print a 32-bit word as eight hexadecimal digits. -/
def hex32 (w : UInt32) : String :=
  let digits := String.ofList (Nat.toDigits 16 w.toNat)
  "0x" ++ "".pushn '0' (8 - digits.length) ++ digits

/-- Print a 64-bit word as sixteen hexadecimal digits. -/
def hex64 (w : UInt64) : String :=
  let digits := String.ofList (Nat.toDigits 16 w.toNat)
  "0x" ++ "".pushn '0' (16 - digits.length) ++ digits

example (a b : Float32) : a + b = Float32.ofModel (a.toModel + b.toModel) := rfl
example (a b : Float) : a * b = Float.ofModel (a.toModel * b.toModel) := rfl
example (bits : UInt32) :
    Float32.ofBits bits = Float32.ofModel (Float32.Model.ofBits bits) := rfl

#eval hex32 (Float32.ofBits 0x7f812345).toBits
-- "0x7fc00000"
```

FloatLib uses the same finite value sets for binary32 and binary64, but retains additional NaN
distinctions. Its configured arithmetic connects software kernels to an explicit specification.
The bridge to Lean's logical arithmetic model proves some shared semantics, described below.
Neither that bridge nor agreement on tests proves that an arbitrary compiler and processor
implement Lean's external operations correctly in every floating-point environment.

<a id="the-same-finite-bits-including-rounding-effects"></a>

## Both implementations lose associativity

Binary32 addition is not associative. Take $x = 2^{25}$, $y = -2^{25}$, and $z = 1$. The exact sum
is 1 under either grouping. In binary32, $y + z$ lies halfway between two representable values;
nearest-even rounding returns $y$. Binary32 has 24 significant bits: on the side of $-2^{25}$
toward zero, consecutive values are 2 apart. The exact value $-33554431$ is halfway between
$-33554432$ and $-33554430$, and the first has an even final significand bit. Thus $x + (y + z)$
is 0, while $(x + y) + z$ is 1. Both the host and FloatLib produce those results.

```lean
def big : Float32 := Float32.ofBits 0x4c000000
def negBig : Float32 := Float32.ofBits 0xcc000000
def one : Float32 := Float32.ofBits 0x3f800000

#eval (big + negBig) + one
-- 1.000000
#eval big + (negBig + one)
-- 0.000000

def sBig : Binary32 := ExecFloat.Binary.ofBits32 0x4c000000
def sNegBig : Binary32 := ExecFloat.Binary.ofBits32 0xcc000000
def sOne : Binary32 := ExecFloat.Binary.ofBits32 0x3f800000

#eval (sBig + sNegBig) + sOne
-- 1
#eval sBig + (sNegBig + sOne)
-- 0
#eval hex32 ((big + negBig) + one).toBits == hex32 (ExecFloat.Binary.toBits32 ((sBig + sNegBig) + sOne))
-- true
#eval hex32 (big + (negBig + one)).toBits == hex32 (ExecFloat.Binary.toBits32 (sBig + (sNegBig + sOne)))
-- true
```

The host prints six decimal places while FloatLib prints these exact integers. The final two
evaluations therefore compare the encoded words, rendered as hexadecimal strings, for each
grouping. Both comparisons return `true`. Agreement here includes the rounding that loses the
unit in the second grouping; it does not restore the associativity of real addition.

The native comparisons extend this example to ties, cancellation, both signed zeros,
subnormals, normal boundaries, overflow, infinities, and NaNs. They compare ordinary
FloatLib operations with their software kernels, guarded host calls with software, and
bit conversions through Lean's native types. These checks passed with zero mismatches.
The [validation chapter](#/chapter/external-validation) explains the
external comparisons and their scope.

Subnormal inputs matter because an environment that flushes them to zero may disagree with
the software operation. These comparisons exercise the compiler, runtime, processor, and process settings together.
Passing on one machine does not establish agreement for every operand and environment.

<a id="nan-payloads-change-at-the-native-conversion-boundary"></a>

## Converting to native floats changes NaN payloads

A binary32 NaN has an all-ones exponent and a nonzero fraction field. That field also carries
payload bits and a quiet/signaling distinction. FloatLib keeps those distinctions in its raw
representation. Lean's `Float32.ofBits` canonicalizes them.

The signaling NaN `0x7f812345` becomes the canonical quiet NaN `0x7fc00000` when imported into
`Float32`. Its payload has been lost before any arithmetic runs. This affects a direct
comparison even when both implementations correctly return a NaN.

The fourteen pairs below include a tie at half an ulp, cancellation, subnormal arithmetic,
normal/subnormal boundaries, overflow, signed zeros, infinity, and two NaN operands.
`rawDisagreements32` applies a raw host operation and a software operation to the same pair of
input words. It compares output words and returns the input pairs that produced differences.
We'll keep the input words visible so that a reported difference tells us which pair to inspect:

```lean
/-- The fourteen binary32 operand pairs of `tests/FloatLibTests/Fixtures/NativeIEEE.lean`. -/
def pairs32 : List (UInt32 × UInt32) :=
  [ (0x3f800000, 0x40000000), (0x3f800000, 0x33800000), (0x3f800001, 0xbf800000)
  , (0xbf800000, 0x3f800000), (0x00000001, 0x00000002), (0x80000001, 0x00000001)
  , (0x00800000, 0x3f000000), (0x007fffff, 0x00000001), (0x007fffff, 0x00800000)
  , (0x7f7fffff, 0x7f7fffff), (0x00000000, 0x80000000), (0x7f800000, 0x3f800000)
  , (0x7fc12345, 0x3f800000), (0x7f812345, 0xff800000) ]

/-- Pairs on which a raw host operation and the proved kernel return different bits. -/
def rawDisagreements32 (host : Float32 → Float32 → Float32)
    (soft : Binary32 → Binary32 → Binary32) : List (String × String) :=
  pairs32.filterMap fun (a, b) =>
    let hostBits := (host (Float32.ofBits a) (Float32.ofBits b)).toBits
    let softBits :=
      ExecFloat.Binary.toBits32 (soft (ExecFloat.Binary.ofBits32 a) (ExecFloat.Binary.ofBits32 b))
    if hostBits == softBits then none else some (hex32 a, hex32 b)

#eval rawDisagreements32 (· + ·) (· + ·)
-- [("0x7fc12345", "0x3f800000"), ("0x7f812345", "0xff800000")]
#eval (rawDisagreements32 (· - ·) (· - ·)).length
-- 2
#eval (rawDisagreements32 (· * ·) (· * ·)).length
-- 2
#eval (rawDisagreements32 (· / ·) (· / ·)).length
-- 2

#eval hex32 (Float32.ofBits 0x7fc12345 + Float32.ofBits 0x3f800000).toBits
-- "0x7fc00000"
#eval hex32 (ExecFloat.Binary.toBits32
  (ExecFloat.Binary.ofBits32 0x7fc12345 + ExecFloat.Binary.ofBits32 0x3f800000))
-- "0x7fc12345"
```

Among the fourteen binary32 input pairs, raw host addition, subtraction,
multiplication, and division each differ from FloatLib on the two pairs containing NaN
operands. The twelve other pairs agree, including the subnormal sums, overflow to infinity,
and signed zeros. The final two evaluations isolate the quiet-NaN addition: Lean returns
`0x7fc00000`, while FloatLib propagates the payload in `0x7fc12345`.

We can locate the payload change by following that one pair through `rawDisagreements32`.
The two paths receive the input words `0x7fc12345` and `0x3f800000`. The host branch first applies
`Float32.ofBits`, turning the first word into `0x7fc00000`; the second word represents 1.
The software branch imports `0x7fc12345` unchanged. Addition then propagates a NaN on each
branch, and `toBits` exposes their different payloads. The comparison returns the original
operand pair, which tells us how to reproduce the discrepancy; it is not returning the two
result words.

The mismatch already begins at `Float32.ofBits`, which canonicalizes the NaN input. Comparing
only the result class would hide the payload difference; comparing words exposes it. The
guarded API later in this chapter uses the same `pairs32` list to demonstrate why keeping these
operands in software changes the outcome of the comparison.

<a id="the-proved-conversion-and-arithmetic-bridges"></a>

## Proofs relating FloatLib to Lean's float model

[[FloatLib.Floats.ExecFloat.Binary.ofFloat32]] imports a native value's `toBits` word through
`ofBits32`. [[FloatLib.Floats.ExecFloat.Binary.toFloat32]] exports the FloatLib word through
`Float32.ofBits`. The binary64 functions `ofFloat` and `toFloat` follow the same pattern.
The native conversion proofs show that importing a native value keeps its stored word,
and exporting it again recovers the value:

```lean
example (x : Float32) :
    ExecFloat.Binary.toBits32 (ExecFloat.Binary.ofFloat32 x) = x.toBits :=
  ExecFloat.Binary.toBits32_ofFloat32 x

example (x : Float) :
    ExecFloat.Binary.toBits64 (ExecFloat.Binary.ofFloat x) = x.toBits :=
  ExecFloat.Binary.toBits64_ofFloat x

example (x : Float32) :
    ExecFloat.Binary.toFloat32 (ExecFloat.Binary.ofFloat32 x) = x :=
  ExecFloat.Binary.toFloat32_ofFloat32 x

example (x : Float) :
    ExecFloat.Binary.toFloat (ExecFloat.Binary.ofFloat x) = x :=
  ExecFloat.Binary.toFloat_ofFloat x

example (v : Binary32) :
    ExecFloat.Binary.ofBits32 (ExecFloat.Binary.toBits32 v) = v :=
  ExecFloat.Binary.ofBits32_toBits32 v

#eval ExecFloat.Binary.toFloat32 (ExecFloat.Binary.ofBits32 0x3fc00000)
-- 1.500000
#eval hex32 (ExecFloat.Binary.toBits32 (ExecFloat.Binary.ofBits32 0x7f812345))
-- "0x7f812345"
#eval hex32 (ExecFloat.Binary.toFloat32 (ExecFloat.Binary.ofBits32 0x7f812345)).toBits
-- "0x7fc00000"
```

[[FloatLib.Floats.ExecFloat.Binary.toFloat32_ofFloat32]] covers every native value, including
both signed zeros, infinities, and Lean's canonical NaN. Its proof uses the shared packing
invariant: unpacking and repacking a valid word recovers that word. We prove this once for
arbitrary exponent and fraction widths, then specialize it to binary32 and binary64.

Starting from a FloatLib word is different. The last theorem keeps every bit through
`ofBits32` and `toBits32`, including a NaN payload. Exporting the signaling word `0x7f812345`
through `toFloat32` instead produces the canonical quiet NaN `0x7fc00000`, as specified by
[[FloatLib.Floats.ExecFloat.Binary.ofFloat32_toFloat32]]. The finite word `0x3fc00000` exports
as 1.5 without changing its bits.

### Integer conversions in Lean 4.34

The newly exposed integer constructors round once to nearest-even. We connect their shared
model operation to FloatLib's existing conversion specification, including the result word
and rounding status. That argument applies to every conventional IEEE descriptor; the
native `Int8`, `Int16`, `Int32`, `Int64`, and `ISize` casts specialize it to the two host widths.
For example, an `Int64` may need rounding when converted to binary32:

```lean
open FloatLib.Numerics.Representations in
example (n : Int64) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat32 n.toFloat32) =
      ExecDType.intToFloat FloatFormat.binary32
        (⟨n.toBitVec⟩ : FixedInt 64) .nearestEven :=
  ExecFloat.Binary.toModel_ofFloat32_int64ToFloat32 n

example (n : Int) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat n.toFloat) =
      Model.roundDyadic FloatFormat.binary64 (FloatLib.Numerics.Dyadic.ofScaledInt n 0) :=
  ExecFloat.Binary.toModel_ofFloat_intToFloat n

example :
    ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat32 Float32.nan) =
      Model.canonicalNaN FloatFormat.binary32 :=
  ExecFloat.Binary.toModel_ofFloat32_nan
```

The exposed `Float.ofNat` and `Float.ofInt` constructors, their binary32 counterparts, and
the new `Int.toFloat` and `Int.toFloat32` names accept unbounded integers. Their bridge proofs
cover both the small-literal path and general integer rounding, so an input larger than a
machine word retains its full magnitude until the final rounding.

Conversion back to a signed integer has a different rule: truncate toward zero, then
saturate to the destination's range. Lean maps NaN to zero and each infinity to the signed
endpoint. The range check therefore concerns the truncated integer: `127.75` still converts
to `Int8` value 127.

```lean
example : (Float32.ofBits 0xbfe00000).toInt8 = (-1 : Int8) := by decide
example : (Float32.ofBits 0x42ff8000).toInt8 = (127 : Int8) := by decide
example : Float32.nan.toInt8 = (0 : Int8) := by decide
example : Float32.inf.toInt8 = (127 : Int8) := by decide
```

FloatLib's `ExecDType.floatToIntSaturating` follows that native policy using the existing
exact decoder and integral rounder. Its agreement theorems also connect it to the checked
`ExecDType.floatToInt`: both return the same integer when the truncated value fits.
The checked operation returns an error for overflow, infinity, or NaN, which is useful
when a caller wants to handle those inputs explicitly.

### Arithmetic through the same model

The arithmetic bridge is broader than the two host widths. Lean's `UnpackedFloat` algorithms
take a format argument, so FloatLib can relate them to every descriptor satisfying its IEEE
format conditions. The decoder theorem
[[FloatLib.Floats.Formats.BinaryInterchange.Model.ieeeToDyadic?_eq_unpackedToDyadic?_toModel]]
identifies the exact dyadic value read by the two models.
[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_eq_unpackedToReal_toModel]] lifts that
agreement to real values.

Addition and subtraction agree on the complete result word whenever both operands are
finite. These hypotheses allow signed zeros, and the result may be zero, subnormal, or
infinite. We can apply the addition theorem directly to ordinary Lean expressions:

```lean
example (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    ExecFloat.Binary.ofFloat32 (x + y) =
      ExecFloat.Binary.ofFloat32 x + ExecFloat.Binary.ofFloat32 y :=
  ExecFloat.Binary.ofFloat32_add_of_isFinite x y hx hy
```

[[FloatLib.Floats.ExecFloat.Binary.ofFloat32_add_of_isFinite]] connects the native expression
on the left to the configured software addition on the right. The corresponding subtraction
and binary64 theorems have the same finite-input conditions. Unlike equality of decoded real
values, this word equality distinguishes positive and negative zero.

The real-valued addition theorem
[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_ofModel_add_finite_eq_roundAt]]
provides a complementary conclusion: under its nonzero finite-input and finite-result
hypotheses, Lean's rounded sum has value
$\operatorname{roundAt}_{\mathrm{fmt}}(\operatorname{value}(x)+\operatorname{value}(y))$.
In our earlier cancellation example, adding $y=-2^{25}$ and $z=1$ therefore rounds the exact
sum $-33554431$ to $-33554432$.

Square root agrees for **every input**, including negative zero, negative arguments,
infinities, and NaNs. We can perform the certified software operation and then export the
result, or export first and take Lean's logical square root:

```lean
example (x : Binary32) :
    ExecFloat.Binary.toFloat32 (ExecFloat.sqrt x) =
      (ExecFloat.Binary.toFloat32 x).sqrt :=
  ExecFloat.Binary.toFloat32_sqrt x
```

[[FloatLib.Floats.ExecFloat.Binary.toFloat32_sqrt]] and its binary64 counterpart follow from
one theorem for every conventional IEEE descriptor. The native boundary canonicalizes NaNs;
all other result bits, including the sign of zero, agree.
[[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeModelSqrt.unpackedSqrt_eq_sqrt]] also
lets the compiler evaluate Lean's model square root through FloatLib's proved integer kernel.

The [multiplication and division comparisons](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Arithmetic/LeanModel.lean)
have narrower hypotheses. Multiplication requires a provisional exponent satisfying Lean's
`roundWithAccuracy` precondition. Division also requires a nonzero provisional quotient from
`divCore`. Their real-valued conclusions apply once those conditions and the stated finite
conditions have been established.

All these proofs concern Lean's logical definitions. Compiled native calls still use external
runtime functions and hardware instructions. The optional guarded host operations below retain
that trust boundary.

## Formats, rounding directions, and status

Lean's native types expose binary32 and binary64. FloatLib's descriptor also supports smaller,
wider, and custom layouts, with the same configured interface. Binary16, for example, rounds
one third differently:

```lean
#eval (1 : Float32) / 3
-- 0.333333
#eval (1 : Binary32) / 3
-- 11184811 * 2^-25
#eval (1 : Binary16) / 3
-- 0.333251953125
#eval (1 : Binary64) / 3
-- 6004799503160661 * 2^-54
#eval hex64 ((1 : Float) / 3).toBits == hex64 (ExecFloat.Binary.toBits64 ((1 : Binary64) / 3))
-- true
```

The host's six-decimal display of one third does not expose the full stored value. FloatLib
prints the exact binary16 quotient as `0.333251953125`, and the exact binary32 and binary64
quotients as a significand times a power of two. Its formatter uses a plain integer or decimal
when the remaining normalized power of two lies between $2^{-18}$ and $2^{18}$, and a dyadic
expression outside that range.

The last evaluation compares the binary64 words directly. It returns `true`: the host quotient
and FloatLib quotient agree even though their ordinary display strings differ. This is a
finite native comparison as well as an illustration of the precision lost when the same
operation is performed at binary16 instead of binary64.

FloatLib also takes the rounding direction as an argument. The named operations
[[FloatLib.Floats.ExecFloat.Binary.add]], `sub`, `mul`, [[FloatLib.Floats.ExecFloat.Binary.div]],
`fma`, and `sqrt` accept
[[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]]. It provides nearest-even,
toward zero, toward positive infinity, and toward negative infinity. Ordinary operators use
nearest-even. For one third, the two directed binary32 results are adjacent words:

```lean
#eval hex32 (ExecFloat.Binary.toBits32
  (ExecFloat.Binary.div (1 : Binary32) 3 (rounding := .towardPositiveInfinity)))
-- "0x3eaaaaab"
#eval hex32 (ExecFloat.Binary.toBits32
  (ExecFloat.Binary.div (1 : Binary32) 3 (rounding := .towardNegativeInfinity)))
-- "0x3eaaaaaa"
#eval hex32 ((1 : Float32) / 3).toBits
-- "0x3eaaaaab"
```

The host result is the upper word, `0x3eaaaaab`, because it is closer to the exact value of one
third. Directed rounding also exposes the lower neighbour, `0x3eaaaaaa`, without changing process
state. Together the two values can bound the exact quotient for interval arithmetic.

The stored values let us check the choice without relying on decimal formatting. The lower
word is $11184810\cdot2^{-25}$ and the upper is $11184811\cdot2^{-25}$. Subtracting each
from the exact quotient in the appropriate direction gives

$$
\begin{aligned}
\frac13-11184810\cdot2^{-25}&=\frac{2}{3\cdot2^{25}},\\
11184811\cdot2^{-25}-\frac13&=\frac{1}{3\cdot2^{25}}.
\end{aligned}
$$

The upper neighbour is half as far from $1/3$, so nearest-even chooses it without needing
the tie-breaking rule. Rounding downward chooses the lower word because it must remain
below the exact quotient. The two modes answer different, precisely stated questions about
the same exact number.

These arguments are useful for interval endpoints and rounding-sensitive proofs. Lean's native
logical model uses nearest-even; changing a process's hardware rounding register is not the same
operation as passing a mode to a proved FloatLib function.

Status-bearing operations return an
[[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEStatus]] alongside the value. Its five
flags are invalid, division by zero, overflow, underflow, and inexact. Watch the flags as well
as the printed value in these calls:

```lean
#eval (1 : Float32) / 0
-- inf
#eval (0 : Float32) / 0
-- NaN
#eval ExecFloat.Binary.divWithStatus (1 : Binary32) 0 (rounding := .nearestEven)
-- (inf, { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := false })
#eval ExecFloat.Binary.divWithStatus (0 : Binary32) 0 (rounding := .nearestEven)
-- (nan, { invalid := true, divideByZero := false, overflow := false, underflow := false, inexact := false })
#eval ExecFloat.Binary.mulWithStatus (ExecFloat.Binary.ofBits32 0x7f7fffff) (2 : Binary32)
  (rounding := .nearestEven)
-- (inf, { invalid := false, divideByZero := false, overflow := true, underflow := false, inexact := true })
#eval ExecFloat.Binary.divWithStatus (ExecFloat.Binary.ofBits32 0x00000001) (2 : Binary32)
  (rounding := .nearestEven)
-- (0, { invalid := false, divideByZero := false, overflow := false, underflow := true, inexact := true })
```

The native evaluations show infinity for $1/0$ and NaN for $0/0$. The status-bearing calls add
the reason: division by zero in the first case and invalid operation in the second. The product
of the largest finite binary32 word, `0x7f7fffff`, by two overflows to infinity and sets both
`overflow` and `inexact`.

The last call halves the smallest positive subnormal, `0x00000001`. Its exact value is halfway
between zero and that smallest subnormal. Nearest-even rounding returns zero, losing the
nonzero exact value, so both `underflow` and `inexact` are set. A subnormal result alone is not
enough to set underflow: FloatLib detects tininess after rounding and requires inexactness.

The value alone cannot distinguish all exception histories. FloatLib computes flags from the
operands, exact arithmetic, and delivered result, rather than reading the host's status register.
[Chapter 08](#/chapter/ieee-binary-formats) develops the status and rounding contracts.

The refinement theorem is available on the ordinary expression used by a program:

```lean
example (x y : Binary32) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y

example (x y : Binary32) : x + y = Configured.Backend.wordAdd x y := rfl

example (x y : Binary32) :
    Configured.Backend.wordAdd x y = Configured.Spec.add x y :=
  Configured.Backend.wordAdd_eq_spec x y

#float_info Float32
-- Float information: Lean native Float32
--   standard: IEEE 754 binary32 runtime format through Lean's native float API
```

Here we use [[FloatLib.Floats.Formats.BinaryInterchange.Configured.Backend.wordAdd_eq_spec]] at
binary32; the same certificate covers other configured formats and carriers. It certifies the
software word kernel, not the processor's floating-point addition.

The `#float_info Float32` query collects the native conversion and logical-model theorems,
with their input conditions, alongside the configured software certificates. It also records
which operations depend on the compiler and host runtime, so we can distinguish the theorem
we are applying from the implementation that executes a native call.

## Opting into guarded host operations

The [unchecked host module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean) must be imported
explicitly; `import FloatLib` does not reach it. It exposes ten arithmetic functions:
[[FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked.add32]], `sub32`,
`mul32`, `div32`, and `sqrt32`, with corresponding `64` functions. They take and return the
ordinary configured binary32 or binary64 values. They do not carry refinement certificates.

The guard decides whether to use a host operation or the proved software fallback:

| Operation | Inputs that use the host operation |
| --- | --- |
| Addition, subtraction, multiplication | Both operands finite |
| Division | Both operands finite and the divisor nonzero |
| Square root | A finite nonnegative operand, or negative zero |

NaNs, infinities, zero divisors, and negative nonzero square-root inputs therefore use the
software path. Square root accepts negative zero so it can return the required negative-zero
result; other negative inputs use software. There is no unchecked FMA: multiplying and then
adding through Lean's primitives would introduce two roundings and would not implement a fused
operation.

The addition guard is short enough to inspect directly. This transcription uses the public
bit conversions and writes the fallback as `left + right`, which the refinement examples above
identify with the certified software entry point. It reuses the fourteen `pairs32` inputs from
the raw comparison:

```lean
/-- Whether a binary32 word is finite: the exponent field is not all ones. -/
def binary32Finite (bits : UInt32) : Bool :=
  ((bits >>> 23) &&& 0xff) != 0xff

/-- A transcription of `NativeFPU.Unchecked.add32`: host addition on finite operands, software otherwise. -/
def guardedHostAdd32 (left right : Binary32) : Binary32 :=
  let l := ExecFloat.Binary.toBits32 left
  let r := ExecFloat.Binary.toBits32 right
  if binary32Finite l && binary32Finite r then
    ExecFloat.Binary.ofBits32 (Float32.ofBits l + Float32.ofBits r).toBits
  else
    left + right

#eval pairs32.countP fun (a, b) =>
  ExecFloat.Binary.toBits32 (guardedHostAdd32 (ExecFloat.Binary.ofBits32 a) (ExecFloat.Binary.ofBits32 b)) !=
    ExecFloat.Binary.toBits32 (ExecFloat.Binary.ofBits32 a + ExecFloat.Binary.ofBits32 b)
-- 0
```

`binary32Finite` checks that the exponent field is not all ones. Finite operand pairs reach
`Float32` addition; a NaN or infinity causes the function to call the software operation instead.
The final evaluation counts output-word disagreements against FloatLib addition and returns
zero. The raw comparison returned two for addition because its NaN pairs always crossed into
Lean's canonicalizing representation. The guard keeps those pairs in software, preserving the
FloatLib payload result.

The branch order is essential. The function inspects the exponent in the FloatLib word before
calling `Float32.ofBits`. For the NaN word `0x7fc12345`, that exponent is all ones, so the
fallback still has the original payload available. For the ordinary pair 1 and 2, both
exponents are finite and the function takes the host branch. Inspecting the words only after
native conversion would be too late to preserve the NaN payload.

All fourteen pairs agree with software under nearest-even rounding on this machine.
That shows how the guard handles these examples; we have no theorem covering every host call.
The division and square-root guards also keep the invalid operations listed in the table
in software.

Compiled host calls require **round-to-nearest, ties-to-even and gradual underflow**. Changing the
rounding register, enabling flush-to-zero, or enabling denormals-are-zero can make a host
call disagree with the software specification. The guard checks operands; it does not certify
the process's floating-point environment. The input comparisons found no mismatches under
the tested environment; they do not prove agreement in every environment.

These functions are explicit calls. They are not `@[implemented_by]` substitutions behind the
certified operations, and the planner cannot select them. The fixed-format candidates and
[[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.selectCertified_binary32AddCandidates]]
keep certified binary32 selection on proved software.

Use `Float` or `Float32` for host arithmetic when their formats and runtime assumptions fit the
application. Use `ExecFloat.Binary` when a computation needs its refinement theorem, explicit
rounding direction, returned status, payload-preserving words, or a different layout. The
unchecked module offers an explicit host call on FloatLib values when the application accepts
the remaining runtime assumptions. Its performance still needs measurement in that application;
the native C bars establish the reference comparison, not the cost of that substitution.

<a id="inspecting-and-reproducing-the-evidence"></a>
