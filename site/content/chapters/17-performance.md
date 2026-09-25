---
number: "17"
slug: performance
title: "Performance"
summary: "Measure ordinary public binary arithmetic against MPFR, then compare other libraries on their separate workloads."
phases: [trust]
---

Our performance goal is to reach MPFR's speed with proved arithmetic. On the ordinary
public binary32 workload below, multiplication takes **17.9 ns in FloatLib and 27.5 ns
in MPFR**. Binary64 and binary128 leave much larger gaps. Individual operations tell us
more than one score for the library.

Lean erases proof terms during compilation [@leanReference]. These measurements time the
arithmetic and the work around each call; the algorithms, representations, and calling paths
still determine how quickly a proved operation runs.

<a id="the-times-behind-the-curves"></a>
<a id="timing-results"></a>
<a id="current-binary-arithmetic"></a>

## Public binary arithmetic

These public `ExecFloat.Binary` calls include the configured representation and selected
software kernel. MPFR matches the precision, exponent bounds, and nearest-even rounding
with gradual underflow. Each point cycles through sixteen prepared input triples whose full
encodings are checked before timing. The loop calls the operation and checksums the low
64 result bits; the checksum does not select inputs.

The three trials ran sequentially on the same pinned CPU of an **Intel Xeon Platinum
8275CL**, shared with other work. Plotted times are each arm's median; ratios use the median
of the within-trial FloatLib/MPFR ratios. Whiskers show the observed minimum and maximum,
not confidence intervals, so small differences deserve little weight.

![FloatLib and MPFR for six public binary operations at encoded widths 32 through 4096](assets/public-binary-performance.png "Median nanoseconds per operation across three trials; whiskers show the observed minimum and maximum, not confidence intervals. Both axes are logarithmic; lower is faster.")

At binary32, FMA also runs faster: **33.2 ns versus 43.1 ns**. Subtraction is close, while
addition, division, and square root take longer than MPFR. Binary64 and binary128 are
slower across all six operations. Binary64 multiplication takes **239 ns**, about **8.82
times** MPFR's time, and square root takes **1.34 µs**, about **45.5 times** MPFR's time.

At 4,096 bits, division takes **4.57 µs**, about **2.12 times** MPFR's time. Multiplication
is about **3.26 times** slower and FMA about **2.77 times** slower. Addition and square
root leave larger gaps, about **21.2** and **8.10 times**, respectively.

![FloatLib and MPFR for six public binary operations below 32 bits](assets/public-binary-low-precision.png "Median nanoseconds per operation across three trials; whiskers show the observed minimum and maximum. The vertical axis is logarithmic; lower is faster.")

[The low-precision plot](#/chapter/performance/figure-public-binary-low-precision) adds binary16,
bfloat16, and four layouts from 7 to 9 bits. The small layouts use IEEE-style encodings
with infinities and NaNs. Binary16 multiplication takes **11.0 ns versus 28.4 ns** for
MPFR, about **2.58 times faster**; bfloat16 multiplication takes **12.1 ns versus
27.5 ns**, about **2.26 times faster**. Addition and subtraction are also faster in
these two formats, while division, square root, and FMA are slower.

The selected kernel matters as much as the width. Square root uses exhaustive tables
in the 7-bit and 8-bit formats and takes about **23 ns**. Binary16 and bfloat16 select
word kernels and take about **1.3 µs** for square root, compared with **30 to 33 ns** for
MPFR. Most other 7-bit and 8-bit operations also take longer than MPFR on these inputs.

The [benchmark instructions and data](#/chapter/performance/public-binary-measurement-record)
describe the complete loop. The remaining experiments use their own workloads and are
reported separately below.

<details>
<summary>The public operation and its theorem</summary>

<a id="executing-the-operation-covered-by-the-theorem"></a>

### Running the code we proved

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

The theorem covers every pair of binary64 inputs and includes the rounding step.
Its right-hand side is a floating-point specification. The public-call walkthrough in
[the planner chapter](#/chapter/backends-and-the-planner/following-a-public-arithmetic-call)
connects this expression to the selected software kernel.

</details>

## Matched binary arithmetic with Flocq and MPFR

We also timed FloatLib, extracted Flocq, and MPFR with matching significand precision,
exponent bounds, and nearest-even rounding. Each adapter rounds the same exact rational
inputs once. The [numerical checks](#/chapter/external-validation/binary-arithmetic-with-flocq-and-mpfr)
compare the complete values before we use these inputs for timing.

![FloatLib, extracted Flocq, and MPFR across eleven matching binary formats and six operations](assets/flocq-matched.png "Nanoseconds per operation at matching binary precision and exponent bounds. Both axes are logarithmic; lower is faster. Measurements ran on an Intel Xeon Platinum 8275CL.")

[The matched plot](#/chapter/performance/figure-flocq-matched) shows the measured widths from
6 to 4,096 bits. FloatLib is faster than the extracted Flocq program except for 8-bit FMA,
where Flocq takes 846 ns and FloatLib takes 1,601 ns. For binary64 multiplication,
FloatLib takes 330 ns and Flocq takes 10,575 ns. MPFR takes 32 ns there and is faster than
FloatLib at every point in this comparison.

Each operation and width draws from sixteen input sets during timing. The experiment ran on
an **Intel Xeon Platinum 8275CL**, with one calibrated trial per entry and no estimate of timing
variability. These dependent scalar loops include input selection, allocation, and observing
the result. FloatLib explicitly calls proved word kernels at binary32/64 and uses public
operations under `PlanningThroughput` at other widths. This differs from the ordinary public
calls above.

<details>
<summary>Extraction, inputs, and the timed Flocq loop</summary>

<a id="flocq-exactly-which-extracted-program"></a>

### The Flocq program we timed

Our [Flocq wrapper](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/rocq/FlocqKernel.v)
uses **Flocq 4.2.2** [@boldoMelquiond2011]. It exposes `Bplus`, `Bminus`, `Bmult`, `Bdiv`,
`Bsqrt`, and `Bfma` from `IEEE754.BinarySingleNaN`. Input conversion uses the proved
`Bdiv_correct_aux` helper to round an exact integer quotient once. Precision and exponent
bounds match the FloatLib descriptor; all three implementations use nearest-even rounding
and gradual underflow. Flocq requires `0 < precision < emax`, so the custom 4-, 5-, and
7-bit layouts are absent from all three curves.

We extracted the wrapper with Coq 8.20.1 and compiled it with OCaml 4.13.1 and Zarith.
FloatLib used Lean 4.34.0; the MPFR adapter used MPFR 4.1.0 and GCC 11.5.0. This experiment
kept the timing processes on the same logical CPU.

In the main loop, each result selects the next of sixteen prepared input sets and contributes
to a checksum; it does not become the next operand. Square root at
1,024, 2,048, and 4,096 bits instead uses complete blocks of sixteen inputs for all three
implementations: each result affects their order, and each block visits every input once.
This ensures that even the slowest wide square roots time the full input set. Other points
use the original chain, whose calibrated length differs between implementations.

The timer includes arithmetic, value allocation, normalization for the fingerprint, and
checksum work. Input construction, warmup, proof checking, and compilation happen before it
starts. The [result README](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/flocq-matched/README.md)
contains the data, environment details, and commands to reproduce the figure.

</details>

## Other measured workloads

### P3109 arithmetic with FLoPS

FLoPS gives us another executable Lean implementation with refinement proofs
[@flopsArtifact]. We compared three P3109 formats using nearest-even rounding and
no saturation. All **529,152 arithmetic cases** and the **192 exact timing fixtures**
agreed bit for bit; [the validation chapter](#/chapter/external-validation/p3109-arithmetic-with-flops)
describes the input coverage.

This [experiment](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/p3109-flops/results.json)
ran on an **Intel Xeon Platinum 8275CL**. The entries below
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
The retained nine-trial IEEE and posit tables below use different formats and a different
machine.

### Scalar conversions with TensorLib

TensorLib's small-format conversions are a useful performance comparison in their own
right [@tensorLib]. We time its specialized `Float32` conversion functions against
FloatLib's general `Model.cast` for the same four formats. All 128 input/output timing
fixtures agree exactly; the [broader conversion checks](#/chapter/external-validation/scalar-conversions-with-tensorlib)
cover rounding boundaries and exceptional values too.

The [results](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/tensorlib/results.json)
are **median nanoseconds per conversion** across nine paired trials on the
**Intel Xeon Platinum 8275CL**, using one logical CPU. “Encode” converts Float32 to the
small format; “decode” converts back.

| Format | FloatLib encode | TensorLib encode | FloatLib decode | TensorLib decode |
| --- | ---: | ---: | ---: | ---: |
| FP16 | 2,201.0 | 265.3 | 2,098.2 | 268.9 |
| BF16 | 2,219.9 | 252.6 | 1,590.0 | 268.3 |
| E4M3FN | 3,642.9 | 279.7 | 2,187.5 | 272.9 |
| E5M2 | 2,248.1 | 267.9 | 2,083.1 | 270.5 |

TensorLib is faster in all eight conversions, by about **5.9 to 13.0 times**.
TensorLib manipulates the fixed-format fields directly; FloatLib's descriptor cast
handles format parameters and uses exact dyadic decoding and rounding. These timings
use its field-copy widening path. Compatible widenings now use a
[proved word shift](#/chapter/ieee-binary-formats/casting-between-widths),
which is not measured in this table.
For the normal inputs timed here, TensorLib's casts use integer shifts, masks, and
rounding. Its FP16 and FP8 subnormal decoders do use `Float32` multiplication, but those
branches are outside this timing workload. The measured speedup therefore does not
establish an FPU advantage. TensorLib's floating tensor arithmetic does use native
operations; [the validation chapter](#/chapter/external-validation/symbolic-arithmetic-and-tensors)
explains that execution choice and FloatLib's optional hardware path.

Both adapters use the same loop over sixteen normal finite inputs from $-4$ to $4$,
excluding zero. Each output selects the next input and contributes to a checked checksum.
Input values are constructed before timing; lookup, conversion, result bits, and checksum
bookkeeping are included. We alternate which library runs first in each pair and use
256 warmup iterations. FloatLib uses Lean 4.33.1 and TensorLib uses Lean 4.33.0, both
with Clang 22.1.4. These are scalar dependent-call timings; a tensor kernel that converts
many independent elements would measure a different workload.

## The nine-trial software comparison

The following tables and optional plots retain a separate experiment on an **Intel Xeon
Platinum 8488C**. It uses sixteen rational input sets and result-dependent input selection:
each result chooses the next set, rather than becoming the next operand. Medians are across
nine trials pinned to one logical CPU; bands show the 5th to 95th percentiles, not confidence
intervals. These times include input selection, representation, adapter work, and checksums.

FloatLib explicitly calls proved word kernels at binary32/64 and uses public operations under
`PlanningThroughput` at other widths. The planner ranks certified candidates by configured
costs; it does not choose the fastest line in a plot. This retained run uses different calling
paths, inputs, and toolchains from the public-call experiment above. Its results describe
that measured version of the library.

### Binary32

The tables report **median nanoseconds per operation**. The
[overview plot](#/chapter/performance/figure-format-comparison-main) also shows the
intermediate and wider formats.

| Implementation | Add | Subtract | Multiply | Divide | Square root | FMA |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| **FloatLib** | **138.6** | **128.3** | **102.0** | **123.7** | **93.0** | **140.5** |
| Berkeley SoftFloat | 22.9 | 23.1 | 18.2 | 19.6 | 27.8 | 29.2 |
| MPFR | 34.1 | 34.9 | 31.8 | 33.3 | 45.5 | 47.6 |
| Native C | 8.4 | 8.4 | 8.7 | 10.7 | 11.4 | 10.9 |

SoftFloat, MPFR, and native C are faster than FloatLib on all six operations here.
Native C uses the processor's floating point unit.

### Binary64

| Implementation | Add | Subtract | Multiply | Divide | Square root | FMA |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| **FloatLib** | **312.8** | **293.5** | **250.7** | **1,447.3** | **1,271.3** | **1,277.2** |
| Berkeley SoftFloat | 23.3 | 23.1 | 18.3 | 29.5 | 30.6 | 29.0 |
| MPFR | 36.7 | 35.4 | 31.9 | 31.3 | 49.2 | 49.4 |
| Native C | 8.2 | 8.2 | 8.5 | 11.6 | 13.1 | 10.7 |
| CPython | 801.3 | 827.3 | 826.0 | 821.9 | 800.1 | n/a |

Against CPython, FloatLib wins addition, subtraction, and multiplication, but takes
longer for division and square root. The Python timings include its runtime; the
version measured has no `math.fma`.

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
for the proved software operation. The separate series identifies that different execution
path.

<a id="comparing-with-leans-native-floats"></a>

### Host arithmetic as a reference

The native C column measures the host's `float` and `double` arithmetic through the same
nine-trial loop. Binary32 addition takes **8.36 ns** compared with **138.6 ns** for FloatLib;
at binary64, the corresponding times are **8.20 ns and 312.8 ns**. The software/native ratios
are 16.6 and 38.2. They vary by operation: binary32 square root is 8.1, and binary64 division
is 124.6. The [host comparison plot](#/chapter/performance/figure-ch17-host-vs-software)
collects these ratios.

These are C-loop measurements. Lean's `Float32` and `Float` wrappers, and FloatLib's
`NativeFPU.Unchecked` functions with their guards and bit conversions, need separate timings.
The [native-floats chapter](#/chapter/lean-native-floats) follows those interfaces through
finite rounding, NaN payloads, and the conditions on a guarded host call.

## More views of the nine-trial comparison

The optional views below expand the same nine-trial data. They expose operation and width
changes without combining them with the current public-call or matched Flocq measurements.

<details>
<summary>Overview, ratios, small formats, wide operations, and host comparison</summary>

### Overview across encoded widths

Blue squares are FloatLib binary and green circles are FloatLib posits. Both curves run proved
software. Lower is faster; both axes are logarithmic. Each marker is a measured encoded width,
and lines connect markers across kernel changes. Posits start at 2 bits and binary at 4 bits.
The largest measured width, 4,096 bits, is not a library limit. Missing markers denote unavailable
or excluded comparisons, as the [validation chapter](#/chapter/external-validation/why-some-performance-markers-are-missing)
explains.

![Six arithmetic operations across encoded widths from 2 to 4,096 bits; median nanoseconds per operation with 5th to 95th percentile bands](assets/format-comparison-main.png "Median nanoseconds per operation across encoded widths, with 5th to 95th percentile bands. Both axes are logarithmic; lower is faster. Missing markers denote unavailable or excluded comparisons.")

<a id="reading-the-ratios"></a>

### Comparing relative times

Equal encoded width is a storage comparison. A binary format has a fixed significand precision;
a posit's precision varies with its value. MPFR uses the binary companion's precision.
Posit-versus-binary timings at the same width do not imply equal
accuracy or equal dynamic range. The 8-bit binary point, for example, uses an E4M3
layout, and the 4,096-bit point is a custom binary layout with 19 exponent bits.

![FloatLib time divided by the external implementation's time for addition, multiplication, and division, at equal encoded widths](assets/ch10-external-ratios.png "FloatLib time divided by the comparison library’s time at equal encoded width. Lower is faster for FloatLib relative to that library; 1 means equal times. Different formats still have different numerical contracts.")

A ratio of 1 means equal median time; 10 means FloatLib took ten times as long.
For binary64 addition, the MPFR point comes from the two measured medians:

$$
\rho_{\mathrm{MPFR}}
= \frac{312.7723\ \mathrm{ns/op}}{36.6719\ \mathrm{ns/op}}
\approx 8.53.
$$

This experiment divides separately computed medians; the public-call experiment instead
uses the median of within-trial ratios. On the logarithmic axis, equal vertical distances
represent equal multiplicative changes. The ratios compare complete timed loops with
different algorithms, representations, and adapters. They cannot isolate a cost attributable
to verification.

<a id="small-formats-and-changes-of-kernel"></a>

### Why a wider format can be faster

![All six operations from 2 to 16 bits, with each measured width labelled, including 5, 6, and 7 bits](assets/format-comparison-low-width.png "Median nanoseconds per operation at widths 2 to 16, with percentile bands and logarithmic axes. Lower is faster; only measured widths have markers.")

The small-width plot expands the crowded left edge of the overview. Each of 5, 6, and 7 bits
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
current API selects. These queries describe the current source, rather than reconstructing
the historical executable used in the nine-trial run:

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

[[FloatLib.Floats.ExecFloat.Backend.selectCertified_run_eq_spec]] connects the selected
candidate's result to the specification. The [planner walkthrough](#/chapter/backends-and-the-planner/following-a-public-arithmetic-call)
follows that certificate into an ordinary `x + y` call.

### Multiplication, fused operations, and wide arithmetic

![Multiplication and fused multiply-add, with median ns/op and percentile bands across encoded widths](assets/format-comparison-mul-fma.png "Multiplication and fused multiply-add timings across encoded widths. Both axes are logarithmic; bands show the 5th to 95th percentiles and lower is faster.")

Fused multiply-add rounds the exact product-plus-addend once. Its intermediate product can
therefore be wider than an ordinary multiplication's rounded result. The plot expands the
width dependence seen in the binary32 and binary64 FMA table entries. CPython 3.11.2 has no
`math.fma`, so it has no FMA point.

![Division and square root, with median ns/op and percentile bands across encoded widths](assets/format-comparison-div-sqrt.png "Division and square-root timings across encoded widths. Both axes are logarithmic; lower is faster. Universal square roots that disagreed on the benchmark inputs are excluded.")

At 4,096 bits in this nine-trial workload,
FloatLib binary division took **10.41 µs**, compared with **2.37 µs** for MPFR.
Square root took **40.71 µs**, compared with **1.69 µs** for MPFR. The ratio is 4.39 for division
and 24.07 for square root. Addition at the same width took 4.26 µs. Wide operations have distinct
costs even when they share the same public representation.

The proved software path builds multiword arithmetic from ordinary machine words, and the
generic engine also allocates arbitrary-precision integers. A planner label alone does not
identify all that work: the 256-bit `ExecFloat.Binary` family selects the exact baseline for
both division and square root, while square root uses the shared integer-root dispatcher
inside that baseline. We can inspect the selected candidates:

```lean
#eval (ExecFloat.Div.selectedCandidate (F := ExecFloat.Binary.Family 8 23)).name
-- "binary-interchange division fixed-format kernel"
#eval (ExecFloat.Div.selectedCandidate (F := ExecFloat.Binary.Family 19 236)).name
-- "binary-interchange division exact baseline"
#eval (ExecFloat.Sqrt.selectedCandidate (F := ExecFloat.Binary.Family 19 236)).name
-- "binary-interchange square root exact baseline"
```

Binary32 division has a fixed-format candidate, while both queries at 256 bits report the exact
baseline. Choosing `ExecFloat.BinaryLimbs` makes direct limb-carrier division and square-root
candidates available, as [chapter 16](#/chapter/backends-and-the-planner/choosing-the-limb-carrier)
shows; those candidates use a different public representation from the `Binary` queries above.
Within the generic IEEE path,
[bounded alignment](#/chapter/kernels-fixed-word-algorithms/bounded-alignment-in-generic-addition)
limits the intermediates for well-separated add/sub/FMA operands, and
[increasing-precision square root](#/chapter/kernels-fixed-word-algorithms/increasing-precision-for-arbitrary-precision-square-root)
starts its refinements on a leading portion of the radicand. Both preserve the specified result.
Their effect on time depends on the operands and must be measured through the public call,
including decoding, rounding, and result observation.

### Host arithmetic and software

![Native C and FloatLib proved software at binary32 and binary64; bars show median ns/op and labels show FloatLib/native time ratios](assets/ch17-host-vs-software.png "Median nanoseconds per operation for native C arithmetic and FloatLib software at binary32 and binary64. Lower is faster; annotations give the software/native time ratio.")

</details>

## Method for the nine-trial comparison

<details>
<summary>Timed work, toolchains, adapters, and input agreement</summary>

### What one timed operation includes

The nine-trial comparison starts with sixteen sets of rational inputs, converted by the
adapters before timing. An arithmetic result selects the next set of inputs and
contributes to a checksum, so later work depends on the operation being measured. This avoids a
loop that repeatedly computes a constant, and avoids letting multiplication or division collapse
into a stream of zeros or infinities.

For example, the first pair in the [exact workload](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/lean/FloatLibBenchmarks/Support/ExactWorkload.lean) is
$-9/8$ and $-69/35$. The first is exactly binary-representable at ordinary IEEE widths; the
second needs rounding. MPFR converts the rationals directly, without an earlier binary64
rounding error. Universal imports the posit encodings generated from these inputs by
FloatLib. This setup work happens before the clock starts.

In one addition iteration, the loop loads an already-converted pair, adds it, observes the
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
intermediate result. The Flocq comparison adds a separate check of complete numerical values.

Fast and slow implementations need different loop lengths to get useful measurements.
A short preliminary run estimates how many iterations will take about 200 ms; every
reported trial lasts at least 50 ms. The order is shuffled and rotated across nine trials
so the same implementation does not always run first. We report the median and show
the 5th to 95th percentiles. The underlying data also includes quartiles, standard deviation,
and median absolute deviation.
Most adapters warm up for 256 iterations.

The timing loops ran one at a time on the same logical CPU. This avoids migration between
CPUs, though other work on the machine can still affect caches and clock speed.
The compiler was GCC 12.2.0 with
`-O3 -march=native` for the C adapters; FloatLib used Lean 4.33.1. The external builds are
described below. Compilation, process startup, input construction, warmup, and CSV output
happen outside the measured interval. Runtime allocation and garbage collection that occur
inside the loop contribute to the reported time.

### How we ran the external implementations

Each adapter follows the dependent loop using its library's own representation. MPFR reuses
a destination object; Python creates and observes Python objects. The separate Flocq experiment
returns structured values. The corresponding allocation and observation costs remain in
each experiment's measured loop.

#### MPFR: matching precision and exponent range

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

#### SoftFloat, native C, and Python

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

#### Universal: checking the posit inputs before timing

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

</details>

<a id="what-the-independent-checks-tell-us-about-speed"></a>
<a id="which-libraries-did-we-time"></a>

## Libraries timed separately

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

<a id="inspecting-and-reproducing-the-evidence"></a>

## Reproducing the measurements

The [benchmark method](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/docs/Comparison.md)
and [results](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/main/README.md)
provide the commands, toolchains, measured sources, and raw trials for reproducing
the retained nine-trial measurements. The dedicated Flocq, P3109, and TensorLib sections
link their own records. The current public-call record follows.

<a id="public-binary-measurement-record"></a>

<details>
<summary>Public binary measurement record</summary>

The public-call
[measurements](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/public-binary/measurements.csv)
retain each trial, execution order, iteration count, elapsed nanoseconds, and checked
warmup/result sinks. The compact
[metadata](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/public-binary/metadata.json)
records source, driver, executable, and fixture SHA256 identities, format layouts,
and CPU affinity.

FloatLib uses Lean **4.34.0** and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
The external arm uses MPFR **4.1.0-p13** with GMP **6.2.1**. Width means encoded
storage: the wide plot uses significand precisions 24, 53, 113, 237, 493, 1,005, 2,029,
and 4,077 bits. Binary16 uses 11 significand bits and bfloat16 uses 8. The smaller
layouts label their stored exponent and fraction widths. MPFR matches each format's
precision and exponent range.

Iteration counts are calibrated separately per arm toward 40 ms, then held fixed across
three trials, with 512 warmup calls. Each timed count covers whole sixteen-input cycles.
The shortest plotted trial is 36.2 ms; recorded CPU-quota throttling is zero.
Parsing, input construction, full-encoding checks, warmup, and process startup precede
timing. Allocation and result observation inside the loop are included.
Speed ratios use the median of paired trial ratios; plotted times use each arm's median.

The [fixture archive](assets/public-binary-fixtures.zip) contains the exact encoded input
triples, expected complete outputs, and retained full-encoding agreement receipts for the
84 plotted format/operation cases. The [benchmark bundle](assets/public-binary-benchmark.tar.gz)
contains the driver, prepared inputs, and instructions for comparing a FloatLib
checkout with MPFR. Its broader encoding checks also cover custom widths, rounding
boundaries, large exponent gaps, and limb storage.

The [figure script](https://github.com/lean-dojo/FloatLib/blob/main/site/content/assets/figures/ch15_public_binary.py)
checks the retained data and regenerates both PNGs:

```bash
python3 site/content/assets/figures/ch15_public_binary.py
```

This command reproduces the figures from measurements; it does not rerun the benchmark.

</details>
