# Format comparisons

We compare FloatLib with other arithmetic libraries to see where our kernels do well and
where an optimization would help. Our plots cover six scalar operations at storage widths
from 2 to 4,096 bits, and every command here runs from the repository root.

## Recreate the saved tables and figures

```bash
benchmarks/scripts/verify-main-result.sh
```

That script checks the saved measurements and regenerates their tables and figures from the
recorded trials. You need Git, Python 3, and Matplotlib, but nothing gets compiled and no
operation is timed again. For the files behind the
[performance chapter](../../site/content/chapters/12-performance.md), see the
[results README](../results/main/README.md). The saved
run departs from the publication profile in two ways: it leaves out Flocq, and one cell has
four trials just under the 50 ms floor.
`release/provenance/publication-exceptions.json` declares both, and
`verify_release_matrix.py --exceptions` accepts the declared departures and nothing more.
Without that option, the verifier applies the full publication profile.

The matched Flocq comparison has its own data and figure:

```bash
python3 benchmarks/plots/flocq_matched.py \
  --out "${TMPDIR:-/tmp}/floatlib-flocq-matched.png"
```

It also rebuilds the nine-trial medians from the raw trials, and it checks the complete
numerical values along the way. You'll find its fixture-chain measurements and the
complete-block square-root supplement described in the
[matched result README](../results/flocq-matched/README.md).

The public binary measurements that open the performance chapter have a record of their own
in [`results/public-binary/`](../results/public-binary/). They compare FloatLib's public binary
arithmetic with MPFR at matching precision, exponent range, and rounding, for the six
operations on 14 formats from 7 to 4,096 bits, with nine trials per format, operation, and
implementation. Multiply that out for the two implementations and you get the 1,512 raw
trials in its `measurements.csv`, each in nanoseconds per public operation. Beside it,
`metadata.json` records the protocol. Both implementations share one pinned CPU and
alternate their order AB, BA, AB, and so on, and each loop cycles through 16 prepared inputs
after 512 warmup iterations, with every measured interval aiming at 40 ms. From the metadata
you also get the Lean, Mathlib, and MPFR versions, the CPU and the affinity of every row, the SHA-256
of the measurements and of the fixture archive `site/content/assets/public-binary-fixtures.zip`,
and, under `measured`, the date, the measured commit (`8c88715`, release 2.0.0), and how this
run differs from the earlier three-trial campaign. For the 84 ordinary finite-input cases,
every complete input and output encoding matched an integer oracle and MPFR, and every warmup
and timed checksum was recomputed independently.

These numbers belong to the source and environment recorded with them. Rebuilding the figures
lets you check how the plotted numbers were calculated, but measuring a change to the
implementation needs a new run. If your Matplotlib version differs from ours, the verifier
compares the tables exactly and only checks that the figures can be generated, since image
files can differ between plotting versions.

## Measure the current code

Running it takes Linux tools, including `/proc`, GNU `time`, and `taskset`. Besides those,
you'll need the repository's pinned Lean toolchain, a C compiler, `pkg-config`, MPFR
development headers and libraries, Git, Python 3, and Matplotlib. MPFR is required even if you
select only a few implementations, because both C adapters use it during setup.

By default we also build Berkeley SoftFloat with Make, for a Linux x86-64 target, and
Stillwater Universal with a C++20 compiler. Unless you supply checkouts with
`SOFTFLOAT_SOURCE` and `UNIVERSAL_SOURCE`, the script fetches pinned external revisions. If
you do, give it
clean checkouts that nothing else uses, because the SoftFloat setup checks out its selected
revision and a supplied Universal checkout must already be at the pinned revision. Flocq is
optional and needs either Docker or an executable supplied through `FLOCQ_BENCH_BINARY`.

Here is a one-trial run to check that the tools are set up:

```bash
FORMAT_COMPARE_DEVELOPMENT_ONLY=1 \
benchmarks/scripts/format-comparison.sh 1 "${TMPDIR:-/tmp}/floatlib-format-check"
```

Each run needs a new output directory outside the checkout, because the script rejects an
existing path. Without an output argument, it creates a timestamped directory under
`${TMPDIR:-/tmp}/floatlib-benchmarks/format-comparison`. The shared
[build helper](../../tests/lib/lake.sh) keeps Lean build products outside the checkout, and
temporary external builds follow `TMPDIR` too, with `FORMAT_COMPARE_TMPDIR` as their own
override.

For the full comparison, we use repeated trials, all implementations, and a fixed CPU:

```bash
FORMAT_COMPARE_DEVELOPMENT_ONLY=0 \
FORMAT_COMPARE_INCLUDE_FLOCQ=1 \
FORMAT_COMPARE_INCLUDE_UNIVERSAL=1 \
FORMAT_COMPARE_INCLUDE_SOFTFLOAT=1 \
FORMAT_COMPARE_INCLUDE_PYTHON=1 \
FORMAT_COMPARE_CPU="$(python3 -c 'import os; print(min(os.sched_getaffinity(0)))')" \
benchmarks/scripts/format-comparison.sh 9 /path/to/results/format-comparison
```

The Python expression picks the first CPU available to the process, and you can set
`FORMAT_COMPARE_CPU` to any other available CPU. A full run requires this setting, at least
seven trials, and calibrated iteration counts. By default each measured interval must last at
least 50 ms, and calibration aims for 200 ms.

For a matched binary fixture-chain comparison with just FloatLib, Flocq, and MPFR:

```bash
FORMAT_COMPARE_PROFILE=flocq \
FORMAT_COMPARE_DEVELOPMENT_ONLY=0 \
FORMAT_COMPARE_CPU="$(python3 -c 'import os; print(min(os.sched_getaffinity(0)))')" \
benchmarks/scripts/format-comparison.sh 9 /path/to/results/flocq-comparison
```

This profile measures all six operations at the 11 widths that all three adapters support,
from 6 to 4,096 bits. It keeps the trial, duration, and agreement checks of the full
comparison but doesn't build the other providers.
It measures the chain at every width and leaves out the complete-block square-root workload
behind nine entries in the [saved Flocq figure](../results/flocq-matched/README.md).

Pinning reduces the noise from moving between CPUs, but a quiet machine matters as well,
because shared caches, memory bandwidth, frequency changes, and other processes can all
affect the result. Keep the recorded source, compiler, and machine details next to any
numbers you compare.

On a full run the script checks the complete measurement matrix, and it rejects disabled
calibration, changed agreement-prefix lengths, reused Lean executables, dirty external
checkouts, and incomplete or short timing rows. `FORMAT_COMPARE_BUILD_JOBS` controls
SoftFloat's `make -j` and leaves Lean and Lake parallelism alone.

When you're working on a particular operation, you can shorten the run:

```bash
FORMAT_COMPARE_DEVELOPMENT_ONLY=1 \
FORMAT_COMPARE_WIDTHS="32 64" \
FORMAT_COMPARE_OPERATIONS="add mul fma" \
benchmarks/scripts/format-comparison.sh 1 "${TMPDIR:-/tmp}/floatlib-format-subset"
```

The plot and metadata mark these as development measurements. They're good for testing the
harness before you spend the time on a full comparison.

## What the benchmark measures

Every run starts from the exact rational inputs in
[`ExactWorkload.lean`](../lean/FloatLibBenchmarks/Support/ExactWorkload.lean). Before timing,
the comparable binary adapters, Flocq among them, round each value once into the destination
format, and the square-root inputs are all nonnegative.

The timed loop is a scalar dependency chain, where each result picks the next member of a
16-value input set. We adapted the dependency-chain technique from
[Abel and Reineke's uops.info methodology](https://doi.org/10.1145/3297858.3304062).
Choosing among fixed inputs keeps multiplication, division, and square root from
overflowing, underflowing, or settling at a fixed point over and over.

So the timings include input lookup, result checksums, and the arithmetic call. What they
measure is the cost of that scalar loop, which is neither throughput over independent
operations nor the latency of a bare CPU instruction.

Each implementation, width, and operation gets its own calibrated iteration count, and we
record the loop's final checksum along with a digest of the chosen input indices. Loops of
different lengths can end on different checksums even when every operation agrees, so we
test agreement on an untimed prefix of 256 operations.

FloatLib, MPFR, and any enabled Flocq rows have to agree on that prefix at every shared binary
width. Native C and SoftFloat join in at binary32 and binary64, and CPython joins for the
binary64 operations it provides.
The runner compares both the result checksum and the input trace, and it rejects missing or
disagreeing prefixes.

We shuffle a deterministic starting order and rotate it between trials, so no implementation
is always first or last, and we save the complete order in `environment/trial-order.csv`.

## Formats and comparison points

Posit storage widths are 2, 3, 4, 5, 6, 7, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, and 4096.
We stop measuring at 4,096 bits here. FloatLib's precision doesn't stop there.

Configured binary formats begin at four bits:

- Widths 4 through 8 use E2M1, E2M2, E3M2, E3M3, and E4M3.
- Widths 16, 32, 64, and 128 use the IEEE interchange layouts.
- Widths 256 and above use 19 exponent bits.
- Optional widths 24, 48, 96, and 112 use E8M15, E11M36, E15M80, and E15M96.
  They have no equal-width posit or external row.

We call the eight-bit point E4M3 because IEEE 754 doesn't define a binary8 interchange
format.

For an optional binary-only point, call the Lean executable yourself:

```bash
source tests/lib/lake.sh
floatlib_benchmark_lake build execFloatFormatComparison
FORMAT_COMPARE_FAMILY=binary-interchange FORMAT_COMPARE_WIDTH=96 \
  FORMAT_COMPARE_ITERATIONS=10000 \
  "$(floatlib_build_path bin/execFloatFormatComparison)"
```

That prints the six operation rows for the chosen width. These widths also work as
standalone binary rows in the comparison script, which checks cross-adapter agreement for the FloatLib/MPFR
pairs you request and rejects any requested row that's missing.
If you select lanes by name, you can also run Flocq alone or next to an unpaired FloatLib or
MPFR lane. The verifier checks every requested row and its agreement-prefix length, and where
the same cell has both FloatLib and MPFR partners, it compares Flocq's result digests.

MPFR and Flocq use the significand precision of the binary format with the same storage
width, which gives us a binary comparison point. A posit's precision changes with its
magnitude, though, so equal storage doesn't make its precision equal to MPFR's.
`plots/ratios.csv` records the MPFR precision and the pairing rule behind each ratio.

## Implementations

The FloatLib curves measure certified binary and posit software arithmetic, and we compare
them with:

| Implementation | What its curve measures |
| --- | --- |
| [Berkeley SoftFloat](https://www.jhauser.us/arithmetic/SoftFloat-3/doc/SoftFloat.html) | Independent IEEE software arithmetic at binary32 and binary64 |
| [MPFR](https://www.mpfr.org/mpfr-current/mpfr.html) | Correctly rounded arbitrary-precision binary arithmetic, labelled `MPFR (binary)` |
| Native C | Host floating-point arithmetic at binary32 and binary64 |
| [CPython float64](https://docs.python.org/3/c-api/float.html) | Ordinary Python floating-point calls, including interpreter and object overhead |
| [Stillwater Universal](https://github.com/stillwater-sc/universal) | Posit arithmetic for the format-operation pairs that agree with the benchmark vectors |
| [Flocq](https://flocq.gitlabpages.inria.fr/) | Extracted OCaml/Zarith arithmetic with matching binary precision and exponent bounds |

CPython FMA shows up only when the interpreter provides `math.fma`. We don't fall back to
`x * y + z`, which rounds twice.

Flocq is off by default because its build uses the pinned Rocq container. To turn it on:

```bash
FORMAT_COMPARE_DEVELOPMENT_ONLY=1 \
FORMAT_COMPARE_INCLUDE_FLOCQ=1 \
benchmarks/scripts/format-comparison.sh
```

The Flocq wrapper rounds exact input fractions with Flocq's proved `Bdiv_correct_aux` helper
and then calls its certified binary operations, with precision, exponent bounds, nearest-even
rounding, and gradual underflow matching FloatLib and MPFR. Flocq's `BinarySingleNaN`
interface requires `precision < emax`, which rules out the custom 4-, 5-, and 7-bit layouts
here. It also has a single NaN that doesn't keep payloads, so the benchmark compares
arithmetic values.

Wide square-root checks are expensive, so each campaign computes Flocq's 256-step agreement
prefix once per format and operation and reuses it, outside timing, across calibration and
trials. Its cache starts empty and is tied to the compiled executable's SHA-256.

For Flocq the website uses the [matched results](../results/flocq-matched/README.md), and the
[main archive](../results/main/README.md) has no Flocq rows. If you supply your own
executable, its hash is recorded alongside its results, so keep its build instructions and
dependency versions too.

Before timing Universal, the C++ adapter checks all 16 operation results against fixed-width
bit vectors that FloatLib generated. A format-operation pair that's unsupported or disagrees
is recorded and left out of the plot, so every row you see has agreed with FloatLib on those
inputs.

We label Universal's software and hardware-assisted results apart. Some of its generic
square-root implementations, for instance, convert through binary64 and call the host square
root.

To pick the implementations yourself:

```bash
FORMAT_COMPARE_DEVELOPMENT_ONLY=1 \
FORMAT_COMPARE_LANES="binary-software mpfr-reference binary-native-c" \
benchmarks/scripts/format-comparison.sh
```

You can also disable an optional implementation or supply a local checkout:

```bash
FORMAT_COMPARE_DEVELOPMENT_ONLY=1 FORMAT_COMPARE_INCLUDE_PYTHON=0 \
  benchmarks/scripts/format-comparison.sh
FORMAT_COMPARE_DEVELOPMENT_ONLY=1 FORMAT_COMPARE_INCLUDE_UNIVERSAL=0 \
  benchmarks/scripts/format-comparison.sh
FORMAT_COMPARE_DEVELOPMENT_ONLY=1 UNIVERSAL_SOURCE=/path/to/universal \
  benchmarks/scripts/format-comparison.sh
```

Selecting a subset doesn't skip the setup of the other enabled implementations, so use the
`INCLUDE` settings if you want to avoid their builds as well.

## Reading the output

Lower time per operation is faster. As the width changes, a FloatLib curve can switch
kernels, and `plots/backend-regimes.csv` tells you which backend ran each operation and
format. We keep the individual trials so the summary can't hide how much they vary.

A new run writes:

| Path | Contents |
| --- | --- |
| `raw/` | Individual timing rows and complete trial CSVs |
| `calibration/` | Pilot measurements and selected iteration counts |
| `environment/` | Host, toolchain, source, CPU affinity, trial order, and agreement checks |
| `resources/` | Whole-process time and memory use |
| `plots/summary.csv` | Medians, quartiles, percentile bands, and median absolute deviations |
| `plots/ratios.csv` | Ratios and their pairing rules |
| `plots/backend-regimes.csv` | Backend choices by format and operation |
| `plots/format-comparison.*` | PNG, SVG, and PDF figures |
| `metadata.txt` | Run settings and plotting versions |
| `MANIFEST.tsv` | File sizes and SHA-256 hashes |

The CSV headers name the recorded fields, including implementation, format, storage width,
operation, execution class, backend, iterations, elapsed nanoseconds, and result and trace
checksums. Whole-process measurements include startup, and the arithmetic timings don't.

For very small formats, input lookup and checksums can be a large share of the measured time,
and even a narrow spread across trials can't tell us that compiler or harness effects are
absent. So we describe the workload alongside the ratios.

For arithmetic checks beyond these benchmark inputs, including the binary16 comparisons and
the [result status labels](../../tests/EXTERNAL.md#status-labels), see
[`tests/EXTERNAL.md`](../../tests/EXTERNAL.md). Those comparisons test agreement with
independent implementations. It's the Lean theorems that establish the stated properties of
FloatLib's arithmetic.
