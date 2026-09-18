# Format comparisons

We compare FloatLib with other arithmetic libraries to see where our kernels are doing well
and where an optimization would help. The plots cover six scalar operations across storage
widths from 2 to 4,096 bits. This guide explains how to rerun them and what each comparison
means. Run the commands from the repository root.

## Recreate the saved tables and figures

```bash
benchmarks/scripts/verify-main-result.sh
```

This checks the saved measurements and regenerates their tables and figures from the recorded
trials. It needs Git, Python 3, and Matplotlib, but does not compile FloatLib or run the timed
operations again. The [results README](../results/main/README.md) describes the files behind the
[performance chapter](../../site/content/chapters/15-performance.md).

The matched Flocq comparison has its own data and figure:

```bash
python3 benchmarks/plots/flocq_matched.py \
  --out "${TMPDIR:-/tmp}/floatlib-flocq-matched.png"
```

This also checks the raw timing selection and complete numerical values. The
[matched result README](../results/flocq-matched/README.md) describes its fixture-chain
measurements and the complete-block square-root supplement.

The data belongs to the source and environment recorded with it. Rebuilding the figures lets us
check the calculation of the plotted numbers; measuring an implementation change needs a new
run. When Matplotlib versions differ, the verifier compares the tables exactly and checks that
figures can still be generated. Image files can differ between plotting versions.

## Measure the current code

The runner uses Linux tools, including `/proc`, GNU `time`, and `taskset`. You will need the
repository's pinned Lean toolchain, a C compiler, `pkg-config`, MPFR development headers and
libraries, Git, Python 3, and Matplotlib. Both C adapters use MPFR during setup, so MPFR is
required even when you select only a few implementations.

By default, we also build Berkeley SoftFloat with Make and Stillwater Universal with a C++20
compiler. The SoftFloat build target is Linux x86-64. The script fetches pinned external
revisions unless you supply checkouts with `SOFTFLOAT_SOURCE` and `UNIVERSAL_SOURCE`. Use clean,
dedicated checkouts: the SoftFloat setup checks out its selected revision, and a supplied
Universal checkout must already be at the pinned revision. Flocq is optional and needs Docker
or an executable supplied through `FLOCQ_BENCH_BINARY`.

Here is a one-trial run to check that the tools are set up:

```bash
FORMAT_COMPARE_DEVELOPMENT_ONLY=1 \
benchmarks/scripts/format-comparison.sh 1 "${TMPDIR:-/tmp}/floatlib-format-check"
```

Choose a new output directory outside the checkout for each run; the script rejects an
existing path. Without an output argument, it creates a timestamped directory under
`${TMPDIR:-/tmp}/floatlib-benchmarks/format-comparison`. The shared
[build helper](../../tests/lib/lake.sh) keeps Lean build products outside the checkout.
Temporary external builds also follow `TMPDIR`, with `FORMAT_COMPARE_TMPDIR` available as
a separate override.

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

The Python expression selects the first CPU available to the process. You can set
`FORMAT_COMPARE_CPU` to another available CPU instead. The full run requires this setting,
at least seven trials, and calibrated iteration counts. Each measured interval must last at
least 50 ms by default; calibration aims for 200 ms.

For a matched binary fixture-chain comparison with just FloatLib, Flocq, and MPFR:

```bash
FORMAT_COMPARE_PROFILE=flocq \
FORMAT_COMPARE_DEVELOPMENT_ONLY=0 \
FORMAT_COMPARE_CPU="$(python3 -c 'import os; print(min(os.sched_getaffinity(0)))')" \
benchmarks/scripts/format-comparison.sh 9 /path/to/results/flocq-comparison
```

This profile measures all six operations at the 11 widths supported by all three adapters,
from 6 to 4,096 bits. It keeps the same trial, duration, and agreement checks as the full
comparison, without building the other providers.
This command measures the chain at every width. It does not run the separate
complete-block square-root workload used for nine entries in the
[saved Flocq figure](../results/flocq-matched/README.md).

Pinning reduces noise from moving between CPUs. An otherwise quiet machine still matters:
shared caches, memory bandwidth, frequency changes, and other processes can affect the result.
Keep the recorded source, compiler, and machine details beside any numbers you compare.

The full run checks the complete measurement matrix and rejects disabled calibration, changed
agreement-prefix lengths, reused Lean executables, dirty external checkouts, and incomplete or
short timing rows. `FORMAT_COMPARE_BUILD_JOBS` controls SoftFloat's `make -j` only; it does not
change Lean or Lake parallelism.

When working on a particular operation, we can shorten the run:

```bash
FORMAT_COMPARE_DEVELOPMENT_ONLY=1 \
FORMAT_COMPARE_WIDTHS="32 64" \
FORMAT_COMPARE_OPERATIONS="add mul fma" \
benchmarks/scripts/format-comparison.sh 1 "${TMPDIR:-/tmp}/floatlib-format-subset"
```

These runs are marked as development measurements in the plot and metadata. They are useful
for checking the harness before spending time on the full comparison.

## What the benchmark measures

We start with the exact rational inputs in
[`ExactWorkload.lean`](../lean/FloatLibBenchmarks/Support/ExactWorkload.lean). The comparable
binary adapters, including Flocq, round each value once into the destination format before
timing. Square-root inputs are nonnegative.

The timed loop forms a scalar dependency chain: each result chooses the next member of a
16-value input set. We adapted the dependency-chain technique from
[Abel and Reineke's uops.info methodology](https://doi.org/10.1145/3297858.3304062).
Choosing among fixed inputs keeps multiplication, division, and square root from repeatedly
overflowing, underflowing, or settling at a fixed point.

These timings include input lookup, result checksums, and the arithmetic call. They measure
the cost of that scalar loop; they do not measure throughput over independent operations or
the latency of a bare CPU instruction.

Each implementation, width, and operation gets its own calibrated iteration count. We record
the loop's final checksum and a digest of the chosen input indices. Different loop lengths
can produce different final checksums even when every operation agrees, so we check agreement
with a separate, untimed prefix of 256 operations.

FloatLib, MPFR, and enabled Flocq rows must agree on that prefix at every shared binary width.
Native C and SoftFloat join the check at binary32 and binary64; CPython joins for the
binary64 operations it provides.
The runner checks both the result checksum and the input trace, and rejects missing or
disagreeing prefixes.

We shuffle a deterministic starting order, then rotate it between trials so no implementation
is always first or last. The complete order is saved in `environment/trial-order.csv`.

## Formats and comparison points

Posit storage widths are 2, 3, 4, 5, 6, 7, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, and 4096.
We stop measuring at 4,096 bits here; that is not a library precision limit.

Configured binary formats begin at four bits:

- Widths 4 through 8 use E2M1, E2M2, E3M2, E3M3, and E4M3.
- Widths 16, 32, 64, and 128 use the IEEE interchange layouts.
- Widths 256 and above use 19 exponent bits.
- Optional widths 24, 48, 96, and 112 use E8M15, E11M36, E15M80, and E15M96.
  They have no equal-width posit or external row.

The eight-bit point is called E4M3 because IEEE 754 does not define a binary8 interchange
format.

For an optional binary-only point, invoke the Lean executable directly:

```bash
source tests/lib/lake.sh
floatlib_benchmark_lake build execFloatFormatComparison
FORMAT_COMPARE_FAMILY=binary-interchange FORMAT_COMPARE_WIDTH=96 \
  FORMAT_COMPARE_ITERATIONS=10000 \
  "$(floatlib_build_path bin/execFloatFormatComparison)"
```

This emits the six operation rows for the chosen width. The comparison script also accepts
these widths as standalone binary rows. It checks cross-adapter agreement for requested
FloatLib/MPFR pairs and rejects missing requested rows.

MPFR and Flocq use the significand precision of the binary format at the same storage width.
That gives us a binary comparison point. A posit's precision changes with its magnitude, so
equal storage does not make its precision equal to MPFR's. `plots/ratios.csv` records the MPFR
precision and pairing rule behind each ratio.

## Implementations

The FloatLib curves measure certified binary and posit software arithmetic. We compare them
with:

| Implementation | What its curve measures |
| --- | --- |
| [Berkeley SoftFloat](https://www.jhauser.us/arithmetic/SoftFloat-3/doc/SoftFloat.html) | Independent IEEE software arithmetic at binary32 and binary64 |
| [MPFR](https://www.mpfr.org/mpfr-current/mpfr.html) | Correctly rounded arbitrary-precision binary arithmetic, labelled `MPFR (binary)` |
| Native C | Host floating-point arithmetic at binary32 and binary64 |
| [CPython float64](https://docs.python.org/3/c-api/float.html) | Ordinary Python floating-point calls, including interpreter and object overhead |
| [Stillwater Universal](https://github.com/stillwater-sc/universal) | Posit arithmetic for the format-operation pairs that agree with the benchmark vectors |
| [Flocq](https://flocq.gitlabpages.inria.fr/) | Extracted OCaml/Zarith arithmetic with matching binary precision and exponent bounds |

CPython FMA appears only when the interpreter provides `math.fma`. We do not substitute
`x * y + z`, which rounds differently.

Flocq is disabled by default because its build uses the pinned Rocq container. Enable it with:

```bash
FORMAT_COMPARE_DEVELOPMENT_ONLY=1 \
FORMAT_COMPARE_INCLUDE_FLOCQ=1 \
benchmarks/scripts/format-comparison.sh
```

The Flocq wrapper rounds exact input fractions with its proved `Bdiv_correct_aux` helper,
then calls its certified binary operations. Precision, exponent bounds, nearest-even rounding,
and gradual underflow match FloatLib and MPFR. Flocq's `BinarySingleNaN` interface requires
`precision < emax`, which excludes the custom 4-, 5-, and 7-bit layouts from this comparison.
Its single NaN does not preserve payloads; the benchmark checks arithmetic values.

Each campaign computes Flocq's 256-step agreement prefix once per format and operation, then
reuses it outside timing across calibration and trials. The cache starts empty and is tied to
the compiled executable's SHA-256. This avoids repeating expensive wide square-root checks.

The website uses the [matched results](../results/flocq-matched/README.md) for Flocq.
The [main archive](../results/main/README.md) retains its original Flocq rows, which use
different input preparation and exponent bounds; those rows are excluded from the website
curves. A supplied executable's hash is recorded alongside its results; keep its build
recipe and dependency versions too.

Before timing Universal, the C++ adapter checks all 16 operation results against fixed-width
bit vectors generated by FloatLib. Unsupported or disagreeing format-operation pairs are
recorded and omitted from the plot. Accepted rows establish agreement on those inputs.

We label Universal's software and hardware-assisted results separately. In particular, some
generic square-root implementations convert through binary64 and call the host square root.

To select implementations directly:

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

Selecting a subset does not skip the setup of other enabled implementations. Use the
`INCLUDE` settings when you also want to avoid their builds.

## Reading the output

Lower time per operation is faster. The FloatLib curves can change kernels as the width
changes; `plots/backend-regimes.csv` identifies the backend used for each operation and
format. We keep individual trials so the summary does not hide their variation.

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
checksums. Whole-process measurements include startup; the arithmetic timings exclude it.

For very small formats, input lookup and checksums can account for much of the measured time.
Even a narrow spread across trials cannot tell us that compiler or harness effects are absent.
This is why we describe the workload alongside the ratios.

For arithmetic checks beyond these benchmark inputs, see
[`tests/EXTERNAL.md`](../../tests/EXTERNAL.md), including the binary16 comparisons and
[result status labels](../../tests/EXTERNAL.md#status-labels). Those comparisons test agreement
with independent implementations; the Lean theorems establish the stated properties of
FloatLib's arithmetic.
