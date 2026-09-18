# Calibration and performance regressions

An arithmetic change can improve a warm loop while making its first call more expensive.
It can also make the generated code larger. We measure these costs separately so we can
understand what an optimization buys us.

Run the commands below from the repository root. For comparisons with other libraries,
see the [format comparison guide](Comparison.md).

## Checking for slowdowns

Start by recording a baseline on the machine and toolchain you plan to use. Choose a new
directory outside the checkout:

```bash
# On Linux, use the same available CPU for the baseline and later checks.
export PERF_CPU="$(python3 -c 'import os; print(min(os.sched_getaffinity(0)))')"
benchmarks/scripts/performance-regression.sh record /path/to/results/baseline
```

The full gate checks generated code, compilation, generated C body size, and median runtime.
The five existing addition compilation probes remain binary32, binary64, binary128, Posit32,
and binary256. Compilation means a fresh format instantiation with imports already built.
The separate generated-code checks still cover the configured-binary, posit, and automatic
selection paths.

Runtime coverage has 159 rows over `add`, `sub`, `mul`, `div`, `sqrt`, and `fma`. Ordinary
finite inputs cover all six operations on these eleven formats:

| Format key | Public carrier |
| --- | --- |
| `binary16`, `binary32`, `binary64`, `binary128` | Configured IEEE binary formats |
| `binary256` | Configured custom E19M236 binary format |
| `descriptor24` | Custom E7M16 IEEE descriptor carrier |
| `descriptor48`, `descriptor64` | Custom E7M40 and E2M61 IEEE descriptors (fraction widths 40 and 61) |
| `posit16`, `posit32`, `posit65` | Configured posit widths, including the 65-bit pair carrier |

A smaller set exercises boundaries so the default campaign stays bounded:

| Input class | Formats | Operations and operands |
| --- | --- | --- |
| `ordinary` | All eleven | All six operations; shared finite vectors, nonnegative square-root inputs |
| `zero` | binary32, binary256, descriptor24, posit32, posit65 | All six; zero first operand, both binary zero signs, nonzero divisors |
| `subnormal` | binary32, binary256, descriptor24 | All six; values near both ends of the subnormal range, normal partners |
| `cancel` | Same five as `zero` | Add, subtract, FMA; exact cancellation and small residuals |
| `gap` | Same five as `zero` | Add, subtract, FMA; unequal exponents with both signs of the small term |
| `tie` | Same three as `subnormal` | Half-ulp add/subtract/FMA, odd significands multiplied by 3/2, odd subnormals divided by two |

Posits have no subnormal class. The tie rows target exact binary halfway results; square root
has no tie row. These are performance fixtures, not a replacement for arithmetic conformance
checks. Binary boundary operands are built from encoding bits before timing. Each monomorphic
loop cycles through sixteen prepared inputs and mixes every result into a sink. Warmup runs
outside timing and its observed result seeds the timed sink. Even trials reverse the order of
formats, operations, and classes. Backend selection is recorded separately for each operation.

Open `baseline.csv` and `environment.env` in the output directory. Schema 2 uses
`schema,metric,subject,baseline,maxRatio,iterations,warmupIterations,sink,backend`. Runtime subjects
are `format/operation/inputClass`, with metric `runtime-nanos-per-operation`; compile subjects
retain their format names and use `-` in the four runtime fields. The existing default budgets
remain 30% for compilation, 15% for generated code size, and 35% for runtime. Edit `maxRatio`
after reviewing measurements on your machine. These budgets are not measurement uncertainty
estimates, and the harness does not assign special thresholds to custom formats.

The addition-only schema is incompatible and must be re-recorded. Every baseline must contain
all 169 metrics: 159 runtime rows and ten compile/code-size rows. Missing, extra, duplicate,
malformed, or wrong-schema rows fail before compilation. Runtime iteration and warmup counts
must match; result sinks must agree across trials and with the baseline. A backend name may
change between baseline and candidate, since evaluating a different implementation is the
purpose of the comparison. Each candidate must use one consistent backend per row across trials.
The comparison table includes `baselineBackend` and `currentBackend`, so a route change such as
an exact baseline becoming a native-word kernel is visible beside its timing ratio.
Raw `runtime-N.csv` trials and generated compilation probes are saved alongside the baseline.

After reviewing those measurements and budgets, run a complete check with:

```bash
PERF_FULL=1 PERF_BASELINE_DIR=/path/to/results/baseline \
  benchmarks/scripts/performance-regression.sh check /path/to/results/check
```

Both `record` and `check` need a fresh output directory. Recording requires all runtime rows;
it leaves baseline selection to `PERF_BASELINE_DIR`. Checking never modifies the baseline.
We do not ship a machine-specific baseline. The environment must match, including Lean and C
compiler versions, compiler path and bundled/custom selection, architecture, CPU model and
count, and affinity. Compiler selection follows Lake: `LEAN_CC`, otherwise Lean's bundled
Clang when available, otherwise `CC` or `cc` if unset. Record a new baseline when changing
machines or toolchains. Baselines recorded before the compiler-selection correction require
re-recording for new comparisons.

Use exact filters to investigate a subset against a complete baseline:

```bash
PERF_FORMAT=descriptor24 PERF_OPERATION=fma PERF_INPUT_CLASS=tie \
PERF_BASELINE_DIR=/path/to/results/baseline \
  benchmarks/scripts/performance-regression.sh check /path/to/results/fma-tie
```

`PERF_FORMAT`, `PERF_OPERATION`, and `PERF_INPUT_CLASS` filter runtime rows only; the five
compilation probes remain. Invalid filters and combinations with no rows are errors.
Filtered checks print `PARTIAL gate` and record coverage in `coverage.txt`. `PERF_FULL=1`
rejects filters that omit rows and rejects `PERF_SKIP_CODEGEN=1`. Skipping those codegen
scripts is useful for harness development and also marks the run partial; the five compilation
probes still undergo their own hot-body checks.

`PERF_RUNS` and `PERF_COMPILE_RUNS` default to five and three. `PERF_ITERATIONS` overrides the
per-row defaults: 100,000 for binary16/32/64, 20,000 for posit16/32, 10,000 for binary128,
and 5,000 for the remaining formats. `PERF_WARMUP_ITERATIONS` defaults to 256. All counts must
be positive. Keep the settings and CPU selection the same for baseline and candidate; choose
iteration counts large enough to obtain stable timings on your machine.

The parser can validate a baseline without building or measuring:

```bash
benchmarks/scripts/performance-regression.sh validate /path/to/results/baseline
python3 benchmarks/scripts/checks/performance-regression.py
```

For a small runtime smoke test, pass the built executable to the parser checks. This runs
32 iterations with 16 warmup iterations on every row, checks reversed order and every filter,
and rejects unsupported combinations. It imposes no timing thresholds:

```bash
source tests/lib/lake.sh
floatlib_benchmark_lake build execFloatPerformanceRegression
python3 benchmarks/scripts/checks/performance-regression.py \
  "$(floatlib_build_path bin/execFloatPerformanceRegression)"
```

The performance, configured-binary, and posit scripts create timestamped output directories
under `${TMPDIR:-/tmp}/floatlib-benchmarks` when no output path is given. Temporary posit work
also follows `TMPDIR`, with `POSIT_BENCH_TMPDIR` as its own override.

## Comparing backend candidates

The planner chooses from certified implementations using static cost estimates. To see what
those estimates mean on your machine, measure both the first call and repeated calls:

```bash
source tests/lib/lake.sh
floatlib_benchmark_lake build execFloatBackendCalibration
for trial in 1 2 3; do
  CALIBRATION_ITERATIONS=100000 \
    "$(floatlib_build_path bin/execFloatBackendCalibration)" \
    > "/path/to/results/backend-calibration-${trial}.csv"
done
```

Create the output directory first and run the trials when the machine is otherwise quiet.
This executable measures every admissible certified candidate for the binary descriptors
in its calibration set. The candidate list comes from the public planner.

For each format and operation, compare `firstNanos + warmTotalNanos` across candidates.
We require the proposed choice to win in all three trials before changing a cost estimate.
Update the [crossover checks](../../tests/FloatLibTests/Conformance/Execution/AutomaticDispatch.lean)
with the change, then run the complete verification suite and generated-code checks.
Selection remains deterministic and happens at compile time; the timings help us choose its
estimates.

For configured binary FMA, we can inspect the small-table crossover directly:

```bash
source tests/lib/lake.sh
floatlib_benchmark_lake build execFloatConfiguredLowBitCalibration
CONFIGURED_LOWBIT_CALIBRATION_ITERATIONS=200000 \
CONFIGURED_LOWBIT_CALIBRATION_MAX_RESIDENT_BYTES=2097152 \
  "$(floatlib_build_path bin/execFloatConfiguredLowBitCalibration)"
```

The two-mebibyte measurement limit includes the seven-bit FMA table and skips the
sixteen-mebibyte eight-bit table. The output still shows whether each candidate is admissible
and selected under the balanced and throughput policies, including candidates too large to
time. Repeat in at least three separate processes before changing cost estimates or the
expected call counts used by a policy.

The corresponding posit diagnostic measures widths 4, 6, and 8:

```bash
source tests/lib/lake.sh
floatlib_benchmark_lake build execFloatPositBackendCalibration
POSIT_CALIBRATION_ITERATIONS=100000 \
  "$(floatlib_build_path bin/execFloatPositBackendCalibration)"
```

It also takes candidates from the public certified portfolios, measures lazy first-use
construction separately from warmed execution, and records the default policy's choice.

## Measuring posit arithmetic

```bash
benchmarks/scripts/posit.sh 9 /path/to/results/posit
```

The posit executable measures all six public operations. Every row records the selected
backend, kernel class, storage carrier, and policy. A small format does not necessarily
use a lookup table: under the balanced policy, building a byte-wide table for a binary
operation costs too much, while its smaller square-root table can still be worthwhile.

Widths through 64 use a built-in scalar carrier. The native-word multiplication and FMA
candidates call direct packed-storage kernels.
Generated-code checks verify that a closed width selects a direct `UInt64` entry point
without a runtime width branch.

By default, `coldNanos` records the first arithmetic call after Lean runtime initialization.
`POSIT_BENCH_COLD_ITERATIONS` changes the number of calls in that interval. Before measuring
`totalNanos`, the executable warms the resources chosen by the planner. The
separate `resources/process.csv` includes whole-process startup and peak memory. Dividing
that startup time by a row's iteration count would give a misleading operation latency.

The harness first calibrates each width-operation pair in a separate process, then passes
the iteration counts to one process per complete trial. Even trials visit widths and
operations in reverse order, so the same row is not always measured at the same point.
`POSIT_BENCH_ISOLATE_ROWS=1` runs every measured row in a separate process instead.

Set `POSIT_BENCH_ITERATIONS` to use one positive iteration count and disable adaptive
calibration. Direct executable calls otherwise use smaller defaults for wider values.
We can narrow a check to one width and operation:

```bash
source tests/lib/lake.sh
floatlib_benchmark_lake build execFloatPositBench
POSIT_BENCH_WIDTH=8 POSIT_BENCH_OPERATION=add \
  POSIT_BENCH_ITERATIONS=10000 "$(floatlib_build_path bin/execFloatPositBench)"
```

For allocation statistics, set `POSIT_BENCH_ALLOCPROF=1` when using a Lean runtime built with
`-D RUNTIME_STATS=ON`. The harness saves the profiler output under `alloc/`. A normal release
runtime can run the benchmark without providing allocation counters.

The result metadata records the binary hash, source and build-configuration hashes,
benchmark and plotting scripts, and relevant generated C files. It also records whether
trials measured all rows together or in separate processes.

The `posit_speed_by_width` figure uses distinct markers for lookup tables, packed-word,
packed-pair, exact-dyadic integer, and exact arbitrary-precision backends.
`posit-backend-selection.csv` shows the choices by width and operation. These files help
explain a change in the timing curve when execution moves to another kernel.

You can overlay existing named-format and external summaries:

```bash
POSIT_NAMED_FORMAT_SUMMARY=/path/to/named-format-summary.csv \
POSIT_EXTERNAL_SUMMARY=/path/to/external-summary.csv \
  benchmarks/scripts/posit.sh
```

Every plotted ratio and its pairing rule appears in `posit-reference-comparison.csv`.
At posit widths 2 through 8, MPFR and extracted Flocq use fixed significand precision
`p = n`. At widths 16 through 512, they use the precision of the equal-storage binary
format. These are arithmetic-cost comparisons: posit precision varies with the value,
so neither pairing gives equal precision everywhere.

Above the lookup-table range, all six posit operations use certified integer kernels.
Addition, subtraction, multiplication, and FMA construct results from exact dyadics.
Division uses a scaled integer quotient checked by exact cross-products; square root uses
an integer root checked by exact squared comparisons. Exact-rational implementations provide
independent reference definitions. Read a run together with its source hash and backend
selection table, since optimizations can change which kernel produced the numbers.

## Measuring the cost of the public API

We compare the usual parameterized binary types with direct calls to the kernels they
select. This lets us measure whether the abstraction adds runtime work:

```bash
CONFIGURED_BINARY_CPU="$(python3 -c 'import os; print(min(os.sched_getaffinity(0)))')" \
BENCH_ITERATIONS=1000000 \
  benchmarks/scripts/configured-binary.sh 9 /path/to/results/configured-binary
```

The script runs the [generated-code check](../scripts/checks/configured-binary-codegen.sh)
before timing. For `ExecFloat.Binary 8 23` and `ExecFloat.Binary 11 52`, it checks that all
six operations compile to first-order functions with native `uint32_t` or `uint64_t`
arguments and results. There should be no residual planner, capability-closure call, or
unchecked host call in these certified operations. Separate probes check that explicit
`NativeFPU.Unchecked` operations reach Lean's host primitives.

Inputs are prepared before timing. We compare individual results and complete loop
checksums, alternate the order of each public/direct pair, and save every raw trial.
Benchmark compiler flags place the functions at the same 4,096-byte page offset.
The script checks that each pair is page-aligned and has the same compiled size, then
records the addresses and sizes in `code-layout.csv`. Code placement can affect timings
at this scale, so we control it in the comparison.

Both sides use the same proved word kernels for addition, subtraction, multiplication,
division, square root, and FMA. Their ratio measures public API overhead. The workload
uses ordinary finite inputs in warmed loops; exceptional inputs and rounding boundaries
are covered by the [arithmetic comparisons](../../tests/EXTERNAL.md).
Hardware C and MPFR comparisons belong to the separate [format benchmark](Comparison.md).
