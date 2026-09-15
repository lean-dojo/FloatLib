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

The script checks generated code, then measures compilation, generated C body size, and
median addition time for binary32, binary64, binary128, Posit32, and a custom binary256
format. Compilation here means a fresh format instantiation with its imports already
built.

Open `baseline.csv` and `environment.env` in the output directory. Each CSV row contains
`metric,subject,baseline,maxRatio`. You can edit `maxRatio` to choose how much slowdown to
allow: the defaults are 30% for compilation, 15% for generated code size, and 35% for runtime.
These are practical regression budgets, not estimates of measurement uncertainty. Raw trials
and generated compilation probes are saved alongside them.

After reviewing those measurements and budgets, compare a change with:

```bash
PERF_BASELINE_DIR=/path/to/results/baseline \
  benchmarks/scripts/performance-regression.sh check /path/to/results/check
```

Both commands need a fresh output directory. Recording a baseline leaves you to select it
explicitly through `PERF_BASELINE_DIR`; checking does not modify it. We do not ship a
machine-specific baseline.

The environment must match, including Lean and C compiler versions, compiler path,
architecture, CPU model and count, and affinity. If you change machines or toolchains,
record a baseline there. The script rejects malformed or incomplete baseline data before
compilation.

`PERF_RUNS` and `PERF_COMPILE_RUNS` control repetition counts. Keep the measurement settings
and CPU selection the same for both runs. `PERF_SKIP_CODEGEN=1` is useful while working on the
timing harness, but skips the generated-code checks included in a complete regression check.

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

Widths through 64 use a built-in scalar carrier. Multiplication uses the direct packed-word
kernel throughout that range; FMA uses a widened internal candidate from width 37.
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
