# Calibration and performance regressions

An arithmetic change can speed up a warm loop while making its first call more expensive, or
the generated code larger. We measure each of those costs on its own, so we can see what an
optimization buys us and what it costs.

All the commands below run from the repository root, and comparisons with other libraries
have their own [format comparison guide](Comparison.md).

## Checking for slowdowns

Start by recording a baseline on the machine and toolchain you plan to use, in a new
directory outside the checkout:

```bash
# On Linux, use the same available CPU for the baseline and later checks.
export PERF_CPU="$(python3 -c 'import os; print(min(os.sched_getaffinity(0)))')"
benchmarks/scripts/performance-regression.sh record /path/to/results/baseline
```

The full gate looks at four things: generated code, compilation, generated C body size, and
median runtime. Compilation is covered by five addition probes, for binary32, binary64,
binary128, Posit32, and binary256, and each one compiles a fresh format instantiation with
its imports already built. Generated-code checks of their own cover the configured-binary,
posit, and automatic selection paths.

Runtime coverage has 159 rows over `add`, `sub`, `mul`, `div`, `sqrt`, and `fma`, and the
ordinary finite inputs run all six operations on these eleven formats:

| Format key | Public carrier |
| --- | --- |
| `binary16`, `binary32`, `binary64`, `binary128` | Configured IEEE binary formats |
| `binary256` | Configured custom E19M236 binary format |
| `descriptor24` | Custom E7M16 IEEE descriptor carrier |
| `descriptor48`, `descriptor64` | Custom E7M40 and E2M61 IEEE descriptors (fraction widths 40 and 61) |
| `posit16`, `posit32`, `posit65` | Configured posit widths, including the 65-bit pair carrier |

Boundary inputs run on a smaller set, so the default campaign stays bounded:

| Input class | Formats | Operations and operands |
| --- | --- | --- |
| `ordinary` | All eleven | All six operations; shared finite vectors, nonnegative square-root inputs |
| `zero` | binary32, binary256, descriptor24, posit32, posit65 | All six; zero first operand, both binary zero signs, nonzero divisors |
| `subnormal` | binary32, binary256, descriptor24 | All six; values near both ends of the subnormal range, normal partners |
| `cancel` | Same five as `zero` | Add, subtract, FMA; exact cancellation and small residuals |
| `gap` | Same five as `zero` | Add, subtract, FMA; unequal exponents with both signs of the small term |
| `tie` | Same three as `subnormal` | Half-ulp add/subtract/FMA, odd significands multiplied by 3/2, odd subnormals divided by two |

Posits have no subnormal class. Tie rows aim at exact binary halfway results, and square
root has none. These are performance fixtures, and they don't replace the arithmetic
conformance checks. We build binary boundary operands from encoding bits before timing
starts. Each monomorphic loop cycles through sixteen prepared inputs and mixes every result
into a sink, and the warmup, which runs outside timing, seeds the timed sink with its
observed result. Even trials reverse the order of formats, operations, and classes, and
backend selection is recorded for each operation on its own.

Now open `baseline.csv` and `environment.env` in the output directory.
Schema 2 has the columns
`schema,metric,subject,baseline,maxRatio,iterations,warmupIterations,sink,backend`. A runtime
subject is `format/operation/inputClass`, with metric `runtime-nanos-per-operation`, and a
compile subject uses its format name with `-` in the four runtime fields. By default the budgets
allow 30% for compilation, 15% for generated code size, and 35% for runtime. They aren't
estimates of measurement uncertainty, so look at the measurements on your machine and then
edit `maxRatio`. Custom formats don't get special thresholds.

A baseline has to contain all 169 metrics, the 159 runtime rows plus ten compile/code-size
rows, and a missing, extra, duplicate, malformed, or wrong-schema row fails before anything
compiles. Runtime iteration and warmup counts must match, and result sinks must agree across
trials and with the baseline. A backend name may change between baseline and
candidate, since trying a different implementation is what the comparison is for, but a
candidate must use one consistent backend per row across its trials. The comparison table
shows `baselineBackend` and `currentBackend` side by side, so when an exact baseline becomes a
native-word kernel, you see that route change right next to its timing ratio.
Raw `runtime-N.csv` trials and the generated compilation probes are saved alongside the
baseline.

Once you've reviewed those measurements and budgets, run a complete check:

```bash
PERF_FULL=1 PERF_BASELINE_DIR=/path/to/results/baseline \
  benchmarks/scripts/performance-regression.sh check /path/to/results/check
```

Both `record` and `check` need a fresh output directory. Recording requires all runtime rows
and leaves the choice of baseline to `PERF_BASELINE_DIR`, and checking never modifies the
baseline. We don't ship a machine-specific baseline, since the environment has to match: the
Lean and C compiler versions, the compiler path and bundled/custom selection, the
architecture, the CPU model and count, and the affinity. Compiler selection follows Lake,
which takes `LEAN_CC`, otherwise Lean's bundled Clang when available, otherwise `CC` or `cc`
if unset. When you change machines or toolchains, record a new baseline.

To investigate a subset against a complete baseline, use exact filters:

```bash
PERF_FORMAT=descriptor24 PERF_OPERATION=fma PERF_INPUT_CLASS=tie \
PERF_BASELINE_DIR=/path/to/results/baseline \
  benchmarks/scripts/performance-regression.sh check /path/to/results/fma-tie
```

`PERF_FORMAT`, `PERF_OPERATION`, and `PERF_INPUT_CLASS` filter runtime rows only, so the five
compilation probes always run. An invalid filter, or a combination that matches no rows, is an
error. A filtered check prints `PARTIAL gate` and records its coverage in `coverage.txt`.
`PERF_FULL=1` rejects filters that omit rows, and it rejects `PERF_SKIP_CODEGEN=1` too.
Skipping those codegen scripts is handy while you work on the harness, and it also marks the
run partial, though the five compilation probes keep their own hot-body checks.

`PERF_RUNS` and `PERF_COMPILE_RUNS` default to five and three, and `PERF_WARMUP_ITERATIONS`
defaults to 256. `PERF_ITERATIONS` overrides the per-row defaults, which are 100,000 for
binary16/32/64, 20,000 for posit16/32, 10,000 for binary128, and 5,000 for the remaining
formats. All counts must be positive. Keep the settings and CPU selection the same for
baseline and candidate, and pick iteration counts large enough to give stable timings on your
machine.

The parser can validate a baseline without building or measuring anything:

```bash
benchmarks/scripts/performance-regression.sh validate /path/to/results/baseline
python3 benchmarks/scripts/checks/performance-regression.py
```

For a quick runtime smoke test, pass the built executable to the parser checks. That runs 32
iterations with 16 warmup iterations on every row, tries reversed order and every filter,
and rejects unsupported combinations, all without any timing thresholds:

```bash
source tests/lib/lake.sh
floatlib_benchmark_lake build execFloatPerformanceRegression
python3 benchmarks/scripts/checks/performance-regression.py \
  "$(floatlib_build_path bin/execFloatPerformanceRegression)"
```

If you don't give an output path, the performance, configured-binary, and posit scripts
create timestamped output directories under `${TMPDIR:-/tmp}/floatlib-benchmarks`. Temporary
posit work follows `TMPDIR` as well, and `POSIT_BENCH_TMPDIR` overrides it for posits alone.

## Comparing backend candidates

The planner picks among certified implementations using static cost estimates. To see what
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

Create the output directory first, and run the trials when the machine is otherwise quiet.
This executable measures every admissible certified candidate for the binary descriptors in
its calibration set, and it takes the candidate list from the public planner.

For each format and operation, compare `firstNanos + warmTotalNanos` across candidates.
Before we change a cost estimate, the proposed choice has to win in all three trials. Update
the [crossover checks](../../tests/FloatLibTests/Conformance/Execution/AutomaticDispatch.lean)
along with the change, then run the complete verification suite and the generated-code
checks. Selection itself is deterministic and happens at compile time, and the timings only
help us choose its estimates.

For configured binary FMA, you can look at the small-table crossover on its own:

```bash
source tests/lib/lake.sh
floatlib_benchmark_lake build execFloatConfiguredLowBitCalibration
CONFIGURED_LOWBIT_CALIBRATION_ITERATIONS=200000 \
CONFIGURED_LOWBIT_CALIBRATION_MAX_RESIDENT_BYTES=2097152 \
  "$(floatlib_build_path bin/execFloatConfiguredLowBitCalibration)"
```

With a two-mebibyte measurement limit, the seven-bit FMA table fits and the sixteen-mebibyte
eight-bit table is skipped. Even the candidates too large to time appear in the output, which
shows whether each one is admissible and whether the balanced and throughput policies select
it. Repeat the run in at least three different processes before you change cost estimates or
the expected call counts a policy uses.

The corresponding posit diagnostic measures widths 4, 6, and 8:

```bash
source tests/lib/lake.sh
floatlib_benchmark_lake build execFloatPositBackendCalibration
POSIT_CALIBRATION_ITERATIONS=100000 \
  "$(floatlib_build_path bin/execFloatPositBackendCalibration)"
```

It also takes its candidates from the public certified portfolios. It times lazy first-use
construction apart from warmed execution and records the default policy's choice.

## Measuring posit arithmetic

```bash
benchmarks/scripts/posit.sh 9 /path/to/results/posit
```

The posit executable measures all six public operations, and every row records the selected
backend, kernel class, storage carrier, and policy. Don't assume a small format uses a lookup
table. Under the balanced policy, building a byte-wide table for a binary operation costs too
much, while the smaller square-root table can be worth it.

Widths through 64 use a built-in scalar carrier, and the native-word multiplication and FMA
candidates call direct packed-storage kernels.
Generated-code checks verify that a closed width selects a direct `UInt64` entry point
without a runtime width branch.

By default, `coldNanos` records the first arithmetic call after Lean runtime initialization,
and `POSIT_BENCH_COLD_ITERATIONS` changes how many calls that interval covers. Before
measuring `totalNanos`, the executable warms the resources the planner chose. Whole-process
startup and peak memory go in their own file, `resources/process.csv`. Don't divide that
startup time by a row's iteration count, because what comes out looks like an operation
latency and is misleading.

The harness first calibrates each width-operation pair in a process of its own, then passes
the iteration counts to one process per complete trial. Even trials visit widths and
operations in reverse order, so a row isn't always measured at the same point in the run.
With `POSIT_BENCH_ISOLATE_ROWS=1`, every measured row gets its own process instead.

Setting `POSIT_BENCH_ITERATIONS` uses one positive iteration count and turns off adaptive
calibration. Without it, direct executable calls use smaller defaults for wider values. You
can narrow a run to one width and operation:

```bash
source tests/lib/lake.sh
floatlib_benchmark_lake build execFloatPositBench
POSIT_BENCH_WIDTH=8 POSIT_BENCH_OPERATION=add \
  POSIT_BENCH_ITERATIONS=10000 "$(floatlib_build_path bin/execFloatPositBench)"
```

For allocation statistics you need a Lean runtime built with `-D RUNTIME_STATS=ON`, and then
`POSIT_BENCH_ALLOCPROF=1` makes the harness save the profiler output under `alloc/`. A normal
release runtime runs the benchmark just as well, without the allocation counters.

The result metadata records the binary hash, the source and build-configuration hashes, the
benchmark and plotting scripts, and the relevant generated C files, along with whether the
trials measured all rows together or each row in its own process.

In the `posit_speed_by_width` figure, lookup tables, packed-word, packed-pair, exact-dyadic
integer, and exact arbitrary-precision backends each get their own marker, and
`posit-backend-selection.csv` lists the choices by width and operation. When the timing curve
changes because execution moved to another kernel, these files are where you see it.

You can overlay existing named-format and external summaries:

```bash
POSIT_NAMED_FORMAT_SUMMARY=/path/to/named-format-summary.csv \
POSIT_EXTERNAL_SUMMARY=/path/to/external-summary.csv \
  benchmarks/scripts/posit.sh
```

Every plotted ratio appears in `posit-reference-comparison.csv` together with its pairing rule.
At posit widths 2 through 8, MPFR and extracted Flocq use the fixed significand precision
`p = n`, and at widths 16 through 512, they use the precision of the binary format with the
same storage. Read these as comparisons of arithmetic cost. A posit's precision varies with
the value, so neither pairing gives equal precision everywhere.

Above the lookup-table range, all six posit operations use certified integer kernels.
Addition, subtraction, multiplication, and FMA build their results from exact dyadics.
Division takes a scaled integer quotient and confirms it by exact cross-products, and square
root takes an integer root and confirms it by exact squared comparisons, while exact-rational
implementations provide independent reference definitions. An optimization can change which
kernel produced the numbers, so read each run together with its source hash and backend
selection table.

## Measuring the cost of the public API

To see whether the abstraction adds runtime work, we compare the usual parameterized binary
types with direct calls to the kernels they select:

```bash
CONFIGURED_BINARY_CPU="$(python3 -c 'import os; print(min(os.sched_getaffinity(0)))')" \
BENCH_ITERATIONS=1000000 \
  benchmarks/scripts/configured-binary.sh 9 /path/to/results/configured-binary
```

Before timing, the script runs the [generated-code check](../scripts/checks/configured-binary-codegen.sh).
For `ExecFloat.Binary 8 23` and `ExecFloat.Binary 11 52` it makes sure that all six
operations compile to first-order functions with native `uint32_t` or `uint64_t` arguments
and results, with no residual planner, capability-closure call, or unchecked host call left
in these certified operations. Other probes confirm that `NativeFPU.Unchecked` operations,
which you have to call by name, reach Lean's host primitives.

Inputs are prepared before timing. We compare individual results and complete loop
checksums, alternate the order of each public/direct pair, and save every raw trial. At this
scale even code placement can affect the timings, so we control it. Benchmark compiler flags
put the functions at the same 4,096-byte page offset, and the script confirms that each pair
is page-aligned and has the same compiled size, then records the addresses and sizes in
`code-layout.csv`.

Both sides use the same proved word kernels for addition, subtraction, multiplication,
division, square root, and FMA, so their ratio measures public API overhead on a workload
of ordinary finite inputs in warmed loops. Exceptional inputs and rounding boundaries are
covered by the [arithmetic comparisons](../../tests/EXTERNAL.md), and hardware C and MPFR
comparisons belong to the [format benchmark](Comparison.md).
