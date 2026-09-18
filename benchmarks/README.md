# Benchmarks

We want FloatLib's proved arithmetic to be useful in real programs, so we measure the cost of
ordinary public operations across small and large formats. These benchmarks help us compare
backends, catch slowdowns, and see how much work remains to reach the speed of libraries such as
MPFR. They are separate from the normal library build.

For a first measurement, run this from the repository root:

```bash
source tests/lib/lake.sh
BENCH_ITERATIONS=1000 floatlib_benchmark_lake exe execFloatSweep add
```

This prints addition timings across 17 significand precisions, from 2 to 4,096 bits. Those are
sample points we chose for the benchmark; you can define other formats. Precision counts the
significand, so the eight-bit precision point is bfloat16, with 16 bits of storage.
Replace `add` with `sub`, `mul`, `div`, `sqrt`, `fma`, or `all` to measure the other operations.

For a short comparison with independent implementations:

```bash
FORMAT_COMPARE_DEVELOPMENT_ONLY=1 \
  benchmarks/scripts/format-comparison.sh 1 "${TMPDIR:-/tmp}/floatlib-comparison"
```

The [comparison guide](docs/Comparison.md) covers the required tools and the full nine-trial
command. Choose a fresh output directory outside the checkout. The scripts use `TMPDIR` for
temporary work and keep build products outside the checkout through the shared build helper.

| What we want to measure | Where to start |
| --- | --- |
| All six operations across significand precisions | `floatlib_benchmark_lake exe execFloatSweep all` |
| FP8 arithmetic | `floatlib_benchmark_lake exe execFloatFP8Bench` |
| Posit arithmetic across storage widths | `benchmarks/scripts/posit.sh` |
| FloatLib alongside MPFR and other implementations | [Format comparisons](docs/Comparison.md) |
| Backend choices and their first-call costs | [Backend calibration](docs/Calibration.md#comparing-backend-candidates) |
| Public API overhead and performance regressions | [Calibration and regression checks](docs/Calibration.md) |
| Recreate the saved tables and figures | `benchmarks/scripts/verify-main-result.sh` |

The [performance chapter](../site/content/chapters/15-performance.md) walks through the plots,
and the [results README](results/main/README.md) describes the data behind them. A fresh run
measures your source, compiler, and machine, so its timings can differ from ours.
The [matched Flocq comparison](results/flocq-matched/README.md) has a separate figure
and complete numerical agreement checks against Flocq and MPFR.

We convert the exact input values before timing and record the selected backend, iteration
count, elapsed time, and result checksums. The comparison guide explains the scalar dependency
chain, agreement checks, and differences between the external adapters. For broader arithmetic
comparisons, see the [external checks](../tests/EXTERNAL.md).
