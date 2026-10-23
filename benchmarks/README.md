# Benchmarks

We want FloatLib's proved arithmetic to be useful in real programs, so we measure what ordinary
public operations cost across small and large formats. With these benchmarks we compare backends,
catch slowdowns, and see how far we still are from the speed of libraries such as MPFR. None of
this is part of the normal library build.

For a first measurement, run this from the repository root:

```bash
source tests/lib/lake.sh
BENCH_ITERATIONS=1000 floatlib_benchmark_lake exe execFloatSweep add
```

That prints addition timings at 17 significand precisions, from 2 to 4,096 bits. We picked those
sample points for the benchmark, and you can define other formats. Precision counts the
significand, so the eight-bit precision point is bfloat16, which takes 16 bits of storage. To
measure the other operations, replace `add` with `sub`, `mul`, `div`, `sqrt`, `fma`, or `all`.

For a short comparison with independent implementations:

```bash
FORMAT_COMPARE_DEVELOPMENT_ONLY=1 \
  benchmarks/scripts/format-comparison.sh 1 "${TMPDIR:-/tmp}/floatlib-comparison"
```

You'll find the tools you need and the full nine-trial command in the
[comparison guide](docs/Comparison.md). Pick a fresh output directory outside the checkout.
Temporary work goes in `TMPDIR`, and the shared build helper keeps build products out of the
checkout too.

| What we want to measure | Where to start |
| --- | --- |
| All six operations across significand precisions | `floatlib_benchmark_lake exe execFloatSweep all` |
| FP8 arithmetic | `floatlib_benchmark_lake exe execFloatFP8Bench` |
| Posit arithmetic across storage widths | `benchmarks/scripts/posit.sh` |
| Additional public operations on mixed inputs | `floatlib_benchmark_lake exe execFloatTimeOps list` |
| Six operations on a supplied operand file | `floatlib_benchmark_lake exe execFloatTimeList e11m52 add FILE 5` |
| FloatLib alongside MPFR and other implementations | [Format comparisons](docs/Comparison.md) |
| Backend choices and their first-call costs | [Backend calibration](docs/Calibration.md#comparing-backend-candidates) |
| Public API overhead and performance regressions | [Calibration and regression checks](docs/Calibration.md) |
| Recreate the saved tables and figures | `benchmarks/scripts/verify-main-result.sh` |

`execFloatTimeOps run CELL COUNT TRIALS REPS` times one cell from `list` (for example
`binary64/scale`) and prints both timings and result digests. Use positive counts.
`execFloatTimeList` reads space-separated decimal encodings, one case per line with up to three
operands, and prints one timing per trial. It handles binary, posit, and explicit limb carriers,
and if you run it without arguments it prints the supported format names.

The [performance chapter](../site/content/chapters/17-performance.md) walks through the plots, and
the [results README](results/main/README.md) describes the data behind them. Your own run measures
your source, compiler, and machine, so expect its timings to differ from ours. There's a separate
figure in the [matched Flocq comparison](results/flocq-matched/README.md), with complete numerical
agreement checks against Flocq and MPFR.

We convert the exact input values before the timer starts, and we record the selected backend,
iteration count, elapsed time, and result checksums. The comparison guide explains the scalar
dependency chain, the agreement checks, and how the external adapters differ. For broader
arithmetic comparisons, see the [external checks](../tests/EXTERNAL.md).
