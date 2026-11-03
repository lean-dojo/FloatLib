# FloatLib, Flocq, and MPFR

We compared addition, subtraction, multiplication, division, square root, and FMA
at matching binary precision and exponent bounds. All three implementations round
the exact rational inputs once, using nearest-even rounding and gradual underflow.
The storage widths are 6, 8, 16, 32, 64, 128, 256, 512, 1,024, 2,048, and 4,096 bits.
The custom 4-, 5-, and 7-bit layouts do not satisfy Flocq's `0 < precision < emax`
requirement and are excluded from all three curves.

The measured code is FloatLib 2.0.0 (commit `8c88715`). FloatLib 3.0.0 was not timed,
and comparing the code Lean generates for both, we found the same arithmetic on these paths. FloatLib uses
explicit proved word kernels at binary32/64 and public operations under
`PlanningThroughput` at the other widths. The comparison uses Lean 4.35.0 with Mathlib
`56a00585`, Flocq 4.2.2 extracted with Coq 8.20.1 and compiled with OCaml 4.13.1 and
Zarith, and MPFR 4.1.0 with GCC 11.5.0. Timing processes ran sequentially on logical
CPU 92 of an Intel Xeon Platinum 8275CL that other work shared, on 2026-10-31.

Each operation and width has sixteen input sets. The main loop uses the previous
result to select the next input set. Implementations run different calibrated
numbers of iterations. For square root at 1,024, 2,048, and 4,096 bits, all three
implementations instead visit every input once per block, with result-dependent
ordering. Those nine cells replace the corresponding main-loop entries. Every
measurement lasts at least 50 ms. Input construction, warmup, compilation, and
process startup are outside the timer. Input selection, arithmetic, result
observation, allocation, and checksum work are inside it.

Both the main loop and the square-root supplement ran nine trials.
`matched-benchmark-summary.csv` gives, per cell, the median, minimum, and maximum time
per operation over those trials, and its `source` and `measurementMethod` columns
name the raw trials behind each row. The archive's `summary/` directory adds the 5th
and 95th percentiles, the one-trial selection rule of the earlier campaign applied
to this run, and a cell-by-cell comparison with that campaign. These results are a
separate experiment from the nine-trial [main comparison](../main/README.md).

Before timing, the adapters agree on the result and input-selection checksums
of 256 operations per main-loop group and sixteen per square-root block.
A separate check compares the full significand, exponent, and sign of all
528 prepared inputs and 1,056 operation results across the three implementations.
They agree exactly after removing redundant powers of two. The fixtures contain
finite values and positive zeros. They do not test exception flags or NaN handling.

## Recreate the figure

From the repository root:

```bash
python3 benchmarks/plots/flocq_matched.py
python3 benchmarks/plots/flocq_matched.py \
  --out "${TMPDIR:-/tmp}/floatlib-flocq-matched.png"
```

The first command needs only Python's standard library, and drawing also needs
Matplotlib. Both commands verify the archive hashes, rebuild the nine-trial medians
from the raw trials, check the agreement prefixes, and compare the complete numerical
outputs. They do not run new measurements.

The ZIP contains the raw trials, calibration and environment records, numerical
outputs, the extracted Flocq sources, the square-root drivers, the analysis scripts,
and build and load logs. The [comparison guide](../../docs/Comparison.md) describes a
fresh run of the main fixture-chain workload. The square-root supplement's sources and
protocol are under `balanced-sqrt/` in the ZIP. Replaying its timings requires
rebuilding the pinned dependencies and adapting the captured paths and CPU affinity.
The ZIP is an evidence archive, not a standalone build package.

Local work and home paths and the host name in the captured records have been
replaced with `/workspace` and `benchmark-host.example.invalid` placeholders.
`publication-redactions.json` records the original and published hashes of each
changed member. The ZIP's member ledger and the verifier's archive hash authenticate
the published bytes. Numerical inputs and timings are unchanged.
