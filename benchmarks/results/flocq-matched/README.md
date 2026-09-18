# FloatLib, Flocq, and MPFR

We compared addition, subtraction, multiplication, division, square root, and FMA
at matching binary precision and exponent bounds. All three implementations round
the exact rational inputs once, using nearest-even rounding and gradual underflow.
The storage widths are 6, 8, 16, 32, 64, 128, 256, 512, 1,024, 2,048, and 4,096 bits.
The custom 4-, 5-, and 7-bit layouts do not satisfy Flocq's `0 < precision < emax`
requirement and are excluded from all three curves.

FloatLib uses explicit proved word kernels at binary32/64 and public operations
under `PlanningThroughput` at the other widths. The comparison uses Lean 4.34.0,
Flocq 4.2.2 extracted with Coq 8.20.1 and compiled with OCaml 4.13.1 and Zarith,
and MPFR 4.1.0 with GCC 11.5.0. Timing processes ran sequentially on logical CPU 39
of an Intel Xeon Platinum 8275CL.

Each operation and width has sixteen input sets. The main loop uses the previous
result to select the next input set; implementations run different calibrated
numbers of iterations. For square root at 1,024, 2,048, and 4,096 bits, all three
implementations instead visit every input once per block, with result-dependent
ordering. Those nine measurements replace the corresponding main-loop entries.
Every selected measurement lasts at least 50 ms. Input construction, warmup,
compilation, and process startup are outside the timer; input selection,
arithmetic, result observation, allocation, and checksum work are inside it.

The selected CSV contains one trial per entry, with no estimate of variability.
It uses the first main trial and the separate complete-block square-root run,
as recorded in its `source` and `measurementMethod` columns. These results are a
separate experiment from the nine-trial [main comparison](../main/README.md).

Before timing, the adapters agree on the result and input-selection checksums
of 256 operations per main-loop group and sixteen per square-root block.
A separate check compares the full significand, exponent, and sign of all
528 prepared inputs and 1,056 operation results across the three implementations.
They agree exactly after removing redundant powers of two. The fixtures contain
finite values and positive zeros; they do not test exception flags or NaN handling.

## Recreate the figure

From the repository root:

```bash
python3 benchmarks/plots/flocq_matched.py
python3 benchmarks/plots/flocq_matched.py \
  --out "${TMPDIR:-/tmp}/floatlib-flocq-matched.png"
```

The first command needs only Python's standard library; drawing also needs
Matplotlib. Both commands verify the archive hashes, reconstruct the selection
from raw timings, check the agreement prefixes, and compare the complete numerical
outputs. They do not run new measurements.

The ZIP contains the raw CSVs, numerical outputs, captured library sources,
adapters, and build records. The [comparison guide](../../docs/Comparison.md)
describes a fresh run of the main fixture-chain workload. The square-root
supplement's sources and protocol are under `balanced-sqrt/` in the ZIP.
Replaying its timings requires rebuilding the pinned dependencies and adapting
the captured paths and CPU affinity; the ZIP is an evidence archive, not a
standalone build package.
