# Scalar conversions with TensorLib

This comparison calls TensorLib's unmodified `TensorLib/Float.lean` functions at revision
[`85e61c9`](https://github.com/leanprover/TensorLib/tree/85e61c9eb3211c736ded72b37254e2d608bbdbeb).
The FloatLib adapter calls `Model.cast`. Both convert between binary32 and FP16, BF16,
E4M3FN, or E5M2, with nearest-even rounding and no saturation.

Run from the FloatLib checkout, choosing local paths outside the repository:

```sh
python3 benchmarks/scripts/compare-tensorlib.py \
  --work-dir /tmp/floatlib-tensorlib \
  --build-dir /tmp/floatlib-build \
  --output /tmp/floatlib-tensorlib-results
```

Python 3, Git, Elan/Lake, and Linux `taskset` are required. The runner downloads the pinned
TensorLib checkout and builds both adapters with their own toolchains. `--cpu N` selects
an allowed logical CPU. `--skip-build` reuses executables already built from the same
adapters; choose a fresh output directory for each run.

The [results](../../results/tensorlib/results.json) contain source and executable hashes,
input/output digests, difference examples, timing fixtures, individual trials, medians,
and 5th to 95th percentiles. Full binary vectors and build products stay in the work directory.

## Correctness workload

- Decode every small-format encoding, including signed zeros, subnormals, infinities, and NaNs.
- Encode every finite destination value, adjacent-value midpoint, and overflow threshold,
  together with neighboring Float32 words and both signs.
- Add every Float32 exponent with selected mantissas, NaN payload boundaries, and 8,192
  seeded random words per format. Duplicate inputs are removed.
- Independently locate the nearest representable destination value, using even encoding
  parity for ties and explicit overflow rules. All destination values and tested midpoints
  are exactly representable in Python's binary64; this does not call either Lean library.

Both implementations pass all **952,612** value checks. Non-NaNs must match exactly.
The **2,964** E4M3FN differences are NaN signs: 2,963 negative finite overflows and
one negative infinity input produce `0x7f` for FloatLib and `0xff` for TensorLib.
Both are NaNs. The runner separately checks that
Float32 input construction changes only NaN encodings, as required by Lean's canonical
native-float representation. This experiment does not compare exception flags or NaN
signaling behavior.

## Timing workload

The shared [Lean protocol](../../lean/FloatLibBenchmarks/Support/ConversionProtocol.lean)
constructs native input values before starting the timer. It visits sixteen normal finite
values between -4 and 4, with each result selecting the next input. A UInt64 checksum
consumes every result and is independently recomputed by Python.

On these normal inputs, TensorLib's casts use integer shifts, masks, and rounding.
Its FP16 and FP8 decoders use native `Float32` multiplication for subnormal inputs,
which are covered by the correctness checks but excluded from the timed fixtures.
The timings therefore do not establish a speed advantage from FPU arithmetic.

Each direction and format has a 10,000-iteration pilot, followed by nine paired trials.
The common iteration count targets at least 20 ms for the faster pilot. Each process
warms up for 256 iterations; the library running first alternates between pairs.
The timed loop includes lookup, conversion, encoded output, index, and checksum work.
It excludes construction, process startup, and file output.

On the Intel Xeon Platinum 8275CL, TensorLib's medians are 5.9 to 13.0 times faster
than FloatLib's general descriptor cast on these fixtures. FloatLib uses Lean 4.33.1;
TensorLib uses Lean 4.33.0; both use Clang 22.1.4. These timings compare scalar cast
interfaces, not tensor throughput or FloatLib's arithmetic backend kernels.
