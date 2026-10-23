# Scalar conversions with TensorLib

We call TensorLib's unmodified `TensorLib/Float.lean` functions at revision
[`85e61c9`](https://github.com/leanprover/TensorLib/tree/85e61c9eb3211c736ded72b37254e2d608bbdbeb),
and the FloatLib adapter calls `Model.cast`. Both sides convert between binary32 and FP16,
BF16, E4M3FN, or E5M2, with nearest-even rounding and no saturation.

Run from the FloatLib checkout, choosing local paths outside the repository:

```sh
python3 benchmarks/scripts/compare-tensorlib.py \
  --work-dir /tmp/floatlib-tensorlib \
  --build-dir /tmp/floatlib-build \
  --output /tmp/floatlib-tensorlib-results
```

You need Python 3, Git, Elan/Lake, and Linux `taskset`. The runner downloads the pinned
TensorLib checkout and builds both adapters, each with its own toolchain. `--cpu N` picks an
allowed logical CPU, and `--skip-build` reuses executables already built from the same
adapters. Use a fresh output directory for each run.

In the [results](../../results/tensorlib/results.json) you'll find source and executable
hashes, input/output digests, difference examples, timing fixtures, individual trials,
medians, and 5th to 95th percentiles. Full binary vectors and build products stay in the
work directory.

## Correctness workload

- Decode every small-format encoding, including signed zeros, subnormals, infinities, and NaNs.
- Encode every finite destination value, adjacent-value midpoint, and overflow threshold,
  together with neighboring Float32 words and both signs.
- Add every Float32 exponent with selected mantissas, NaN payload boundaries, and 8,192
  seeded random words per format, then drop duplicate inputs.
- Find the nearest representable destination value independently, breaking ties by even
  encoding parity and applying stated overflow rules. Every destination value and tested
  midpoint is exactly representable in Python's binary64, and this reference calls neither
  Lean library.

Both implementations pass all **952,612** value checks, and non-NaN results have to match
exactly. All **2,964** E4M3FN differences are NaN signs. For 2,963 negative finite overflows
and one negative infinity input, FloatLib produces `0x7f` and TensorLib produces `0xff`, and
both of those are NaNs. We also check that building the Float32 inputs changes only NaN
encodings, which Lean's canonical native-float representation requires. Exception flags and
NaN signaling behavior aren't part of this experiment.

## Timing workload

Both sides share a
[Lean protocol](../../lean/FloatLibBenchmarks/Support/ConversionProtocol.lean) that builds
the native input values before the timer starts. It then visits sixteen normal finite values
between -4 and 4, each result picking the next input. A UInt64 checksum consumes every
result, and Python recomputes it independently.

On these normal inputs, TensorLib's casts use integer shifts, masks, and rounding. Its FP16
and FP8 decoders do use native `Float32` multiplication for subnormal inputs, but subnormals
are covered by the correctness checks and left out of the timed fixtures. So the timings
can't show a speed advantage from FPU arithmetic.

Each direction and format gets a 10,000-iteration pilot and then nine paired trials. The pilot
timings set a common iteration count that targets at least 20 ms for the faster implementation.
Each process warms up for 256 iterations, and the library that runs first alternates between
pairs. The timed loop covers lookup, conversion, encoded output, index, and checksum work.
Construction, process startup, and file output are outside it.

On the Intel Xeon Platinum 8275CL, TensorLib's medians are 5.9 to 13.0 times faster than
FloatLib's general descriptor cast on these fixtures. FloatLib uses Lean 4.33.1 and
TensorLib uses Lean 4.33.0, both with Clang 22.1.4. What's being compared here is the scalar
cast interface. Tensor throughput and FloatLib's arithmetic backend kernels don't enter into
it.
