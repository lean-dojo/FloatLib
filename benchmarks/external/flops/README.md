# P3109 arithmetic: FloatLib and FLoPS

This comparison calls each library's executable P3109 arithmetic on the same encoded
inputs, using nearest-even rounding and no saturation. It covers `Binary4p2sf`,
`Binary8p4se`, and `Binary8p3se`, with addition, multiplication, division, and fused
multiply-add.

[FLoPS](https://github.com/rutgers-apl/FLoPS/tree/4ead906d8bceefd400620dcc52ec3245f84669e9),
by Tung-Che Chang, Sehyeok Park, Jay P. Lim, and Santosh Nagarakatte, provides the
independent implementation. We use its FMCAD artifact, which includes executable
bit-level kernels and refinement proofs. The
[paper](https://arxiv.org/abs/2602.15965v3) explains the P3109 model and numerical results.

## Run it

Use a Linux machine with Git, Python 3, `taskset`, and Lean's Elan toolchain manager.
The script builds each library with its pinned Lean version: 4.33.1 for FloatLib and
4.28.0 for this FLoPS revision. It downloads FLoPS and its Mathlib dependencies.
Choose local directories for source dependencies, builds, and the new result:

```bash
python3 benchmarks/scripts/compare-p3109-flops.py \
  --work-dir /tmp/p3109-comparison \
  --build-dir /tmp/floatlib-p3109-build \
  --output /tmp/p3109-result
```

`--cpu N` selects one logical CPU from the process's allowed set; otherwise the first
allowed CPU is used. An existing result is never overwritten. Build logs and generated
comparison vectors stay in the work directory. `results.json` contains the source and
compiler information, exact fixture words, agreement counts, individual measurements,
and summary statistics.

## What is checked

Addition, multiplication, and division enumerate every ordered pair of encoded inputs
in each format, including zero, NaN, and the extended formats' infinities. FMA
enumerates all 4,096 four-bit triples. For each eight-bit format it checks all 65,536
pairs `(x, y)`, choosing `z = (17*x + 29*y + 43) mod 256`. This gives **529,152
arithmetic cases**. The script compares the complete byte streams.

It separately compares the 16 exact input/output fixtures used by each of the 12 timing
configurations: **192 more cases**. A mismatch stops the experiment before timing.
These checks cover the chosen formats and policy; they do not test stochastic rounding
or either saturation mode.

## What is timed

Both adapters compile the same
[Lean workload](../../lean/FloatLibBenchmarks/Support/P3109Protocol.lean). Format
construction and the conversion of input codes to each library's carrier happen before
the timer. Each iteration reads one of 16 finite input triples, calls the operation,
observes its result code, and uses that result to select the next triple. The checksum
and input selection are included in the time. Process startup, warmup, and file output
are excluded.

Each process warms up for 256 iterations. A 10,000-iteration pilot chooses a common
iteration count targeting at least 100 ms for the faster implementation. Nine pairs
of fresh processes then alternate which library runs first, on the same logical CPU.
Every checksum must also match an independent Python simulation of the fixture chain.

The reported median and 5th–95th percentiles are computed from those nine measurements;
the percentiles describe trial variation, not a confidence interval. Different pinned
Lean and C compiler versions make this a comparison of the compiled libraries and
their adapters. It does not isolate the cost of an algorithm from its compiler.

The [results](../../results/p3109-flops/results.json) and
[guide table](../../../site/content/chapters/15-performance.md#p3109-arithmetic-with-flops)
report this workload separately from the IEEE and posit benchmark machine.
