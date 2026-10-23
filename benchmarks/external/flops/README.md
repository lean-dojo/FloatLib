# P3109 arithmetic: FloatLib and FLoPS

We call each library's executable P3109 arithmetic on the same encoded inputs, with
nearest-even rounding and no saturation. That covers three formats, `Binary4p2sf`,
`Binary8p4se`, and `Binary8p3se`, and four operations: addition, multiplication, division,
and fused multiply-add.

[FLoPS](https://github.com/rutgers-apl/FLoPS/tree/4ead906d8bceefd400620dcc52ec3245f84669e9),
by Tung-Che Chang, Sehyeok Park, Jay P. Lim, and Santosh Nagarakatte, is the independent
implementation. We use its FMCAD artifact, which has executable bit-level kernels and
refinement proofs, and their [paper](https://arxiv.org/abs/2602.15965v3) explains the P3109
model and the numerical results.

## Run it

You need a Linux machine with Git, Python 3, `taskset`, and Lean's Elan toolchain manager.
The script downloads FLoPS and its Mathlib dependencies and builds each library with its own
pinned Lean version (our reported measurements used Lean 4.33.1 for FloatLib and 4.28.0 for
FLoPS). Choose local directories for source dependencies, builds, and the new result:

```bash
python3 benchmarks/scripts/compare-p3109-flops.py \
  --work-dir /tmp/p3109-comparison \
  --build-dir /tmp/floatlib-p3109-build \
  --output /tmp/p3109-result
```

`--cpu N` picks one logical CPU from the process's allowed set, and without it the script
uses the first allowed CPU. It never overwrites an existing result. Build logs and generated
comparison vectors stay in the work directory, while `results.json` gets the source and
compiler information, exact fixture words, agreement counts, individual measurements, and
summary statistics.

## What is checked

For addition, multiplication, and division we enumerate every ordered pair of encoded inputs
in each format, including zero, NaN, and the extended formats' infinities. FMA enumerates
all 4,096 four-bit triples. In each eight-bit format it checks all 65,536 pairs `(x, y)`
with `z = (17*x + 29*y + 43) mod 256`. That's **529,152 arithmetic cases** in all, and the
script compares the complete byte streams.

On top of those, it compares the 16 exact input/output fixtures used by each of the 12
timing configurations, which adds **192 more cases**. Any mismatch stops the experiment
before timing starts. These checks cover the chosen formats and policy, so stochastic
rounding and both saturation modes go untested.

## What is timed

Both adapters compile the same
[Lean workload](../../lean/FloatLibBenchmarks/Support/P3109Protocol.lean). Constructing the
format and converting input codes to each library's carrier happen before the timer starts.
Each iteration reads one of 16 finite input triples, calls the operation, looks at its
result code, and uses that result to pick the next triple. The timed loop includes the
checksum and input selection, and leaves out process startup, warmup, and file output.

Each process warms up for 256 iterations. Then a 10,000-iteration pilot picks a common iteration
count that targets at least 100 ms for the faster implementation. Nine pairs of fresh processes
follow on the same logical CPU, alternating which library runs first, and every checksum also
has to match an independent Python simulation of the fixture chain.

We report the median and the 5th–95th percentiles of those nine measurements. Those
percentiles describe how much the trials varied, and they aren't a confidence interval.
Because the two libraries pin different Lean and C compiler versions, this compares the
compiled libraries and their adapters. It can't separate the cost of an algorithm from its
compiler.

Both the [results](../../results/p3109-flops/results.json) and the
[guide table](../../../site/content/chapters/17-performance.md#p3109-arithmetic-with-flops)
report this workload on its own, apart from the IEEE and posit benchmark machine.
