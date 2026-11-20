# Benchmarks

We want FloatLib's proved arithmetic to be useful in real programs, so we measure what ordinary
public operations cost across small and large formats. These benchmarks are how we compare
backends, catch slowdowns, and see where we stand against libraries such as MPFR. None of this
is part of the normal library build.

For a first measurement, run this from the repository root:

```bash
source tests/lib/lake.sh
BENCH_ITERATIONS=1000 floatlib_benchmark_lake exe execFloatSweep add
```

That prints addition timings at 17 significand precisions, from 2 to 4,096 bits. Those are
just the sample points we picked for the benchmark, and you can define other formats.
Precision here counts significand bits, so the eight-bit precision point is bfloat16 even
though it takes 16 bits of storage. To time the other operations, replace `add` with `sub`,
`mul`, `div`, `sqrt`, `fma`, or `all`.

For a short comparison with independent implementations:

```bash
FORMAT_COMPARE_DEVELOPMENT_ONLY=1 \
  benchmarks/scripts/format-comparison.sh 1 "${TMPDIR:-/tmp}/floatlib-comparison"
```

The [comparison guide](docs/Comparison.md) lists the tools you need and the full nine-trial
command. Give each run a fresh output directory outside the checkout. Temporary work goes in
`TMPDIR`, and the shared build helper keeps build products out of the checkout as well.

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
| Kernel time of one operation, for proofs by `decide +kernel` | `benchmarks/kernel/run.sh kernel` |
| Kernel time of outcomes with status flags, comparisons, conversions and literals | `benchmarks/kernel/extras.sh` |
| Kernel time of three theorems about loops of 1,000 steps | `benchmarks/kernel/loops.sh` |
| Kernel time of two statements about all 65,536 pairs of E4M3 encodings | `benchmarks/kernel/exhaustive.sh` |
| Kernel time of every operation of IEEE 754-2019, binary and decimal, as written and with the kernel rules | `benchmarks/kernel/ieee2019.sh` |
| Kernel time of the P3109 operations, of posits with any number of exponent bits, and of the MX and NVFP4 quantizers | `floatlib_lake env lean benchmarks/kernel/P3109.lean`, and `PositGeneral.lean`, `MX.lean`, `NVFP4.lean` beside it |
| The proof checkers that ship with Lean, on the proofs by kernel evaluation | `benchmarks/kernel/checkers.sh` |
| Generated `roundoff` bounds against measured errors, in binary32 | `python3 benchmarks/roundoff/bounds.py` |
| Both modes in one run: kernel and compiled code, every family, Coq with Flocq, MPFR and SoftFloat | `benchmarks/suite/run.sh OUT` |
| Every figure of the speed work and its numbers, measured again on this checkout | `python3 benchmarks/plots/figures.py time RAW` |
| FPBench, MetiTarski and Flyspeck, hard-to-round inputs, Berkeley TestFloat | `benchmarks/suites/run.sh SUITE...` |

`execFloatTimeOps run CELL COUNT TRIALS REPS` times one cell from `list` (for example
`binary64/scale`) and prints both timings and result digests, and its counts have to be
positive. `execFloatTimeList` reads space-separated decimal encodings, one case per line with
up to three operands, and prints one timing per trial. It handles binary, posit, and explicit
limb carriers. Run it without arguments and it prints the supported format names.

The `benchmarks/kernel` scripts and files time Lean's kernel, the proof checker, not compiled code.
`run.sh PATHNAME` prints microseconds per operation for the six operations in seven formats
(and in the interchange formats of 256 to 4,096 bits when they are named), on
normal, subnormal and special operands: `public` reduces the public operations, `spec` the
reference operations, and `kernel` the operations that `float_decide` rewrites to, in the
rounding direction `KERNEL_BENCH_MODE`. `extras.sh` does the same for operations with
`status := true`, comparisons, the total order, classification, conversions to integers and
to exact rational values, casts and literals in binary32 and binary64, each term as written and
as `float_decide` rewrites it.
`loops.sh` type-checks three theorems both ways, and
`FlocqConversion.v` states the same three results for Coq with Flocq. `exhaustive.sh`
type-checks two statements about all pairs of E4M3 encodings. `ieee2019.sh` reduces every
operation of IEEE 754-2019 clauses 5 and 9 under its name in the standard, as written and
after the rewrite, from 8 to 4,096 bits and in the three decimal formats
([saved tables](results/ieee2019/README.md)). The four Lean files are a list of
`#kernel_cost` lines each: elaborate one and it prints the kernel time of every term with the
rules, and as written where that is fast enough to run. The
[saved tables](results/kernel/README.md) say what we measured and where.

`checkers.sh` asks whether the proof checkers that ship with the Lean toolchain accept these
proofs, and what the proofs cost them. `leanchecker` and `leanchecker-paranoid` replay a module's
`.olean` file in Lean's kernel. `nanoda_bin` and `con-ron` are checkers of their own that read an
export written by `leanexport`, and `leanchecker --from-export` runs Lean's kernel on that same
export. There are five families: the definition modules of `Numerics.Kernel`, which import no
mathematics from Mathlib; the kernel-arithmetic checks of the test suite, with each `example`
named; the three loop
theorems of `loops.sh` by `float_decide` and by `decide +kernel`; and the two statements of
`Exhaustive.lean`. Each run has a baseline with the same imports and without the family's own
declarations: a module with only the imports for the replaying checkers, and for an export the
constants that the family uses from other modules, which `Closure.lean` lists.
[`kernel/checkers.csv`](kernel/checkers.csv) has one row per family and checker: the verdict, the
seconds of the run and of its baseline, and their difference. The saved file is one run of each
checker with Lean 4.36.0 on 2026-11-17, on the shared Xeon machine of the
other benchmarks while other jobs were running, so a difference of a few seconds is within the
noise of the two runs it is taken from. The rows of the first family are from a second call of the
script, `checkers.sh exact-layer`.

All five checkers accepted four of the families. On `exhaustive`, `leanchecker`,
`leanchecker-paranoid` and `con-ron` accepted the two theorems. `nanoda_bin` and
`leanchecker --from-export` gave no verdict on that family within the limits of the run, which
the file shows as `no verdict` with the seconds at which each run ended: on an export, a checker
checks every declaration that the theorems depend on again.

Two more things to know when you run the checkers yourself: `nanoda_bin` and `con-ron` decline
an export that contains an `unsafe` or `partial` definition, such as the code Lean generates for
a well-founded recursion, so the script leaves those out; and `leanchecker` matches module names
by prefix, so the script starts it once per module.

`benchmarks/roundoff` asks how tight the bounds are that `roundoff` proves from code.
`Programs.lean` generates the theorems of ten programs, and `bounds.py` runs the programs in
binary32 and divides each bound by the measured error. The [saved table](results/roundoff/README.md)
says which numbers are Lean's and which are the script's.

`benchmarks/suite/run.sh OUT [SECTION...]` runs both modes and writes tables and CSV files
into `OUT`. Its sections are the kernel sweep of the binary formats from 8 to 4,096 bits
with two custom layouts (`kernel-binary`), the same five loops in Lean's kernel and in Coq with
Flocq with a check that both print the same values (`matched`, `flocq`), one operation in fixed
point, logarithmic, P3109, posit, decimal and MX formats as written and with the tagged kernel
rules (`families`), statements about all pairs of encodings by a loop and by one run on all
lanes (`exhaustive`), and compiled code: the precision sweep, FP8, posits, and FloatLib next to
MPFR, Berkeley SoftFloat and the native FPU (`compiled`). `tables` turns the logs into
`README.md` and CSV files. The header of `run.sh` lists the options.

`benchmarks/plots/figures.py` is the one script behind the figures of the speed work.
`figures.py time RAW` measures the checkout it runs in: it starts the runners of
`benchmarks/kernel/`, `benchmarks/suite/` and `benchmarks/exact/` section by section, with
their logs in `RAW` (a directory outside the checkout), writes their tables and CSV files
under `results/`, and draws every figure into `results/figures/` as PNG and PDF with the CSV
of what is drawn. The kernel sections run one at a time, because a cell there is a difference
of a few microseconds and a second job on the machine shows in it. On Linux with core
scheduling a measuring process also has its cores to itself, because a job on the second
hardware thread of a core makes a measurement on the first 1.5 to 2 times slower. The rows of
1,024 and 4,096 bits of the IEEE table are the exception: they run eight at a time. The
compiled sections and those rows follow the kernel sections, up to eight sections at a time,
and the rows set the length of a run: they take about 85 minutes here. The mode needs the
library built and links the benchmark executables itself, which takes about ten minutes the
first time. `--only` measures some sections again and keeps the others, and the record says
which run each section is from. It names the measured commit when a remote branch has it.
`figures.py draw` draws again from the result files, and `figures.py list` names the figures
and the timing sections. An image holds only the plot: axes with units, a legend of short
series names and panel letters, in the style of the guide's `figstyle.py`. Everything else is
in [`results/FIGURES.md`](results/FIGURES.md), which numbers the figures (Figure 1, Figure 2,
...) and has for each one its files, its alt text, its caption (what it shows, what was
measured and in which unit, the scales, the machine and the toolchain), notes on the
method, on which numbers come from Lean and which from scripts, and its CSV columns. The
result READMEs of `kernel/`, `backends/`, `ieee2019/` and `suites/` end with their own
figures, numbered from Figure 1, and `draw` also redraws the guide's matched Flocq comparison.
What the timing mode does not measure (Coq, the complex functions, the interval corpora) is
recorded in `results/figures/recorded/` with its own provenance.

`benchmarks/suites/` holds four standard community suites: FPBench programs for `roundoff`,
the MetiTarski and Flyspeck inequalities for `interval`, published hard-to-round inputs for the
correctly rounded functions, and Berkeley TestFloat. [Their README](suites/README.md) says how
to run them, and [`results/suites/README.md`](results/suites/README.md) has the results.

The [performance chapter](../site/content/chapters/12-performance.md) walks through the plots, and
[`results/FIGURES.md`](results/FIGURES.md) describes the data behind them. Don't expect your
timings to match ours, because your run measures your source, compiler, and machine. There's a
separate figure in the [matched Flocq comparison](results/flocq-matched/README.md), with
complete numerical agreement checks against Flocq and MPFR.

We convert the exact input values before the timer starts, and we record the selected backend,
iteration count, elapsed time, and result checksums. The comparison guide explains the scalar
dependency chain, the agreement checks, and how the external adapters differ. For broader
arithmetic comparisons, see the [external checks](../tests/EXTERNAL.md).
