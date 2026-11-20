# Standard community benchmarks

Read [the experiment contract](PROOF.md) and [trust scope](TRUST.md), then the suite README:

1. [FPBench](../fpbench/README.md): translated floating-point programs and error analysis.
2. [Real inequalities](../inequalities/README.md): MetiTarski and Flyspeck.
3. [Correct rounding](../correct-rounding/README.md): published hard cases and binary32 screening.
4. [Berkeley TestFloat](../testfloat/README.md): basic operations, conversions and flags.
5. [Capability reproductions](repro/README.md): small, source-derived failure probes.

From the repository root:

```sh
bash benchmarks/suites/run.sh selftest
bash benchmarks/suites/run.sh fpbench fpbench-tools inequalities correct-rounding testfloat
```

The driver runs the suites one after the other. Inside a suite, `FLOATLIB_SUITE_WORKERS`
Lean processes are measured at a time (default one), each with
`FLOATLIB_SUITE_THREADS` threads (default eight). With `FLOATLIB_SUITE_SLICE` set
to a systemd user slice, the driver first checks the host's free memory and idle
CPU, then moves itself into a scope of that slice with a memory cap
(`FLOATLIB_SUITE_MEMORY`, default 16 GiB), at nice 19 and under an outer timeout
(`FLOATLIB_SUITE_JOB_TIMEOUT`, default 540 seconds). Large campaigns can use
successive ranges:
`FLOATLIB_SUITE_OFFSET` and `FLOATLIB_SUITE_LIMIT`. Every inventory row remains
present; an unselected row is `not_run`. `FLOATLIB_SUITE_RESULTS` selects the
output directory. Without it, results go under `suites/results/<git-commit>/`.
`FLOATLIB_SUITE_TIMEOUT` is the per-process limit for Lean proof and runtime checks,
and `FLOATLIB_NUMERIC_TIMEOUT` the one for FPBench's numerical proofs.
A finished proof is cached under its plan, harness, commit and limit, so a run
that stops can be started again and repeats only what did not finish.

No server or JavaScript runtime is used. Source acquisition uses pinned sparse
Git checkouts or checksummed downloads. `fetch.py` rejects a different revision,
modified tracked source, or any selected file with the wrong checksum. Upstream
trees, build products and raw working results are ignored by Git.

Python parses sources, generates plans, checks reference agreement and writes CSV.
`Proofs.lean` elaborates each proof in a restored command environment and checks
the transitive axiom set. It is a `module`, so a case elaborates with the exported
declarations of its imports, as a module of the library does. Native Lean executables perform the differential tests;
these executable observations are not kernel proofs. `process.py` records wall
time and a sampled RSS peak, and kills the process group on timeout. The outer
job log records `/usr/bin/time -v` resource use.

Each proof result records its generated statement, actual diagnostics, plan hash,
source commit, tracked diff hash, harness hash and measurement timestamp. A
cached measurement keeps its timestamp. The Lean proof timer includes command
elaboration, diagnostics, the transitive axiom check and statement printing.
Numerical-bound attempts also re-elaborate their conditional theorem in the
fresh environment; their elapsed time includes that work.
Timings from that proof check, native
calls, process startup, reference generation and external tools are separate
fields. Empty numerical-bound or ratio fields mean no such measurement was
established; they never mean zero.

The suite Lake configuration reuses the repository's existing dependency pins
and build location through `tests/lib/lake.sh`. The benchmark additions do not
repair library or test failures. Run the repository's `lake lint` and check
runner separately; capability probes deliberately contain rejected cases.

## Results

[`../results/suites/README.md`](../results/suites/README.md) has the results of the last
run of each suite, on Lean v4.36.0, as tables, with one short CSV file per suite
next to it and `counts.csv` for every number. `summarize.py` writes them from the
results directory of a run:

```sh
python3 benchmarks/suites/summarize.py RESULTS --tools FPBENCH_TOOLS_RESULTS.csv
```

A suite that `RESULTS` does not hold keeps its summary, so one suite can be run again
alone. Without `--tools` the bounds of the external FPBench tools are the recorded ones
of `fpbench-tools.csv`. A run's own `results.csv` files hold every statement, plan and
command and are tens of megabytes, so they stay outside the repository, and
`provenance.json` records their sizes and SHA-256 hashes. The figures `suites-fpbench`, `suites-inequalities`,
`suites-hard-cases` and `suites-testfloat` of
[`../results/FIGURES.md`](../results/FIGURES.md) draw the summaries.

What the runs found beyond their counts:

- FPBench's generated numerical proof splits its premises with `And.intro` only, because
  `constructor` also applies to `a ≤ b` on the reals, and it sets a recursion depth of
  10,000. Its refusals are refusals of that proof, most of them in an `interval` step
  that has no rational bound for a computed value.
- With the constraint engine imported, `interval` proves 340 MetiTarski goals where it
  proves 124 without it, and 64 attempts pass the 20 seconds of the suite. No process
  stops at Lean's 4 GB memory limit.
- Of the eight MetiTarski problems named after π, `interval` proves three with
  `FloatLib.Tactic.Interval` alone and six with `import FloatLib`.
- The complex `exp`, `expm1`, `log` and `log1p` agree with GNU MPC on every part
  of every hard-to-round argument `x + i x` of the selection.
