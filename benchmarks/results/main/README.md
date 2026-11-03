# Main format comparison

We measured six arithmetic operations, comparing implementations at equal encoded
widths from 2 through 4096 bits. The results cover 364
implementation/width/operation combinations, each measured in nine trials.

The comparison includes:

- FloatLib posit at 2 to 4096 bits and binary at 4 to 4096 bits;
- MPFR at the binary format's significand precision;
- 71 Stillwater Universal posit cells that passed the workload preflight;
- native C and Berkeley SoftFloat at binary32 and binary64; and
- CPython binary64 for the five operations available in the measured interpreter.

The measured code is FloatLib 2.0.0 (commit `8c88715`), built with Lean 4.35.0 and
Mathlib `56a00585`. FloatLib 3.0.0 was not timed. Comparing the code Lean generates for
both releases, we found the same arithmetic on every timed path: the changes there are
erased proof arguments, renames, and documentation.
The run took place on 2026-10-31 between 19:34 and 22:07 UTC, pinned to logical CPU
91 of an Intel Xeon Platinum 8275CL that other work shared. The adapters were built
with GCC 11.5.0 against MPFR 4.1.0, Universal `26e69f5`, and SoftFloat `a0c6494`.

Flocq is not in this run. It has its own [matched comparison](../flocq-matched/README.md),
which pairs exponent ranges and inputs with FloatLib. The campaign script labels any
run without Flocq as development-only, so `metadata.txt` records
`developmentOnly=1`. Every other setting is the publication profile: nine trials,
calibration toward 200 ms, a 256-operation agreement prefix, one pinned CPU, and the
full width and operation matrix. One cell falls short of the 50 ms row floor: four of
the nine MPFR 1024-bit addition trials lasted 49.1 to 49.7 ms, because the pilot
overestimated that cell's cost. `release/provenance/publication-exceptions.json`
records both departures, and the verifier accepts exactly those and nothing else.

Every adapter uses the same result-dependent fixture chain. This keeps each
operation observable to the optimizer and makes the next input depend on the
previous result. Alongside the individual trials, we record calibration, trial order,
process resources, backend selection, workload-agreement checks, and source information.

The main artifacts are under `release/benchmark/plots/`:

- `format-comparison.{png,svg,pdf}`
- `summary.csv`
- `ratios.csv`
- `backend-regimes.csv`

The figure connects the measured widths for each implementation. FloatLib can change
certified kernels as the width grows, and `backend-regimes.csv` records the backend at each point.

We check the saved files and regenerate their tables and figures with:

```bash
benchmarks/scripts/verify-main-result.sh
```

The charts compare equal storage widths, not equal value sets or exceptional
semantics. MPFR is a binary software reference. Native C and SoftFloat use the
same dependent-chain protocol as FloatLib. The native rows are a host-hardware
baseline, not an instruction-latency or reciprocal-throughput claim. CPython
includes interpreter and object overhead. Posit precision varies with magnitude,
so its shared width axis is a storage comparison rather than a claim of equal
binary precision.

At binary32 and binary64 this campaign times the configured word kernels by name,
as `benchmarks/docs/Comparison.md` describes, not the public `ExecFloat.Binary`
calls. The [public-call comparison](../public-binary/) times those calls against MPFR.

The source snapshot in `provenance/SNAPSHOT.txt` names the commit and the hash of
its library sources and build configuration. That hash matches
`leanSourceAndBuildConfigHash` in `metadata.txt`, and the verifier recomputes it from
the commit when the repository history is available. Local paths and the host name
in `metadata.txt` and two provenance files are replaced by placeholders.
`release/provenance/publication-redactions.json` records the original and published
hashes, and `release/provenance/original-benchmark-MANIFEST.tsv` is the run's own
manifest. No timing row or derived table was changed.
