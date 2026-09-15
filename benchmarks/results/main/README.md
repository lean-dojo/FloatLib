# Main format comparison

Before releasing FloatLib, we measured six public operations, comparing implementations
at equal encoded widths from 2 through 4096 bits. The results cover 448
implementation/width/operation combinations, each measured in nine trials.

The comparison includes:

- FloatLib posit at 2–4096 bits and binary at 4–4096 bits;
- MPFR and extracted Flocq at matched binary significand precision;
- 71 Stillwater Universal posit cells that passed the workload preflight;
- native C and Berkeley SoftFloat at binary32 and binary64; and
- CPython binary64 for the five operations available in the recorded interpreter.

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
certified kernels as the width grows; `backend-regimes.csv` records the backend at each point.

We check the saved files and regenerate their tables and figures with:

```bash
benchmarks/scripts/verify-main-result.sh
```

The charts compare equal storage widths, not equal value sets or exceptional
semantics. MPFR and Flocq are binary software references. Native C and
SoftFloat use the same dependent-chain protocol as FloatLib; the native rows
are a host-hardware baseline, not an instruction-latency or reciprocal-
throughput claim. CPython includes interpreter and object overhead. Posit
precision varies with magnitude, so its shared width axis is a storage
comparison rather than a claim of equal binary precision.

The evaluator image did not contain `rg`, which the original provenance helper
used only while computing one aggregate source hash. During publication we
recomputed that field from the authenticated per-file source ledger. The
original staged metadata and manifests, together with the exact correction,
are preserved under `release/provenance/`; no timing row or derived result was
changed.

The reports and figures use the current FloatLib name. Raw output retains the names
recorded by the campaigns; its contents and the original source-file hashes are unchanged.
Result manifests cover the published files and updated report labels.

The original Git history bundles contain unpublished manuscript history and are kept
private. Their recorded hashes remain in the original metadata. The public check verifies
the retained measured-source files against the original source ledger; it does
not verify the original Git history. Maintainers can also check an original bundle with
`verify_campaign_provenance.py --repository-bundle PATH`.

The benchmark source capture also included a nested history bundle. That one file is
omitted from `provenance/FloatLib-source-public.tar.gz`.
[`public-source-archive.json`](provenance/public-source-archive.json) records its original
hash and the public archive's hash. Every retained archive member must still match the
original source ledger.
