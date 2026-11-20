# FPBench

Source: [FPBench/FPBench](https://github.com/FPBench/FPBench), commit
`8ac4ff6cf0c3be4f9669a562ef2bbbbc3b15182d`, MIT (`LICENSE.txt`). The source
manifest pins all 12 `benchmarks/*.fpcore` suite files and the exporter. Fetch
with `python3 benchmarks/suites/fetch.py benchmarks/fpbench/fpbench-source.json`
inside the campaign resource wrapper.

```sh
FLOATLIB_SUITE_OFFSET=0 FLOATLIB_SUITE_LIMIT=12 \
  bash benchmarks/suites/run.sh fpbench
FLOATLIB_TOOL_CONFIG=/absolute/path/to/tools.json \
  FLOATLIB_SUITE_OFFSET=0 FLOATLIB_SUITE_LIMIT=4 \
  bash benchmarks/suites/run.sh fpbench-tools
```

The Lean experiment has one row per source program, default precision
(`binary32`, `binary64`) and method (forward mixed, closed, backward). Explicit
source precision and rounding annotations override the default. Thus a
source-fixed binary64 program is not relabeled as binary32 in the first run.
Input arguments denote stored values. The ideal reference is the real
interpretation of the program body, rather than the optional `:spec` expression.

The scalar translator preserves lexical scope, parallel `let` versus sequential
`let*`, evaluation order, constants, casts and supported rounding attributes.
It handles arithmetic, FMA, square root, supported correctly rounded calls,
comparisons and conditionals. Unsupported operators, loops, tensors, precision
families and unsupported mixed-precision operations produce explicit refusals.
In particular, it does not truncate loops or narrow an operand before an
operation that should have only one final rounding.

A generated symbolic theorem retains its finiteness and domain premises. Its
full pretty-printed statement is the bound record. Success on that theorem
alone is not a uniform error bound over the FPBench precondition. Numerical
comparisons require the domain premises to be discharged and the reference
input convention to agree; otherwise the numeric bound and ratio remain empty.

`tools.py` invokes the pinned FPBench exporter, using one identical FPCore
specialization for `.fptaylor`, `.gappa`, `.scala`, `.sollya` and `.smt2`.
Each output hash, export command, warning and export time is retained. FPTaylor,
Gappa and Daisy bounds have their own tool time. Sollya's exporter defines
procedures: loading those procedures is recorded separately and is not called
an error analysis. The original Sollya export is retained byte-for-byte; the
invocation copy appends `quit;` because Sollya 8.0 returns code 3 at EOF after
a valid procedure declaration. Both input hashes are recorded. SMT-LIB export
is an interchange artifact.

Configure installed plain CLIs with JSON:

```json
{
  "racket": {"executable": "/absolute/path/to/racket"},
  "environment": {"PLTUSERHOME": "/absolute/path/to/racket-packages"},
  "fptaylor": {
    "executable": "/absolute/path/to/fptaylor",
    "cwd": "/absolute/path/to/fptaylor-source",
    "version": "pinned build",
    "revision": "46e0d2ff37fa84e513048d3445be8c030831b11f"
  },
  "gappa": {"executable": "/absolute/path/to/gappa", "version": "1.8.3"},
  "daisy": {"executable": "/absolute/path/to/daisy", "arguments": []},
  "sollya": {"executable": "/absolute/path/to/sollya", "version": "8.0"}
}
```

The FPTaylor working directory supplies its `default.cfg`; additional runtime
environment values can be supplied under the tool's `environment` key.
`FLOATLIB_TOOL_TIMEOUT` bounds each export and analysis, default 30 seconds.
`FLOATLIB_CLI_TOOLS=gappa,daisy` selects particular CLI tools for a rerun;
other recorded measurements are retained.
No server entry point is used. An unavailable executable gets an explicit row.

Reference projects and papers:

- The numerical transcriptions in `published-papers.json` come from the
  authors' [FM 2015 paper](https://soarlab.org/papers/2015_fm_sjrg.pdf),
  Tables 2 and 4, and the [Satire v1 paper](https://arxiv.org/pdf/2004.11960v1),
  Table 1 (2020-04-24). PDF and extracted-text hashes accompany the observations.
  The FM table includes Gappa 1.1.2 with and without hints; its timings are
  reported per program only for `jetEngine`. The Satire table reports
  first-order analysis. The table does not establish each program's precision,
  so the transcription does not infer it from a benchmark name.
- FPTaylor: Solovyev et al., *Rigorous Estimation of Floating-Point Round-Off
  Errors with Symbolic Taylor Expansions*, ACM TOPLAS 2018,
  [doi:10.1145/3230733](https://doi.org/10.1145/3230733). Pinned source and
  regression bounds: `fptaylor-source.json`; MIT.
- Daisy: Darulova et al., *Daisy - Framework for Analysis and Optimization of
  Numerical Programs*, TACAS 2018. Pinned source and regression CSV:
  `daisy-source.json`; Apache-2.0.
- Satire: [published project and artifact](https://github.com/arnabd88/Satire),
  pinned by `satire-source.json`; MIT. Its own workload is not substituted for
  the FPBench program being compared.
- Gappa: [project documentation](https://gappa.gitlabpages.inria.fr/), version
  1.8.3; CeCILL. Generated Gappa input is retained for auditing any domain
  widening or ignored source constraints.
- Sollya: [version 8.0 source](https://www.sollya.org/releases/sollya-8.0/sollya-8.0.tar.gz);
  CeCILL-C, as stated in the release's `COPYING`.

The exporter can weaken source preconditions: its FPTaylor backend extracts
variable ranges, and its Gappa backend can widen strict endpoints or omit
unsupported inequalities. Export warnings and input contracts must be considered
before interpreting a ratio. Published timings remain labeled as published;
they are not timings on the current machine.

`contracts.py` audits a conservative subset of the local FPTaylor exports:
plain scalar inputs, a closed conjunctive box, one binary32/binary64 precision,
supported rounding and arithmetic. FPTaylor leaves these input variables
unrounded, so its continuous input domain contains the stored finite inputs
of the Lean theorem. Ratios on this subset compare applicable upper bounds;
they do not assert that both tools optimize over exactly the same set.
The Gappa audit additionally accepts integer-coefficient `+`, `-`, `*` and
parallel `let` expressions with integer box endpoints. A coarse magnitude
check excludes overflow at every operation. The exported real-input bound
then applies to stored inputs because rounding those inputs again is exact.
The argument and limits are in `suites/PROOF.md`; each row records its largest
checked pre-rounding magnitude. Other Gappa expressions remain unmatched.
Daisy's rounded literal emission still needs a source-contract audit, and its
CLI prints a decimal converted through binary64 rather than its internal exact
rational bound. Its displayed numbers remain labeled and have no admitted ratio.

`historical.py` compares the pinned FPTaylor regression inputs with named
FPBench candidates. `published-fptaylor/` contains MIT-licensed FPCore exports
from that project's native exporter, with source, output and exporter hashes.
The audit preserves operation order, precision, rounding mode, narrowing casts,
and every box constraint. It expands lexical bindings and removes only exact
casts; rational literals retain any required rounding. Negative-zero literals
and nondefault source rounding encodings require a separate audit.

`published-contracts.csv` reports every candidate match or refusal. A matched
historical real-input contract supplies an applicable upper bound for the
finite stored inputs in the Lean theorem. The comparison driver emits
`*_fptaylor_published_ratios` only when a numerical Lean proof also exists and
the source hashes agree. Historical timings remain metadata, with no machine
speedup ratio. This syntactic audit is Python evidence, not a Lean proof of
the external analyzer.

Join the two result files without rerunning measurements:

```sh
python3 benchmarks/fpbench/compare.py \
  /results/fpbench/results.csv /results/fpbench-tools/results.csv \
  /results/fpbench-comparison.csv
```

The joined CSV has one row per source program and default precision, all three
Lean methods, local bounds and times, candidate published records, exact
rational bound ratios where audited, and numerical coverage classes. A
conditional theorem alone does not count as numerical coverage. Each numerical
attempt uses one untrusted propagated estimate rounded up to a power of two.
The campaign does not search for an optimized bound; Lean must prove the proposal.

## Results on Lean v4.36.0

The suite ran on 2026-11-20, eight Lean processes at a time with
three threads each and 60 seconds per process. [`../results/suites/README.md`](../results/suites/README.md)
has the tables, [`fpbench.csv`](../results/suites/fpbench.csv) one row per program, default precision
and method, and [`fpbench-comparison.csv`](../results/suites/fpbench-comparison.csv) the ratios.

| Method | Conditional proofs | Tactic refusals | Timeouts | Translation refusals | Numerical proofs | Numerical: refused | over 60 s | out of memory |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Forward | 184 | 4 | 0 | 84 | 33 | 71 | 0 | 0 |
| Closed | 180 | 8 | 0 | 84 | 18 | 82 | 2 | 0 |
| Backward | 22 | 166 | 0 | 84 | n/a | n/a | n/a | n/a |

With 60 seconds no conditional attempt runs out of time. The twelve forward and closed theorems
that are refused all stop at the heartbeat limit (`maximum number of heartbeats (200000) has been
reached`).

Over all 206 numerical attempts, 2 pass 60 seconds and no Lean process stops at its 4 GB memory
limit (`lean -M 4096`): the largest takes 2.3 GB. The 153 refusals are refusals of the generated
proof. In 123 of them an `interval` step gives up: 95 with `interval needs a rational lower bound
for` or `upper bound for` a computed value, and 40 with `interval expects a real or
nonnegative-real inequality`.

The external tools' bounds do not depend on FloatLib, and they are the ones of 2026-11-17. Joined
with them, 41 specializations have a numerical Lean proof and a local tool bound,
88 a tool bound only, 0 a Lean bound only and
143 neither. The audited contracts admit 23 local FPTaylor
ratios (2.13333 to 698373), 14 Gappa ratios (1.03854 to 1.93939) and
7 ratios to bounds that FPTaylor's regression files publish.

The generated numerical proof (`numeric.py`) splits the premises with `repeat' apply And.intro`,
because `constructor` also applies to `a ≤ b` on the reals and goes on into the definition of the
order, and it sets `maxRecDepth` to 10,000.
