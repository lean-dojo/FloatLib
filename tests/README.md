# Tests

We prove general properties in Lean, compare our compiled arithmetic with independent
implementations, and check which axioms and execution mechanisms the proofs depend on.
The comparisons can catch a mistake in our reading of a standard as well as a runtime bug.
Run these commands from the
repository root, after the [project setup](../README.md#installation).

```bash
bash tests/verify.sh
```

This builds the library, checks conformance proofs, runs native regressions, and checks lint,
imports, API docs, and the axioms of library declarations loaded by the trust audit. That includes
compiler equality proofs and the public root's dependencies. Arb runs when
`python-flint` is installed; otherwise the verifier reports that it was skipped. Any failed
check fails the command.

For just the proofs and native regressions, or to choose a native suite:

```bash
source tests/lib/lake.sh
floatlib_test_lake test
floatlib_test_lake exe check --help
```

The helper shares the scripts' build lock and keeps compiler output outside the checkout.
Set `FLOATLIB_BUILD_DIR` before sourcing it to choose a local build directory; `TMPDIR` controls
temporary work. The commands below also start at the repository root.

Native suites cover models, public instances, rounding policies, integer kernels, tiny formats,
transcendental kernels (behind the named `Configured.Transcendentals` import), host-FPU behavior,
and a smoke run of the format-comparison example. The example check succeeds if the demonstration
returns without throwing; it does not compare the printed values with expected results.

We report failures by named check through `ReportSection.ofRows` in
[Accounting.lean](FloatLibTests/Accounting.lean).

## Checking a change

For an ad-hoc calculation or proof check, use a scratch file on local disk outside the tracked
source tree. After building its imports, check it with:

```bash
source tests/lib/lake.sh
floatlib_lake env lean /path/to/local-scratch/Check.lean
```

We use scratch files for one-off experiments and remove them once the question is settled.
The maintained `tests/` directory holds symbolic API integration, runtime regressions,
reusable comparison adapters, and trust checks.
[CONTRIBUTING.md](../CONTRIBUTING.md) explains the build and proof workflow.

## Results and external comparisons

We can check the saved results or run new comparisons:

| Command | What it does |
| --- | --- |
| `bash tests/oracles/verify-main-result.sh` | Check saved artifacts and captured sources, regenerate figures, and compare the captured source inputs with this checkout |
| `bash tests/oracles/check.sh --profile quick` | Build current source and run a bounded set of independent comparisons and native checks |
| `bash tests/oracles/check.sh --profile release` | Build current source and run the full set of comparisons supported by the runner |

The verifier checks the files and source information recorded with each result and regenerates
the figures. It also compares the recorded library, build, test, and benchmark inputs with
the checkout; documentation changes do not affect that comparison. The `quick` and `release`
profiles run the outside tools on the current source and environment.
The runner inherits CPU affinity, caps its default worker count at the available CPUs or eight,
and writes to a new directory under `TMPDIR` (normally `/tmp`). Use `--results` to choose a
different new directory.

Both runner profiles check binary16 addition and multiplication against MPFR using 16 left
operands: signed zeros, subnormals, the smallest normal, ordinary normals, the largest finite
magnitudes, infinities, and quiet and signaling NaNs. Each is paired with all 65,536 right
encodings, for 2,097,152 comparisons across the two operations. Saved results retain the smaller
operand selection used when they were captured.

The [external guide](EXTERNAL.md) gives prerequisites, individual commands, comparison policies,
and instructions for rerendering saved data. Its [SoftPosit discussion](EXTERNAL.md#softposit)
explains why differences remain in the results. Most [ecosystem rows](results/main/ecosystem)
run an upstream project's own checks; those passes do not establish agreement with FloatLib.
For timing experiments, use the [benchmark guide](../benchmarks/README.md).

## Optional Arb

The Arb adapter calls Python's `python-flint` bindings to FLINT/Arb. Lean checks the JSON schema
and reconstructs rational bounds; it does not verify Arb's computation. Public library proofs
do not depend on this.

```bash
python3 -m pip install python-flint   # in your Python environment
source tests/lib/lake.sh
floatlib_test_lake exe check arb
python3 tests/FloatLibTests/Arb/arb_oracle.py --func exp --lo=-1 --hi=1 --prec-bits 200 --digits 50
```

The Lean entry points are `FloatLibTests.Arb.run`, `runExpr`, `runMLP`, and
`ModelTranscendentals`. The docstring in `arb_oracle.py` describes the JSON messages.
`FLOATLIB_ARB_KEEP_TMP` keeps successful request files, and `FLOATLIB_ARB_PY` selects
the Python interpreter for the Lean adapter.

## Trust surface

| Mechanism | Where | Audit |
| --- | --- | --- |
| `NativeFPU.Unchecked` host arithmetic | `Configured/NativeFPU/Unchecked.lean` | `floatlib_test_lake exe check native`; checks agreement with the software path |
| Posit `toDyadic?` `@[implemented_by]` | `Posit/Model/Decode.lean` | `toDyadicImpl?_eq_toDyadic?` |
| `native_decide` in conformance | `FloatLibTests/Conformance/**` | exact counts in `checks/trust-surface.sh`; none in library semantics |
| `unsafe` expression evaluation in the inspection command | `ExecFloat/Info/Inspection.lean` | one use in `readString`, counted by `checks/trust-surface.sh` |
| `unsafe` site-export entry point | `site/tooling/ExportNodes.lean` | one use in `main`, counted by `checks/trust-surface.sh` |

We use `native_decide` when native evaluation makes a useful finite check faster. That saves
time while checking the proposition during the build; it does not speed up FloatLib's arithmetic
at runtime. The tradeoff is trusting the compiler and evaluator for that check, so we track these
uses separately from the library's general proofs. A useful native check belongs here; a one-off
experiment still belongs in scratch.

The inspection command evaluates a closed string in `MetaM` to display a chosen execution plan;
the site exporter loads a Lean environment with initializers enabled. These uses belong to
tooling. Aesop's `unsafe` rule annotations only control proof search and are not uses of Lean's
unchecked execution.

`checks/trust-surface.sh` inventories native proof evaluation, compiler replacements, unchecked
imports, and `unsafe` uses across library, test, benchmark, and site Lean sources.
[Axioms.lean](FloatLibTests/Conformance/Trust/Axioms.lean) checks every loaded production declaration
from the public root and optional configured transcendental imports, including available private
declarations and `@[csimp]` lemmas. The quotient compiler certificate is imported explicitly
because its clients use a private import. Other unimported modules are outside that audit. It also
checks the posit decoder's actual replacement against the two endpoints of its general equality theorem;
collecting axioms alone cannot establish that relationship.
[RootImports.lean](FloatLibTests/Conformance/Trust/RootImports.lean) checks the root's complete
imported module set, rejecting the unchecked host-FPU module and both elementary-function
barrels. It compiles separately from tests that explicitly opt into those modules and runs as
part of the normal conformance build.

For source-only checks during a coordinated module rename:

```bash
bash tests/checks/architecture.sh
bash tests/checks/trust-surface.sh --source-only
bash tests/checks/version-pins.sh --source-only
```

The source-only flags skip Lean execution; the full verifier still compiles the axiom audit and
checks the active toolchain. Source discovery includes untracked renamed files and skips deleted
paths, `.lake`, and saved results.

## Layout

| Path | Contents |
| --- | --- |
| `Check.lean` / `Oracle.lean` | Native driver; external-tool commands |
| `FloatLibTests/Conformance/` | Symbolic API integration, automation, trust, and selected finite checks |
| `FloatLibTests/Regression/` | Executable arithmetic and backends |
| `FloatLibTests/Fixtures/` | Shared encodings (also used by benchmarks) |
| `FloatLibTests/Oracle/`, `Arb/`, `External/` | Vector emitters, Arb, process support |
| `verify.sh`, `checks/`, `oracles/` | Full verification and independent checkers |
| `lib/` | Source discovery and Lake helper shared with benchmarks and the website |

The `floatlibTests` Lake package requires `floatlib` from `..` and exports the `FloatLibTests`
modules, so `import FloatLib` does not load tests. It inherits the repository's `lean-toolchain`.
Scripts use `floatlib_test_lake` from `tests/lib/lake.sh` so build products stay outside the
checkout, under `FLOATLIB_BUILD_DIR`.
