# Tests

We prove general properties in Lean, compare our compiled arithmetic with independent
implementations, and check which axioms and execution mechanisms the proofs depend on. Those
comparisons can catch a misreading of a standard as well as a runtime bug. Run these commands from
the repository root, after the [project setup](../README.md#installation).

```bash
bash tests/verify.sh
```

That builds the library, checks conformance proofs, runs native regressions, and checks lint,
imports, API docs, and the axioms of library declarations loaded by the trust audit, compiler
equality proofs and the public root's dependencies included. Arb runs if `python-flint` is
installed, and otherwise the verifier reports it as skipped. One failed check fails the whole
command.

CI runs these checks first, then MPFR smoke comparisons, benchmark command checks, and the guide's
Lean examples.

To also replay the compiled FloatLib declarations through Lean's kernel:

```bash
FLOATLIB_RUN_INDEPENDENT_CHECKER=1 bash tests/verify.sh
```

This runs `leanchecker`, which loads the stored declarations and checks them again with the same
kernel used during compilation. It's opt-in because loading the dependency environments can take
hundreds of GiB of memory.

For just the proofs and native regressions, or to choose a native suite:

```bash
source tests/lib/lake.sh
floatlib_test_lake test
floatlib_test_lake exe check --help
```

The helper shares the scripts' build lock and keeps compiler output outside the checkout. To
choose a local build directory, set `FLOATLIB_BUILD_DIR` before you source it. `TMPDIR` controls
where temporary work goes. Every command below also starts at the repository root.

Native suites cover models, public instances, rounding policies, integer kernels, tiny formats,
transcendental kernels (behind the named `Configured.Transcendentals` import), exact
rational-power comparisons and the posit operations that use them, host-FPU behavior, and a smoke
run of the format-comparison example. `powers` prints the time of each of its groups, and
`reduction`, which `all` leaves out, checks sine and cosine arguments whose reduction computes the
`2^20`- and `2^21`-bit levels of `2 / pi` (several seconds of first-use work) and prints its time.
For the example, the check passes as long as the demonstration returns without throwing. It
doesn't compare the printed values with expected results.

We report failures by named check through `ReportSection.ofRows` in
[Accounting.lean](FloatLibTests/Accounting.lean).

## Checking a change

For an ad-hoc calculation or proof check, put a scratch file on local disk, outside the tracked
source tree. Once its imports are built, check it with:

```bash
source tests/lib/lake.sh
floatlib_lake env lean /path/to/local-scratch/Check.lean
```

Scratch files are for one-off experiments, and we delete them once the question is settled. What
lives in `tests/` is maintained: symbolic API integration, runtime regressions, reusable
comparison adapters, and trust checks. [CONTRIBUTING.md](../CONTRIBUTING.md) explains the build
and proof workflow.

## Results and external comparisons

You can check the saved results or run new comparisons:

| Command | What it does |
| --- | --- |
| `bash tests/oracles/verify-main-result.sh` | Check saved artifacts and captured sources, regenerate figures, and compare the captured source inputs with this checkout |
| `bash tests/oracles/check.sh --profile quick` | Build current source and run a bounded set of independent comparisons and native checks |
| `bash tests/oracles/check.sh --profile release` | Build current source and run the full set of comparisons supported by the runner |

The verifier checks the files and source information recorded with each result, regenerates the
figures, and compares the recorded library, build, test, and benchmark inputs with your checkout.
Documentation changes don't affect that comparison. The `quick` and `release` profiles, by
contrast, run the outside tools on the current source and environment. Their runner inherits CPU
affinity, caps its default worker count at the available CPUs or eight, and writes to a new
directory under `TMPDIR` (normally `/tmp`). To pick a different new directory, use `--results`.

Both profiles check binary16 addition and multiplication against MPFR with 16 left operands:
signed zeros, subnormals, the smallest normal, ordinary normals, the largest finite magnitudes,
infinities, and quiet and signaling NaNs. Pairing each with all 65,536 right encodings gives
2,097,152 comparisons across the two operations. Saved results keep the smaller operand selection
they were captured with.

The [external guide](EXTERNAL.md) has the prerequisites, individual commands, comparison policies,
and instructions for rerendering saved data, and its [SoftPosit discussion](EXTERNAL.md#softposit)
explains why the results still contain differences. Most [ecosystem rows](results/main/ecosystem)
run an upstream project's own checks, so a pass there doesn't show agreement with FloatLib. For
timing experiments, use the [benchmark guide](../benchmarks/README.md).

## Exhaustive fused multiply-add

The native `core` suite already checks every addition, subtraction, multiplication, and division
of the eight-bit format `ieee 4 3` in all six rounding directions against an exact rational
reference, along with every square root and 4,096 fused multiply-add triples per direction. Below
is an opt-in campaign that goes further and checks every fused multiply-add triple of `ieee 4 3`
and E5M2 against the same reference, 201,326,592 cases in all. Each shard takes the first operands
congruent to its index:

```bash
for shard in 0 1 2 3 4 5 6 7; do
  bash tests/oracles/rounding-fma-exhaustive.sh "$shard" 8 &
done
wait
```

## Optional Arb

The Arb adapter calls Python's `python-flint` bindings to FLINT/Arb. Lean checks the JSON schema
and reconstructs rational bounds, but it doesn't verify Arb's computation, and none of the public
library proofs depend on it.

```bash
python3 -m pip install python-flint   # in your Python environment
source tests/lib/lake.sh
floatlib_test_lake exe check arb
python3 tests/FloatLibTests/Arb/arb_oracle.py --func exp --lo=-1 --hi=1 --prec-bits 200 --digits 50
```

On the Lean side, the entry points are `FloatLibTests.Arb.run`, `runExpr`, `runMLP`, and
`ModelTranscendentals`. For the JSON messages, see the docstring in `arb_oracle.py`. Set
`FLOATLIB_ARB_KEEP_TMP` to keep successful request files, and `FLOATLIB_ARB_PY` to choose the
Python interpreter for the Lean adapter.

## Trust surface

| Mechanism | Where | Audit |
| --- | --- | --- |
| `NativeFPU.Unchecked` host arithmetic | `Configured/NativeFPU/Unchecked.lean` | `floatlib_test_lake exe check native`; checks agreement with the software path |
| Posit `toDyadic?` `@[implemented_by]` | `Posit/Model/Decode.lean` | `Internal.toDyadic?_eq` |
| `native_decide` in conformance | `FloatLibTests/Conformance/**` | exact counts in `checks/trust-surface.sh`; none in library semantics |
| `unsafe` expression evaluation in the inspection command | `ExecFloat/Info/Inspection.lean` | one use in `readString`, counted by `checks/trust-surface.sh` |
| `unsafe` site-export entry point | `site/tooling/ExportNodes.lean` | one use in `main`, counted by `checks/trust-surface.sh` |

We use `native_decide` when native evaluation makes a useful finite check faster. It saves time
while the build checks the proposition, and it does nothing for FloatLib's arithmetic at runtime.
In exchange we trust the compiler and evaluator for that check, which is why we track these uses
apart from the library's general proofs. So a useful native check belongs here, and a one-off
experiment still goes in scratch.

The inspection command evaluates a closed string in `MetaM` to display a chosen execution plan,
and the site exporter loads a Lean environment with initializers enabled. Both are tooling.
Aesop's `unsafe` rule annotations are a different thing: they only steer proof search and never
use Lean's unchecked execution.

`checks/trust-surface.sh` inventories native proof evaluation, compiler replacements, unchecked
imports, and `unsafe` uses across library, test, benchmark, and site Lean sources.
[Axioms.lean](FloatLibTests/Conformance/Trust/Axioms.lean) checks every loaded production
declaration from the public root and the optional configured transcendental imports, including
available private declarations and `@[csimp]` lemmas. We add an import for the quotient compiler
certificate because its clients use a private import, and other modules that aren't imported fall
outside the audit. Axioms.lean also checks the posit decoder's actual replacement against the two
endpoints of its general equality theorem, since collecting axioms alone can't establish that
relationship. [RootImports.lean](FloatLibTests/Conformance/Trust/RootImports.lean) checks the
root's complete imported module set and rejects the unchecked host-FPU module and both
elementary-function barrels. It compiles apart from the tests that opt into those modules, and it
runs as part of the normal conformance build.

For source-only checks during a coordinated module rename:

```bash
bash tests/checks/architecture.sh
bash tests/checks/trust-surface.sh --source-only
bash tests/checks/version-pins.sh --source-only
```

The source-only flags skip Lean execution, but the full verifier still compiles the axiom audit
and checks the active toolchain. Source discovery picks up untracked renamed files and skips
deleted paths, `.lake`, and saved results.

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
modules, so `import FloatLib` never loads tests. It inherits the repository's `lean-toolchain`.
Scripts call `floatlib_test_lake` from `tests/lib/lake.sh`, which keeps build products outside the
checkout under `FLOATLIB_BUILD_DIR`.
