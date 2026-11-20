# Tests

We prove general properties in Lean, compare our compiled arithmetic with independent
implementations, and audit which axioms and execution mechanisms the proofs depend on. Those
comparisons earn their place next to the proofs, because they can catch a misreading of a
standard as well as a runtime bug. Run these commands from the repository root, after the
[project setup](../README.md#installation).

```bash
bash tests/verify.sh
```

That builds the library and its conformance proofs, runs the native regressions, and checks
lint, imports, API docs, and the axioms of the library declarations loaded by the trust audit,
compiler equality proofs and the public root's dependencies included. If `python-flint` is
installed, Arb runs too, and otherwise the verifier reports it as skipped. A single failure
fails the whole command.

CI runs these checks first, then MPFR smoke comparisons, benchmark command checks, and the guide's
Lean examples.

To also replay the compiled FloatLib declarations through Lean's kernel:

```bash
FLOATLIB_RUN_INDEPENDENT_CHECKER=1 bash tests/verify.sh
```

This runs `checks/kernel-replay.sh`, which loads the stored declarations of each library module
and checks them again with the same kernel used during compilation, one module per process. It
also fails if one of them is an axiom. It's
opt-in because the whole library takes about an hour of processor time. Set
`KERNEL_REPLAY_JOBS` to the number of processes to run at a time (default 4, up to 6 GB each),
or name module prefixes to replay a part: `bash tests/checks/kernel-replay.sh FloatLib.Numerics.Kernel`.

For just the proofs and native regressions, or to choose a native suite:

```bash
source tests/lib/lake.sh
floatlib_test_lake test
floatlib_test_lake exe check --help
```

The helper shares the scripts' build lock and keeps compiler output outside the checkout. If
you want a particular local build directory, set `FLOATLIB_BUILD_DIR` before you source it, and
`TMPDIR` controls where temporary work goes. Every command below also starts at the repository
root.

The conformance modules are checked when they compile. Besides the format and operation
contracts they cover the kernel path and its lane programs (`Tactic/FloatDecide`,
`Tactic/LaneDecide`, `Tactic/LaneTable`, `Conformance/Formats/KernelPaths`, `Conformance/Numerics/KernelExact`), the generated
`roundoff` theorems (`Tactic/Roundoff/Backward`, `Tactic/Roundoff/Closed`, `Tactic/Roundoff/MixedPrecision`,
`Tactic/Roundoff/Block`, `Tactic/Roundoff/Shape`), the backend tags and what they refuse
(`Tactic/KernelOptimize`, `Tactic/CompilerOptimize`), the block formats
(`Conformance/Formats/BlockTheory`, with worked instances on explicit data in `BlockExamples`),
stochastic rounding (`Numerics/Stochastic*`), the constraint route of `interval`
(`Tactic/Interval/Constraints`: goal shapes, zero margins, sets without a box, hints,
failure messages, the trace of the route, and certificates written by hand) and the bounds
that its enclosure route gives `π` without a hypothesis (`Tactic/Interval/Constants`).

Native suites cover models, public instances, rounding policies, integer kernels, tiny formats,
transcendental kernels (behind the named `Configured.Transcendentals` import), exact
rational-power comparisons and the posit operations that use them, host-FPU behavior, and a smoke
run of the format-comparison example. `powers` prints the time of each of its groups.
`reduction`, which `all` leaves out, tests sine and cosine arguments whose reduction computes the
`2^20`- and `2^21`-bit levels of `2 / pi` (several seconds of first-use work), and it prints its
time too. For the example, the smoke run passes as long as the demonstration returns without
throwing, and it doesn't compare the printed values with expected results.

We report failures by named check through `ReportSection.ofRows` in
[Accounting.lean](FloatLibTests/Accounting.lean).

## Checking a change

For an ad-hoc calculation or proof, put a scratch file on local disk, outside the tracked
source tree. Once its imports are built, run Lean on it with:

```bash
source tests/lib/lake.sh
floatlib_lake env lean /path/to/local-scratch/Check.lean
```

Scratch files are for one-off experiments, and we delete them once the question is settled. What
lives in `tests/` is maintained: symbolic API integration, runtime regressions, reusable
comparison adapters, and trust checks. [CONTRIBUTING.md](../CONTRIBUTING.md) explains the build
and proof workflow.

## Results and external comparisons

To run the comparisons:

| Command | What it does |
| --- | --- |
| `bash tests/oracles/check.sh --profile quick` | Build current source and run a bounded set of independent comparisons and native checks |
| `bash tests/oracles/check.sh --profile release` | Build current source and run the full set of comparisons supported by the runner |

The verifier validates the files and source information recorded with each result, regenerates
the figures, and compares the recorded library, build, test, and benchmark inputs with your
checkout. Documentation changes don't affect that comparison. By contrast, the `quick` and
`release` profiles run the outside tools on the current source and environment. Their
runner inherits CPU affinity, caps its default worker count at the available CPUs or eight, and
writes to a new directory under `TMPDIR` (normally `/tmp`). To pick a different new directory,
use `--results`.

Both profiles compare binary16 addition and multiplication with MPFR on 16 left operands:
signed zeros, subnormals, the smallest normal, ordinary normals, the largest finite magnitudes,
infinities, and quiet and signaling NaNs. Pairing each with all 65,536 right encodings gives
2,097,152 comparisons across the two operations.

The [external guide](EXTERNAL.md) has the prerequisites, individual commands and comparison
policies, and its [SoftPosit discussion](EXTERNAL.md#softposit) explains why the results contain
some differences. For timing experiments, use the [benchmark guide](../benchmarks/README.md).

## Exhaustive fused multiply-add

The native `core` suite already checks every addition, subtraction, multiplication, and division
of the eight-bit format `ieee 4 3` in all six rounding directions against an exact rational
reference, along with every square root and 4,096 fused multiply-add triples per direction. Below
is an opt-in campaign that goes further and tests every fused multiply-add triple of `ieee 4 3` and
E5M2 against the same reference. Two formats, six directions, and every triple of eight-bit
encodings come to 201,326,592 cases. Each shard takes the first operands congruent to its index:

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

The complete list, with the reason each item is trusted, is in [TRUST.md](../TRUST.md). The
table below says where each mechanism is and what audits it.

| Mechanism | Where | Audit |
| --- | --- | --- |
| `NativeFPU.Unchecked` host arithmetic | `Configured/NativeFPU/Unchecked.lean` | `floatlib_test_lake exe check native`; checks agreement with the software path |
| Posit `toDyadic?` `@[implemented_by]` | `Posit/Model/Decode.lean` | `Internal.toDyadic?_eq`, registered with `@[replacement_proof]`; `@[compiler_optimize]` refuses a backend that reaches any other replacement (`Util/Provenance.lean`) |
| Lean's generated `T.ctorIdx._impl` tag read | every inductive type with several constructors, since Lean 4.36 | names, type and both bodies checked by `Provenance.isGeneratedCtorIdx` and counted by `Trust/Axioms.lean`; no equality theorem |
| Host binary32 arithmetic of the native 16-bit carriers | `IEEE754/Native/Half.lean` | `floatlib_test_lake exe check native`; compares the arithmetic, square root, negation and comparisons with the software models. Narrowing, widening and NaN normalization are proved |
| `native_decide` in conformance | `FloatLibTests/Conformance/**` | exact counts in `checks/trust-surface.sh`; none in library semantics |
| `unsafe` expression evaluation in the inspection command | `FloatLib/Tactic/FloatInfo/Inspection.lean` | one use in `readString`, counted by `checks/trust-surface.sh` |
| `unsafe` site-export entry point | `site/tooling/ExportNodes.lean` | one use in `main`, counted by `checks/trust-surface.sh` |
| `unsafe` evaluation of a registered extension | `FloatLib/Tactic/Roundoff/Extension.lean` | one `evalConstCheck` use, counted by `checks/trust-surface.sh` |

We use `native_decide` when native evaluation makes a useful finite check faster. It saves time
while the build proves the proposition and does nothing for FloatLib's arithmetic at runtime. In
exchange we trust the compiler and evaluator for that check, which is why we track these uses
apart from the library's general proofs. A useful native check belongs here, and a one-off
experiment goes in scratch like any other.

The inspection command evaluates a closed string in `MetaM` to display a chosen execution plan,
and the site exporter loads a Lean environment with initializers enabled. Both are tooling. The
`roundoff` analysis evaluates each `@[roundoff_extension]` definition to read the extension it
registers. That value only configures the analysis: every theorem it produces is still checked by
the kernel.
Aesop's `unsafe` rule annotations are a different thing: they only steer proof search and never
use Lean's unchecked execution.

`checks/trust-surface.sh` inventories native proof evaluation, compiler replacements, unchecked
imports, and `unsafe` uses across library, test, benchmark, and site Lean sources.
[Axioms.lean](FloatLibTests/Conformance/Trust/Axioms.lean) audits every production declaration
its environment holds, including private declarations and `@[csimp]` lemmas. Its imports reach
every module of the library except the unchecked host-FPU module, and `checks/trust-surface.sh`
follows them through the sources and fails when a library module is missing. A declaration the
audit doesn't hold is checked through the ones that use it. We add `import all` for the compiler
certificates, the backend proof modules that every client imports privately and the packed FP8
tables, so their declarations are checked directly. Declarations neither held nor used, mostly
compiler-generated auxiliaries, fall outside the audit. For those, `checks/trust-surface.sh`
rejects `sorry` and `axiom` in every source, and it loads every level of every library module
and fails if the kernel holds one of the library's constants as an axiom. Lean keeps a declaration
that its kernel rejects as an axiom, so this is how a rejected proof that a command left behind
gets caught. Axioms.lean also compares the posit decoder's
actual replacement with the two endpoints of its general equality theorem, since collecting
axioms alone can't establish that relationship.
[RootImports.lean](FloatLibTests/Conformance/Trust/RootImports.lean) inspects the root's complete
imported module set and rejects the unchecked host-FPU module and both elementary-function
barrels. It compiles apart from the tests that opt into those modules, and it
runs as part of the normal conformance build.

For source-only checks during a coordinated module rename:

```bash
bash tests/checks/architecture.sh
bash tests/checks/trust-surface.sh --source-only
bash tests/checks/version-pins.sh --source-only
```

The source-only flags skip Lean execution, while the full verifier compiles the axiom audit and
checks the active toolchain as usual. Source discovery picks up untracked renamed files and skips
deleted paths, `.lake`, and saved results.

`checks/source-screen.py` counts duplicate definitions, duplicate theorems, theorems with one
statement under two names, and library declarations that nothing uses. It reads the source text,
so it finds candidates and proves nothing about them; a name in the list of an axiom audit and a
`#check` line are not uses. `checks/source-screen.txt` holds its output for this release, and
the verifier fails when a count exceeds the recorded limit:

```bash
python3 tests/checks/source-screen.py --list            # the groups and the candidates
python3 tests/checks/source-screen.py --revision main   # the counts of another revision
```

`checks/doc-links.py` checks the links of every Markdown file: guide links and their anchors,
relative files, links into this repository on GitHub, and the citations and declaration links of
the guide chapters. It needs no build, so the verifier runs it before anything is compiled:

```bash
python3 tests/checks/doc-links.py
```

`checks/linters.sh` builds the library and the tests with `--wfail`, so that a linter warning
fails the check, and then runs `lake lint` on every lint root. The linters are the
`linterOptions` of `lakefile.lean` and of `tests/lakefile.lean`. A module that loads no package
(`checks/core-only.py` prints them: the kernel number types and the packed rows) does not load
Mathlib's source linters, so the check elaborates each of these once more with `Mathlib.Init`
imported:

```bash
bash tests/checks/linters.sh
```

The library and its tests are modules, and a module doesn't load the bodies of the private
declarations of its imports. A file that doesn't start with `module` does, so a tactic can
behave differently in one. `checks/plain-file.sh` elaborates `checks/PlainFile.lean` as such a
file and fails on any message. It holds `roundoff` theorems whose statements have to be the
ones a module gets:

```bash
bash tests/checks/plain-file.sh
```

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
