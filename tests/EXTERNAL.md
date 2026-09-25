# External validation

We compare FloatLib with independent implementations because a proof can agree with our
specification even when we have misread the standard. These checks also exercise the compiled
code, input decoders, and foreign-library boundary. A match is evidence over the stated inputs
and policies; the proofs carry the general statements.

All commands below start at the repository root. Follow the [project setup](../README.md#installation)
first when running current source.

## Check or redraw the results

The [direct comparisons](results/main/release/external) contain results, raw logs, and the
SoftPosit analysis. The [ecosystem results](results/main/ecosystem) mostly record upstream
projects' own checks. Their [manifests](results/main/MANIFEST.tsv) and
[source records](results/main/provenance/SNAPSHOT.txt) identify the files, revisions, and
environment behind the measurements.

To check those saved files:

```bash
bash tests/oracles/verify-main-result.sh
```

The verifier checks hashes, provenance, status and count consistency, and the saved SQLite
databases. It redraws the summaries and figures in temporary space and compares them byte for
byte. It needs Git, Python, and Matplotlib; it does not rebuild FloatLib or rerun external tools.
Benchmark evidence has a [separate verifier](../benchmarks/README.md).

To redraw just the direct-comparison summary and figures into a directory of your choice:

```bash
python3 tests/oracles/render_release_result.py \
  tests/results/main/release/external/summary.tsv \
  /path/to/local-output/external-figures
```

This reads saved data and does not validate or regenerate numerical answers. Use an output
directory outside `tests/results/`. `render_ecosystem_result.py` accepts the same two arguments
for the ecosystem summary. New figures use FloatLib; the verifier passes `--historical-branding`
to match the original titles and SVG identifiers. We leave the old names and hashes in the
recorded files unchanged.

## Run comparisons on current source

The `quick` profile runs a bounded set of comparisons:

```bash
bash tests/oracles/check.sh --profile quick
```

For all comparisons supported by the runner, choose a new output directory:

```bash
bash tests/oracles/check.sh --profile release --results /path/to/new-external-result
```

The runner builds the current checkout and fetches the pinned upstream sources it needs.
It inherits the process's CPU affinity and defaults to at most eight workers, capped at the
available CPUs. `--workers` can reduce or increase parallelism within that allocation;
`--cpu-set` can restrict it further. Suites run sequentially, with parallelism inside each
suite. With no `--results`, output goes to a fresh directory under `TMPDIR` (normally `/tmp`);
an explicitly chosen path must not already exist. `FLOATLIB_BUILD_DIR` chooses the local
compiler-output directory.

These are new runs. Current source, adapter coverage, tool versions, and machine settings can
differ from the saved results. Recreating an old environment requires its linked source and
environment records; running today's script is not an exact replay of that snapshot.

The runners use Linux command-line tools, Git, Make, and C/C++ compilers; TestFloat and SoftPosit
currently select their upstream Linux x86-64 build directories. MPFR checks need its development
files (version 4.1.0 or newer) and `pkg-config`. Python needs `matplotlib`, `onnx`, `numpy`, and
`python-flint`; the release profile also needs the `z3` executable. Arb is required by these
profiles, though it is optional in `tests/verify.sh`.

The `release` profile runs the following suites. `quick` runs `01`–`07`, with TestFloat's smoke
subset and P3109 tables through 8 bits.

| Suite | Evidence class | Scope |
| --- | --- | --- |
| `00-adapter-unit-tests` | Adapter integrity | Corruption, schema, stream, and build checks for the external adapters |
| `01-testfloat` | Differential conformance | Complete maintained TestFloat level-1 overlap |
| `02-format-standards` | Published-table conformance | ONNX low-bit formats and published P3109 descriptors through 16 bits |
| `03-mpfr-primitives` | Numerical reference validation | Maintained finite primitive corpus and rounding directions |
| `04-mpfr-reductions` | Numerical reference validation | Exact finite sums and dot products across maintained formats |
| `05-arb` | Numerical reference validation | Maintained interval and transcendental corpus |
| `06-native-fpu` | Boundary validation | Public binary32/64 dispatch and explicit unchecked host-FPU operations |
| `07-binary16-mpfr-rows` | Differential conformance | Addition and multiplication: 16 representative left operands, each paired with every binary16 right encoding |
| `08-testfloat-level2-smoke` | Differential conformance | Three selected functions, each with its complete TestFloat level-2 generator |
| `09-ibm-fpgen` | Differential conformance | Pinned IBM FPgen vectors in the supported overlap |
| `10-smt-qf-fp` | Differential conformance | Bounded ground QF_FP expressions through Z3 |
| `11-softposit` | Differential conformance with adjudication | Exhaustive small-posits and deterministic sampled wider posits |
| `12-transcendentals` | Observational comparison | FloatLib, MPFR, CORE-MATH, OpenLibm, and supported RLIBM functions |

Each suite writes its scope and outcome beside its logs. A nonzero comparison makes the runner
fail, including known differences in the pinned SoftPosit implementation. We explain
those differences in the [SoftPosit analysis below](#softposit).

## Run an individual comparison

These entry points isolate a comparison. The examples use one worker and inherit affinity;
the top-level runner above chooses parallelism automatically.

```bash
# Berkeley TestFloat
bash tests/oracles/testfloat.sh \
  --profile full --level 1 --seed 1 --workers 1 --cpu-set none
bash tests/oracles/testfloat.sh \
  --profile smoke --level 2 --seed 1 --workers 1 --cpu-set none

# Published low-bit and P3109 tables
FORMAT_STANDARDS_WORKERS=1 FORMAT_STANDARDS_CPU_SET=none \
  bash tests/oracles/format-standards.sh

# MPFR, Arb, and the native boundary
bash tests/oracles/mpfr.sh primitives
bash tests/oracles/mpfr.sh reductions
# Fix the left operand to 0x3555 (near 1/3), with every right encoding.
bash tests/oracles/binary16-exhaustive.sh add 13653 65536
source tests/lib/lake.sh
floatlib_test_lake exe check arb
floatlib_test_lake exe check native

# Other independent references
bash tests/oracles/ibm_fpgen.sh
bash tests/oracles/smt_fp.sh
bash tests/oracles/transcendental_compare.sh --jobs 1
```

The binary16 command checks one input-pair shard, not every binary16 pair. CI checks four
left operands for both addition and multiplication: the smallest positive subnormal (`0x0001`),
a value near 1/3 (`0x3555`), the next value below -1 (`0xbc01`), and the largest finite positive
value (`0x7bff`). Each is paired with every right encoding, for 524,288 pairs. This exercises
finite arithmetic as well as exceptional operands. The `quick` and `release` profiles use
the larger 16-row selection listed above.

The transcendental command uses MPFR; its `--help` lists options for adding CORE-MATH,
OpenLibm, and RLIBM.

For one SoftPosit format and operation, supply a clean checkout at the revision pinned in
[`softposit.sh`](oracles/softposit.sh):

```bash
bash tests/oracles/softposit.sh --softposit-dir /path/to/SoftPosit \
  --bits 6 --op add --exhaustive
```

The script checks the revision and builds from a Git archive in temporary space. The `release`
profile fetches that checkout and runs the full matrix. `floatlib_test_lake exe oracle --help`
lists the Lean executable's stream protocols after sourcing `tests/lib/lake.sh`.

## What we compare

| Comparison | Independent source |
| --- | --- |
| IEEE arithmetic, conversions, comparisons, and flags | [Berkeley TestFloat](https://github.com/ucb-bar/berkeley-testfloat-3) with [Berkeley SoftFloat](https://www.jhauser.us/arithmetic/SoftFloat-3/doc/SoftFloat.html) |
| Low-bit interchange values | [ONNX float8 specification](https://onnx.ai/onnx/technical/float8.html) |
| Configurable low-precision values | [IEEE P3109 public tables](https://github.com/P3109/Public) |
| P3109 arithmetic and timing in three small formats | [FLoPS executable artifact](../benchmarks/external/flops/README.md) |
| FP16, BF16, E4M3FN, and E5M2 scalar conversions | [TensorLib conversion comparison](../benchmarks/external/tensorlib/README.md) |
| Binary arithmetic and rounding | [GNU MPFR](https://www.mpfr.org/mpfr-current/mpfr.html) |
| Ball and transcendental arithmetic | [Arb](https://arblib.org/) through [python-flint](https://python-flint.readthedocs.io/) |
| Additional IEEE vectors | [IBM FPgen test suite](https://github.com/sergev/ieee754-test-suite) |
| SMT floating-point semantics | [SMT-LIB QF_FP](https://smt-lib.org/logics-all.shtml#QF_FP) through [Z3](https://github.com/Z3Prover/z3) |
| Independent posit execution | [SoftPosit](https://gitlab.com/cerlane/SoftPosit) |
| Transcendental observations | [CORE-MATH](https://gitlab.inria.fr/core-math/core-math), [OpenLibm](https://github.com/JuliaMath/openlibm), and [RLIBM](https://github.com/rutgers-apl/rlibm) |

### TestFloat details

The maintained overlap covers binary16, binary32, binary64, and binary128 arithmetic;
round-to-integral; quiet and signaling comparisons; cross-format binary conversions; and the BF16
conversions exposed by the pinned TestFloat interface. It checks nearest-even, toward zero, toward
positive infinity, and toward negative infinity, together with invalid, divide-by-zero, overflow,
underflow, and inexact flags.

Non-NaN outputs are compared bit-for-bit. NaNs are compared by class while signaling and invalid
behavior are still checked. We do not claim strict payload-selection agreement.

The selected level-2 subset is deliberately small. Each selected function runs its
complete level-2 generator, but the three rows are not a complete level-2 matrix. Very large
level-2 combinations require `--allow-huge-level2`; schedule those by operation and format and
save each summary.

This adapter excludes binary80's explicit-integer-bit encoding, BF16 arithmetic not exposed by
the pinned interface, floating-point/integer conversions without a shared invalid-result policy,
nearest-away, round-to-odd, tininess-before-rounding, and universal NaN payload identity.

### ONNX and P3109 details

The representation adapter compares decoded values with the published ONNX and P3109 tables.
It checks FloatLib's exact dyadic decoding against the public ONNX decoders and pinned P3109
hexadecimal value tables; the P3109 emitter uses the format descriptor.

### P3109 arithmetic with FLoPS

The separate [FLoPS comparison](../benchmarks/external/flops/README.md) checks addition,
multiplication, division, and FMA for `Binary4p2sf`, `Binary8p4se`, and `Binary8p3se`,
with nearest-even rounding and no saturation. All 529,152 arithmetic cases and the
192 exact timing fixtures agree bit for bit. The same runner then times both compiled
libraries on identical result-dependent inputs. Its instructions, adapters, and individual
measurements are linked there; this focused experiment is separate from the `release` profile.

### Scalar conversions with TensorLib

The [TensorLib comparison](../benchmarks/external/tensorlib/README.md) enumerates every
FP16, BF16, E4M3FN, and E5M2 encoding for conversion to Float32 and tests rounding boundaries
and selected Float32 inputs in the other direction. Both libraries pass 952,612 numerical
checks against an independent adjacent-value reference. The 2,964 differing result words
are E4M3FN NaN signs on negative overflow or negative infinity. NaN payloads, signaling
behavior, and exception flags are outside this comparison. Separate timings use 128 matching
normal finite fixtures.
The linked instructions reproduce this focused experiment without running the release suite.

### MPFR and underflow

MPFR is the finite arithmetic and rounding oracle. It is not our IEEE NaN-precedence oracle:
MPFR has one NaN class and its fused-operation behavior does not encode every IEEE payload and
signaling rule. The adapter therefore decodes signaling NaNs and invalid arithmetic causes from
the input encodings; TestFloat remains the independent status oracle over its supported overlap.

The binary operations in these checks detect tininess after rounding and report underflow only
for a tiny, inexact result.
The TestFloat adapter selects `-tininessafter`. The MPFR adapters normalize the result to the
target exponent range and report underflow only together with inexact, matching the policy under
test rather than treating every exact subnormal as underflow.

### Native FPU boundary

The native suite compares the public binary32/64 dispatch results with proved software kernels and
separately samples the explicit `NativeFPU.Unchecked` operations. Agreement is valuable regression
evidence for the current compiler, ABI, and machine. It is not the missing theorem that the host
replacement implements the software model for every input.

### SoftPosit

The [saved SoftPosit results](results/main/release/external/11-softposit) include disagreements.
We kept the failed rows and checked every disputed answer against FloatLib's exact rational
specification. The [analysis](results/main/release/external/11-softposit/ADJUDICATION.md) records
the operands and neighboring encodings: the 32-bit cases expose inconsistent pX2 endpoint
handling, and the 16-bit FMA cases lose sticky information that should decide the rounding.
FloatLib's executable agrees with its exact specification on those inputs.

That supports the recorded `external-limitation` classification; it does not make the raw
comparison pass. The [website's validation chapter](../site/content/chapters/19-external-validation.md)
also discusses later checks at more widths. Its broader counts should not be substituted into
the older result manifest.

### SMT and transcendentals

SMT-LIB floating-point values expose one abstract NaN, so QF_FP comparisons check NaN class rather
than payload identity. The adapter records exact bit agreement where the theory exposes
it and class agreement for NaNs.

The saved transcendental row is `observational-complete`. MPFR supplies high-precision reference values,
while CORE-MATH, OpenLibm, and RLIBM expose different supported functions and rounding contracts.
We record every available result and difference. These observations concern the approximate
binary kernels, separately from the proved posit functions described on the website.

## Reading the ecosystem results

We also built tools for floating-point testing, rewriting, error analysis, and reproducible
arithmetic. Most rows below run an upstream project's own checks. A pass means that project
worked in the recorded environment; only a direct comparison establishes agreement with FloatLib.

| Family | What was checked |
| --- | --- |
| [FPBench](https://fpbench.org/) | Upstream workflow and standalone diagnostics; no direct FloatLib comparison |
| [Daisy](https://github.com/malyzajko/daisy) and [FPTaylor](https://github.com/soarlab/FPTaylor) | Upstream analysis and regression suites; no direct FloatLib comparison |
| [Herbie](https://herbie.uwplse.org/) | Upstream tests and workload observations; no direct FloatLib comparison |
| OpenLibm and RLIBM | Upstream gates plus a separate direct transcendental observation where adapters overlap |
| CORE-MATH | All 169 available binary16, bfloat16, binary32, and binary64 function checks; 166 passed and three could not link against the recorded MPFR version |
| [Verificarlo](https://github.com/verificarlo/verificarlo) | Upstream instrumentation diagnostics; no direct FloatLib comparison |
| [FLiT](https://github.com/PRUNERS/FLiT) | The complete 140-configuration GCC/Clang litmus matrix in base, OpenMPI, and MPICH modes, with final comparison CSVs and SQLite databases |
| [ReproBLAS](https://bebop.cs.berkeley.edu/reproblas/) and [ExBLAS](https://github.com/riakymch/exblas) | Upstream reproducible or exact-reduction checks and secondary diagnostics |
| SMT QF_FP | Direct FloatLib/Z3 exact-bit and NaN-class differential results |

The [summary](results/main/ecosystem/summary.tsv) links each row to its log;
[provenance](results/main/ecosystem/provenance) records source revisions, commands, and any
compatibility patches. Those launch records describe the original environment. They are not
a portable rerun command, and `check.sh --profile release` does not run this wider collection.

The three CORE-MATH compound-interest functions could not link because MPFR 4.2.1 does not
export `mpfr_compound`. FLiT's three modes passed with timing disabled: we checked output
variation across compiler configurations. Its Makefile removes the earlier `*-out`
intermediates after generating the comparison CSVs; those final CSVs and databases are saved.

### Status labels

The summaries distinguish the outcomes:

| Status | Meaning |
| --- | --- |
| `pass` | All acceptance checks for the stated run passed |
| `qualified-pass` | The main check passed with a named limitation or secondary diagnostic |
| `observational-complete` | All planned observations ran and differences were recorded; there is no conformance pass/fail claim |
| `unsupported` | The comparison requires a representation, operation, or policy FloatLib does not expose |
| `external-limitation` | The external implementation could not supply a suitable reference for FloatLib's result |
| `diagnostic-failure` | An additional diagnostic failed |
| `upstream-failure` | The external project failed to build or pass its own checks before a meaningful comparison |

Each qualification points to an explanation. An upstream pass, a matching value table, a sampled
arithmetic comparison, and a timing measurement answer different questions.

## Limits of the saved comparisons

The saved direct-comparison bundle has these coverage limits:

| Area | Historical coverage limit |
| --- | --- |
| Representations | No IEEE decimal32/64/128 or binary80 explicit-integer-bit comparisons |
| Rounding and conversion | Not every floating-point/integer policy; no nearest-away, round-to-odd, tininess-before-rounding, or universal NaN payload-selection rule |
| P3109 and OCP MX | Representation tables do not establish complete P3109 arithmetic or exception handling, OCP MX block operations or scaling, saturation, or hardware FP8 interoperability |
| Certification | Table agreement is not IEEE certification; no official posit certification |
| Transcendentals | No global correct-rounding or real-error theorems for all transcendentals |
| Linear algebra | No optimized verified BLAS implementation |

These are limits of that comparison, not a current inventory of the library. Later decimal,
posit, and other checks are described in the
[validation chapter](../site/content/chapters/19-external-validation.md).
Even exhaustive testing at one finite width cannot establish a theorem over every descriptor.
Likewise, scalar arithmetic checks do not establish a verified GEMM implementation.

When a comparison finds a bug, we isolate it in scratch space and fix the general specification
or implementation. The [testing guide](README.md#checking-a-change) explains where those
experiments belong.
