# External validation

We compare FloatLib with independent implementations because a proof can agree with our
specification even when we have misread the standard. These checks also exercise the compiled code,
the input decoders and the boundary with each foreign library. A match is evidence over the stated
inputs and policies, and for the general statements you need the proofs.

Run every command below from the repository root. If you're running current source, follow the
[project setup](../README.md#installation) first.

## Check or redraw the results

In the [direct comparisons](results/main/release/external) you'll find results, raw logs, and the
SoftPosit analysis, while the [ecosystem results](results/main/ecosystem) mostly record upstream
projects' own checks. For both, the [manifests](results/main/MANIFEST.tsv) and [source
records](results/main/provenance/SNAPSHOT.txt) identify the files, revisions, and environment behind
each measurement.

To check those saved files:

```bash
bash tests/oracles/verify-main-result.sh
```

This checks hashes, provenance, the consistency of statuses and counts, and the saved SQLite
databases. Then it redraws the summaries and figures in temporary space and compares them byte for
byte. You need Git, Python, and Matplotlib. Nothing is rebuilt: the verifier never compiles FloatLib
or reruns an external tool. Benchmark evidence has its own [verifier](../benchmarks/README.md).

To redraw just the direct-comparison summary and figures into a directory of your choice:

```bash
python3 tests/oracles/render_release_result.py \
  tests/results/main/release/external/summary.tsv \
  /path/to/local-output/external-figures
```

The renderer only reads saved data. It doesn't validate or regenerate any numerical
answer. Point it at an output directory outside `tests/results/`. For the ecosystem summary,
`render_ecosystem_result.py` takes the same two arguments. New figures carry the FloatLib name, but
the verifier passes `--historical-branding` so that its redraws match the original titles and SVG
identifiers. We left the old names and hashes in the recorded files as they were.

## Run comparisons on current source

The `quick` profile runs a bounded set of comparisons:

```bash
bash tests/oracles/check.sh --profile quick
```

For all comparisons supported by the runner, choose a new output directory:

```bash
bash tests/oracles/check.sh --profile release --results /path/to/new-external-result
```

The runner builds the current checkout and fetches the pinned upstream sources it needs. It inherits
the process's CPU affinity and uses at most eight workers by default (fewer if fewer CPUs are
available), which you can raise or lower within that allocation with `--workers` and restrict
further with `--cpu-set`. Suites run one after another, with parallelism inside each suite. Without
`--results`, output goes to a fresh directory under `TMPDIR` (normally `/tmp`), and a path you pick
yourself must not exist yet. `FLOATLIB_BUILD_DIR` sets the local directory for compiler output.

These are new runs. The source, adapter coverage, tool versions, and machine settings can all differ
from the saved results. Running today's script won't replay an old snapshot. To recreate one, you
need its linked source and environment records.

You'll need Linux command-line tools, Git, Make, and C/C++ compilers. TestFloat and SoftPosit
currently pick their upstream Linux x86-64 build directories. For MPFR you need its development
files (version 4.1.0 or newer) and `pkg-config`. On the Python side you need `matplotlib`, `onnx`,
`numpy`, and `python-flint`, and the release profile also wants the `z3` executable. Arb is optional
in `tests/verify.sh`, but both of these profiles require it.

Here are the suites in the `release` profile. `quick` runs `01`–`07`, with TestFloat's smoke subset
and P3109 tables through 8 bits.

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
| `12-transcendentals` | Known-failure gate with observations | FloatLib against MPFR, plus CORE-MATH, OpenLibm, and supported RLIBM functions |

Each suite writes its scope and outcome next to its logs. Any nonzero comparison fails the runner.
That includes the known differences in the pinned SoftPosit implementation, which we explain in the
[SoftPosit analysis below](#softposit).

## Run an individual comparison

Each of these entry points runs one comparison on its own, and in the examples they use one worker
and inherit the affinity, whereas the top-level runner above picks its parallelism automatically.

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

For the exhaustive and MPFX checks you need a built SoftFloat checkout (the one `testfloat.sh`
caches works) and, optionally, an MPFX checkout:

```bash
# One of 256 blocks of binary16 addition pairs, nearest-even; blocks 0..255 cover all 2^32 pairs.
bash tests/oracles/exhaustive16.sh --softfloat-dir /path/to/berkeley-softfloat-3 \
  --mpfx-dir /path/to/mpfx pairs f16 add near_even 60
# One of 1,024 blocks of binary32 square roots, toward negative infinity.
bash tests/oracles/exhaustive16.sh --softfloat-dir /path/to/berkeley-softfloat-3 \
  sqrt f32 sqrt min 300

# Certified expMinus1 on a 2^22 block of binary32 inputs and on listed inputs of any format.
source tests/lib/lake.sh
floatlib_benchmark_lake build execFloatCertifiedExpLog
cc -O2 tests/oracles/certified_explog_block.c -lmpfr -lgmp -o /tmp/explog_block
"$(floatlib_build_path bin/execFloatCertifiedExpLog)" range expm1 1056964608 4194304 /tmp/block.bin
/tmp/explog_block expm1 1056964608 4194304 /tmp/block.bin
python3 -I tests/oracles/coremath_words.py expm1.wc /tmp/expm1-words.txt

# MPFX on one format, operation, and operand set.
bash tests/oracles/mpfx/run.sh --mpfx-dir /path/to/mpfx --work /tmp/mpfx 11 50 sqrt tiny 200000
```

That binary16 command checks one shard of input pairs, so it doesn't cover every binary16 pair. CI
checks 17 left operands for both addition and multiplication and pairs each with all 65,536 right
encodings: **2,228,224 ordered pairs**. Those operands cover signed zeros, subnormal boundaries,
adjacent normal values, both largest finite magnitudes, infinities, and quiet/signaling NaNs. For
the `quick` and `release` profiles it's 16 left operands, or **2,097,152 ordered pairs**. Our saved
release evidence predates this expansion and records two rows, or 131,072 pairs.

The transcendental command compares FloatLib's `exp`, `log`, `sin`, `cos`, `sinh`, `cosh`, `tanh`,
`pow` and `pi` with MPFR in binary16, bfloat16, binary32, binary64, binary128 and `ieee 31 23`.
Inputs and results cross the boundary as exact encodings. MPFR emulates each format's exponent range
and subnormals. In any of the five MPFR rounding modes the oracle can report the sign of the ternary
value, but FloatLib's functions round to nearest only, so the emitter asks for `RNDN`. The corpus
mixes edges, fixed-seed samples drawn as integers, and the checked-in [hard
cases](oracles/data/transcendental-hard-cases.tsv) from
[`transcendental_hard_cases.py`](oracles/transcendental_hard_cases.py): continued-fraction arguments
near multiples of `pi / 2` in every binade, plus the overflow, underflow, saturation and midpoint
boundaries of the other functions. Generated sine and cosine arguments stop below `2^16385`, beyond
which MPFR's own reduction needs that many bits of `pi`, but for `ieee 31 23` the corpus also lists
arguments near `2^(2^20)`, which FloatLib reduces with the `2^20`- and `2^21`-bit levels of
`2 / pi`.

A run fails on any difference that the [known-failures
list](oracles/data/transcendental-known-failures.tsv) doesn't name, on a listed case whose kind,
FloatLib encoding or FloatLib ternary changes, on a listed case that now matches, and on any value
difference in a domain FloatLib declares correctly rounded. Right now that domain is `pow` in
nearest rounding, for formats with the IEEE encoding and the conventional exponent bias, of a finite
nonzero base with an integral exponent whenever FloatLib's result is finite. A run fails, too, when
a shard is missing, when the shards disagree about the invocation or its manifest is incomplete, and
when its requests differ from those the [census](oracles/data/transcendental-census.json) records
for the same random count, tier and exhaustive16 setting. The script tells the report which options
it gave the emitter, so an emitter that misreports them fails, and the release check in `check.sh`
requires the census entry for its invocation. The census covers three runs: the default run, the
release run (`--random-count 256`) and the qualification run (`--slow --random-count 256`). For each
it holds the manifest, the hash of the hard-case file, the number of requests per format and
operation, and a hash of the sorted case ids. The qualification run must also exercise every listed
case, while other invocations report their coverage as unchecked. A default run takes about a
minute. `--slow` adds every binary128 continued-fraction case with both signs and neighbours and
every binary16 and bfloat16 code, about two minutes on eight cores. Its `--help` lists the options,
including CORE-MATH, OpenLibm, and RLIBM observations, `--write-known-failures` to regenerate the
list after a repair, and `--write-census` to record the three runs again after the emitter or the
corpus changes. The oracle also answers `contain` requests. It decides whether a function value lies
in a dyadic interval by rounding the value down and up at rising precision, which is the check a
proved enclosure needs, since a single rounded value can fall inside a wrong interval.

For one SoftPosit format and operation, supply a clean checkout at the revision pinned in
[`softposit.sh`](oracles/softposit.sh):

```bash
bash tests/oracles/softposit.sh --softposit-dir /path/to/SoftPosit \
  --bits 6 --op add --exhaustive
```

The script checks the revision and builds from a Git archive in temporary space. In the `release`
profile the runner fetches that checkout itself and runs the full matrix. After sourcing
`tests/lib/lake.sh`, `floatlib_test_lake exe oracle --help` lists the Lean executable's stream
protocols.

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
| Every binary16 and bfloat16 arithmetic pair, every binary32 square root | [Berkeley SoftFloat](https://www.jhauser.us/arithmetic/SoftFloat-3/doc/SoftFloat.html) and an MPFR emulation of each format |
| Certified `expMinus1` and `logPlus1` | [GNU MPFR](https://www.mpfr.org/mpfr-current/mpfr.html) and the [CORE-MATH](https://gitlab.inria.fr/core-math/core-math) worst-case lists |
| A double-rounding format simulator | [MPFX](https://github.com/bksaiki/mpfx) |

### TestFloat details

Our maintained overlap with TestFloat covers arithmetic in binary16, binary32, binary64, and
binary128, plus round-to-integral, quiet and signaling comparisons, cross-format binary conversions,
and the BF16 conversions exposed by the pinned TestFloat interface. It checks nearest-even, toward
zero, toward positive infinity, and toward negative infinity, together with the invalid,
divide-by-zero, overflow, underflow, and inexact flags.

Non-NaN outputs are compared bit for bit. For NaNs we compare the class and still check signaling
and invalid behavior, but we don't claim strict agreement on payload selection.

We kept the level-2 subset small on purpose. Each selected function runs its complete level-2
generator, but three rows don't make a complete level-2 matrix. Very large level-2 combinations need
`--allow-huge-level2`, and if you run them, schedule them by operation and format and save each
summary.

Some things stay outside this adapter: binary80's explicit-integer-bit encoding, BF16 arithmetic
that the pinned interface doesn't expose, floating-point/integer conversions without a shared
invalid-result policy, nearest-away, round-to-odd, tininess-before-rounding, and universal NaN
payload identity.

### ONNX and P3109 details

Here the representation adapter compares decoded values with the published ONNX and P3109 tables. It
checks FloatLib's exact dyadic decoding against the public ONNX decoders and the pinned P3109
hexadecimal value tables, and the P3109 emitter works from the format descriptor.

### P3109 arithmetic with FLoPS

In the [FLoPS comparison](../benchmarks/external/flops/README.md) we check addition, multiplication,
division, and FMA for `Binary4p2sf`, `Binary8p4se`, and `Binary8p3se`, with nearest-even rounding
and no saturation. All 529,152 arithmetic cases and the 192 exact timing fixtures agree bit for bit.
Then the same runner times both compiled libraries on identical result-dependent inputs. It's a
focused experiment outside the `release` profile, and its page links the instructions, adapters, and
individual measurements.

### Scalar conversions with TensorLib

In the [TensorLib comparison](../benchmarks/external/tensorlib/README.md) we convert every FP16,
BF16, E4M3FN, and E5M2 encoding to Float32, and in the other direction we test rounding boundaries
and selected Float32 inputs. Both libraries pass 952,612 numerical checks against an independent
adjacent-value reference, and all 2,964 result words that differ are E4M3FN NaN signs, on negative
overflow or negative infinity. This comparison doesn't look at NaN payloads, signaling behavior, or
exception flags. Timings use 128 matching normal finite fixtures. You can reproduce this focused
experiment from the linked instructions without running the release suite.

### MPFR and underflow

We use MPFR as the oracle for finite arithmetic and rounding, but not for IEEE NaN precedence,
because MPFR has one NaN class and its fused-operation behavior doesn't encode every IEEE payload
and signaling rule. So the adapter works out signaling NaNs and invalid arithmetic causes from the
input encodings, and TestFloat stays the independent status oracle over its supported overlap.

In these checks the binary operations detect tininess after rounding and report underflow only for a
result that is tiny and inexact. The TestFloat adapter selects `-tininessafter`. On the MPFR side,
the adapters normalize the result to the target exponent range and report underflow only together
with inexact, which matches the policy under test. An exact subnormal doesn't count as underflow.

### Native FPU boundary

In the native suite we compare the public binary32/64 dispatch results with the proved software
kernels, and we also sample the opt-in `NativeFPU.Unchecked` operations. Agreement is valuable
regression evidence for the current compiler, ABI, and machine, but the theorem that the host
replacement implements the software model for every input is still missing.

### SoftPosit

Our [saved SoftPosit results](results/main/release/external/11-softposit) include disagreements. We
kept the failed rows and checked every disputed answer against FloatLib's exact rational
specification, and in the [analysis](results/main/release/external/11-softposit/ADJUDICATION.md) we
record the operands and neighboring encodings: the 32-bit cases expose inconsistent pX2 endpoint
handling, and the 16-bit FMA cases lose sticky information that should decide the rounding. On those
inputs, FloatLib's executable agrees with its exact specification.

That analysis backs the recorded `external-limitation` classification, but the raw comparison still
fails. Later checks at more widths are in the [website's validation
chapter](../site/content/chapters/19-external-validation.md). Don't substitute its broader counts
into the older result manifest.

### SMT and transcendentals

SMT-LIB floating-point values expose one abstract NaN, so QF_FP comparisons check NaNs by class and
can't check payload identity. Where the theory exposes the bits, the adapter records bit-for-bit
agreement.

Our saved transcendental row is `observational-complete`, since it predates the known-failure gate
and recorded every result and difference without failing. MPFR supplies the correctly rounded
references, while CORE-MATH, OpenLibm, and RLIBM support different functions and rounding contracts
and stay observational. Today's command gates FloatLib against MPFR by case identity. Because MPFR
has a single NaN, the Lean fixtures check signaling-NaN and payload behavior instead. Since the
known-failure list is empty, a passing run of the gate has no listed differences: no case differs
from MPFR in its encoding, its NaN class or its ternary sign. Those observational comparisons are
why a release run is recorded as `qualified-pass`. To accept the evidence, the verifier requires a
passing gate with no new, changed or stale differences, none in a correctly rounded domain, and
coverage that matched the census entry `release`. It also recomputes the summary rows, the provider
coverage and the census counts from the retained `details.tsv`. All of this is about the approximate
binary kernels, and none of it about the proved posit functions described on the website.

### Exhaustive 16-bit arithmetic

`execFloatExhaustive` evaluates the `Model` operations with `status := true` on every ordered pair
of binary16 or bfloat16 encodings, for addition, subtraction, multiplication, and division in the
four rounding directions required for binary formats, and on every binary32 square root. In
nearest-even mode it also records whether the planner-selected kernel behind the ordinary operator
returns a different encoding. Our [reference](oracles/exhaustive16_reference.cpp) compares each
value and all five flags with SoftFloat (binary16, binary32) or with MPFR set to the format's
precision and exponent range (bfloat16, which SoftFloat lacks), detecting tininess after rounding.
Binary16 runs against both references, so every pair also checks the MPFR emulation against
SoftFloat.

Across the 12,288 blocks that's 154,618,822,656 results, and none shows a value, flag, kernel, or
reference difference ([summary](results/differential/exhaustive16-floatlib.csv)).

### Certified expMinus1 and logPlus1

We ran the certified functions on all 2^32 binary32 inputs, every finite binary16 and bfloat16
input, and the distinct entries of CORE-MATH's binary64 `expm1.wc` and `log1p.wc` lists (123,552 and
347,766), and every returned result is MPFR's correctly rounded value. On those inputs a call fails
exactly when its input is not finite or its result overflows or is undefined
([binary32](results/differential/certified-expm1-log1p-binary32.csv), [other
formats](results/differential/certified-expm1-log1p-other.csv)).

### MPFX

[MPFX](oracles/mpfx/README.md) computes a round-to-odd result in a `double` or `float` container and
then rounds it again. We compared both of its engines with FloatLib on six formats (binary16,
bfloat16, IEEE-style `e4m3` and `e5m2`, and the two formats at the edge of its supported class), six
operations, four directions, and three operand sets, which comes to 316.8 million comparisons, and
on every binary16 and bfloat16 pair of the exhaustive campaign. Four MPFX problems reproduce in
standalone examples, reported upstream as
[bksaiki/mpfx#36](https://github.com/bksaiki/mpfx/issues/36): exact zeros under roundTowardNegative
come back as `+0`, `sqrt(-inf)` raises no invalid flag, the overflow flag is lost when the container
overflows, and error-free-transformation results go wrong when their rounding error underflows the
container ([sampled](results/differential/mpfx-sampled-classes.csv),
[exhaustive](results/differential/mpfx-exhaustive16.csv)). We group the remaining EFT differences by
engine without assigning a cause to every case.

## Reading the ecosystem results

We also built upstream tools for floating-point testing, rewriting, error analysis, and reproducible
arithmetic. Most rows below run each project's own checks, so a pass means that project worked in
the recorded environment. Agreement with FloatLib takes a direct comparison.

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

Each row of the [summary](results/main/ecosystem/summary.tsv) links to its log, and
[provenance](results/main/ecosystem/provenance) records source revisions, commands, and any
compatibility patches. Those launch records describe the original environment, so they won't work as
a portable rerun command (and `check.sh --profile release` doesn't run this wider collection).

The three CORE-MATH compound-interest functions couldn't link, because MPFR 4.2.1 doesn't export
`mpfr_compound`. FLiT's three modes passed with timing disabled, since what we checked was output
variation across compiler configurations. Its Makefile removes the earlier `*-out` intermediates
after generating the comparison CSVs, but those final CSVs and databases are saved.

### Status labels

Summaries label each outcome with one of these statuses:

| Status | Meaning |
| --- | --- |
| `pass` | All acceptance checks for the stated run passed |
| `qualified-pass` | The main check passed with a named limitation or secondary diagnostic |
| `observational-complete` | All planned observations ran and differences were recorded; there is no conformance pass/fail claim |
| `unsupported` | The comparison requires a representation, operation, or policy FloatLib does not expose |
| `external-limitation` | The external implementation could not supply a suitable reference for FloatLib's result |
| `diagnostic-failure` | An additional diagnostic failed |
| `upstream-failure` | The external project failed to build or pass its own checks before a meaningful comparison |

Every qualification points to an explanation. An upstream pass, a matching value table, a sampled
arithmetic comparison, and a timing measurement each answer a different question.

## Limits of the saved comparisons

Our saved direct-comparison bundle has these coverage limits:

| Area | Historical coverage limit |
| --- | --- |
| Representations | No IEEE decimal32/64/128 or binary80 explicit-integer-bit comparisons |
| Rounding and conversion | Not every floating-point/integer policy; no nearest-away, round-to-odd, tininess-before-rounding, or universal NaN payload-selection rule |
| P3109 and OCP MX | Representation tables do not establish complete P3109 arithmetic or exception handling, OCP MX block operations or scaling, saturation, or hardware FP8 interoperability |
| Certification | Table agreement is not IEEE certification; no official posit certification |
| Transcendentals | No global correct-rounding or real-error theorems for all transcendentals |
| Linear algebra | No optimized verified BLAS implementation |

These limits belong to that comparison and don't describe the library as it stands now. Later
decimal, posit, and other checks are in the [validation
chapter](../site/content/chapters/19-external-validation.md). Even exhaustive testing at one finite
width can't establish a theorem over every descriptor, and scalar arithmetic checks don't give you a
verified GEMM implementation.

When a comparison finds a bug, we isolate it in scratch space and then fix the general specification
or implementation. The [testing guide](README.md#checking-a-change) says where those experiments go.
