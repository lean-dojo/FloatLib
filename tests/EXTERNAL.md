# External validation

We compare FloatLib with independent implementations because a proof can agree with our
specification even when we have misread the standard. These checks also exercise the compiled code,
the input decoders and the boundary with each foreign library. A match is evidence over the stated
inputs and policies, and for the general statements you need the proofs.

Run every command below from the repository root. If you're running current source, follow the
[project setup](../README.md#installation) first.

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

Every run is a new measurement of your checkout, with the adapter coverage, tool versions and
machine settings of that run. The runner writes them next to the results.

You'll need Linux command-line tools, Git, Make, and C/C++ compilers. TestFloat and SoftPosit
use their upstream Linux x86-64 build directories. For MPFR you need its development
files (version 4.1.0 or newer) and `pkg-config`. On the Python side you need `matplotlib`, `onnx`,
`numpy`, and `python-flint`, and the release profile also wants the `z3` executable. Arb is optional
in `tests/verify.sh`, but both of these profiles require it.

Here are the suites in the `release` profile. `quick` runs `01` through `07`, with TestFloat's
smoke subset and P3109 tables through 8 bits.

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

# Block-scaled formats against torchao, microxcaling, and PyTorch casts
source tests/lib/lake.sh
floatlib_test_lake build oracle
python3 tests/oracles/block_formats.py --oracle "$FLOATLIB_BUILD_DIR/bin/oracle" \
  --torchao /path/to/torchao-target --microxcaling /path/to/microxcaling --out /path/to/result.json

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

# Certified expm1 on a 2^22 block of binary32 inputs and on listed inputs of any format.
source tests/lib/lake.sh
floatlib_benchmark_lake build execFloatCertifiedExpLog
cc -O2 tests/oracles/certified_explog_block.c -lmpfr -lgmp -o /tmp/explog_block
"$(floatlib_build_path bin/execFloatCertifiedExpLog)" range expm1 1056964608 4194304 /tmp/block.bin
/tmp/explog_block expm1 1056964608 4194304 /tmp/block.bin
python3 -I tests/oracles/coremath_words.py expm1.wc /tmp/expm1-words.txt

# MPFX on one format, operation, and operand set.
bash tests/oracles/mpfx/run.sh --mpfx-dir /path/to/mpfx --work /tmp/mpfx 11 50 sqrt tiny 200000
```

That binary16 command covers one shard of input pairs, so it doesn't reach every binary16 pair.
CI takes 17 left operands for both addition and multiplication and pairs each with all 65,536
right encodings, which makes **2,228,224 ordered pairs**. Those operands cover signed zeros, subnormal boundaries,
adjacent normal values, both largest finite magnitudes, infinities, and quiet/signaling NaNs. For
the `quick` and `release` profiles it's 16 left operands, or **2,097,152 ordered pairs**.

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
list](oracles/data/transcendental-known-failures.tsv) doesn't name. It also fails when a listed
case changes its kind, FloatLib encoding or FloatLib ternary, when a listed case now matches, and
on any value difference in a domain FloatLib declares correctly rounded. Those domains are `pi`, and `pow` with
an integral exponent, in nearest rounding for formats with the IEEE encoding and the conventional
exponent bias. For `pow` that means a finite base whenever FloatLib's result is finite, except
where both results are zeros, since the theorem fixes the value but not the sign of a zero. The
bookkeeping can fail a run as well: a missing shard, shards that disagree about the invocation, a
shard whose manifest is incomplete, or requests that differ from those the
[census](oracles/data/transcendental-census.json) records for the same random count, tier and
exhaustive16 setting. The script tells the report which options
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
| FP16, BF16, E4M3, and E5M2 scalar conversions | [TensorLib conversion comparison](../benchmarks/external/tensorlib/README.md) |
| Binary arithmetic and rounding | [GNU MPFR](https://www.mpfr.org/mpfr-current/mpfr.html) |
| Ball and transcendental arithmetic | [Arb](https://arblib.org/) through [python-flint](https://python-flint.readthedocs.io/) |
| Additional IEEE vectors | [IBM FPgen test suite](https://github.com/sergev/ieee754-test-suite) |
| SMT floating-point semantics | [SMT-LIB QF_FP](https://smt-lib.org/logics-all.shtml#QF_FP) through [Z3](https://github.com/Z3Prover/z3) |
| Independent posit execution | [SoftPosit](https://gitlab.com/cerlane/SoftPosit) |
| Transcendental observations | [CORE-MATH](https://gitlab.inria.fr/core-math/core-math), [OpenLibm](https://github.com/JuliaMath/openlibm), and [RLIBM](https://github.com/rutgers-apl/rlibm) |
| Every binary16 and bfloat16 arithmetic pair, every binary32 square root | [Berkeley SoftFloat](https://www.jhauser.us/arithmetic/SoftFloat-3/doc/SoftFloat.html) and an MPFR emulation of each format |
| Certified `expm1` and `logp1` | [GNU MPFR](https://www.mpfr.org/mpfr-current/mpfr.html) and the [CORE-MATH](https://gitlab.inria.fr/core-math/core-math) worst-case lists |
| A double-rounding format simulator | [MPFX](https://github.com/bksaiki/mpfx) |
| OCP MX block quantization and decoding, NVFP4 quantization, FP8, FP6 and FP4 element casts | [torchao](https://github.com/pytorch/ao) `prototype.mx_formats`, [microxcaling](https://github.com/microsoft/microxcaling), and PyTorch's `float8_e4m3fn` and `float8_e5m2` casts |

### TestFloat details

Our maintained overlap with TestFloat covers arithmetic in binary16, binary32, binary64, and
binary128, plus round-to-integral, quiet and signaling comparisons, cross-format binary conversions,
and the BF16 conversions exposed by the pinned TestFloat interface. It covers nearest-even, toward
zero, toward positive infinity, and toward negative infinity, together with the invalid,
divide-by-zero, overflow, underflow, and inexact flags.

Non-NaN outputs are compared bit for bit. For NaNs we compare the class and test signaling and
invalid behavior too, but we don't claim strict agreement on payload selection.

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

In the [FLoPS comparison](../benchmarks/external/flops/README.md) we test addition, multiplication,
division, and FMA for `Binary4p2sf`, `Binary8p4se`, and `Binary8p3se`, with nearest-even rounding
and no saturation. All 529,152 arithmetic cases and the 192 exact timing fixtures agree bit for bit.
Then the same runner times both compiled libraries on identical result-dependent inputs. It's a
focused experiment outside the `release` profile, and its page links the instructions, adapters, and
individual measurements.

### P3109 operations on encodings

Lean's kernel evaluates the operations of the interim report on natural-number encodings
(`P3109.KernelPath`). `tests/oracles/p3109_kernel.py` computes each of them independently: it
decodes the operands to exact values, applies the operation of the report on `Fraction` with its
rules for infinities and NaN, and projects the exact result with the `Fraction` reference of
`p3109_comparison.py`. A square root is rounded from integer square roots of scaled radicands,
and an infinite result is saturated by the table of section 4.7.5. Each request is compared in
51 rounding modes (the six deterministic ones, and stochastic A, B and C with every random word
of zero to three bits) and the three saturation modes.

```bash
source tests/lib/lake.sh
floatlib_test_lake build oracle
python3 tests/oracles/p3109_kernel.py --oracle "$FLOATLIB_BUILD_DIR/bin/oracle" \
  --out /path/to/result.json
```

The run of 2026-11-19 (seed 20261119): 149,052 requests and 18,554,428 encodings, none
different.

| Compared | Operands |
| --- | --- |
| `convert`, `negate`, `abs`, `recip`, `sqrt`, `rsqrt`, the eight classification queries and the two neighbours | every code of the 42 descriptors of three to five bits |
| `add`, `sub`, `mul`, `div`, `copysign`, `hypot`, the ten extrema and the three comparisons | every pair of codes of the descriptors of three and four bits, and 48 pairs of each descriptor of five bits |
| `fma`, `faa`, `clamp` | 64 triples of each of these descriptors |
| all of the above with operands and destination of different descriptors | 300 draws among the 94 descriptors of three to six and of eight bits |
| `convertbinary`, the conversion of a word of a binary interchange format | every word of ten binary formats of four to nine bits, IEEE and the three encodings without an infinity, into six drawn descriptors each; the special values and 600 drawn words of binary16, bfloat16, binary32, binary64 and of three wide formats of the other encodings, into drawn descriptors |

### Scalar conversions with TensorLib

In the [TensorLib comparison](../benchmarks/external/tensorlib/README.md) we convert every FP16,
BF16, E4M3, and E5M2 encoding to Float32, and in the other direction we test rounding boundaries
and selected Float32 inputs. Both libraries pass 952,612 numerical checks against an independent
adjacent-value reference, and all 2,423 result words that differ come from NaN inputs, where
FloatLib keeps the input's sign and payload and TensorLib returns a canonical NaN. This comparison
records those NaN encodings without counting them as errors, and it doesn't test signaling behavior
or exception flags. Timings use 128 matching normal finite fixtures. You can reproduce this focused
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
regression evidence for the current compiler, ABI, and machine, but no theorem states that the
host replacement implements the software model for every input.

### SoftPosit

The comparison with the pinned SoftPosit revision reports disagreements, and the raw comparison
fails on them. We keep the failed rows and check every disputed answer against FloatLib's exact
rational specification. The 32-bit cases expose inconsistent pX2 endpoint handling, and the 16-bit
FMA cases lose sticky information that should decide the rounding. On those inputs FloatLib's
executable agrees with its exact specification, so the runner classifies the suite as
`external-limitation`.

#### Other exponent sizes

The Posit Standard (2022) fixes two exponent bits. The kernel operations take the number of
exponent bits as a parameter, and `Posit.General` proves them for every number. An implementation
written for other numbers checks them: SoftPosit's 8-bit posits have no exponent bit and its
16-bit posits have one (the 2018 draft). `tests/oracles/posit_general.py` compares
`oracle posit-general P ES` with the `softposit` Python package, bit for bit.

```bash
source tests/lib/lake.sh
floatlib_test_lake build oracle
python3 tests/oracles/posit_general.py --oracle "$FLOATLIB_BUILD_DIR/bin/oracle" \
  --out /path/to/result.json
```

The run of 2026-11-19 (softposit 0.3.4.4, seed 20261119): 1,478,927 results, none different.

| Compared | 8 bits, no exponent bit | 16 bits, one exponent bit |
| --- | ---: | ---: |
| `add`, `sub`, `mul`, `div`, `lt`, `le`, each | 65,536 (every pair) | 62,145 |
| `fma` | 63,375 | 63,375 |
| `sqrt`, `neg`, `abs`, each | 256 (every encoding) | 65,536 (every encoding) |
| to a signed integer of 32 and of 64 bits, each | 255 | 65,535 |
| to an unsigned integer of 32 and of 64 bits, each | 128 | 32,768 |

Conversions between formats: 8 to 16 bits (256), 16 to 8 bits (65,536), 16 to 32 bits with two
exponent bits (65,536) and 32 to 16 bits (60,015). SoftPosit follows the 2018 draft for the
conversions to integers, in which NaR and a negative value converted to an unsigned integer give
zero. The 2022 standard gives the word with only its most significant bit set, so NaR is left
out, and the unsigned conversions are compared on the encodings below the sign bit.

### SMT and transcendentals

SMT-LIB floating-point values expose one abstract NaN, so QF_FP comparisons treat NaNs by class and
can't check payload identity. Where the theory exposes the bits, the adapter records bit-for-bit
agreement.

MPFR supplies the correctly rounded references of the transcendental comparison, while CORE-MATH,
OpenLibm, and RLIBM support different functions and rounding contracts and stay observational. The
command gates FloatLib against MPFR by case identity. MPFR has a single NaN, so the Lean fixtures
cover signaling-NaN and payload behavior. Since the known-failure list is empty, a passing run of
the gate has no listed differences: no case differs from MPFR in its encoding, its NaN class or its
ternary sign. Those observational comparisons are why a release run is recorded as
`qualified-pass`. All of this is about the approximate binary kernels, and none of it about the
proved posit functions described on the website.

### Exhaustive 16-bit arithmetic

`execFloatExhaustive` evaluates the `Model` operations with `status := true` on every ordered pair
of binary16 or bfloat16 encodings, for addition, subtraction, multiplication, and division in the
four rounding directions required for binary formats, and on every binary32 square root. In
nearest-even mode it also records whether the planner-selected kernel behind the ordinary operator
returns a different encoding. Our [reference](oracles/exhaustive16_reference.cpp) compares each
value and all five flags with SoftFloat (binary16, binary32) or with MPFR set to the format's
precision and exponent range (bfloat16, which SoftFloat lacks), detecting tininess after rounding.
Binary16 runs against both references, so every pair also tests the MPFR emulation against
SoftFloat.

Across the 12,288 blocks that's 154,618,822,656 results, and none shows a value, flag, kernel, or
reference difference ([summary](results/differential/exhaustive16-floatlib.csv)).

### Certified expm1 and logp1

We ran the certified functions on all 2^32 binary32 inputs, every finite binary16 and bfloat16
input, and the distinct entries of CORE-MATH's binary64 `expm1.wc` and `log1p.wc` lists (123,552 and
347,766), and every returned result is MPFR's correctly rounded value. On those inputs a call fails
exactly when its input is not finite or its result overflows or is undefined
([binary32](results/differential/certified-expm1-log1p-binary32.csv), [other
formats](results/differential/certified-expm1-log1p-other.csv)).

### IEEE 754-2019 additions

`tests/oracles/ieee2019.sh` checks the operations of IEEE 754-2019 that were added in 2026-11. Its
first part runs the binary operations of clauses 9.4 to 9.7 (`augmentedAddition`,
`augmentedSubtraction`, `augmentedMultiplication`, the four minimum and maximum operations by
magnitude, `sumAbs`, `sumSquare`, `scaledProd`) on every ordered pair of encodings of a six-bit
IEEE format, and the three payload operations on every encoding of a ten-bit format. The expected
results are computed by [brute force from the definitions](FloatLibTests/Oracle/IEEE2019.lean): the
nearest of all finite values to the exact rational result, with the tie rule and the overflow
threshold of the operation.

The second part compares generated cases with other implementations
([references](oracles/ieee2019/reference.py), [payload reference](oracles/ieee2019/payload.c)):
decimal addition, subtraction and multiplication in decimal32, decimal64 and decimal128 and the
five rounding directions, values and flags, against Python's `decimal` module (libmpdec), for the
specification and for the kernel path; the decimal `maximumNumber`, `minimumNumber`,
`maximumMagnitudeNumber` and `minimumMagnitudeNumber` against its `max`, `min`, `max_mag` and
`min_mag`; the augmented operations, `sumAbs`, `sumSquare` and `scaledProd` on binary64 against
exact rational arithmetic in Python; and `getPayload`, `setPayload` and `setPayloadSignaling` on
binary32 and binary64 against glibc 2.34. Python's `decimal` follows IEEE 754-2008 for `max` and
`min`, so cases with a signaling NaN or with two NaN operands are left out there.

With 20,000 generated cases of each kind that's 225,320 cases, and none fails
([summary](results/differential/ieee2019.csv)).

The formatOf operations of clause 5.4.1 are compared with `add`, `sub`, `mul`, `div` and `fma`
on every pair of encodings of the six-bit format in six rounding directions, value, flags and
ternary value, and across three formats with the rules of the standard and the rounded exact
rational result: 1,228,800 cases, none fails.

The decimal reductions `sum`, `sumAbs`, `sumSquare` and `dot` of clause 9.4 are compared with
Python's `decimal`: the reference adds the terms without rounding in a context of 26,000
digits and rounds the exact sum once in the interchange context, with its flags. 20,000 cases
of up to five operands in the three formats and the five rounding directions, none fails.

The recommended functions of clause 9.2 on binary formats (`exp2`, `log10p1`, `sinPi`, `atan2Pi`,
`powr`, `compound` and the others, 30 in all) are compared with
[`mpmath`](oracles/ieee2019/functions.py), a Python package, when `IEEE2019_PACKAGES` names the
directory that holds it. The reference computes each result with a working precision far above
the format and rounds it with exact rational arithmetic, and it states the special cases of
ISO/IEC 9899:2024 F.10.1 to F.10.4 a second time, independently of the Lean definitions. Values
and all five flags are compared, in the five rounding directions of the standard: every
encoding of an eight-bit format for the 26 functions of one operand, every pair of encodings of
a six-bit format for `atan2`, `atan2Pi` and `powr`, `compound` on that format with thirteen
exponents, and pseudo-random operands of binary16, binary32 and binary64 in a pseudo-random
direction. With 20 operands for each function and format, and with the other small formats of
the last paragraph, that's 259,720 cases, and none fails. While the reference was written it
disagreed with FloatLib twice, and FloatLib was right both times: `sin x` is inexact for the
smallest subnormal `x`, which a fixed precision of 800 bits does not show, and `tanh`, `exp2m1`
and `exp10m1` of a large operand are inexact although the result is the limit.

The certified decimal functions of clause 9.2 (`Transcendentals.Certified.exp2`, `sin`, `atanh`
and the others of one argument, `exp` and `log`) are compared with `mpmath` by
[`decimal_functions.py`](oracles/ieee2019/decimal_functions.py): the reference computes each
result with four times the precision of the format and 60 digits more and rounds it to the
precision of the format with exact rational arithmetic. A decimal function returns a result
only when an enclosure settles the rounding, so the oracle compares the value of every result
that is returned and counts the cases without one. With 20 operands of magnitude between
1/1000 and 100 for each of the 28 functions in each of decimal32, decimal64 and decimal128,
1,676 of 1,680 cases return a result and none of them differs from the reference. The 4
cases without a result are `exp10` (3) and `exp` (1) of operands whose result is too small
for the two grids.

The same scripts cover the other operations of the clause table. `functions.py` also writes
`pow`, `hypot`, `rootn`, `pown`, `rSqrt`, `cbrt` and the forms with flags of `exp`, `expm1`,
`log` and `logp1`, and every encoding of five small formats in each of the five rounding
directions: an IEEE eight-bit format, OCP E5M2 and E4M3, and the ONNX formats E4M3FNUZ and
E5M2FNUZ, with every pair of encodings of a six-bit IEEE format and of the four-bit format
E2M1 for the functions of two operands. A format without an infinity delivers its NaN where an
IEEE format delivers an infinity, and a format without a NaN its largest finite value and `+0`
for an invalid operation. The roots of `rSqrt`, `rootn` and `hypot` are computed with exact
integers. `decimal_functions.py` also writes the total decimal functions
(`Transcendentals.CorrectlyRounded`) with their flags in the five directions, at ordinary
operands and at operands whose results overflow or underflow, `atan2`, `atan2Pi`, `pow`, `powr`
and `compound` included. `reference.py` also writes the decimal scaled products
(`decimal-scaled`: the exact product in a context of 80,000 digits, scaled by the adjusted
exponent and rounded once) and the decimal reductions from left to right in an accumulator
format (`decimal-ordered`: a chain of additions of Python's `decimal` in the accumulator's
context, whose flags accumulate). The formatOf square root is compared on every encoding of the
six-bit format in six directions with the rounded exact root, in one format and across three.
`p3109_functions.py` covers `Exp10`, `Exp2MinusOne`, `Exp10MinusOne`, `Log10`, `Log2OnePlus`,
`Log10OnePlus` and `Cbrt` on P3109 formats with directed MPFR enclosures, `Pow` and `Powr` with
an exponent in Binary8p3se, and `Pown`, `Rootn` and `Compound` with the integers from -3 to 3,
which are exact rationals except for the roots.

In the recorded campaign (`tests/oracles/ieee2019.sh 20000 20261116`) the binary functions of
clause 9.2 are 461,520 cases, the total decimal functions 13,500, the decimal scaled products
20,000, the ordered decimal reductions 20,000 and the formatOf square root 3,456. With the groups
above that's 1,994,276 cases in 145 groups, and none fails.

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

### Block-scaled formats

`tests/oracles/block_formats.py` compares the stored codes and decoded values of the general block
format (`Formats.Block`) bit for bit with three references: torchao's `to_mx`, `to_dtype` and
`nvfp4_quantize` and its FP4 and FP6 kernels, microxcaling's `_quantize_mx`, and PyTorch's casts
to `float8_e4m3fn` and `float8_e5m2`. FloatLib runs through `oracle block`, which reads tensors of
binary32 words. The inputs are random tensors and adversarial ones: block maxima at binade
boundaries, ties of the element rounding, saturation, zeros and negative zeros, and scales at
both ends of the scale format's range. Inputs that are not finite are not generated, and torchao's
`EVEN` scale mode is not compared. This comparison is not part of the `quick` and `release`
profiles. It needs `torch`, `numpy`, a torchao install and a microxcaling checkout.

The run of 2026-11-14 (torchao 0.18.0, torch 2.13.0, microxcaling `7bc4195`, seed 20261114, 150
draws per generator) has no unexplained difference. A difference counts as explained when the
script recognizes its class from the input alone:

| Comparison | Compared | Different | Inputs that differ |
| --- | --- | --- | --- |
| OCP MX, five FP profiles, torchao `FLOOR`, `CEIL`, `RCEIL`: scale code, element codes, decoded values | 761,520 | 28,260 | blocks whose stored scale is `2^-127`, where FloatLib divides the elements by the stored scale as the specification's conversion does; all-zero blocks, whose scale the specification leaves open (FloatLib stores `2^0`) |
| OCP MX, six profiles, microxcaling with `round="even"`: decoded values | 128,992 | 765 | block maxima one ulp below a power of two, where FloatLib has the exact exponent `floor(log2 max)`; INT8 inputs at the negative end, where FloatLib stores `-2` and the specification also permits the symmetric range that ends at `-127/64` |
| NVFP4 without and with an outer scale, exact scale arithmetic: scale and element codes | 43,622 | 1,074 | blocks whose exact scale is below `2^-6`; scaled inputs within `2^-20` of a rounding tie, where the exact format rounds the exact quotient once |
| NVFP4, exact scale arithmetic with a floor of `2^-6` on the block scale | 43,622 | 386 | the ties alone |
| NVFP4, the same tensors through FloatLib's binary32 arithmetic in torchao's order | 43,622 | 0 | |
| `float8_e4m3fn` cast against the SAT conversion, `float8_e5m2` against the OVF conversion, torchao's E2M1, E2M3 and E3M2 kernels, and both FP8 decoders | 23,658 | 0 | |
| `float8_e4m3fn` cast against the OVF conversion, `float8_e5m2` against the SAT conversion | 10,036 | 1,005 | PyTorch saturates E4M3 and returns the E5M2 infinity above the largest finite value |

The exact-arithmetic NVFP4 format rounds each exact scaled input once. A reference that scales in
binary32 can differ from it at a tie, and `oracle block nvfp4f32` shows that this is the only
arithmetic difference on these inputs. That command runs `Block.nvfp4Working`, the library's
quantizer on binary32 encodings in torchao's order.

No tensor of that corpus makes a binary32 operation overflow. `tests/oracles/nvfp4_working.py`
covers those: it repeats the order of operations with NumPy's float32, which is the binary32
arithmetic of the processor, rounds to E4M3 and E2M1 with exact fractions and compares the words
with `oracle block nvfp4f32`. It needs `numpy` only.

```bash
source tests/lib/lake.sh
floatlib_test_lake build oracle
python3 tests/oracles/nvfp4_working.py --oracle "$FLOATLIB_BUILD_DIR/bin/oracle" \
  --out /path/to/result.json
```

The run of 2026-11-19 (NumPy 2.5.0, seed 20261119, 4,000 tensors of two blocks without an outer
scale and 4,000 with one):

| Comparison | Words | Different |
| --- | ---: | ---: |
| Without an outer scale: scale words and element words | 136,000 | 0 |
| With an outer scale, from the least subnormal to the largest finite value | 135,932 | 0 |

Of the tensors with an outer scale, the scale quotient overflows in 719, the reciprocal in 13 and
a product of an element with the reciprocal in 682. Two tensors have a zero element under an
overflowed reciprocal, which is `0 * inf`, a NaN: they are counted and left out.

### The standards' operations and the complex functions

Each standard has compiled producers, Lake executables of the test workspace that print what the
public operations return, and Python references that read those observations. The references are
written from the documents and don't call FloatLib. These comparisons are not part of the `quick`
and `release` profiles.

| Producer | Reference | Compared with |
| --- | --- | --- |
| `positStandard` | `oracles/posit_standard.py` | SoftPosit's generic `pX2` family and the signed-word order |
| `positFunctions` | `oracles/posit_functions.py` | a decoder and rounder on `Fraction` written from sections 4.1 and 5 of the Posit Standard, with MPFR directed enclosures for the elementary functions and the quire |
| `positConversions`, `positIEEE` | `oracles/posit_conversions.py`, `oracles/posit_ieee.py` | exact rational conversion between widths, text, integers and IEEE formats (sections 6.1 and 6.3 to 6.5) |
| `ofp8Standard` | `oracles/ofp8.py`, `oracles/ofp8_secondary.py` | gfloat's encodings, and microxcaling's saturating conversion and PyTorch's casts |
| `blockStandard` | `oracles/mx_standard.py`, `mx_element.py`, `mx_dot.py`, `mx_finite_dot.py`, `nvfp4.py` | gfloat and microxcaling for MX blocks and elements, exact fractions rounded once by MPFR for the dot products, and CPU torchao for NVFP4 |
| `p3109Comparison`, `p3109Functions`, `p3109Queries`, `p3109Blocks`, `p3109BlockFunctions` | the scripts of the same names in `oracles/` | the formulas of the interim report v4.1 on `Fraction`, MPFR directed enclosures for the functions, and gfloat 0.5.2 for the queries and the small-word block operations |
| `oracle p3109-kernel` | `oracles/p3109_kernel.py` | the operations of sections 4.10 to 4.13 and 4.16 of the interim report v4.1 on `Fraction`, and the conversion of a binary interchange word decoded from its fields, projected by the reference of `p3109_comparison.py` |
| `embeddedFixedPoint`, `embeddedText`, `embeddedConstant`, `embeddedFormatted` | the scripts of the same names in `oracles/` | exact `Fraction` arithmetic, regular expressions and an independent automaton for the text conversions, and Clang's fixed-point types |
| `oracle complex` | `oracles/complex_mpc.py`, `oracles/complex_cmath.py` | GNU MPC through gmpy2 in every rounding direction, and CPython's `cmath` for the special values of C23 Annex G |

Each script says what it needs with `--help`. The run of 2026-11-18 (Lean v4.36.0) had no
unexplained difference:

| Family | Cases |
| --- | --- |
| Posit operations | 508 per unary operation and 87,376 per binary operation, fused multiply-add or comparison; for the quire 567 quire-minus-quire, 4,572 quire-minus-posit and 49,104 each for multiply-add and multiply-subtract |
| P3109 | 9,818,928 projections, 635,040 elementary-function projections and 7,278,336 block cases |
| OFP8 | every code decoded, 262,144 conversions each from binary16 and bfloat16 and 19,768 from binary32 |
| OCP MX and NVFP4 | 75,240 and 368,603 |
| Embedded C fixed point | 1,196,256 interface cases, with 160,196 ordinary and 409,536 policy comparisons |
| Complex functions | 10,944 MPC comparisons in binary16, bfloat16, binary32 and binary64, and 1,673 `cmath` references: 1,648 agreements, 19 signs that C23 leaves unspecified and six values that C23 requires where `cmath` returns NaN |
| Complex functions at small arguments (run of 2026-11-19, `--styles small,wide --hard`) | 234,744 MPC comparisons of sixteen functions: 117,372 in binary64 in six rounding directions, and 58,686 each in binary32 and binary16 in three |
| Complex powers (run of 2026-11-19, `--functions pow --modes all --samples 600 --hard`) | 60,204 MPC comparisons in six rounding directions: 20,364 in binary64, 20,364 in binary32 and 19,476 in binary16, with bases next to an axis, perturbed perfect powers, bases whose parts have the least ratio of the format, even powers of a base on a diagonal and exponents up to `2^90`. No difference and no power without a certificate; 12 results are not compared, two exactly real powers in six directions on which MPC at two precisions disagrees |

Two differences from a reference are known, and in both FloatLib has the result of the exact
specification. One is `nearestInt` of the eight-bit posit word 129: the word denotes the integer
`-2^24`, so the operation returns it unchanged
(`tests/FloatLibTests/Conformance/Posit/Standard.lean` proves it). The other is an input
negative zero in the finite saturating conversions to OFP8 and to the MX floating-point
elements, where the result keeps the sign. The NVFP4 comparison covers the modelled format with
a finite positive outer binary32 scale. It says nothing about a GPU implementation or about
stochastic hardware behaviour.

## Status labels

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

## Limits of the `release` profile

The suites of the `release` profile have these coverage limits:

| Area | Coverage limit |
| --- | --- |
| Representations | No IEEE decimal32/64/128 or binary80 explicit-integer-bit comparisons |
| Rounding and conversion | Not every floating-point/integer policy; no nearest-away, round-to-odd, tininess-before-rounding, or universal NaN payload-selection rule |
| P3109 and OCP MX | Representation tables do not establish complete P3109 arithmetic or exception handling, OCP MX block operations or scaling, saturation, or hardware FP8 interoperability |
| Certification | Table agreement is not IEEE certification; no official posit certification |
| Transcendentals | No global correct-rounding or real-error theorems for all transcendentals |
| Linear algebra | No optimized verified BLAS implementation |

The comparisons outside the profile that this page describes (the IEEE 754-2019 additions with
their decimal cases, the standards' operations, the block-scaled formats) cover some of these
areas. Even exhaustive testing at one finite width can't establish a theorem over every descriptor,
and scalar arithmetic checks don't give you a verified GEMM implementation.

When a comparison finds a bug, we isolate it in scratch space and then fix the general specification
or implementation. The [testing guide](README.md#checking-a-change) says where those experiments go.
