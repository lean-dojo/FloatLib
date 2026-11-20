<h1 align="center">
  <img src="site/content/assets/floatlib-logo.png" alt="FloatLib logo" width="88" align="center">
  Verified Floating-Point Arithmetic in Lean
</h1>

FloatLib is a Lean 4 library for arbitrary precision floating-point arithmetic and verified
numerical computation. It provides executable operations, numerical specifications and
proofs connecting them, together with rounding theorems, error bounds and numerical proof
automation.

The library supports IEEE binary and decimal formats, posits with exact quire accumulation,
and low precision formats for machine learning. Shared integer kernels and numerical
interfaces support custom formats and rounding rules. The specifications include signed
zeros, infinities, NaNs and exception flags.

You can prove a concrete floating-point result by running the calculation in Lean's kernel.
Try the [binary32 example below](#a-calculation-and-a-proof), or read
[Speeding up computation in Lean's kernel](https://lean-dojo.github.io/FloatLib/#/chapter/proof-by-computation)
for proofs about arithmetic, rounding flags and whole tables of encodings. If you're new to
FloatLib, the [first chapter](https://lean-dojo.github.io/FloatLib/#/chapter/using-the-library)
covers installation and your first calculation.

## Installation

From a checkout of this repository, fetch the Mathlib cache and build FloatLib:

```bash
lake exe cache get
lake build
```

Use the Lean version in [lean-toolchain](lean-toolchain). Everything else is pinned in
[lake-manifest.json](lake-manifest.json), so you get the same dependency versions we use.

In your own Lake project, add FloatLib with `require`:

```lean
require floatlib from git
  "https://github.com/lean-dojo/FloatLib.git" @ "main"
```

Then run `lake update`, `lake exe cache get` and `lake build`. For the toolchain and your
first file, see the
[project setup instructions](https://lean-dojo.github.io/FloatLib/#/chapter/using-the-library/how-to-set-up-a-project).

## A calculation and a proof

Like Lean's `native_decide`, the `float_decide` tactic proves a closed goal by computation.
It rewrites floating-point operations using proved equations and runs `decide +kernel`, so
Lean's kernel checks the arithmetic itself.

```lean
import FloatLib

open FloatLib.Floats

#eval (1.5 : Binary32) + 2.25  -- 3.75
example : (1.5 : Binary32) + 2.25 = 3.75 := by float_decide
```

On a 1,000-term binary64 dot product, Lean's kernel checked the loop in 152 ms, compared
with 730 ms for Flocq under Rocq's `vm_compute`. On a separate integer square-root proof,
FloatLib's exact arithmetic took 11.5 ms with `decide +kernel` and 13.1 ms with
`native_decide`. See the [floating-point timings](benchmarks/results/kernel/README.md#three-theorems-about-loops-of-1000-steps)
and [exact arithmetic timings](benchmarks/results/exact/native.md).

## What you can work with

- **Proof by computation.** `float_decide` proves closed, decidable statements by rewriting
  supported operations to equivalent computations on their encodings. For example, the kernel
  can check a binary addition together with its rounding flags. The rules reach nearly every
  operation of IEEE 754-2019 on binary and decimal formats, the conversions to and from
  character sequences, the augmented operations and the reductions among them. They also
  cover posit arithmetic, the P3109 operations and the OCP MX and NVFP4 quantizers. The
  certified functions of clause 9.2 are the main exception. `lane_decide` proves equalities
  of supported natural-number expressions over all pairs of small finite indices. It evaluates
  each side once with all input pairs packed together. The
  [guide](https://lean-dojo.github.io/FloatLib/#/chapter/proof-by-computation) gives examples
  and lists the operations with kernel rules for each format.
- **Backend registration.** Tag a proved equation with `@[kernel_optimize]` to make it available
  to `float_decide`, or tag a certified implementation with `@[compiler_optimize]` to make it
  available to the compiled planner. Both require a complete proof using only Lean's three
  standard axioms. `#kernel_rules` and `#compiler_backends` list the available implementations.
- **Exact arithmetic in the kernel.** `Numerics.Kernel` provides integers, rationals, dyadics
  and real and complex enclosures for checking numerical certificates. Its arithmetic operations
  have proofs relating them to ordinary arithmetic. The packed-row operations can check a dot
  product or a polynomial product by multiplying two natural numbers.

- **Native 16-bit carriers.** `Floats.Native.Half` and `BFloat16` store binary16 and bfloat16
  words. Their conversions are proved: narrowing from any format, widening to binary32 and NaN
  normalization agree with the reference cast. Their arithmetic is the host's binary32
  arithmetic rounded once more; it is tested against the software models, not proved.
- **IEEE binary and decimal.** Binary arithmetic handles subnormals, signed zeros, infinities,
  NaNs, rounding modes and status flags. Decimal32, decimal64 and decimal128 come in both the
  BID and DPD encodings, with arithmetic, conversions and rounding proofs. You can call an
  operation by the name IEEE 754-2019 gives it, such as `roundToIntegralTiesToEven`,
  `compareQuietLess` or `augmentedAddition`, and
  [a table in the guide](https://lean-dojo.github.io/FloatLib/#/chapter/ieee-binary-formats/where-is-each-operation-of-ieee-754-2019)
  maps the required operations of clause 5 and the recommended families of clause 9 to
  their binary and decimal implementations. It lists the available theorems and identifies
  gaps by format. The augmented operations, the minimum and maximum by magnitude, the NaN payload
  operations and the reductions `sumAbs`, `sumSquare` and the scaled products are there, and so
  are the formatOf operations, where the operands and the result may have three different
  formats and the exact result is rounded once.
- **Posits and quires.** Pick a total width with `ExecFloat.Posit (bits := n)`. Its quire,
  `ExecFloat.Posit.Quire (bits := n)`, is an exact accumulator: it adds up products with no
  rounding as long as they fit its capacity, and rounds once at the end. We follow the 2022
  posit standard, and the operations carry its names. The standard fixes two exponent bits.
  The operations on encodings underneath take that number as a parameter and are proved for
  every value of it, so the kernel also computes with posits of another exponent size, such
  as SoftPosit's 8-bit and 16-bit types.
- **Small and custom formats.** FP8, FP6, FP4, fixed point, logarithmic and codebook
  representations all share the same numerical interfaces. Block-scaled formats are one
  definition with OCP MX, NVFP4 and Four Over Six as instances, for any element format, scale
  format, block shape and scale-selection rule, and the executable OCP MX and NVFP4 quantizers
  are proved to compute the real formats the theorems are about. A deployed NVFP4 quantizer
  works in binary32 instead of exact rationals, so `Block.nvfp4Working` is that computation on
  binary32 encodings, in torchao's order of operations, with theorems for the stored scale and
  elements that need no premise about overflow. It is one instance of a quantizer for any
  block and any binary working format. OCP's two FP8 formats are
  `E4M3` and `E5M2`, as OFP8 spells them, with saturating and non-saturating conversion. An MX
  dot product can keep its intermediates exact or run in a finite accumulator you name, and the
  second comes with an error bound. Fixed point follows Embedded C (ISO/IEC TR 18037), as one
  family over layout, rounding and overflow policy. P3109 gets
  [its own chapter](https://lean-dojo.github.io/FloatLib/#/chapter/low-precision-formats-for-machine-learning/what-is-ieee-p3109),
  which explains the working group's format rules and the report our implementation follows.
- **Classical rounding results.** Correct rounding, half-ulp error bounds and Sterbenz's
  exact-subtraction lemma tie the real-valued theory to the arithmetic that runs.
  Mixed-precision bounds cover casts, products and accumulator updates, under their stated
  finiteness assumptions.
- **The `roundoff` tactic.** With the `Tactic.Roundoff` import, the tactic proves error bounds
  for configured computations, loops over lists, arrays, vectors and matrices included.
  `MixedError` propagates relative and absolute error bounds through binary operations, casts
  and sums. The `roundoff theorem` and `roundoff mixed theorem` commands generate a theorem and
  its proof, with the required range conditions as hypotheses.
  `roundoff (backward := true) theorem` generates a backward-error theorem instead: the computed
  value is within an absolute underflow allowance of the exact computation on inputs
  `x * (1 + δ)`, with a bound on each `δ` and the allowance read off the code. The equality is
  exact where no operation can underflow. `roundoff closed theorem` generates the forward bound
  in closed form. The commands read a `match` alternative by alternative, and they read a
  program on Lean's own `Float` and `Float32` as the same program on `Binary64` and `Binary32`.
  A subtraction that your hypotheses make exact (Sterbenz) is charged nothing. `#roundoff_check`
  runs a generated theorem at inputs and warns you when its bound is too large to fix the sign
  of the result. See the
  [roundoff guide](https://lean-dojo.github.io/FloatLib/#/chapter/proving-numerical-bounds/how-to-get-an-error-bound-for-floating-point-code).
- **Stochastic rounding.** We prove the law of one stochastic rounding once: the mean is the
  input and the variance is at most a quarter of the squared spacing. The executable rounder,
  which compares `entropy % denominator` with a remainder, is proved to follow that law when the
  denominator divides the entropy range. `roundoff stochastic theorem` then generates the mean,
  second moment, tail bound and confidence radius of a sum, a dot product or an affine map that
  draws fresh entropy at every rounding. See
  [the guide](https://lean-dojo.github.io/FloatLib/#/chapter/proving-numerical-bounds/fresh-stochastic-rounding).
- **Intervals and affine quantization.** One interval API takes binary, decimal, posit and
  custom endpoints, each with a stated outward-rounding contract. The
  [`interval` tactic](https://lean-dojo.github.io/FloatLib/#/chapter/proving-numerical-bounds) proves real
  inequalities, elementary functions included, by certified evaluation and subdivision. It also
  proves that a set of constraints has no point: the goal `False` from hypotheses,
  `¬ ∃ x, P x`, or any combination by `∧`, `∨`, `¬` and `→` of comparisons. A compiled search
  writes a tree of boxes and the kernel checks it in one evaluation, and quadratic forms decide
  the points where a margin is zero, such as the equilibrium of a Lyapunov function. A variable
  bounded on one side only has a range with an infinite end, and the enclosures work on it. A
  comparison in one variable whose two sides meet at an end of the range, such as
  `1 + x ≤ Real.exp x` at zero, is decided by the sign of a derivative, and `∃ x : ℝ, P x` by
  a witness that the tactic finds. On the 169 goals of four projects' test suites it
  closes 161. Affine quantization has a real-valued specification with a rounding rule you
  supply, plus a proof connecting nearest-even quantization to the executable rational
  implementation. See the
  [guide](https://lean-dojo.github.io/FloatLib/#/chapter/proving-numerical-bounds/how-to-prove-that-constraints-have-no-common-point).
- **Bounds from coefficients.** The same `interval` tactic proves bounds over a whole domain
  from coefficients: trigonometric polynomials with cosine and sine terms on the circle, power
  polynomials on intervals with rational endpoints, Chebyshev series after affine rescaling, and
  norms of polynomials on the unit circle of `ℂ`, with rational coefficients or the exact values
  of float data. Lean's kernel checks sum-of-squares certificates using packed integer rows.
  Wiener algebra defect theorems also bound the errors of approximations to inverse and inverse
  square root functions. See
  [the coefficient guide](https://lean-dojo.github.io/FloatLib/#/chapter/proving-numerical-bounds/how-to-bound-a-polynomial-on-the-whole-circle).
- **Repeatedly rounded sums.** A reduction tree fixes the order of the additions, and its error
  bounds account for rounding at every node, absolute-error terms near underflow included. The
  bound grows with the depth of the tree, `((1 + u) ^ depth - 1)` times the sum of the
  magnitudes, so pairing `n` terms pays for `⌈log₂ n⌉` roundings where the plain loop pays for
  `n - 1`. For a sum that rounds only once, use the exact accumulators. IEEE 754-2019 lets a
  reduction associate in any order and accumulate in any wider format, so `sumInOrder` and
  `sumAlong` take the accumulator format and the order as arguments, with an error bound for
  every order. For a left-to-right, nearest-even sum of `n` terms in an IEEE format, starting
  at zero and ending with a finite result, the error is at most `(n - 1) u` times the sum of
  their magnitudes (Rump). For a dot product the factor is `n u` on the sum of the absolute
  exact products, provided each exact product is zero or in the normal range (Jeannerod and Rump).
- **Elementary functions and complex numbers.** Posit elementary functions are proved to return
  the correctly rounded real result. For IEEE binary formats, `ExecFloat.Binary.Certified.exp`,
  `log`, `pow`, `expm1` and `logp1` return a correctly rounded finite result when rational
  enclosure refinement succeeds, and tell you why when it doesn't. Import
  `Configured.CorrectlyRounded` and you get total `ExecFloat.Binary.CorrectlyRounded.exp`,
  `log`, `expm1`, `logp1` and `expMul`, correctly rounded on IEEE formats with no premise on the
  search budget, plus the other functions that IEEE 754-2019 recommends (`exp2`, `log10`,
  `sinPi`, `atan2`, `pow`, `powr`, `compound` and the rest). For finite inputs in the theorem's
  domain, each result is the real function rounded once in the rounding direction you ask for,
  in all five IEEE directions, so the upward and downward results are the closest representable
  values on their side. On configured values that theorem is stated for the functions of one
  argument. `atan2`, `atan2Pi`, `pow`, `powr` and `compound` are the descriptor-model functions
  through the storage codec, and their theorems are stated on the descriptor model. The
  descriptor model has every function of clause 9.2 in this form,
  `exp`, `log`, `rSqrt`, `hypot`, `rootn` and `pown` included, with exception flags, and the
  theorem also holds for the eight-bit formats OCP E5M2 and E4M3. Decimal formats have the same
  functions with flags in five directions, and P3109 formats in every rounding and saturation
  mode. `Configured.Transcendentals` brings deterministic approximations for a
  wider set of binary functions. We haven't proved general error bounds for those approximation
  kernels, but they match MPFR on every case of the elementary-function test tiers. Sine and
  cosine can return an invalid result if they run out of argument-reduction budget. For
  IEEE-style descriptors, that import's `pow` of a positive base is correctly rounded whenever
  its enclosure search settles, and its `pi` is correctly rounded. `ExecComplex` gives you
  arithmetic on pairs of binary components, with theorems that track the scalar rounding and
  bounds for the whole operation: the product is within `√5 u |xy|` of the exact one (Brent,
  Percival and Zimmermann), within `2u |xy|` with fused multiply-adds, both up to an underflow
  term, and the ratio division within `√2 γ₇ |x/y|` when no intermediate underflows. Under
  `Complex.Elementary`, the complex `exp`, `log`, `sqrt`, `rsqrt`, `expm1`, `log1p`, the six
  trigonometric and hyperbolic functions and their inverses are correctly rounded in every
  rounding direction at every finite argument, with the special values of C23 Annex G. For a finite nonzero
  base and a finite exponent in an IEEE format, `pow_eq` proves correct rounding when
  `powCertified` returns `true`. Use `powChecked` to get the value and that flag together. You can see them in use in the
  [examples](FloatLib/Examples/Transcendentals.lean) and the
  [complex section](https://lean-dojo.github.io/FloatLib/#/chapter/ieee-binary-formats/how-to-work-with-complex-numbers).

Our [theorem index](FloatLib/Floats/THEOREMS.md) collects the major theorems. Like other
formalization projects, we keep a [formalization.yaml](formalization.yaml) that lists the
mathematical sources, scope, and key results. It also says how we used AI: we spent several
months planning the library and building its foundations, and Codex helped us finish some of
the proofs and optimize the arithmetic backends.

## Limitations

FloatLib has every operation that the notes of the 754 working group list for IEEE 754-2019,
for binary and for decimal formats, and
[the table in the guide](https://lean-dojo.github.io/FloatLib/#/chapter/ieee-binary-formats/where-is-each-operation-of-ieee-754-2019)
names the theorems of each. The conformance predicate `is754version2019` still answers `false`,
because these parts are tested against references and not proved:

- **The special cases of the functions of clause 9.2.** On binary formats the value in every
  rounding direction, its sign and the overflow result are proved at finite operands in the
  domain. So are the five flags, for every function, `cbrt` as the `rootn` of degree three that
  it is: `inexact` for a finite result, `invalid` and `divideByZero` clear, and where the real
  value is not zero `overflow` by the rule of clause 7.4 and `underflow` by the rule of clause
  7.5 with tininess detected after rounding. Tininess is stated by the boundary of each
  direction, the one of the arithmetic operations, and is not derived from a rounding function
  with an unbounded exponent range. Where the real value is zero the result is proved to be a
  zero, and `overflow` and `underflow` have no theorem there. The results at infinities, NaNs
  and outside the domains are definitions without a theorem. For decimal formats the theorem
  covers the five flags at finite operands in the domain, and the same special cases are
  definitions.
- **The formatOf operations across formats.** In one format they are proved to be the
  operations of that format for every operand, with flags and ternary value. Across formats the
  value is proved for finite operands: in every direction for addition, subtraction,
  multiplication and fusedMultiplyAdd when the exact result is in the range of the destination,
  and to nearest-even for division. The quotient in the other directions, the flags and the
  special cases across formats are compared with the rules of the standard on every pair of
  encodings of a six-bit format. The formatOf square root is proved correctly rounded in every
  direction, and its flags other than `inexact` are compared the same way.
- **Configured values.** `ExecFloat.Binary.CorrectlyRounded` has the 30 recommended functions
  and `pow`. The forms with flags of `exp`, `expm1`, `log`, `logp1`, `rSqrt`, `hypot`, `rootn`
  and `pown` in every direction are functions of the descriptor model
  (`Model.Transcendentals.Directed`, `Model.Algebraic.Directed`).
- **Alternate exception handling.** FloatLib returns the exception flags as data. The
  attributes of clause 8 for alternate exception handling are not implemented.
- **P3109 extensions.** `Exp10`, `Log10`, `Cbrt`, `Rootn`, `Pown`, `Pow`, `Powr`, `Compound` and
  their siblings on P3109 formats are outside the interim report. They follow its conventions:
  one zero, one NaN, and NaN at a pole at zero.

## Speed and independent checks

We've put a lot of work into making the proved arithmetic fast, because we want MPFR's speed
without giving up the connection between the arithmetic and its proofs. Binary128, for example,
is stored in two machine words and has kernels of its own, so an operation doesn't split and
join GMP numbers. The
[planner](https://lean-dojo.github.io/FloatLib/#/chapter/performance) picks among lookup tables, word
kernels and wider limb algorithms, and every certified choice has to prove that it agrees with
the same specification. You can set the backend policy yourself, too. There's also a host-FPU
path, but it's unchecked and you have to call it by name.

For a single operation, rewriting brought kernel checking time down to 72 to 141 microseconds
on normal binary64 operands. At 4,096 bits, all six operations took at most 283 microseconds
on normal operands. The [chapter on kernel computation](https://lean-dojo.github.io/FloatLib/#/chapter/proof-by-computation)
gives the timings by operation and compares proof checkers.

On ordinary binary64 calls, FloatLib's proved addition, subtraction and multiplication beat
MPFR at the same precision, multiplication by about 2.4 times. Our
[benchmarks](https://lean-dojo.github.io/FloatLib/#/chapter/performance) compare scalar operations from 2 to 4,096
bits, so you can see where the kernels win and where MPFR is faster. Lean checks the proofs
before execution and erases them during compilation, so the compiled arithmetic does not
check proofs at runtime. To give every compiled declaration of FloatLib to Lean's kernel once
more, module by module, run the opt-in command
`FLOATLIB_RUN_INDEPENDENT_CHECKER=1 bash tests/verify.sh`.

A proof only shows that the code matches the specification we wrote, so we test the
specifications too, against other people's implementations. All **127,741,704** Berkeley
TestFloat level-1 vectors in our 210 campaigns matched on values and exception flags under
the reference's NaN comparison rules. The campaigns cover binary16, binary32, binary64 and
binary128, plus conversions involving bfloat16. Separate comparisons cover MPFR, decimal
arithmetic, small-format tables and posits. Our
comparisons with MPFX found four bugs in that library, which we've reported upstream. SoftPosit
disagrees with us on a small set of boundary cases, and
[the analysis](https://lean-dojo.github.io/FloatLib/#/chapter/external-validation/why-did-softposit-disagree-with-floatlib) works
through the calculations behind each side.

You can reproduce the external comparisons with the [testing guide](tests/README.md), or
measure your own machine with the [benchmark guide](benchmarks/docs/Comparison.md).
[TRUST.md](TRUST.md) lists everything a claim about FloatLib rests on besides Lean's kernel.

## Source files

To follow an operation down into its implementation and proof, start from the four main parts
of the library:

| Directory | What belongs here |
| --- | --- |
| [`FloatLib/Numerics`](FloatLib/Numerics) | Representation-independent meaning, exact arithmetic, contracts, enclosures, packed rows for kernel certificates, and coefficient bounds |
| [`FloatLib/Kernels`](FloatLib/Kernels) | Shared word and limb algorithms with refinement proofs |
| [`FloatLib/Floats`](FloatLib/Floats) | Concrete formats, real-valued rounding theory, executable operations, and their proofs |
| [`FloatLib/Tactic`](FloatLib/Tactic) | Tactics, commands and attributes: `roundoff`, `interval`, `float_decide`, the backend tags, `#float_info` |

Tests and benchmarks live in their own Lake workspaces, so importing the library never pulls
them in. The [website](site/) holds the guide, checked Lean examples, references, and
dependency graphs that show how the definitions and proofs fit together.

## Contributing

Thanks for your interest in FloatLib. If you have a format you want to add, a kernel you think
could be faster, or a proof that could be simpler, we'd love to hear from you :) You can
[reach out with questions or ideas](https://github.com/lean-dojo/FloatLib/issues).

FloatLib builds on Mathlib and follows its proof style and naming conventions, and the
[contributing guide](CONTRIBUTING.md) explains how to get started.

For a local check of the library and website:

```bash
bash tests/verify.sh     # build the library and run its checks
bash site/build.sh       # build the guide and check its examples
```

## License and credits

Thanks to the Lean, Mathlib, and Flocq communities, and to the authors of the libraries
used in our comparisons.

FloatLib's own code is [MIT licensed](LICENSE). See [third-party licenses](third_party/README.md)
for external code, data, and fonts.
