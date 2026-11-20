# Execution backends

We often have several ways to compute the same `x + y`: a lookup table, a word kernel, or exact
arbitrary-precision arithmetic. This directory connects those implementations to their format's
specification. No candidate reaches the planner's cost comparison without a proof of
`run = spec`.

`Numerics` supplies the exact values and contracts, `Kernels/` supplies shared integer
algorithms, and the backends here apply those algorithms to a format. `Compiled/Dispatch` tries
a specialized kernel first and falls back to the exact baseline when the kernel declines an
input. A `Capability` lets the planner choose among these certified implementations, and that
choice is the only step that uses a cost model.

## Layout

The code is sorted by the mode an implementation serves.

| Where | What it holds |
| --- | --- |
| [`FloatLib/Tactic/`](../../../Tactic/CompilerOptimize.lean) | the two tags, `@[compiler_optimize]` ([`CompilerOptimize.lean`](../../../Tactic/CompilerOptimize.lean)) and `@[kernel_optimize]` ([`KernelOptimize.lean`](../../../Tactic/KernelOptimize.lean)), `float_decide`, `#kernel_eval`, `#kernel_cost`, `#kernel_rules`, `#compiler_backends`, the commands that declare a family's capabilities, and the forms that write a definition the way Lean's kernel evaluates it best (`kernel_inline%`, `kernel_shape`, `kernel_constant`, `kernel_refl%`). The checks that a tagged implementation is proved and that its compiled code is the code of its definitions are in [`Util/Provenance.lean`](../../../Util/Provenance.lean) |
| [`FloatLib/Kernels/Selection/`](../../../Kernels/Selection/Policy.lean) and [`Execution/`](../../../Kernels/Execution/Capability.lean) | the planner (policy, scoring, portfolio, report) and the capabilities, certificates and dispatch that every family shares |
| [`Compiled/`](Compiled/) | the certified kernels for compiled code: the dispatchers (`Dispatch/`) and `TinyTable/`, `Word/`, `FixedLimb/`, `WideLimb/`, `Generic/` |
| [`Kernel/`](Kernel/Form.lean) | what Lean's kernel needs that is not tied to one family: the kernel form of a family's operation and the rules that rewrite a public operation to it (`Form`: `KernelForm`, `DirectReference`), the loop rules (`Loop`), the rules of exact arithmetic (`Exact`), of lists, arrays and options (`Plumbing`), and of the integer square root (`Root`) |

A family keeps its own kernels in its own directory: the kernel operations of the binary formats
are in `Formats/BinaryInterchange/KernelPath/`, those of the decimal formats in
`Formats/DecimalInterchange/KernelPath/`, those of posits in `Formats/Posit/KernelPath/`, and those
of P3109 in `Formats/P3109/KernelPath/`.

[`Tactic/KernelPrepare.lean`](../../../Tactic/KernelPrepare.lean) provides `kernel_prepare% e`.
It applies the registered equations once and returns the rewritten expression
with its equality to `e`. Storing this pair in a definition avoids repeating
the same preparation at each call. P3109 shares three such functions across arithmetic: exact
decoding, rational projection and square-root projection, with arbitrary descriptors and
policies. The generated proof passes the ordinary kernel check; preparation
introduces no additional trusted evaluator.
[`Kernel/Root.lean`](Kernel/Root.lean) registers the shared proved integer
square-root replacement; its checked candidate and fallback equal `Nat.sqrt`
for every natural input.

## Backend tags

An implementation is registered by a tag, for the mode it serves, together with its proof.

* `@[compiler_optimize]` goes on a definition of a `Backend.Certified spec` (or an `Option` or a
  `List` of them): a compiled kernel with its estimate and the proof `run = spec`. Instance
  search collects every tagged candidate whose specification matches a format
  (`Backend.Portfolio spec`), and the planner selects among them and the family's own
  candidates. `@[compiler_optimize baseline]` and `@[compiler_optimize direct]` mark the
  candidates that a family names in its capability.
* `@[kernel_optimize]` goes on a theorem `reference = implementation`: an implementation on
  natural-number encodings for Lean's kernel. `float_decide` rewrites with the tagged equations,
  the one with the lowest declared cost first. `@[kernel_optimize ←]` tags a theorem stated
  `implementation = reference`, as the equations of `Numerics.Kernel` are. The packed tables of a format of at most eight
  bits are such implementations: `kernel_tables` declares them with their rules, and importing
  the module that holds them (`Formats.OCP.FP8.KernelTables` for E4M3 and E5M2) makes
  `float_decide` look a sum, difference or product up.

Both tags refuse a declaration without a complete proof: a definition with no equation, a
statement that is not an equation, a term that is not a certified implementation, and a proof
that uses `sorry` or an axiom beyond the standard three (`Provenance.requireProved`).
`@[compiler_optimize]` also refuses a candidate whose code is not the code of its definitions
(`Provenance.requireCompiled`): a definition it calls that carries `@[implemented_by]` or
`@[extern]` outside Lean's own library needs a registered `@[replacement_proof]`, a theorem
`replacement x = definition x` for all arguments. The check follows the definition bodies that
the tagging module can read. It does not verify the machine code that the compilers produce.

A candidate tagged in any module is used by every format it covers in the modules that import
it, with no edit to the family. A family without a static form builds its capability from the
portfolio of tagged candidates, which it takes as an instance argument (`Capability.ofTagged`),
so the collection happens where an operation is written. A format whose arithmetic has a static
form (binary32 and binary64, the built-in carriers, the byte families, the posit carriers)
declares that form as a `Capability.Static`, and instance search decides what runs
(`Capability.ofStatic`): the static kernel itself where it proves that no tagged candidate
applies, with the same generated code as a capability declared directly, and the planner's
choice among that kernel and the tagged candidates otherwise.
`#compiler_backends` and `#kernel_rules` print the two registries.

The six operations of a family differ in the operation only, so each family writes its
capability once as a command and lists the operations, one line each.
`portfolio_capability Op op FormatType`
([`Tactic/PortfolioCapability.lean`](../../../Tactic/PortfolioCapability.lean)) declares the
capability of a family on any carrier. The static forms have a command in the
module that holds them: `native_capability` for binary32 and binary64, `automatic_capability`
and `limb_capability` for the built-in carriers, `byte_capability` and `byte_table_capability`
for the byte families, `plan_capability` and `planned_capability` for the posit carriers, and
`fixed_format`, `first_order` and `candidate_set` for the certificates and candidate sets of
the configured binary planner. Each generated declaration has the name and the docstring it
would have written by hand.

The exact dyadic fallback is executable too. We import the
[rounding proof](../../Formats/BinaryInterchange/Dyadic/RoundingKernel/Proof.lean) into the
[dyadic specification](../../Formats/BinaryInterchange/Spec/Dyadic.lean) before defining
addition, subtraction, multiplication, and FMA, so their compiled rounding uses bulk integer
shifts and nearest-even rounding at every width while keeping the descriptor's encoding
policies. Order matters here, because a compiler substitution applies when a caller is
compiled, and importing a proof later won't rewrite functions that were already compiled.

## Backends

Eligibility is a decidable proposition on the descriptor's fields, so a custom
`ExecFloat.Binary` with the same layout gets the same backend as a named format. You can't
select the shared word pieces (`Word/NormalPair`, `ProductRound`, `Quotient`, `ModelSqrt`) on
their own. The directories of the first eight rows are under `Compiled/`.

| Directory | Class | Eligible | Ops | Status |
| --- | --- | --- | --- | --- |
| `TinyTable/` (tables built in `Configured/ByteTable/`) | exhaustive table | ≤ 8 encoded bits | six | proved |
| `Word/Small/` | native-word | IEEE ≤ 64 bits; operation-specific fraction caps | six | proved |
| `Word/TwoWordMul/` | via fixed-limb route | IEEE ≤ 64 bits, 32–62 fraction bits | mul | proved |
| `Word/Narrow/` | fixed-format | exactly binary32 | six | proved |
| `Word/Full/` | fixed-format | exactly binary64 | six | proved |
| `FixedLimb/Pair/` | two `UInt64` limbs | IEEE, `64 < fracWidth`, `bitWidth ≤ 128` | six; sqrt declines some layouts, and FMA every layout with more than 120 fraction or 32 exponent bits | proved |
| `WideLimb/` | 32-bit limbs | IEEE > 128 bits, exponent ≤ 32; `ExecFloat.BinaryLimbs` | six; div/sqrt use integer arithmetic | proved |
| `Generic/` | exact baseline | every binary descriptor | six | proved |
| `Configured/NativeFPU/Unchecked.lean` | not a planner class | binary32/64, explicit call site | add, sub, mul, div, sqrt (not fma) | unchecked |
| `IEEE754/Native/Half.lean` | separate native carriers | binary16 and bfloat16 | binary32 arithmetic followed by word rounding; elementary functions | proved narrowing, widening and normalization; unchecked arithmetic |

The second unchecked path supplies `FloatLib.Floats.Native.Half` and `BFloat16`. Their addition,
subtraction, multiplication, division and square root rely on the host `Float32` behaving as IEEE
binary32 and on the Figueroa double-rounding argument: binary32's 24 significand bits meet the
`2p + 2` condition for both narrow precisions. These arithmetic claims are checked against the
software models, not proved in Lean: the four operations, square root, negation and the
comparisons on random words, and the four operations on every pair of bfloat16 words of the two
lowest exponent fields, where the binary32 intermediate is subnormal. Native transcendentals
have no correctly-rounded guarantee.

Both word conversions are proved. `Native.Carrier.val_eq_spec` states that widening is the
binary32 word of the reference cast, from the law `Format.widen_eq` that each layout proves
(`Word.widenHalfWord_eq_cast` and `Word.shiftLeft_eq_cast` check all 65,536 words in Lean's
kernel). `Native.Word.roundWord_eq_spec` relates the kernel cast to
`Model.cast` for every pair of descriptors, and `roundWord_toNat` shows that a destination of at
most 64 bits is stored without truncation. `Native.Carrier.ofWord_eq_spec` applies that cast and
the carrier's NaN normalization for every 16-bit layout. `ofFloat32_eq_spec` and `ofFloat_eq_spec`
specialize it to the host interchange words; the latter rounds directly from binary64, avoiding
an intermediate binary32 rounding. The normalization theorems `ofBits_toBits`, `toBits_ofBits`
and `toBits_ofBits_nan` remain independent of host arithmetic. These carriers are exported by
`IEEE754` and `FloatLib`; they do not enter the certified planner.

[AutomaticDispatch.lean](../../../../tests/FloatLibTests/Conformance/Execution/AutomaticDispatch.lean)
checks the balanced-policy selections below.

| Type | Selected (balanced policy) |
| --- | --- |
| `Binary32` | all six = fixed-format |
| `Binary64` | all six = fixed-format |

Selection picks a certified operation, but that operation can use the exact fallback for
individual inputs. Wide-limb multiplication and FMA, for example, require normal operands and
check the result's leading position both before rounding and after the rounding carry. So a
value just below the normal range can take the fallback even when it would round to the smallest
normal value. FMA's alignment core accepts exact cancellation as positive zero.

The exact fallback, the generic baseline and the directed kernels add operands that lie far apart
in exponent with `Model.addDyadicForRounding`, which folds the far operand into a sticky bit before
rounding and is proved to round like the exact sum. So addition, subtraction and FMA also run on
exponent fields of 32 bits and more, where an exact sum can be wider than any shift the runtime
supports. The operations with status flags (`(status := true)`) and the quantization-policy
arithmetic of `Model.Policy`, stochastic rounding included, still form exact sums and rationals,
so on such formats they can exhaust memory or stop with a panic.

Posits use `Formats/Posit/Configured/Backend/` with the same `Certified` / `PolicyFor` machinery.

`#float_info T` prints the selection, and `#float_info! T` adds its scores. Inside Lean, you can
get the same information from `ExecFloat.Add.selectedCandidate (F := F)` and
`Backend.selectionReport`.

## Policy

Our default, `Backend.Policy.default`, estimates 100,000 calls and allows 1 MiB of resident
memory. A scoped policy lets you favor lower setup cost or sustained throughput:

```lean
open scoped FloatLib.Floats.ExecFloat.Backend.PlanningLatency     -- one call; skip table setup
open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput   -- 5M calls, 16 MiB ceiling
```

A local `PolicyFor` instance can retune one family. Because the equality `run = spec` holds for
every candidate, changing that choice keeps the same values, literals, and arithmetic theorems.
Binary32/64 use proved software under every policy. If you want the host FPU, import
`FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked`, which `import FloatLib`
does not load, and call its operations by name:

```lean
open FloatLib.Floats.Formats.BinaryInterchange.Configured in
NativeFPU.Unchecked.add32 x y
```

These host operations have no `Backend.Certified` proof, so they can't supply a scoped
`ExecFloat.Add` instance.

## Adding a backend

The one-word kernels are a good model to copy when you add an implementation. We keep runtime
code apart from its proofs, and every compiler substitution is justified by a proved equation:
a `@[csimp]` theorem, or for the one `@[implemented_by]` in the library, the posit decoder, the
theorem registered with `@[replacement_proof]`.

1. **Eligibility.** State a decidable `Prop` on descriptor data. Writing the decision out, as in
   `if h : … then isTrue h else isFalse h`, makes the supported layouts easy to read.
2. **Kernel.** Put the implementation in `Runtime.lean`, with runtime imports only, and reuse
   `FloatLib/Kernels`. When the kernel returns `none`, the dispatcher falls back to the exact
   operation.
3. **Proof.** Prove the successful-result equation in a sibling `Proof.lean`, for example
   `kernel? x y = some r → r = Model.Spec.add x y`.
4. **Total operation.** Fall back to the reference where the kernel declines,
   `run x y = (kernel? x y).getD (Spec.add x y)`, and prove `run = spec` from step 3. The
   built-in word kernels share one dispatcher per operation in `Compiled/Dispatch/`; a tagged
   candidate needs no branch there.
5. **Certificate.** Supply a `Backend.Candidate` estimate and package the kernel with
   `Certified.binary` (or `unary`, `ternary`), stated for every format the kernel covers and
   returning `none` or `[]` for the formats it declines.
6. **Registration.** Tag the certificate `@[compiler_optimize]`. Every format whose reference
   operation matches the certificate's specification then considers it, in each module that
   imports yours, and runs it when the planner prefers it under the policy in scope. For a
   kernel on encodings for proofs by evaluation, tag the theorem `reference = implementation`
   with `@[kernel_optimize (cost := n)]`.
7. **Tests.** Put expected selections in `tests/.../AutomaticDispatch.lean` and codegen scripts
   under `benchmarks/scripts/checks/`. Measure with `execFloatBackendCalibration`, then compare
   against your reviewed same-machine baseline with
   `PERF_BASELINE_DIR=/path/to/baseline benchmarks/scripts/performance-regression.sh check`. The
   [calibration guide](../../../../benchmarks/docs/Calibration.md) explains how to record a
   baseline. Change a cost prior only after three isolated trials beat the selected candidate.
