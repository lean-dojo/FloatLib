# Execution backends

We often have several ways to compute the same `x + y`: a lookup table, a word kernel, or
exact arbitrary-precision arithmetic. This directory connects those implementations to
their format's specification. Every candidate carries a proof of `run = spec` before
the planner compares its cost.

`Numerics` supplies the exact values and contracts, and `Kernels/` supplies shared integer
algorithms. The backends here apply those algorithms to a format. `Backends/Dispatch` tries
a specialized kernel and uses the exact baseline when the kernel declines an input.
A `Capability` lets the planner choose among these certified implementations; that choice
is the only step that uses a cost model.

The exact dyadic fallback is executable too. We import the
[rounding proof](../../Formats/BinaryInterchange/RoundDyadicImpl/Proof.lean) in the
[dyadic specification](../../Formats/BinaryInterchange/Spec/Dyadic.lean) before defining addition,
subtraction, multiplication, and FMA. Their compiled rounding uses bulk integer shifts and
nearest-even rounding at every width, preserving the descriptor's encoding policies. Compiler
substitutions apply when compiling callers; importing a proof later does not rewrite functions
that were already compiled.

## Backends

We determine eligibility from a decidable proposition on the descriptor's fields. A custom
`ExecFloat.Binary` with the same layout therefore gets the same backend as a named format. Shared word pieces
(`Word/NormalPair`, `ProductRound`, `Quotient`, `ModelSqrt`) are not separately selectable.

| Directory | Class | Eligible | Ops | Status |
| --- | --- | --- | --- | --- |
| `TinyTable/` (tables built in `Configured/ByteTable/`) | exhaustive table | ≤ 8 encoded bits | six | proved |
| `Word/Small/` | native-word | IEEE ≤ 64 bits; tighter caps on add/div/mul | six | proved |
| `Word/TwoWordMul/` | via fixed-limb route | IEEE ≤ 64 bits, 32–62 fraction bits | mul | proved |
| `Word/Narrow/` | fixed-format | exactly binary32 | six | proved |
| `Word/Full/` | fixed-format | exactly binary64 | six | proved |
| `FixedLimb/Pair/` | two `UInt64` limbs | IEEE, `64 < fracWidth`, `bitWidth ≤ 128` | six; sqrt declines some layouts | proved |
| `WideLimb/` | 32-bit limbs | IEEE > 128 bits, exponent ≤ 32; `ExecFloat.BinaryLimbs` | add, sub, mul, fma (else exact) | proved |
| `Generic/` | exact baseline | every binary descriptor | six | proved |
| `Configured/NativeFPU/Unchecked.lean` | not a planner class | binary32/64, explicit call site | add, sub, mul, div, sqrt (not fma) | unchecked |

The balanced-policy selections below are checked in
[AutomaticDispatch.lean](../../../../tests/FloatLibTests/Conformance/Execution/AutomaticDispatch.lean).

| Type | Selected (balanced policy) |
| --- | --- |
| `ExecFloat.Binary 8 23` | all six = fixed-format |
| `ExecFloat.Binary 11 52` | all six = fixed-format |

Selection chooses a certified operation, which can use the exact fallback for individual inputs.
For example, wide-limb multiplication and FMA require normal operands and check the result's
leading position before rounding and after rounding carry. A value just below the normal range
can therefore take the fallback even if it would round to the smallest normal value. FMA's
alignment core accepts exact cancellation as positive zero.

Posits use `Formats/Posit/Configured/Backend/` with the same `Certified` / `PolicyFor` machinery.

`#float_info T` prints the selection, and `#float_info! T` adds its scores.
The same information is available in Lean through
`ExecFloat.Add.selectedCandidate (F := F)` and `Backend.selectionReport`.

## Policy

Our default, `Backend.Policy.default`, estimates 100,000 calls and allows 1 MiB of resident
memory. Scoped policies let us favor lower setup cost or sustained throughput:

```lean
open scoped FloatLib.Floats.ExecFloat.Backend.PlanningLatency     -- one call; skip table setup
open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput   -- 5M calls, 16 MiB ceiling
```

A local `PolicyFor` instance can retune one family. The equality `run = spec` lets us change
that choice while keeping the same values, literals, and arithmetic theorems.
Binary32/64 use proved software under every policy. We also provide explicit host operations:

```lean
NativeFPU.Unchecked.add32 x y
```

The host operations have no `Backend.Certified` proof, so they cannot supply a scoped
`ExecFloat.Add` instance.

## Adding a backend

The one-word kernels provide examples of how we add an implementation. We separate runtime
code from its proofs and justify compiler substitutions with proved `@[csimp]` equations.

1. **Eligibility.** State a decidable `Prop` on descriptor data. An explicit decision such as
   `if h : … then isTrue h else isFalse h` makes the supported layouts clear.
2. **Kernel.** Put the implementation in `Runtime.lean` with runtime imports only, reusing
   `FloatLib/Kernels`. Returning `none` lets the dispatcher fall back to the exact operation.
3. **Proof.** Prove the successful-result equation in a sibling `Proof.lean`, for example
   `kernel? x y = some r → r = Model.Spec.add x y`.
4. **Dispatcher.** Add a branch in `Dispatch/<Op>/Runtime.lean` and extend `word_eq_spec`.
5. **Certificate.** Supply a `Backend.Candidate` estimate and use `Certified.binary` for
   representation-specific kernels. The exact generic kernel remains the required baseline.
6. **Registration.** Make the candidate available automatically to eligible `ExecFloat.Binary` types.
   Use `Backend.selectCertified_cons_of_dominant` when a candidate satisfies the dominance
   hypotheses for the chosen policy.
7. **Tests.** Expected selections in `tests/.../AutomaticDispatch.lean`; codegen scripts under
   `benchmarks/scripts/checks/`; measure with `execFloatBackendCalibration`; then
   compare against your reviewed same-machine baseline with
   `PERF_BASELINE_DIR=/path/to/baseline benchmarks/scripts/performance-regression.sh check`.
   The [calibration guide](../../../../benchmarks/docs/Calibration.md) explains how to record
   a baseline. Change a cost prior only after three isolated trials beat the selected candidate.
