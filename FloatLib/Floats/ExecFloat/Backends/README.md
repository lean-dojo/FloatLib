# Execution backends

We often have several ways to compute the same `x + y`: a lookup table, a word kernel, or exact
arbitrary-precision arithmetic. This directory connects those implementations to their format's
specification. No candidate reaches the planner's cost comparison without a proof of
`run = spec`.

`Numerics` supplies the exact values and contracts, `Kernels/` supplies shared integer
algorithms, and the backends here apply those algorithms to a format. `Backends/Dispatch` tries
a specialized kernel first and falls back to the exact baseline when the kernel declines an
input. A `Capability` lets the planner choose among these certified implementations. That choice
is the only step that uses a cost model.

The exact dyadic fallback is executable too. We import the
[rounding proof](../../Formats/BinaryInterchange/Dyadic/RoundingKernel/Proof.lean) into the
[dyadic specification](../../Formats/BinaryInterchange/Spec/Dyadic.lean) before defining
addition, subtraction, multiplication, and FMA, so their compiled rounding uses bulk integer
shifts and nearest-even rounding at every width while keeping the descriptor's encoding
policies. Order matters here. A compiler substitution applies when a caller is compiled, and
importing a proof later won't rewrite functions that were already compiled.

## Backends

Eligibility is a decidable proposition on the descriptor's fields, so a custom
`ExecFloat.Binary` with the same layout gets the same backend as a named format. You can't
select the shared word pieces (`Word/NormalPair`, `ProductRound`, `Quotient`, `ModelSqrt`) on
their own.

| Directory | Class | Eligible | Ops | Status |
| --- | --- | --- | --- | --- |
| `TinyTable/` (tables built in `Configured/ByteTable/`) | exhaustive table | ≤ 8 encoded bits | six | proved |
| `Word/Small/` | native-word | IEEE ≤ 64 bits; operation-specific fraction caps | six | proved |
| `Word/TwoWordMul/` | via fixed-limb route | IEEE ≤ 64 bits, 32–62 fraction bits | mul | proved |
| `Word/Narrow/` | fixed-format | exactly binary32 | six | proved |
| `Word/Full/` | fixed-format | exactly binary64 | six | proved |
| `FixedLimb/Pair/` | two `UInt64` limbs | IEEE, `64 < fracWidth`, `bitWidth ≤ 128` | six; sqrt declines some layouts | proved |
| `WideLimb/` | 32-bit limbs | IEEE > 128 bits, exponent ≤ 32; `ExecFloat.BinaryLimbs` | six; div/sqrt use integer arithmetic | proved |
| `Generic/` | exact baseline | every binary descriptor | six | proved |
| `Configured/NativeFPU/Unchecked.lean` | not a planner class | binary32/64, explicit call site | add, sub, mul, div, sqrt (not fma) | unchecked |

[AutomaticDispatch.lean](../../../../tests/FloatLibTests/Conformance/Execution/AutomaticDispatch.lean)
checks the balanced-policy selections below.

| Type | Selected (balanced policy) |
| --- | --- |
| `Binary32` | all six = fixed-format |
| `Binary64` | all six = fixed-format |

Selection picks a certified operation, and that operation can still use the exact fallback for
individual inputs. Wide-limb multiplication and FMA, for example, require normal operands and
check the result's leading position both before rounding and after the rounding carry. So a
value just below the normal range can take the fallback even when it would round to the smallest
normal value. FMA's alignment core accepts exact cancellation as positive zero.

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
Binary32/64 use proved software under every policy. If you want the host FPU, call its
operations by name:

```lean
NativeFPU.Unchecked.add32 x y
```

These host operations have no `Backend.Certified` proof, so they can't supply a scoped
`ExecFloat.Add` instance.

## Adding a backend

The one-word kernels are a good model to copy when you add an implementation. We keep runtime
code apart from its proofs, and every compiler substitution is justified by a proved `@[csimp]`
equation.

1. **Eligibility.** State a decidable `Prop` on descriptor data. Writing the decision out, as in
   `if h : … then isTrue h else isFalse h`, makes the supported layouts easy to read.
2. **Kernel.** Put the implementation in `Runtime.lean`, with runtime imports only, and reuse
   `FloatLib/Kernels`. When the kernel returns `none`, the dispatcher falls back to the exact
   operation.
3. **Proof.** Prove the successful-result equation in a sibling `Proof.lean`, for example
   `kernel? x y = some r → r = Model.Spec.add x y`.
4. **Dispatcher.** Add a branch in `Dispatch/<Op>/Runtime.lean` and extend `word_eq_spec`.
5. **Certificate.** Supply a `Backend.Candidate` estimate and use `Certified.binary` for
   representation-specific kernels. Keep the exact generic kernel as the required baseline.
6. **Registration.** Make the candidate available automatically to eligible `ExecFloat.Binary` types.
   Use `Backend.selectCertified_cons_of_dominant` when a candidate satisfies the dominance
   hypotheses for the chosen policy.
7. **Tests.** Put expected selections in `tests/.../AutomaticDispatch.lean` and codegen scripts
   under `benchmarks/scripts/checks/`. Measure with `execFloatBackendCalibration`, then compare
   against your reviewed same-machine baseline with
   `PERF_BASELINE_DIR=/path/to/baseline benchmarks/scripts/performance-regression.sh check`. The
   [calibration guide](../../../../benchmarks/docs/Calibration.md) explains how to record a
   baseline. Only change a cost prior after three isolated trials beat the selected candidate.
