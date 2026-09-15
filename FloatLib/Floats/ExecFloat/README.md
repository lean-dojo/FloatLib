# ExecFloat

With `ExecFloat`, we use the same value type to run arithmetic and prove things about it.
For binary32 addition, the connection is a single theorem:

```lean
import FloatLib

open FloatLib.Floats

abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

def add (left right : Binary32) : Binary32 := left + right

example (left right : Binary32) : add left right = ExecFloat.Spec.add left right :=
  ExecFloat.Proof.add_eq_spec left right
```

`ExecFloat F` stores the code chosen by format `F`. Each certified implementation carries
a proof that `run = spec`. The format's theorems then connect that specification to its
numerical meaning; we've collected the major results in the [theorem index](../THEOREMS.md).

Import `FloatLib.Floats.ExecFloat`. Runtime-only clients can import
`FloatLib.Floats.ExecFloat.Runtime`. Concrete formats live under `FloatLib/Floats/Formats/`.

## Casts and mixed arithmetic

A cast names its destination. A mixed operation names its result type:

```lean
abbrev Binary64 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

def widen (source : Binary32) : ExecFloat.ConversionOutcome Binary64 :=
  source.cast (target := Binary64)

def addWide (left : Binary32) (right : Binary64) : ExecFloat.ConversionOutcome Binary64 :=
  ExecFloat.addAs (result := Binary64) left right
```

We evaluate finite mixed operations in the destination's exact domain, then quantize once.
The family's decoder, arithmetic, and quantizer laws establish what the result means.
Binary destinations use `Numerics.SignedRat`, a rational with an IEEE sign bit, so a cast can
preserve negative zero when the destination encoding supports it. Posits and fixed point use
`Rat`. The [`ExactMap` embeddings](ExactMap.lean) connect the source and destination domains.

We give `fma` its own operation because rounding `x * y + z` once can differ from rounding
the product and then the sum. For longer finite calculations, `ExactExpression.operand`
builds an exact expression that `roundOnce` or `roundOnceWith` rounds at the end.

## Backends

Several certified backends can implement the same operation: byte tables, one- and two-word
kernels, binary32/64 specializations, two-limb binary128, wide-limb arithmetic, and the exact
baseline. We choose among them with a planner that compares estimated costs.
`NativeFPU.Unchecked` requires an explicit call and is outside that selection.

`#float_info YourType` shows the certified selection; `#float_info!` adds costs and theorems;
`#float_info [errors] YourType` lists registered bounds. The [backend guide](Backends/README.md)
explains eligibility, policies, and how to add an implementation.

## Elementary functions

`import FloatLib` provides the `MathFunctions` class and its host `Float` and real instances.
The binary functions `ExecFloat.Binary.exp`, `Model.exp`, `Model.pow`, and the configured and
model binary `MathFunctions` instances require
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals` (or the model barrel
`BinaryInterchange.Transcendentals` for model values). These are deterministic software kernels with
representation-bridge theorems, not a host-FPU path. Certified `sqrt` and `abs` stay on the
default import.

## Intervals

- Proof-side outward-rounded reals: `FloatLib/Floats/Interval/Quantized.lean` (Flocq-style grid).
- Executable binary endpoints: `Model.Interval fmt`. Unordered or NaN endpoints become `whole fmt`.
- Optional Arb-backed transcendentals: `FloatLibTests.Arb.ModelTranscendentals` (not kernel-checked).
