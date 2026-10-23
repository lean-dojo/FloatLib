# ExecFloat

With `ExecFloat`, the value type you run arithmetic on is the one you prove things about. For
binary32 addition, one theorem connects the two:

```lean
import FloatLib

open FloatLib.Floats

def add (left right : Binary32) : Binary32 := left + right

example (left right : Binary32) : add left right = ExecFloat.Spec.add left right :=
  ExecFloat.Proof.add_eq_spec left right
```

`ExecFloat F` stores the code that format `F` chooses, and every certified implementation
carries a proof that `run = spec`. From there, the format's own theorems give that specification
its numerical meaning, and we've collected the major results in the
[theorem index](../THEOREMS.md).

Import `FloatLib.Floats.ExecFloat`, or `FloatLib.Floats.ExecFloat.Runtime` if you only need to
run code. Concrete formats live under `FloatLib/Floats/Formats/`.

## Casts and mixed arithmetic

A cast or a mixed operation names its destination type as `target`:

```lean
def widen (source : Binary32) : ExecFloat.ConversionOutcome Binary64 :=
  source.cast (target := Binary64)

def narrowDown (source : Binary64) : ExecFloat.ConversionOutcome Binary32 :=
  source.cast (target := Binary32) (mode := .down)

def addWide (left : Binary32) (right : Binary64) : ExecFloat.ConversionOutcome Binary64 :=
  ExecFloat.addAs (target := Binary64) left right
```

For a binary destination, `mode` picks the rounding direction. Any other destination policy goes
in `context`, for example rejecting infinities for a posit or saturating a bounded fixed-point
value.

We evaluate a finite mixed operation in the destination's exact domain and quantize once at the
end, and what the result means comes from the family's decoder, arithmetic, and quantizer laws.
Binary destinations use `Numerics.SignedRat` (a rational with an IEEE sign bit), so a cast can
keep a negative zero when the destination encoding has one. Posits and fixed point use `Rat`.
The [`ExactMap` embeddings](ExactMap.lean) connect the source and destination domains.

`fma` gets its own operation because rounding `x * y + z` once can give a different answer from
rounding the product and then the sum. For longer finite calculations, build an exact expression
with `ExactExpression.operand` and let `roundOnce` round it at the end.

## Backends

One operation can have several certified backends: byte tables, one- and two-word kernels,
binary32/64 specializations, two-limb binary128, wide-limb arithmetic, and the exact baseline. A
planner picks among them by comparing estimated costs. `NativeFPU.Unchecked` never takes part in
that choice, and you have to call it yourself.

`#float_info YourType` shows the certified selection, and `#float_info!` adds costs and
theorems. To list the registered bounds, use `#float_info [errors] YourType`. The
[backend guide](Backends/README.md) explains eligibility, policies, and how to add an
implementation.

## Elementary functions

`import FloatLib` gives you the `MathFunctions` class with its host `Float` and real instances.
For the binary functions `ExecFloat.Binary.exp`, `Model.exp`, `Model.pow`, and the configured
and model binary `MathFunctions` instances, you need
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals` (or the model barrel
`BinaryInterchange.Transcendentals` for model values). They're deterministic software kernels
with representation-bridge theorems, and they never go through the host FPU. For an IEEE
descriptor, `Model.pow` with a finite nonzero base and a finite integral exponent is correctly
rounded whenever its result is finite (`Model.Power.toReal_pow_of_eq_intCast`), and with a
finite positive base and any other finite exponent it's correctly rounded whenever its certified
enclosure search settles (`Model.Power.pow_spec_of_certified`). Certified `sqrt` and `abs` stay
on the default import.

To get proved real rounding from `exp`, `log`, and `pow`, pass `certify := true`. (`expMinus1`
and `logPlus1` always certify.) A certified call returns `.ok` only once it has certified a
finite rounded result. Otherwise you get a `Certified.Failure` that says why it couldn't.

## Intervals

`Numerics.Interval α` works with any endpoint representation through an `OutwardRounding`
adapter. The binary, decimal, and posit adapters decode endpoints as exact rationals, and a
successful operation encloses every real value between the input bounds. When the shared
[arithmetic](../../Numerics/Enclosure/Interval/Runtime.lean) can't produce a finite enclosure
(division across zero, for instance), it returns `none`. Its
[real containment theorems](../../Numerics/Enclosure/Interval/Real.lean) compose across
operations.

`ExecFloat.Binary.Interval` also exposes the directed `Model.Interval` operations. Its IEEE
arithmetic theorems take finite input bounds and allow infinite output bounds after overflow. In
a finite-only format, the endpoint calculations have to stay in range.

Proved exponential and logarithm bounds come from the
[rational enclosure kernels](../../Numerics/Enclosure/Elementary/Runtime.lean). For proofs that
stay in the real numbers, [quantized intervals](../Interval/Quantized.lean) use a Flocq-style
rounding grid.

With `import FloatLib`, the [`interval` tactic](../../../site/content/chapters/20-proving-numerical-bounds.md)
proves real inequalities from rational input bounds using certified expression evaluation and
subdivision.
