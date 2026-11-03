/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Conversion.Core
public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.ExecFloat.ExactMap

/-!
# Conversion and mixed arithmetic

Name the destination type when converting a value or combining different formats:

```lean
source.cast (target := Binary64)
source.cast (target := Binary32) (mode := .up)
ExecFloat.Mixed.add (target := Binary64) left right
```

Each operation decodes its operands, maps them into the destination's exact domain through
`ExactMap`, and quantizes the result once. Every entry point takes the same two options. `mode` is
the rounding direction. Binary and nominal static-byte destinations take a `Numerics.RoundingMode`:
the six directions of `IEEERoundingMode` and `.stochastic`. P3109 destinations take a P3109
`RoundingMode`. A family without directed conversion has the single mode `()`, so naming a
direction for it is a type error. `context` is the destination's `RoundingModes.Policy`, every
policy except the direction, such as a rejected infinity, binary saturation or flush-to-zero,
stochastic entropy, P3109 saturation, a saturating bounded fixed point, or a shared block
exponent. A call without `context` uses the destination's canonical policy (`ModeContext`), and
destinations without one, such as shared-scale blocks, require `context`.

The mode decides the direction: a policy has no direction field, so `(mode := .down)` and
`(context := ...)` combine and neither can cancel the other. Every entry point quantizes in
`RoundingModes.withMode mode context`, and `spec_convert` and the other contracts in
`Conversion.Proof` are stated in that context.

Casts pass infinities and exceptional observations to the destination's policy. The mixed
operations `Mixed.add`, `sub`, `mul`, `div`, and `fma` require finite inputs and report the first
rejected operand. Division also rejects a denominator satisfying the exact domain's `ExactZero`
predicate.

Binary destinations use `SignedRat` as their exact domain, so a signed zero survives a cast and
mixed addition, subtraction, and FMA select a cancellation sign from the call's rounding mode.
Posit destinations use `Rat`, with a single zero.

For longer finite calculations, `ExactExpression.operand` and `roundOnce` use the same path with
an ordinary `Except`-based `do` expression. Use `ExactExpression.add` and `sub` with a `mode` when a
directed cancellation sign is required inside that expression. `Conversion.Proof` proves that each
entry point satisfies the destination's `Quantization.Spec` relation. These composition theorems
use the supplied exact-domain operations. That the maps and arithmetic hooks preserve numerical
values has to be proved separately for each family.
-/

@[expose] public section

namespace FloatLib.Floats
namespace ExecFloat

open FloatLib.Numerics

universe u v w x y z a b

namespace ExactDecoder

variable {Source : Type u} {SourceExact : Type v} {TargetExact : Type w}

/-- Decode one source through its canonical exact-domain capability. -/
@[inline] def run [self : ExactDecoder Source SourceExact] (value : Source) :
    NumericalValue SourceExact :=
  self.decode value

/--
Decode a source and embed its finite payload into the destination computation domain.

Infinity signs and exceptional observations are preserved structurally by `NumericalValue.map`.
-/
@[inline] def decodeTo [ExactDecoder Source SourceExact]
    [embedding : ExactMap SourceExact TargetExact] (value : Source) :
    NumericalValue TargetExact :=
  (run value).map embedding.map

end ExactDecoder

namespace Quantizer

variable {Destination : Type u} {Exact : Type v}

/-- Quantize one complete exact observation under a given destination context. -/
@[inline] def quantize [self : Quantizer Destination Exact]
    (context : self.Context) (value : NumericalValue Exact) :
    ConversionOutcome Destination :=
  self.run context value

end Quantizer

/--
Convert any exactly decodable source into the destination `target`, rounding once.

`mode` is the rounding direction, nearest-even by default, and `context` the destination's other
policies, its canonical policy by default. The quantizer runs in
`RoundingModes.withMode mode context`. This function form also accepts sources outside the
`ExecFloat` carrier, such as `Rat`, `Int`, or a native float, when a module supplies their exact
decoder. `ExecFloat` values may use `value.cast`.
-/
@[inline] def convert {Source : Type u} (value : Source)
    {target : Type v} {SourceExact : Type w} {TargetExact : Type x}
    [ExactDecoder Source SourceExact] [ExactMap SourceExact TargetExact]
    [quantizer : Quantizer target TargetExact]
    {Mode : Type} [modes : RoundingModes target TargetExact Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  quantizer.run (modes.withMode mode context) (ExactDecoder.decodeTo value)

/--
Convert an `ExecFloat` value with field notation, as in
`value.cast (target := Binary64)` or `value.cast (target := Binary32) (mode := .up)`.

The `mode` and `context` options are those of `convert`.
-/
@[inline] def cast {F : Type u} [EncodedFormat F]
    (value : FloatLib.Floats.ExecFloat F)
    {target : Type v} {SourceExact : Type w} {TargetExact : Type x}
    [ExactDecoder (FloatLib.Floats.ExecFloat F) SourceExact]
    [ExactMap SourceExact TargetExact]
    [quantizer : Quantizer target TargetExact]
    {Mode : Type} [modes : RoundingModes target TargetExact Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  convert (target := target) (SourceExact := SourceExact)
    (TargetExact := TargetExact) value mode context

namespace Conversion

/-- Extract a finite operand or report its exact non-finite observation and position. -/
@[inline] def requireFinite {Exact : Type u} (position : InputPosition) :
    NumericalValue Exact → Except ConversionFailure Exact
  | .finite value => .ok value
  | .infinity negative => .error (.infinity position negative)
  | .exceptional value => .error (.exceptional position value)

/-- Prepare exact finite binary arithmetic, checking the left operand before the right. -/
@[inline] def prepareBinary {Exact : Type u}
    (operation : Exact → Exact → Exact)
    (left right : NumericalValue Exact) :
    Except ConversionFailure (NumericalValue Exact) := do
  let leftValue ← requireFinite .left left
  let rightValue ← requireFinite .right right
  pure (.finite (operation leftValue rightValue))

/--
Prepare exact finite division and reject a zero exact denominator.

`ExactZero` states and decides which values the exact domain declares to be zero. Domains with
several zero representations justify that choice in their own bridge theorems.
-/
@[inline] def prepareDiv {Exact : Type u} [Zero Exact] [ExactZero Exact] [Div Exact]
    (left right : NumericalValue Exact) :
    Except ConversionFailure (NumericalValue Exact) := do
  let leftValue ← requireFinite .left left
  let rightValue ← requireFinite .right right
  if ExactZero.test rightValue then
    .error .divisionByZero
  else
    pure (.finite (leftValue / rightValue))

/-- Prepare finite fused multiply-add using a supplied exact addition and no intermediate rounding. -/
@[inline] def prepareFmaWith {Exact : Type u} [Mul Exact]
    (add : Exact → Exact → Exact)
    (left right addend : NumericalValue Exact) :
    Except ConversionFailure (NumericalValue Exact) := do
  let leftValue ← requireFinite .left left
  let rightValue ← requireFinite .right right
  let addendValue ← requireFinite .addend addend
  pure (.finite (add (leftValue * rightValue) addendValue))

/-- Prepare exact finite fused multiply-add with the exact domain's ordinary addition. -/
@[inline] def prepareFma {Exact : Type u} [Mul Exact] [Add Exact]
    (left right addend : NumericalValue Exact) :
    Except ConversionFailure (NumericalValue Exact) :=
  prepareFmaWith (· + ·) left right addend

/-- Quantize a prepared exact input, preserving a preparation failure verbatim. -/
@[inline] def quantizePrepared {Destination : Type u} {Exact : Type v}
    [quantizer : Quantizer Destination Exact]
    (context : quantizer.Context) :
    Except ConversionFailure (NumericalValue Exact) → ConversionOutcome Destination
  | .ok value => quantizer.run context value
  | .error reason => .failure reason

/-- Relational contract for preparation followed by one destination quantization. -/
def PreparedSpec {Destination : Type u} {Exact : Type v}
    [quantizer : Quantizer Destination Exact]
    (context : quantizer.Context)
    (prepared : Except ConversionFailure (NumericalValue Exact))
    (outcome : ConversionOutcome Destination) : Prop :=
  match prepared with
  | .ok value => quantizer.spec context value outcome
  | .error reason => outcome = .failure reason

end Conversion

namespace ExactExpression

/--
Decode `value`, the operand numbered `index`, into the exact domain used by an enclosing
expression.

Finite inputs are mapped through `ExactMap`, whose instances must preserve value. The class does
not check this; the instances FloatLib provides in `ExecFloat.ExactMap` have their value facts
proved. The chosen exact domain determines which representation metadata survives, so mapping a
`SignedRat` into `Rat` forgets its zero sign.
Infinity and exceptional observations become position-indexed failures, so a longer expression
still reports which operand was rejected.
-/
@[inline] def operand {Source : Type u} {SourceExact : Type v} {Exact : Type w}
    [ExactDecoder Source SourceExact] [ExactMap SourceExact Exact]
    (index : Nat) (value : Source) : ExactExpression Exact :=
  Conversion.requireFinite (.operand index) (ExactDecoder.decodeTo value)

/--
Add exact values with the cancellation-sign rule of the destination `target`, without quantizing.

For signed-rational destinations, `(mode := .down)` gives an exact cancellation the negative zero
that a later `roundOnce (mode := .down)` keeps, while ordinary `+` keeps the nearest-even positive
zero. Name `target`: the exact domain alone does not determine it. The options are those of
`convert`.
-/
@[inline] def add {target : Type u} {Exact : Type v} [Add Exact]
    [quantizer : Quantizer target Exact] (left right : Exact)
    {Mode : Type} [modes : RoundingModes target Exact Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ExactExpression Exact :=
  .ok (quantizer.addExact (modes.withMode mode context) left right)

/--
Subtract exact values with the cancellation-sign rule of the destination `target`, without
quantizing. The options are those of `add`.
-/
@[inline] def sub {target : Type u} {Exact : Type v} [Sub Exact]
    [quantizer : Quantizer target Exact] (left right : Exact)
    {Mode : Type} [modes : RoundingModes target Exact Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ExactExpression Exact :=
  .ok (quantizer.subExact (modes.withMode mode context) left right)

/--
Divide two exact finite values, rejecting a denominator declared zero by `ExactZero`.

Use this inside a `do` expression. Ordinary exact-domain operations stay available for steps that
cannot fail, and `add` and `sub` also follow the destination's cancellation-sign rule.
-/
@[inline] def div {Exact : Type u} [Zero Exact] [ExactZero Exact] [Div Exact]
    (numerator denominator : Exact) : ExactExpression Exact :=
  if ExactZero.test denominator then
    .error .divisionByZero
  else
    .ok (numerator / denominator)

/-- Lift a successful exact scalar into the complete finite observation expected by a quantizer. -/
@[inline] def toPrepared {Exact : Type u} :
    ExactExpression Exact → Except ConversionFailure (NumericalValue Exact)
  | .ok value => .ok (.finite value)
  | .error reason => .error reason

end ExactExpression

/--
Evaluate an exact scalar expression and quantize its result once into `target`.

The expression may contain any executable operation supported by its exact domain. A failed
operand or checked division bypasses the quantizer and is returned unchanged.
For signed-rational binary destinations that support signed zero, quantization preserves the
supplied zero sign, but it cannot recover how that zero arose. Ordinary `SignedRat` addition and
subtraction use their nearest-even cancellation convention. For directed cancellation, use
`ExactExpression.add` and `sub` with the same `target` and `mode`. The options are those of
`convert`.
-/
@[inline] def roundOnce {target : Type u} {Exact : Type v}
    [quantizer : Quantizer target Exact] (expression : ExactExpression Exact)
    {Mode : Type} [modes : RoundingModes target Exact Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  Conversion.quantizePrepared (modes.withMode mode context) expression.toPrepared

/-!
## Mixed-format arithmetic

`Mixed.add`, `sub`, `mul`, `div`, and `fma` combine operands of different types and name the result
type as `target`. Each decodes its operands exactly, embeds them in the destination's exact domain,
computes the exact result there, and rounds it once into `target`, with the `mode` and `context`
options of `convert`.

They are the finite part of IEEE 754's formatOf operations, not the complete operations. A
non-finite operand fails with `.infinity` or `.exceptional` and its position, checked left to
right, and `div` fails with `.divisionByZero` when the exact domain declares the divisor zero,
where IEEE arithmetic would return an infinity or a NaN and raise a flag. The P3109 report
arithmetic `Formats.P3109.Arithmetic.Mixed` is a different interface: it takes a `Destination`
value and is total, carrying infinities and NaN through the report's closed arithmetic.
-/

namespace Mixed

section Binary

variable {Left : Type u} {Right : Type v} {target : Type w}
  {LeftExact : Type x} {RightExact : Type y} {Exact : Type z}
  [ExactDecoder Left LeftExact] [ExactMap LeftExact Exact]
  [ExactDecoder Right RightExact] [ExactMap RightExact Exact]

/--
Add finite values exactly and quantize once into `target`, with the options of `convert`.

The exact sum uses the destination's cancellation-sign rule for the call's `mode`, so
`(mode := .down)` gives an exactly cancelling binary sum the negative zero of IEEE 754.
-/
@[inline] def add
    [Add Exact] [quantizer : Quantizer target Exact]
    (left : Left) (right : Right)
    {Mode : Type} [modes : RoundingModes target Exact Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  let directed := modes.withMode mode context
  Conversion.quantizePrepared directed <|
    Conversion.prepareBinary (quantizer.addExact directed)
      (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)

/-- Subtract finite values exactly and quantize once into `target`, with `add`'s options. -/
@[inline] def sub
    [Sub Exact] [quantizer : Quantizer target Exact]
    (left : Left) (right : Right)
    {Mode : Type} [modes : RoundingModes target Exact Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  let directed := modes.withMode mode context
  Conversion.quantizePrepared directed <|
    Conversion.prepareBinary (quantizer.subExact directed)
      (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)

/-- Multiply finite values exactly and quantize once into `target`, with `convert`'s options. -/
@[inline] def mul
    [Mul Exact] [quantizer : Quantizer target Exact]
    (left : Left) (right : Right)
    {Mode : Type} [modes : RoundingModes target Exact Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  Conversion.quantizePrepared (modes.withMode mode context) <|
    Conversion.prepareBinary (· * ·)
      (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)

/--
Divide finite values exactly and quantize once into `target`, with `convert`'s options.

A divisor that the exact domain declares zero fails with `.divisionByZero`.
-/
@[inline] def div
    [Zero Exact] [ExactZero Exact] [Div Exact]
    [quantizer : Quantizer target Exact]
    (left : Left) (right : Right)
    {Mode : Type} [modes : RoundingModes target Exact Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  Conversion.quantizePrepared (modes.withMode mode context) <|
    Conversion.prepareDiv (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)

end Binary

/--
Compute finite `left * right + addend` exactly and quantize once into `target`.

The exact product is added to `addend` under the destination's cancellation-sign rule for the
call's `mode` before the destination quantizer runs. The options are those of `add`.
-/
@[inline] def fma {Left : Type u} {Right : Type v} {Addend : Type w}
    {target : Type x} {LeftExact : Type y} {RightExact : Type z}
    {AddendExact : Type a} {Exact : Type b}
    [ExactDecoder Left LeftExact] [ExactMap LeftExact Exact]
    [ExactDecoder Right RightExact] [ExactMap RightExact Exact]
    [ExactDecoder Addend AddendExact] [ExactMap AddendExact Exact]
    [Mul Exact] [Add Exact] [quantizer : Quantizer target Exact]
    (left : Left) (right : Right) (addend : Addend)
    {Mode : Type} [modes : RoundingModes target Exact Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  let directed := modes.withMode mode context
  Conversion.quantizePrepared directed <|
    Conversion.prepareFmaWith (quantizer.addExact directed)
      (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)
      (ExactDecoder.decodeTo addend)

end Mixed
end ExecFloat
end FloatLib.Floats
