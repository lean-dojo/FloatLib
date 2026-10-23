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
ExecFloat.addAs (target := Binary64) left right
```

Each operation decodes its operands, maps them into the destination's exact domain through
`ExactMap`, and quantizes the result once. Every entry point takes the same two options. `mode`
selects the rounding direction of the destination's canonical context, through `ModeContext`.
Binary and nominal static-byte destinations accept the six `IEEERoundingMode` directions. A family
without directed conversion has the single mode `()`, so naming a direction for it is a type
error. `context` replaces the canonical context with a family-specific policy, such as a rejected
infinity, a saturating bounded fixed point, or a shared block exponent. A context carries its own
rounding direction, so give one option or the other. Destinations without
a canonical context, such as shared-scale blocks, require `context`.

Casts pass infinities and exceptional observations to the destination's policy. Mixed arithmetic
requires finite inputs and reports the first rejected operand. Division also rejects a denominator
satisfying the exact domain's `ExactZero` predicate.

Binary destinations use `SignedRat` as their exact domain, so a signed zero survives a cast and
mixed addition, subtraction, and FMA select a cancellation sign from the destination's rounding
context. Posit destinations use `Rat`, with a single zero.

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

`mode` selects the rounding direction of the destination's canonical context, nearest-even by
default, and `context` replaces that context with a family-specific policy. This function form
also accepts sources outside the `ExecFloat` carrier, such as `Rat`, `Int`, or a native
float, when a module supplies their exact decoder. `ExecFloat` values may use `value.cast`.
-/
@[inline] def convert {Source : Type u} (value : Source)
    {target : Type v} {SourceExact : Type w} {TargetExact : Type x}
    [ExactDecoder Source SourceExact] [ExactMap SourceExact TargetExact]
    [quantizer : Quantizer target TargetExact]
    {Mode : Type} [modes : RoundingModes target Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  quantizer.run context (ExactDecoder.decodeTo value)

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
    {Mode : Type} [modes : RoundingModes target Mode] (mode : Mode := modes.default)
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
Decode one numbered operand into the exact domain used by an enclosing expression.

Finite inputs are mapped without rounding through `ExactMap`. The chosen exact domain determines
which representation metadata survives, so mapping a `SignedRat` into `Rat` forgets its zero sign.
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
    {Mode : Type} [modes : RoundingModes target Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ExactExpression Exact :=
  .ok (quantizer.addExact context left right)

/--
Subtract exact values with the cancellation-sign rule of the destination `target`, without
quantizing. The options are those of `add`.
-/
@[inline] def sub {target : Type u} {Exact : Type v} [Sub Exact]
    [quantizer : Quantizer target Exact] (left right : Exact)
    {Mode : Type} [modes : RoundingModes target Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ExactExpression Exact :=
  .ok (quantizer.subExact context left right)

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
    {Mode : Type} [modes : RoundingModes target Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  Conversion.quantizePrepared context expression.toPrepared

section Binary

variable {Left : Type u} {Right : Type v} {target : Type w}
  {LeftExact : Type x} {RightExact : Type y} {Exact : Type z}
  [ExactDecoder Left LeftExact] [ExactMap LeftExact Exact]
  [ExactDecoder Right RightExact] [ExactMap RightExact Exact]

/--
Add finite values exactly and quantize once into `target`, with the options of `convert`.

The exact sum uses the destination context's cancellation-sign rule, so `(mode := .down)` gives
an exactly cancelling binary sum the negative zero of IEEE 754.
-/
@[inline] def addAs
    [Add Exact] [quantizer : Quantizer target Exact]
    (left : Left) (right : Right)
    {Mode : Type} [modes : RoundingModes target Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  Conversion.quantizePrepared context <|
    Conversion.prepareBinary (quantizer.addExact context)
      (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)

/-- Subtract finite values exactly and quantize once into `target`, with `addAs`'s options. -/
@[inline] def subAs
    [Sub Exact] [quantizer : Quantizer target Exact]
    (left : Left) (right : Right)
    {Mode : Type} [modes : RoundingModes target Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  Conversion.quantizePrepared context <|
    Conversion.prepareBinary (quantizer.subExact context)
      (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)

/-- Multiply finite values exactly and quantize once into `target`, with `convert`'s options. -/
@[inline] def mulAs
    [Mul Exact] [quantizer : Quantizer target Exact]
    (left : Left) (right : Right)
    {Mode : Type} [modes : RoundingModes target Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  Conversion.quantizePrepared context <|
    Conversion.prepareBinary (· * ·)
      (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)

/-- Divide finite values exactly and quantize once into `target`, with `convert`'s options. -/
@[inline] def divAs
    [Zero Exact] [ExactZero Exact] [Div Exact]
    [quantizer : Quantizer target Exact]
    (left : Left) (right : Right)
    {Mode : Type} [modes : RoundingModes target Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  Conversion.quantizePrepared context <|
    Conversion.prepareDiv (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)

end Binary

/--
Compute finite `left * right + addend` exactly and quantize once into `target`.

The exact product is added to `addend` under the context's cancellation-sign rule before the
destination quantizer runs. The options are those of `addAs`.
-/
@[inline] def fmaAs {Left : Type u} {Right : Type v} {Addend : Type w}
    {target : Type x} {LeftExact : Type y} {RightExact : Type z}
    {AddendExact : Type a} {Exact : Type b}
    [ExactDecoder Left LeftExact] [ExactMap LeftExact Exact]
    [ExactDecoder Right RightExact] [ExactMap RightExact Exact]
    [ExactDecoder Addend AddendExact] [ExactMap AddendExact Exact]
    [Mul Exact] [Add Exact] [quantizer : Quantizer target Exact]
    (left : Left) (right : Right) (addend : Addend)
    {Mode : Type} [modes : RoundingModes target Mode] (mode : Mode := modes.default)
    (context : ContextFor target mode :=
      by exact FloatLib.Floats.ExecFloat.ModeContext.context) :
    ConversionOutcome target :=
  Conversion.quantizePrepared context <|
    Conversion.prepareFmaWith (quantizer.addExact context)
      (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)
      (ExactDecoder.decodeTo addend)

end ExecFloat
end FloatLib.Floats
