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
abbrev Binary64 :=
  ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

source.cast (target := Binary64)
ExecFloat.addAs (result := Binary64) left right
```

Each operation decodes its operands, maps them into the destination's exact domain through
`ExactMap`, and quantizes the result once. Casts pass infinities and exceptional observations to the
destination's
policy. Mixed arithmetic requires finite inputs and reports the first rejected operand; division
also rejects a denominator satisfying the exact domain's `ExactZero` predicate.

Binary destinations use `SignedRat` as their exact domain, so a signed zero survives a cast and
mixed addition, subtraction, and FMA select a cancellation sign from the destination's rounding
context. Posit destinations use `Rat`, with a single zero.

For longer finite calculations, `ExactExpression.operand` and `roundOnce` use the same path with
an ordinary `Except`-based `do` expression. Use `ExactExpression.addWith` and `subWith` when a
directed cancellation sign is required inside that expression. `Conversion.Proof` proves that each
entry point satisfies the destination's `Quantization.Spec` relation. These composition theorems
use the supplied exact-domain operations; numerical preservation of the maps and arithmetic hooks
is a separate family-specific obligation, as described in `Conversion.Core`.
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

/-- Quantize one complete exact observation with explicit destination context. -/
@[inline] def quantize [self : Quantizer Destination Exact]
    (context : self.Context) (value : NumericalValue Exact) :
    ConversionOutcome Destination :=
  self.run context value

end Quantizer

/--
Convert any exactly decodable source into a named destination under family-specific context.

This function-form API also supports sources outside the `ExecFloat` carrier when an integration
module supplies their exact decoder. Ordinary `ExecFloat` values may also use
`value.castWith` through field notation.
-/
@[inline] def convertWith {Source : Type u} (value : Source)
    {target : Type v} {SourceExact : Type w} {TargetExact : Type x}
    [ExactDecoder Source SourceExact] [ExactMap SourceExact TargetExact]
    [quantizer : Quantizer target TargetExact]
    (context : quantizer.Context) : ConversionOutcome target :=
  quantizer.run context (ExactDecoder.decodeTo value)

/-- Convert any exactly decodable source using the destination's canonical context. -/
@[inline] def convert {Source : Type u} (value : Source)
    {target : Type v} {SourceExact : Type w} {TargetExact : Type x}
    [ExactDecoder Source SourceExact] [ExactMap SourceExact TargetExact]
    [quantizer : Quantizer target TargetExact]
    [defaults : DefaultQuantizer target TargetExact] : ConversionOutcome target :=
  convertWith value defaults.defaultContext

/--
Convert an `ExecFloat` value under explicit destination context, with field notation.

The source type lets Lean resolve `value.castWith`; the destination can be a local alias such as
`Binary64` or `Posit32`. Use `convertWith` for source types outside `ExecFloat`.
-/
@[inline] def castWith {F : Type u} [EncodedFormat F]
    (value : FloatLib.Floats.ExecFloat F)
    {target : Type v} {SourceExact : Type w} {TargetExact : Type x}
    [ExactDecoder (FloatLib.Floats.ExecFloat F) SourceExact]
    [ExactMap SourceExact TargetExact]
    [quantizer : Quantizer target TargetExact]
    (context : quantizer.Context) : ConversionOutcome target :=
  convertWith value context

/-- Convert an `ExecFloat` value using the destination's canonical context. -/
@[inline] def cast {F : Type u} [EncodedFormat F]
    (value : FloatLib.Floats.ExecFloat F)
    {target : Type v} {SourceExact : Type w} {TargetExact : Type x}
    [ExactDecoder (FloatLib.Floats.ExecFloat F) SourceExact]
    [ExactMap SourceExact TargetExact]
    [quantizer : Quantizer target TargetExact]
    [defaults : DefaultQuantizer target TargetExact] : ConversionOutcome target :=
  convert (target := target) (SourceExact := SourceExact)
    (TargetExact := TargetExact) value

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
several zero representations justify that choice in their own bridge theorems, not in this
algorithm.
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
which representation metadata survives; mapping a `SignedRat` into `Rat` forgets its zero sign.
Infinity and exceptional observations become position-indexed failures, so a longer expression
still reports which operand was rejected.
-/
@[inline] def operand {Source : Type u} {SourceExact : Type v} {Exact : Type w}
    [ExactDecoder Source SourceExact] [ExactMap SourceExact Exact]
    (index : Nat) (value : Source) : ExactExpression Exact :=
  Conversion.requireFinite (.operand index) (ExactDecoder.decodeTo value)

/--
Add exact values under the destination context without quantizing.

For signed-rational destinations this selects the sign of exact cancellation before a later
`roundOnceWith`. Name `result` when the context alone does not determine the destination type.
-/
@[inline] def addWith {result : Type u} {Exact : Type v} [Add Exact]
    [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (left right : Exact) : ExactExpression Exact :=
  .ok (quantizer.addExact context left right)

/-- Subtract exact values using the destination's cancellation-sign rule, without quantizing. -/
@[inline] def subWith {result : Type u} {Exact : Type v} [Sub Exact]
    [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (left right : Exact) : ExactExpression Exact :=
  .ok (quantizer.subExact context left right)

/--
Divide two exact finite values, rejecting a denominator declared zero by `ExactZero`.

Use this inside a `do` expression. Ordinary exact-domain operations remain available for
calculations without an additional failure case; `addWith` and `subWith` also respect the
destination's cancellation-sign rule.
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
Evaluate an exact scalar expression and quantize its result once under an explicit context.

The expression may contain any executable operation supported by its exact domain. A failed
operand or checked division bypasses the quantizer and is returned unchanged.
For signed-rational binary destinations that support signed zero, quantization preserves the
supplied zero sign; it cannot recover how that zero arose. Ordinary `SignedRat` addition and
subtraction use their nearest-even cancellation convention. For directed cancellation, use
`ExactExpression.addWith` and `subWith` with the intended destination and context.
-/
@[inline] def roundOnceWith {result : Type u} {Exact : Type v}
    [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (expression : ExactExpression Exact) :
    ConversionOutcome result :=
  Conversion.quantizePrepared context expression.toPrepared

/-- Evaluate an exact scalar expression and quantize its result once using the default context. -/
@[inline] def roundOnce {result : Type u} {Exact : Type v}
    [quantizer : Quantizer result Exact]
    [defaults : DefaultQuantizer result Exact]
    (expression : ExactExpression Exact) : ConversionOutcome result :=
  roundOnceWith defaults.defaultContext expression

section Binary

variable {Left : Type u} {Right : Type v} {result : Type w}
  {LeftExact : Type x} {RightExact : Type y} {Exact : Type z}
  [ExactDecoder Left LeftExact] [ExactMap LeftExact Exact]
  [ExactDecoder Right RightExact] [ExactMap RightExact Exact]

/-- Add finite values exactly and quantize once into `result` under explicit context. -/
@[inline] def addAsWith
    [Add Exact] [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (left : Left) (right : Right) :
    ConversionOutcome result :=
  Conversion.quantizePrepared context <|
    Conversion.prepareBinary (quantizer.addExact context)
      (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)

/-- Add finite values exactly and quantize once using the destination's canonical context. -/
@[inline] def addAs
    [Add Exact] [quantizer : Quantizer result Exact]
    [defaults : DefaultQuantizer result Exact]
    (left : Left) (right : Right) : ConversionOutcome result :=
  addAsWith defaults.defaultContext left right

/-- Subtract finite values exactly and quantize once into `result` under explicit context. -/
@[inline] def subAsWith
    [Sub Exact] [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (left : Left) (right : Right) :
    ConversionOutcome result :=
  Conversion.quantizePrepared context <|
    Conversion.prepareBinary (quantizer.subExact context)
      (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)

/-- Subtract finite values exactly and quantize once using the destination's canonical context. -/
@[inline] def subAs
    [Sub Exact] [quantizer : Quantizer result Exact]
    [defaults : DefaultQuantizer result Exact]
    (left : Left) (right : Right) : ConversionOutcome result :=
  subAsWith defaults.defaultContext left right

/-- Multiply finite values exactly and quantize once into `result` under explicit context. -/
@[inline] def mulAsWith
    [Mul Exact] [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (left : Left) (right : Right) :
    ConversionOutcome result :=
  Conversion.quantizePrepared context <|
    Conversion.prepareBinary (· * ·)
      (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)

/-- Multiply finite values exactly and quantize once using the destination's canonical context. -/
@[inline] def mulAs
    [Mul Exact] [quantizer : Quantizer result Exact]
    [defaults : DefaultQuantizer result Exact]
    (left : Left) (right : Right) : ConversionOutcome result :=
  mulAsWith defaults.defaultContext left right

/-- Divide finite values exactly and quantize once into `result` under explicit context. -/
@[inline] def divAsWith
    [Zero Exact] [ExactZero Exact] [Div Exact]
    [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (left : Left) (right : Right) :
    ConversionOutcome result :=
  Conversion.quantizePrepared context <|
    Conversion.prepareDiv (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)

/-- Divide finite values exactly and quantize once using the destination's canonical context. -/
@[inline] def divAs
    [Zero Exact] [ExactZero Exact] [Div Exact]
    [quantizer : Quantizer result Exact]
    [defaults : DefaultQuantizer result Exact]
    (left : Left) (right : Right) : ConversionOutcome result :=
  divAsWith defaults.defaultContext left right

end Binary

/--
Compute finite `left * right + addend` exactly and quantize once into `result`.

The exact product is added to `addend` under the context's cancellation-sign rule before the
destination quantizer runs.
-/
@[inline] def fmaAsWith {Left : Type u} {Right : Type v} {Addend : Type w}
    {result : Type x} {LeftExact : Type y} {RightExact : Type z}
    {AddendExact : Type a} {Exact : Type b}
    [ExactDecoder Left LeftExact] [ExactMap LeftExact Exact]
    [ExactDecoder Right RightExact] [ExactMap RightExact Exact]
    [ExactDecoder Addend AddendExact] [ExactMap AddendExact Exact]
    [Mul Exact] [Add Exact] [quantizer : Quantizer result Exact]
    (context : quantizer.Context) (left : Left) (right : Right) (addend : Addend) :
    ConversionOutcome result :=
  Conversion.quantizePrepared context <|
    Conversion.prepareFmaWith (quantizer.addExact context)
      (ExactDecoder.decodeTo left) (ExactDecoder.decodeTo right)
      (ExactDecoder.decodeTo addend)

/-- Fused multiply-add using the destination's canonical quantization context. -/
@[inline] def fmaAs {Left : Type u} {Right : Type v} {Addend : Type w}
    {result : Type x} {LeftExact : Type y} {RightExact : Type z}
    {AddendExact : Type a} {Exact : Type b}
    [ExactDecoder Left LeftExact] [ExactMap LeftExact Exact]
    [ExactDecoder Right RightExact] [ExactMap RightExact Exact]
    [ExactDecoder Addend AddendExact] [ExactMap AddendExact Exact]
    [Mul Exact] [Add Exact] [quantizer : Quantizer result Exact]
    [defaults : DefaultQuantizer result Exact]
    (left : Left) (right : Right) (addend : Addend) : ConversionOutcome result :=
  fmaAsWith defaults.defaultContext left right addend

end ExecFloat
end FloatLib.Floats
