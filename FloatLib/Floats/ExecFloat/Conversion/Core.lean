/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Spec
public import FloatLib.Numerics.Exact.Dyadic.Basic
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Core conversion capabilities and outcomes

A source's `ExactDecoder` gives its exact value. An `ExactMap` embeds that value into the
destination's exact domain, and a `Quantizer` rounds it under the policy of its context.
`ConversionOutcome` retains the resulting value and flags, or the reason conversion failed.
`RoundingModes` and `ModeContext` give the type of a conversion's `(mode := ...)` option and the
destination context each mode selects.

`Conversion.Runtime` has the entry points, and `Conversion.Proof` has their correctness theorems
and the laws for composing outcomes.
-/

@[expose] public section

namespace FloatLib.Floats
namespace ExecFloat

open FloatLib.Numerics

universe u v

/-- Location of an input that prevented a conversion or mixed operation. -/
inductive InputPosition where
  /-- The sole input of a conversion. -/
  | source
  /-- The left input of a binary or fused operation. -/
  | left
  /-- The right input of a binary or fused operation. -/
  | right
  /-- The third input of a fused multiply-add. -/
  | addend
  /-- A zero-based input of a user-defined exact expression. -/
  | operand (index : Nat)
  deriving DecidableEq, Repr

/-- Why an explicit conversion or mixed-format operation produced no destination value. -/
inductive ConversionFailure where
  /-- An infinity reached an operation that requires an ordinary finite input. -/
  | infinity (position : InputPosition) (negative : Bool)
  /-- An exceptional value reached an operation that requires an ordinary finite input. -/
  | exceptional (position : InputPosition) (value : ExceptionalValue)
  /-- Exact division was requested with a zero denominator. -/
  | divisionByZero
  /-- A finite exact result is outside a destination configured to reject overflow. -/
  | outOfRange
  /-- The requested family-specific conversion policy is not implemented by the destination. -/
  | unsupportedPolicy
  deriving DecidableEq, Repr

/--
An exact scalar computation that may reject a non-finite input or an undefined operation.

Successful expressions contain an unrounded value in the destination's exact domain. Applying
`roundOnce` quantizes the result once. The `Except` alias supports ordinary `do` notation and stops
at the first failure.
-/
abbrev ExactExpression (Exact : Type u) :=
  Except ConversionFailure Exact

/--
Representation-independent information about a successful quantization.

Flags describe one conversion. `saturated` and `wrapped` distinguish clamping from modular
reduction, and either can also be `inexact`. Composing successful outcomes with `bind` combines
their flags with Boolean OR.
-/
structure ConversionStatus where
  /-- The stored destination does not denote the exact finite input. -/
  inexact : Bool := false
  /-- The rounded result did not fit the destination's finite range. Binary destinations set this
  after rounding, in the IEEE 754 sense. Each quantizer documents its own rule. -/
  overflow : Bool := false
  /-- The result was tiny. Binary destinations use the IEEE 754 rule, tiny after rounding and
  inexact. P3109 reports a nonzero exact input below its least positive datum. -/
  underflow : Bool := false
  /-- The result was clamped to a finite endpoint. -/
  saturated : Bool := false
  /-- The result was reduced modulo a bounded storage width. -/
  wrapped : Bool := false
  /-- A source infinity or exceptional value was mapped to another value class. -/
  mappedSpecial : Bool := false
  /-- The conversion signaled invalid operation. Binary destinations raise it for a signaling NaN
  source, as IEEE 754 §7.2 requires. -/
  invalid : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace ConversionStatus

/-- Combine the flags raised by two successful conversion steps. -/
@[inline] def merge (first second : ConversionStatus) : ConversionStatus where
  inexact := first.inexact || second.inexact
  overflow := first.overflow || second.overflow
  underflow := first.underflow || second.underflow
  saturated := first.saturated || second.saturated
  wrapped := first.wrapped || second.wrapped
  mappedSpecial := first.mappedSpecial || second.mappedSpecial
  invalid := first.invalid || second.invalid

end ConversionStatus

/-- Result of an explicit conversion or destination-driven mixed operation. -/
inductive ConversionOutcome (α : Type u) where
  /-- A destination value together with conversion status. -/
  | success (value : α) (status : ConversionStatus := {})
  /-- A conversion rejected by its policy or by finite-only mixed arithmetic. -/
  | failure (reason : ConversionFailure)
  deriving DecidableEq, Repr

namespace ConversionOutcome

variable {α : Type u} {β : Type v}

/-- Transform a successful value while preserving status and failure information. -/
@[inline] def map (f : α → β) : ConversionOutcome α → ConversionOutcome β
  | .success value status => .success (f value) status
  | .failure reason => .failure reason

/--
Continue from a successful value, accumulating status from both successful steps.

A failure short-circuits unchanged. Because `ConversionOutcome.failure` does not carry status,
flags from an earlier success are unavailable when a later step fails.
-/
@[inline] def bind (outcome : ConversionOutcome α)
    (next : α → ConversionOutcome β) : ConversionOutcome β :=
  match outcome with
  | .success value status =>
      match next value with
      | .success nextValue nextStatus =>
          .success nextValue (status.merge nextStatus)
      | .failure reason => .failure reason
  | .failure reason => .failure reason

/-- Extract a successful destination value. -/
@[inline] def value? : ConversionOutcome α → Option α
  | .success value _ => some value
  | .failure _ => none

/-- Extract status from a successful conversion. -/
@[inline] def status? : ConversionOutcome α → Option ConversionStatus
  | .success _ status => some status
  | .failure _ => none

/-- Extract the reason for a failed conversion. -/
@[inline] def failure? : ConversionOutcome α → Option ConversionFailure
  | .success _ _ => none
  | .failure reason => some reason

end ConversionOutcome

/--
Executable exact interpretation of a source value.

`Exact` is an output parameter so the source type selects its canonical executable exact domain.
For example, configured binary sources select `SignedRat` to retain signed zero, posit sources
select `Rat`, and a shared-scale block may select `Vector Rat lanes`.
-/
class ExactDecoder (Source : Type u) (Exact : outParam (Type v)) where
  /-- Decode every source value, retaining infinity and exceptional observations. -/
  decode : Source → NumericalValue Exact

namespace ExactDecoder

/-- Natural numbers enter explicit conversion as exact finite natural values. -/
instance natural : ExactDecoder Nat Nat where
  decode value := .finite value

/-- Integers enter explicit conversion as exact finite integer values. -/
instance integer : ExactDecoder Int Int where
  decode value := .finite value

/-- Rationals enter explicit conversion without an intermediate floating-point approximation. -/
instance rational : ExactDecoder Rat Rat where
  decode value := .finite value

/-- Dyadic values enter explicit conversion with their exact significand and binary exponent. -/
instance dyadic : ExactDecoder FloatLib.Numerics.Dyadic FloatLib.Numerics.Dyadic where
  decode value := .finite value

end ExactDecoder

/--
Context-indexed quantization capability for one destination value type.

Its specification is relational, so stochastic, state-indexed and otherwise nondeterministic
mathematics stay expressible even when `run` chooses one executable result.

`Exact` is an output parameter, so a destination has one canonical mathematical input domain.
Alternative execution backends must refine that semantics and keep the domain users see. Sources
with a different exact domain reach it through an `ExactMap`.

Mixed addition and subtraction also consult this context before quantization. The default
operations are those of `Exact`, and a signed-zero domain can refine the sign of an exact
cancellation without changing its numerical value. Multiplication and division use the operations
of the exact domain.

`correct` relates `run` to `spec` and does not constrain these arithmetic hooks, so a family
proves separately that its hooks keep the numerical sum and difference. The generic prepared-spec
theorems compose quantization with the supplied hooks, and an arithmetic correctness result also
needs those preservation lemmas, as the binary instances supply.

What `spec` says is up to the family. Choosing `Spec.ofFunction run` makes `correct` reflexive and
gives no rounding property of its own. A family contract can expose denotation, coefficient or
policy predicates while keeping full output and status equality, and the generic conversion
theorems transport the clauses that the installed relation contains and no others.
-/
class Quantizer (Destination : Type u) (Exact : outParam (Type v)) where
  /--
  Family-specific context, such as rounding policy, entropy, overflow rule, or block exponent.
  -/
  Context : Type
  /-- Executable quantizer. -/
  run : Context → NumericalValue Exact → ConversionOutcome Destination
  /-- Mathematical relation implemented by `run`. -/
  spec :
    Quantization.Spec Context (NumericalValue Exact) (ConversionOutcome Destination)
  /-- The executable quantizer always chooses a result permitted by `spec`. -/
  correct : spec.Implements run
  /--
  Exact addition under the destination context, including any direction-dependent zero sign.

  A family overriding this operation must retain the numerical sum in its exact domain.
  -/
  addExact : [Add Exact] → Context → Exact → Exact → Exact := fun _ left right => left + right
  /--
  Exact subtraction under the destination context, including any direction-dependent zero sign.

  A family overriding this operation must retain the numerical difference in its exact domain.
  -/
  subExact : [Sub Exact] → Context → Exact → Exact → Exact := fun _ left right => left - right

/--
The canonical context used when a conversion or mixed operation names neither `mode` nor
`context`.
-/
class DefaultQuantizer (Destination : Type u) (Exact : outParam (Type v))
    [Quantizer Destination Exact] where
  /-- Context selected by a conversion that names neither `mode` nor `context`. -/
  defaultContext : Quantizer.Context Destination

/--
The type of the `mode` option of conversions into `Destination`, with the direction used when a
call names none.

Binary destinations use `IEEERoundingMode`, nearest-even by default. A destination without
directed conversion falls back to `RoundingModes.unit`, so naming a direction for it is a type
error rather than an ignored option.
-/
class RoundingModes (Destination : Type u) (Mode : outParam Type) where
  /-- The direction used when a call names no `mode`. -/
  default : Mode

/-- A destination without selectable rounding directions has the single mode `()`. -/
instance (priority := low) RoundingModes.unit {Destination : Type u} :
    RoundingModes Destination Unit where
  default := ()

/--
The context type of `Destination`, indexed by the `mode` that selects its default.

Conversions take `(context : ContextFor target mode := ...)`. The index lets the default value
find `ModeContext target mode`, and a caller's context of type `Quantizer.Context target` fits
because the two types are definitionally equal.
-/
abbrev ContextFor (Destination : Type u) {Exact : Type v}
    [quantizer : Quantizer Destination Exact] {Mode : Type} (_mode : Mode) : Type :=
  quantizer.Context

/--
The destination context that a conversion's `mode` option selects when it names no `context`.

`ModeContext.canonical` gives the canonical context to every destination with a
`DefaultQuantizer` and no rounding directions. Binary destinations install an instance for every
direction. A destination without a canonical context, such as a shared-scale block, has no
instance and needs a `context` argument.
-/
class ModeContext (Destination : Type u) (Exact : outParam (Type v))
    [Quantizer Destination Exact] {Mode : Type} (mode : Mode) where
  /-- The context that rounds in direction `mode`. -/
  context : ContextFor Destination mode

/-- A destination without rounding directions uses its canonical context for its one mode. -/
@[inline] instance ModeContext.canonical {Destination : Type u} {Exact : Type v}
    [Quantizer Destination Exact] [defaults : DefaultQuantizer Destination Exact] (mode : Unit) :
    ModeContext Destination Exact mode where
  context := defaults.defaultContext

end ExecFloat
end FloatLib.Floats
