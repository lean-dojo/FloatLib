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
`ConversionOutcome` retains the resulting value and flags, or the reason conversion failed, and
`#eval` shows it as `.success v { inexact := true }` or `.failure .outOfRange`, with only the
raised flags. `RoundingModes` gives the types of a conversion's `(mode := ...)` and
`(context := ...)` options, the rounding direction and a policy without one, and combines them into
the quantizer's context. `ModeContext` supplies the policy a call uses when it names none.

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
  deriving DecidableEq

/-- `#eval` writes a position with a leading dot, as `.source` or `.operand 2`. -/
instance : Repr InputPosition where
  reprPrec position prec :=
    match position with
    | .source => reprConstructor "source" [] prec
    | .left => reprConstructor "left" [] prec
    | .right => reprConstructor "right" [] prec
    | .addend => reprConstructor "addend" [] prec
    | .operand index => reprConstructor "operand" [repr index] prec

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
  deriving DecidableEq

/--
`#eval` writes a failure with leading dots and names the sign of an infinity, as
`.infinity .source (negative := false)`, `.exceptional .left .nan` or `.outOfRange`.
-/
instance : Repr ConversionFailure where
  reprPrec failure prec :=
    match failure with
    | .infinity position negative =>
        reprConstructor "infinity" [reprArg position, reprNamedArg "negative" (repr negative)] prec
    | .exceptional position value =>
        reprConstructor "exceptional" [reprArg position, reprArg value] prec
    | .divisionByZero => reprConstructor "divisionByZero" [] prec
    | .outOfRange => reprConstructor "outOfRange" [] prec
    | .unsupportedPolicy => reprConstructor "unsupportedPolicy" [] prec

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
  deriving DecidableEq, Inhabited

/-- `#eval` lists only the raised flags, as `{ inexact := true, overflow := true }`, and shows `{}`
when none is raised. -/
instance : Repr ConversionStatus where
  reprPrec flags _ :=
    reprFlags
      [("inexact", flags.inexact), ("overflow", flags.overflow), ("underflow", flags.underflow),
        ("saturated", flags.saturated), ("wrapped", flags.wrapped),
        ("mappedSpecial", flags.mappedSpecial), ("invalid", flags.invalid)]

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
  deriving DecidableEq

/--
`#eval` writes `.success v` followed by the raised flags, which it leaves out when none is raised,
or `.failure reason`. The value prints as its type displays it, so this is text to read, not a
serialization. An overflow to an IEEE infinity shows as
`.success inf { inexact := true, overflow := true }`.
-/
instance {α : Type u} [Repr α] : Repr (ConversionOutcome α) where
  reprPrec outcome prec :=
    match outcome with
    | .success value status =>
        reprConstructor "success" (reprArg value :: if status = {} then [] else [reprArg status])
          prec
    | .failure reason => reprConstructor "failure" [reprArg reason] prec

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
The `mode` and `context` options of conversions into `Destination`. `Mode` is the type of the
rounding direction, and `default` is the direction of a call that names none. `Policy` is the type
of `context`, every other destination policy, and `withMode` combines a direction and a policy
into the quantizer's context.

A policy has no direction, so the mode decides it. A conversion runs the destination quantizer in
`withMode mode context`, whether the caller passes `context` or the call uses the canonical
policy. Binary and nominal static-byte destinations take a `Numerics.RoundingMode`, nearest-even
by default, and the binary `Conversion.Policy`, whose `entropy` feeds `.stochastic`. P3109
destinations take a P3109 `RoundingMode` and a `SaturationMode`. A destination without selectable
directions, such as a posit, falls back to the mode type `NoRoundingDirection`.
-/
class RoundingModes (Destination : Type u) (Exact : outParam (Type v))
    [quantizer : Quantizer Destination Exact] (Mode : outParam Type) where
  /-- The destination's policies other than the rounding direction: the type of `context`. -/
  Policy : Type
  /-- The direction used when a call names no `mode`. -/
  default : Mode
  /-- The quantizer context that rounds in direction `mode` under `policy`. -/
  withMode : Mode → Policy → quantizer.Context

/--
The mode type of a destination without selectable rounding directions. Its one value is the mode
of every conversion into such a destination.

Naming a direction for such a destination is an error rather than an ignored option.
`(mode := .down)` is looked up in this type and fails as the unknown constant
`NoRoundingDirection.down`, and a mode of another type, such as an `IEEERoundingMode` variable, has
no `RoundingModes` instance for the destination.
-/
structure NoRoundingDirection where
  deriving DecidableEq, Repr, Inhabited

/--
A destination without selectable rounding directions has the single mode of `NoRoundingDirection`,
and its policy is the whole quantizer context.
-/
instance (priority := low) RoundingModes.noRoundingDirection {Destination : Type u}
    {Exact : Type v} [quantizer : Quantizer Destination Exact] :
    RoundingModes Destination Exact NoRoundingDirection where
  Policy := quantizer.Context
  default := {}
  withMode _ context := context

/--
The canonical policy of a destination, used by a conversion or mixed operation that names no
`context`. The call's `mode` gives the rounding direction.
-/
class DefaultQuantizer (Destination : Type u) (Exact : outParam (Type v))
    [Quantizer Destination Exact] {Mode : Type} [modes : RoundingModes Destination Exact Mode] where
  /-- Policy used by a conversion that names no `context`. -/
  defaultContext : modes.Policy

/--
The type of the `context` option of conversions into `Destination`, the destination's
`RoundingModes.Policy`.

Conversions take `(context : ContextFor target mode := ...)`. The `mode` index does not change the
type: it is there so that the default value can find `ModeContext target mode`. A caller's policy
of type `RoundingModes.Policy target` fits because the two types are definitionally equal.
-/
abbrev ContextFor (Destination : Type u) {Exact : Type v}
    [Quantizer Destination Exact] {Mode : Type} [modes : RoundingModes Destination Exact Mode]
    (_mode : Mode) : Type :=
  modes.Policy

/--
The policy a conversion uses when it names no `context`.

`ModeContext.canonical` gives every destination with a `DefaultQuantizer` its canonical policy,
whatever the mode. A destination without a canonical policy, such as a shared-scale block, has no
instance and needs a `context` argument.
-/
class ModeContext (Destination : Type u) (Exact : outParam (Type v))
    [Quantizer Destination Exact] {Mode : Type} [RoundingModes Destination Exact Mode]
    (mode : Mode) where
  /-- The policy used for a call with this `mode` and no `context`. -/
  context : ContextFor Destination mode

/-- A destination with a canonical policy uses it for every mode. -/
@[inline] instance (priority := low) ModeContext.canonical {Destination : Type u} {Exact : Type v}
    [Quantizer Destination Exact] {Mode : Type} [RoundingModes Destination Exact Mode]
    [defaults : DefaultQuantizer Destination Exact] (mode : Mode) :
    ModeContext Destination Exact mode where
  context := defaults.defaultContext

end ExecFloat
end FloatLib.Floats
